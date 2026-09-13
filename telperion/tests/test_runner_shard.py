"""Tests for the multi-node campaign runner (C2) + lake package sharding (B2).

C2: height-sharded append-only journals + a merge tool that rebuilds a unified
`campaign_state.json`-shaped view, asserting agreement on any tag overlap and
unioning per-shard stretch caches (Platt queries ~0.3 s each -- must never be
lost).  B2: per-block lake package codegen validated by generated TEXT (this
worktree has no `.lake` cache, so no build).  conjecture1_proved = False.

The zeta_zero_localization example dir is added to sys.path so `campaign` and
`campaign_shard` import; no flint / no Lean build is exercised.
"""
import argparse
import json
import sys
from pathlib import Path

import pytest

_EX = (Path(__file__).resolve().parents[1]
       / "examples" / "zeta_zero_localization")
sys.path.insert(0, str(_EX))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import campaign as C          # noqa: E402
import campaign_shard as S    # noqa: E402


@pytest.fixture(autouse=True)
def _hermetic(tmp_path, monkeypatch):
    """Redirect all shared production state to tmp so no test writes it.

    `band_module`/`band_box` (exercised by the B2 codegen path) call
    `stretch_box`, which memoizes Platt lookups into `edge_stretch.json` -- the
    LIVE shared cache.  Point it (and the default STATE/journal dir) at tmp so
    the suite is hermetic and never churns the root-owned campaign state."""
    monkeypatch.setattr(C, "_STRETCH_CACHE_FILE", tmp_path / "edge_stretch.json")
    monkeypatch.setattr(C, "_stretch_cache", None)
    monkeypatch.setattr(C, "STATE", tmp_path / "campaign_state.json")
    monkeypatch.setattr(S, "STATE_DIR", tmp_path / "state")


def _rec(den, lo, hi, status="ok", n=43, ts=1.0, **extra):
    r = {"status": status, "ts": ts}
    if status == "ok":
        r["n"] = n
    else:
        r["error"] = extra.pop("error", "refused")
    r.update(extra)
    return S.journal_record(den, lo, hi, r)


# --- journal: append / fold / resume --------------------------------------------

def test_journal_append_and_fold(tmp_path):
    jp = S.journal_path(25000, 26000, tmp_path)
    S.append_journal(jp, _rec(4_000_000, 25000, 25040, n=43, ts=1.0))
    S.append_journal(jp, _rec(4_000_000, 25040, 25080, n=41, ts=2.0))
    folded = S.read_journal(jp)
    assert len(folded) == 2
    tag = C.band_tag(4_000_000, 25000, 25040)
    assert folded[tag]["status"] == "ok" and folded[tag]["n"] == 43


def test_journal_resume_keeps_latest_ts(tmp_path):
    # A refused band re-emitted `ok` at a higher density (later ts) must win.
    jp = S.journal_path(25000, 26000, tmp_path)
    S.append_journal(jp, _rec(4_000_000, 25040, 25080, status="refused",
                              error="close pair", ts=1.0))
    S.append_journal(jp, _rec(4_000_000, 25040, 25080, n=44, ts=9.0, density=4.0))
    folded = S.read_journal(jp)
    tag = C.band_tag(4_000_000, 25040, 25080)
    assert folded[tag]["status"] == "ok" and folded[tag]["n"] == 44


def test_journal_torn_final_line_tolerated(tmp_path):
    # A crash mid-append leaves a partial final line: dropped on read, earlier
    # records intact.  A torn NON-final line is a hard error (data corruption).
    jp = S.journal_path(25000, 26000, tmp_path)
    S.append_journal(jp, _rec(4_000_000, 25000, 25040, n=43, ts=1.0))
    with open(jp, "a", encoding="utf-8") as f:
        f.write("{partial-json")
    folded = S.read_journal(jp)
    assert len(folded) == 1


def test_journal_torn_interior_line_raises(tmp_path):
    jp = S.journal_path(25000, 26000, tmp_path)
    with open(jp, "w", encoding="utf-8") as f:
        f.write("{bad}\n")
        f.write(json.dumps(_rec(4_000_000, 25000, 25040)) + "\n")
    with pytest.raises(json.JSONDecodeError):
        S.read_journal(jp)


def test_journal_record_is_self_describing():
    r = _rec(4_000_000, 25000, 25040, n=43)
    assert r["tag"] == C.band_tag(4_000_000, 25000, 25040)
    assert r["den"] == 4_000_000 and r["lo"] == 25000 and r["hi"] == 25040
    assert "ts" in r


# --- merge: union + conflict assert ---------------------------------------------

def test_merge_disjoint_shards(tmp_path):
    jp1 = S.journal_path(25000, 26000, tmp_path)
    jp2 = S.journal_path(26000, 27000, tmp_path)
    S.append_journal(jp1, _rec(4_000_000, 25000, 25040, n=43))
    S.append_journal(jp2, _rec(4_000_000, 26000, 26040, n=43))
    merged = S.merge_journals([jp1, jp2])
    assert len(merged) == 2


def test_merge_overlap_identical_decision_ok(tmp_path):
    # Same band in two shards, same certified n, different run-metadata: allowed.
    jp1 = S.journal_path(25000, 26000, tmp_path)
    jp2 = S.journal_path(25500, 26500, tmp_path)
    S.append_journal(jp1, _rec(4_000_000, 25500, 25540, n=43, secs=2.0, ts=1.0))
    S.append_journal(jp2, _rec(4_000_000, 25500, 25540, n=43, secs=9.0, ts=2.0))
    merged = S.merge_journals([jp1, jp2])
    assert len(merged) == 1
    # later ts wins the metadata
    assert merged[C.band_tag(4_000_000, 25500, 25540)]["secs"] == 9.0


def test_merge_overlap_conflicting_n_aborts(tmp_path):
    jp1 = S.journal_path(25000, 26000, tmp_path)
    jp2 = S.journal_path(25500, 26500, tmp_path)
    S.append_journal(jp1, _rec(4_000_000, 25500, 25540, n=43, ts=1.0))
    S.append_journal(jp2, _rec(4_000_000, 25500, 25540, n=99, ts=2.0))
    with pytest.raises(AssertionError, match="disagree on a certified count"):
        S.merge_journals([jp1, jp2])


def test_merge_status_conflict_aborts(tmp_path):
    jp1 = S.journal_path(1, 2, tmp_path)
    jp2 = S.journal_path(2, 3, tmp_path)
    S.append_journal(jp1, _rec(4_000_000, 25500, 25540, n=43, ts=1.0))
    S.append_journal(jp2, _rec(4_000_000, 25500, 25540, status="refused", ts=2.0))
    with pytest.raises(AssertionError):
        S.merge_journals([jp1, jp2])


# --- stretch cache union --------------------------------------------------------

def test_stretch_union(tmp_path):
    f1 = tmp_path / "shard_a.edge_stretch.json"
    f2 = tmp_path / "shard_b.edge_stretch.json"
    f1.write_text(json.dumps({"down:25000": "24999", "up:26000": "26001"}))
    f2.write_text(json.dumps({"down:25000": "24999", "up:26500": "26501"}))
    u = S.merge_stretch_caches([f1, f2], tmp_path / "nope.json")
    assert u == {"down:25000": "24999", "up:26000": "26001", "up:26500": "26501"}


def test_stretch_union_conflict_aborts(tmp_path):
    f1 = tmp_path / "shard_a.edge_stretch.json"
    f2 = tmp_path / "shard_b.edge_stretch.json"
    f1.write_text(json.dumps({"down:25000": "24999"}))
    f2.write_text(json.dumps({"down:25000": "88888"}))
    with pytest.raises(AssertionError, match="stretch cache conflict"):
        S.merge_stretch_caches([f1, f2], tmp_path / "nope.json")


# --- merge-shards CLI: into legacy state ----------------------------------------

def test_merge_shards_cli_into_legacy(tmp_path):
    into = tmp_path / "campaign_state.json"
    live_tag = C.band_tag(4_000_000, 25000, 25040)
    into.write_text(json.dumps({"bands": {live_tag: {"status": "ok", "n": 43}}}))
    jp = S.journal_path(26000, 27000, tmp_path)
    S.append_journal(jp, _rec(4_000_000, 26000, 26040, n=43, ts=5.0))
    ns = argparse.Namespace(state_dir=str(tmp_path), journals=None,
                            into=str(into), no_stretch_write=True)
    assert S.cmd_merge_shards(ns) == 0
    st = json.loads(into.read_text())
    assert set(st["bands"]) == {live_tag, C.band_tag(4_000_000, 26000, 26040)}


def test_merge_shards_cli_conflict_leaves_live_untouched(tmp_path):
    into = tmp_path / "campaign_state.json"
    live_tag = C.band_tag(4_000_000, 25000, 25040)
    into.write_text(json.dumps({"bands": {live_tag: {"status": "ok", "n": 43}}}))
    jp = S.journal_path(25000, 26000, tmp_path)
    S.append_journal(jp, _rec(4_000_000, 25000, 25040, n=777, ts=9.0))
    ns = argparse.Namespace(state_dir=str(tmp_path), journals=None,
                            into=str(into), no_stretch_write=True)
    assert S.cmd_merge_shards(ns) == 1
    st = json.loads(into.read_text())
    assert st["bands"][live_tag]["n"] == 43  # untouched


def test_merge_shards_cli_no_journals(tmp_path):
    ns = argparse.Namespace(state_dir=str(tmp_path), journals=None,
                            into=str(tmp_path / "s.json"), no_stretch_write=True)
    assert S.cmd_merge_shards(ns) == 1


# --- B2 lake package sharding: codegen goldens ----------------------------------

def test_lake_block_top():
    assert C.lake_block_top(24999) == 25000
    assert C.lake_block_top(25000) == 25000
    assert C.lake_block_top(25001) == 50000


def test_block_lakefile_golden():
    txt = C.emit_block_lakefile(25000, ["RHInBoxT_x_1_41", "AllZeros_h25000"])
    assert 'name = "ZetaBands_h25000"' in txt
    assert 'defaultTargets = ["RHInBoxT_x_1_41", "AllZeros_h25000"]' in txt
    # requires the shared core + mathlib + ZeroFreeBridge
    assert 'name = "zzl_core"\npath = "../zzl_core"' in txt
    assert 'name = "mathlib"' in txt and f'rev = "{C.MATHLIB_REV}"' in txt
    assert 'name = "ZeroFreeBridge"' in txt
    # one lean_lib stanza per module, no others
    assert txt.count("[[lean_lib]]") == 2
    assert '[[lean_lib]]\nname = "RHInBoxT_x_1_41"' in txt


def test_umbrella_lakefile_golden():
    txt = C.emit_umbrella_lakefile([50000, 25000])
    assert 'name = "zzl_umbrella"' in txt
    # sorted block requires
    i25 = txt.index('name = "ZetaBands_h25000"')
    i50 = txt.index('name = "ZetaBands_h50000"')
    assert i25 < i50
    assert 'name = "zzl_core"\npath = "zzl_core"' in txt
    # umbrella owns no lean_lib of its own
    assert "[[lean_lib]]" not in txt


def test_register_lakefile_sharded_routes_and_creates_packages(tmp_path):
    lean_dir = tmp_path / "lean"
    lean_dir.mkdir()
    # a band range wholly inside one block; segments too.  lake_block_top rounds
    # a module's TOP height UP to the next 25000-multiple, so bands ending in
    # (25000, 50000] route to block 50000.
    added = C.register_lakefile_sharded(25000, 25200, segments=True,
                                        lean_dir=lean_dir)
    assert set(added) == {50000}
    pkg = lean_dir / "ZetaBands_h50000" / "lakefile.toml"
    assert pkg.exists()
    txt = pkg.read_text()
    # all routed modules present as lean_lib
    for m in added[50000]:
        assert f'name = "{m}"' in txt
    # umbrella written requiring the block
    umb = (lean_dir / "lakefile.umbrella.toml").read_text()
    assert 'name = "ZetaBands_h50000"' in umb


def test_register_lakefile_sharded_idempotent(tmp_path):
    lean_dir = tmp_path / "lean"
    lean_dir.mkdir()
    C.register_lakefile_sharded(25000, 25200, segments=True, lean_dir=lean_dir)
    pkg = lean_dir / "ZetaBands_h50000" / "lakefile.toml"
    before = pkg.read_text()
    added2 = C.register_lakefile_sharded(25000, 25200, segments=True,
                                         lean_dir=lean_dir)
    # nothing new to add the second time
    assert sum(len(v) for v in added2.values()) == 0
    assert pkg.read_text() == before


def test_register_lakefile_sharded_multi_block(tmp_path):
    lean_dir = tmp_path / "lean"
    lean_dir.mkdir()
    # a range crossing the 25000/50000 block boundary
    added = C.register_lakefile_sharded(24800, 25200, segments=True,
                                        lean_dir=lean_dir)
    # bands with hi <= 25000 -> block 25000; hi > 25000 -> block 50000
    assert (lean_dir / "ZetaBands_h25000" / "lakefile.toml").exists()
    assert (lean_dir / "ZetaBands_h50000" / "lakefile.toml").exists()
    umb = (lean_dir / "lakefile.umbrella.toml").read_text()
    assert 'name = "ZetaBands_h25000"' in umb
    assert 'name = "ZetaBands_h50000"' in umb


# --- shard planning: disjointness of aligned blocks -----------------------------

def test_aligned_shards_have_disjoint_band_tags():
    # Two block-aligned shards share no band tag (band edges never straddle a
    # 1000-block boundary) -- so the normal case has NO merge overlap at all.
    b1 = {C.band_tag(*b) for b in C.plan_bands(25000, 26000)}
    b2 = {C.band_tag(*b) for b in C.plan_bands(26000, 27000)}
    assert b1 and b2 and not (b1 & b2)
