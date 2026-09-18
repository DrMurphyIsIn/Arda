"""Multi-node campaign runner: height-sharded journals + merge (PROGRAM ANDÚRIL C2).

Imports the single-node band planner/driver from `campaign.py` and adds the
scale-out substrate:

  * `--shard FROM TO` emit-bands writing an APPEND-ONLY journal
    `state/shard_<FROM>_<TO>.jsonl` (one record per band completion) instead of
    rewriting the whole `campaign_state.json` per band (the O(N^2) fix);
  * `merge-shards` rebuilding a unified `campaign_state.json`-shaped view from
    journals, asserting identical records on any tag overlap (safety net for
    misconfigured overlapping ranges);
  * stretch-cache union so no Platt query (~0.3 s each) is ever lost.

Full backward compat: the legacy single-state mode in `campaign.py` is untouched
and remains the default runner.  See `telperion/docs/RUNNER_SHARD_DESIGN.md`.

    python3 campaign_shard.py shard-emit --from 25000 --to 26000 --jobs 8
    python3 campaign_shard.py merge-shards                 # -> campaign_state.json
    python3 campaign_shard.py merge-shards --into ~/arda-million/.../campaign_state.json

conjecture1_proved = False.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import campaign as C  # noqa: E402

HERE = Path(__file__).resolve().parent
STATE_DIR = HERE / "state"


# ---------------------------------------------------------------- journal

def journal_path(t_from: int, t_to: int, state_dir: Path | None = None) -> Path:
    d = state_dir or STATE_DIR
    return d / f"shard_{t_from}_{t_to}.jsonl"


def stretch_shard_path(t_from: int, t_to: int, state_dir: Path | None = None) -> Path:
    d = state_dir or STATE_DIR
    return d / f"shard_{t_from}_{t_to}.edge_stretch.json"


def journal_record(den: int, lo: int, hi: int, rec: dict) -> dict:
    """A self-describing journal line: the driver record + tag/edges + timestamp."""
    out = {"tag": C.band_tag(den, lo, hi), "den": den, "lo": lo, "hi": hi,
           "ts": rec.get("ts", time.time())}
    out.update({k: v for k, v in rec.items() if k != "ts"})
    return out


def append_journal(path: Path, record: dict) -> None:
    """Append one JSONL record.  Append-only: no whole-file rewrite (O(1) write).

    fsync so a crash cannot lose a committed band.  One line per record; a torn
    final line (partial write on crash) is dropped on read, not here."""
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(record, sort_keys=True) + "\n"
    with open(path, "a", encoding="utf-8") as f:
        f.write(line)
        f.flush()
        import os
        os.fsync(f.fileno())


def read_journal(path: Path) -> dict[str, dict]:
    """Fold a journal to the latest record per tag (max ts).

    A torn final line (crash mid-append) fails JSON parse and is dropped; only
    the last line can be torn (appends are line-atomic in practice, and we guard
    just the parse), so earlier records are always intact."""
    if not path.exists():
        return {}
    folded: dict[str, dict] = {}
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, ln in enumerate(lines):
        ln = ln.strip()
        if not ln:
            continue
        try:
            rec = json.loads(ln)
        except json.JSONDecodeError:
            if i == len(lines) - 1:
                # tolerated: torn final line from a crash mid-write
                continue
            raise
        tag = rec["tag"]
        prev = folded.get(tag)
        if prev is None or rec.get("ts", 0) >= prev.get("ts", 0):
            folded[tag] = rec
    return folded


# ---------------------------------------------------------------- shard-emit

def cmd_shard_emit(args) -> int:
    """Emit all bands in [FROM, TO) to an append-only shard journal.

    Resume-safe: reads its own journal, skips bands already `ok` (matching the
    legacy `emit-bands` skip logic but sourced from the journal)."""
    state_dir = Path(args.state_dir) if args.state_dir else STATE_DIR
    jpath = journal_path(args.t_from, args.t_to, state_dir)
    # Point the driver's stretch cache at this shard's own file so shards don't
    # contend on the global edge_stretch.json.  Merged back by merge-shards.
    if args.isolate_stretch:
        C._STRETCH_CACHE_FILE = stretch_shard_path(args.t_from, args.t_to, state_dir)
        C._stretch_cache = None  # force reload from the shard file

    bands = C.plan_bands(args.t_from, args.t_to)
    done = read_journal(jpath)
    force = getattr(args, "force", False)
    todo = []
    for den, lo, hi in bands:
        tag = C.band_tag(den, lo, hi)
        rec = done.get(tag)
        lean_file = C.LEAN_DIR / f"{C.band_module(den, lo, hi)}.lean"
        sidecar = lean_file.with_suffix(".cert.json")
        needs_gate = int(lo) >= C.TURING_FROM and not sidecar.exists()
        if (rec and rec.get("status") == "ok" and lean_file.exists()
                and not force and not needs_gate):
            continue
        todo.append((den, lo, hi))
    print(f"shard [{args.t_from},{args.t_to}): {len(bands)} bands planned, "
          f"{len(bands) - len(todo)} done, {len(todo)} to emit; jobs={args.jobs}")
    print(f"  journal: {jpath}")

    n_ok = n_fail = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(C.emit_one_band, den, lo, hi): (den, lo, hi)
                for den, lo, hi in todo}
        for fut in as_completed(futs):
            den, lo, hi = futs[fut]
            rec = fut.result()
            rec["ts"] = time.time()
            append_journal(jpath, journal_record(den, lo, hi, rec))
            if rec["status"] == "ok":
                n_ok += 1
                print(f"  [{n_ok + n_fail}/{len(todo)}] {C.band_tag(den, lo, hi)}: "
                      f"N={rec['n']} (density={rec['density']}, {rec['secs']}s)")
            else:
                n_fail += 1
                print(f"  [{n_ok + n_fail}/{len(todo)}] {C.band_tag(den, lo, hi)}: "
                      f"REFUSED -- {rec['error'][:200]}")
    print(f"shard-emit done: {n_ok} ok, {n_fail} refused")
    return 0 if n_fail == 0 else 1


# ---------------------------------------------------------------- merge

def _rec_decision(rec: dict) -> tuple:
    """The load-bearing part of a record for conflict detection: status + count.

    Run-metadata (secs, ts, density, prec) may legitimately differ between two
    emits of the same band; the certified `status`/`n` may NOT."""
    if rec.get("status") == "ok":
        return ("ok", rec.get("n"))
    return ("refused",)


def merge_journals(journals: list[Path]) -> dict[str, dict]:
    """Fold all journals, asserting agreement on any cross-journal tag overlap.

    Returns {tag: record}.  Raises AssertionError if two DIFFERENT journals
    disagree on a tag's certified decision (status/n)."""
    merged: dict[str, dict] = {}
    origin: dict[str, Path] = {}
    for jp in journals:
        folded = read_journal(jp)
        for tag, rec in folded.items():
            if tag in merged and origin[tag] != jp:
                d0, d1 = _rec_decision(merged[tag]), _rec_decision(rec)
                assert d0 == d1, (
                    f"merge conflict on band {tag}: {origin[tag].name} says "
                    f"{d0}, {jp.name} says {d1} -- two nodes disagree on a "
                    f"certified count; refusing to merge")
                # identical decision: keep the later ts
                if rec.get("ts", 0) > merged[tag].get("ts", 0):
                    merged[tag] = rec
            else:
                merged[tag] = rec
                origin[tag] = jp
    return merged


def merge_stretch_caches(shard_files: list[Path], base: Path) -> dict:
    """Union per-shard stretch caches into one dict; assert agreement on collisions.

    Stretch results are deterministic per edge, so any key present in two files
    must have the same value (idempotent boundary-edge pricing)."""
    out: dict[str, str] = {}
    src: dict[str, str] = {}
    files = list(shard_files)
    if base.exists():
        files = [base] + files
    for f in files:
        if not f.exists():
            continue
        data = json.loads(f.read_text())
        for k, v in data.items():
            if k in out:
                assert out[k] == v, (
                    f"stretch cache conflict on {k}: {out[k]!r} ({src[k]}) vs "
                    f"{v!r} ({f.name})")
            else:
                out[k] = v
                src[k] = f.name
    return out


def cmd_merge_shards(args) -> int:
    state_dir = Path(args.state_dir) if args.state_dir else STATE_DIR
    journals = ([Path(p) for p in args.journals] if args.journals
                else sorted(state_dir.glob("shard_*.jsonl")))
    if not journals:
        print(f"merge-shards: no journals found in {state_dir}", file=sys.stderr)
        return 1
    print(f"merge-shards: folding {len(journals)} journal(s)")
    try:
        merged = merge_journals(journals)
    except AssertionError as e:
        print(f"MERGE ABORTED: {e}", file=sys.stderr)
        return 1

    # union stretch caches (never lose a Platt query)
    stretch_files = sorted(state_dir.glob("shard_*.edge_stretch.json"))
    try:
        stretch = merge_stretch_caches(stretch_files, C._STRETCH_CACHE_FILE)
    except AssertionError as e:
        print(f"MERGE ABORTED (stretch): {e}", file=sys.stderr)
        return 1

    into = Path(args.into) if args.into else C.STATE
    # load existing legacy state and overlay, asserting against live records too
    if into.exists():
        st = json.loads(into.read_text())
        st.setdefault("bands", {})
    else:
        st = {"bands": {}}
    conflicts = 0
    for tag, rec in merged.items():
        live = st["bands"].get(tag)
        if live is not None and _rec_decision(live) != _rec_decision(rec):
            print(f"  CONFLICT vs live state on {tag}: {_rec_decision(live)} "
                  f"vs {_rec_decision(rec)}", file=sys.stderr)
            conflicts += 1
            continue
        # strip journal-only fields not present in legacy records? keep them --
        # legacy reader ignores extra keys; downstream reads status/n only.
        st["bands"][tag] = rec
    if conflicts:
        print(f"MERGE ABORTED: {conflicts} conflict(s) vs live state; "
              f"{into} untouched", file=sys.stderr)
        return 1

    # atomic write (tmp + replace), matching campaign.save_state
    tmp = into.with_suffix(into.suffix + ".tmp")
    tmp.parent.mkdir(parents=True, exist_ok=True)
    tmp.write_text(json.dumps(st, indent=1, sort_keys=True))
    tmp.replace(into)
    print(f"merged {len(merged)} band record(s) into {into} "
          f"({len(st['bands'])} total)")

    if stretch and not args.no_stretch_write:
        stmp = C._STRETCH_CACHE_FILE.with_suffix(".tmp")
        stmp.write_text(json.dumps(stretch, sort_keys=True))
        stmp.replace(C._STRETCH_CACHE_FILE)
        print(f"unioned stretch cache: {len(stretch)} edges -> "
              f"{C._STRETCH_CACHE_FILE.name}")
    return 0


# ---------------------------------------------------------------- migrate

def parse_tag(tag: str) -> tuple[int, str, str]:
    """Recover (den, lo, hi) from a band tag `1d{den}_{den-1}d{den}_{lo}_{hi}`.

    lo/hi may be integers or dyadics rendered `NdD` (see campaign.band_tag);
    returned as the strings campaign uses so a re-render round-trips."""
    parts = tag.split("_")
    # parts: [1d{den}, {den-1}d{den}, lo, hi]  (lo/hi never contain '_')
    den = int(parts[0].split("d")[1])
    lo, hi = parts[2], parts[3]
    return den, lo, hi


def cmd_migrate_to_journal(args) -> int:
    """Dump an existing legacy campaign_state.json's bands into ONE synthetic
    journal, so the live climb can switch to journal mode without losing history.

    Idempotent: re-running appends nothing new (read_journal folds by tag).  The
    synthetic records carry the legacy fields verbatim plus tag/den/lo/hi and a
    `ts` derived from position (monotone) so later real emits always supersede."""
    src = Path(args.state) if args.state else C.STATE
    if not src.exists():
        print(f"migrate: no state file at {src}", file=sys.stderr)
        return 1
    st = json.loads(src.read_text())
    bands = st.get("bands", {})
    state_dir = Path(args.state_dir) if args.state_dir else STATE_DIR
    jpath = (journal_path(args.t_from, args.t_to, state_dir)
             if args.t_from is not None and args.t_to is not None
             else state_dir / "shard_migrated.jsonl")

    already = read_journal(jpath)
    n_written = 0
    for i, (tag, rec) in enumerate(sorted(bands.items())):
        if tag in already:
            continue
        den, lo, hi = parse_tag(tag)
        out = {"tag": tag, "den": den, "lo": lo, "hi": hi,
               "ts": float(i)}  # position-derived; < any real emit's wall-clock ts
        out.update({k: v for k, v in rec.items() if k != "ts"})
        append_journal(jpath, out)
        n_written += 1
    print(f"migrate: {len(bands)} legacy band(s) -> {jpath}: "
          f"{n_written} written, {len(bands) - n_written} already present")
    return 0


# ---------------------------------------------------------------- main

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("shard-emit", help="emit bands to an append-only journal")
    p.add_argument("--from", dest="t_from", type=int, required=True)
    p.add_argument("--to", dest="t_to", type=int, required=True)
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--force", action="store_true")
    p.add_argument("--state-dir", default=None, help="journal dir (default: ./state)")
    p.add_argument("--isolate-stretch", action="store_true",
                   help="use a per-shard stretch cache (merge-shards unions it)")

    p = sub.add_parser("merge-shards", help="fold journals into a unified state")
    p.add_argument("--state-dir", default=None)
    p.add_argument("--journals", nargs="*", default=None,
                   help="explicit journal paths (default: all shard_*.jsonl)")
    p.add_argument("--into", default=None,
                   help="merge INTO this legacy state file (default: campaign_state.json)")
    p.add_argument("--no-stretch-write", action="store_true")

    p = sub.add_parser("migrate-to-journal",
                       help="dump legacy campaign_state.json bands into a journal")
    p.add_argument("--state", default=None,
                   help="legacy state file (default: campaign_state.json)")
    p.add_argument("--state-dir", default=None, help="journal dir (default: ./state)")
    p.add_argument("--from", dest="t_from", type=int, default=None,
                   help="name the journal shard_<from>_<to> (default: shard_migrated)")
    p.add_argument("--to", dest="t_to", type=int, default=None)

    args = ap.parse_args()
    return {"shard-emit": cmd_shard_emit,
            "merge-shards": cmd_merge_shards,
            "migrate-to-journal": cmd_migrate_to_journal}[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
