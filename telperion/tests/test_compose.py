"""The compositional judge (telperion.missions.compose): every check the peer governance review
of 2026-09-27 made a condition, as a test that FAILS when the check is removed.

The two fixtures under fixtures/compose/ are REAL part files from a local run (Comparator PASS,
ComposeInspect, lean4export sha256) of the h1000 segment and the implication; the other seven
segments are cloned from the h1000 one with the height substituted, which is what their real
parts look like (verified shape: type = the bare BandHyp constant, closure = that segment's
Arb4_H<H>* certificate modules).  Each negative test mutates exactly one field.

The same three negative controls were also run for real against Lean (see the PR): a tampered
hypothesis, an implication that imports and uses an edge module, a dropped hypothesis, plus an
alpha-renamed statement that changes the export bytes.  These tests pin the checks that caught them.
"""
import copy
import json
from pathlib import Path

import pytest

from telperion.missions import compose, judge_log
from telperion.missions.schema import ComposeSpec, ComparatorRecord, SchemaError, load_node

T = Path(__file__).resolve().parents[1]
FIX = Path(__file__).resolve().parent / "fixtures" / "compose"
NODE = "AND_ladder_h8000_kernel"
SPEC = load_node(T / "missions" / "anduril" / "nodes" / f"{NODE}.toml").compose


def _parts():
    seg = json.loads((FIX / f"{NODE}__seg_h1000.part.json").read_text())
    comp = json.loads((FIX / f"{NODE}__compose.part.json").read_text())
    out = [comp]
    for nm, stmt, _thm, _mod in SPEC.segments:
        p = copy.deepcopy(seg)
        h = nm[1:]                                    # "h3000" -> "3000"
        p["part"] = f"seg:{nm}"
        p["slug"] = compose.seg_slug(NODE, nm)
        p["inspect"]["theorem"] = compose.bridge(p["slug"])
        p["inspect"]["type_const"] = stmt
        p["inspect"]["closure_modules"] = [m.replace("H1000", f"H{h}").replace("h1000", f"h{h}")
                                           for m in seg["inspect"]["closure_modules"]]
        p["statement_exports"] = {stmt: comp["statement_exports"][stmt]}
        out.append(p)
    return out


def _by(parts, label):
    return next(p for p in parts if p["part"] == label)


def test_fixtures_are_real_and_agree_on_h1000():
    """The real seg_h1000 job and the real implication job exported AllZeros_h1000.BandHyp to
    the same bytes (and a third, independent export matched too, see the PR)."""
    seg = json.loads((FIX / f"{NODE}__seg_h1000.part.json").read_text())
    comp = json.loads((FIX / f"{NODE}__compose.part.json").read_text())
    s = "AllZeros_h1000.BandHyp"
    assert seg["statement_exports"][s] == comp["statement_exports"][s]
    assert seg["inspect"]["type_const"] == s
    assert comp["inspect"]["binders"][:8] == list(SPEC.segment_statements)
    assert comp["inspect"]["closure_modules"] == ["Arb4_Compose_h8000"]


def test_complete_honest_parts_compose():
    assert compose.verify(NODE, SPEC, _parts()) == []


def _fails(parts, needle):
    errs = compose.verify(NODE, SPEC, parts)
    assert errs, "the mutation was not caught"
    assert any(needle in e for e in errs), errs


# (a) identity --------------------------------------------------------------------------------

def test_a_segment_judged_a_different_type():
    ps = _parts(); _by(ps, "seg:h3000")["inspect"]["type_const"] = "AllZeros_h2000.BandHyp"
    _fails(ps, "not the bare constant")


def test_a_tampered_hypothesis_is_not_a_bare_constant():
    """Real NC 1: `(b_h1000 : BandHyp ∧ True)` -- the Comparator PASSED it; binders came back []."""
    ps = _parts(); _by(ps, "compose")["inspect"]["binders"] = []
    _fails(ps, "leading hypotheses")


def test_a_hypotheses_out_of_order():
    ps = _parts(); b = _by(ps, "compose")["inspect"]["binders"]; b[0], b[1] = b[1], b[0]
    _fails(ps, "in order")


def test_a_dropped_hypothesis():
    ps = _parts(); b = _by(ps, "compose")["inspect"]["binders"]; del b[0]
    _fails(ps, "leading hypotheses")


def test_a_export_bytes_differ():
    """Real NC 4: an alpha-renamed bound variable in BandHyp changed the implication-side hash."""
    ps = _parts()
    _by(ps, "compose")["statement_exports"]["AllZeros_h1000.BandHyp"] = \
        "0dd9163f82f2d8e993a6ecc355b6ee57b73151ad917a92bd529c1fbe90f207e8"
    _fails(ps, "exported differently")


def test_a_missing_export_hash():
    ps = _parts(); _by(ps, "seg:h5000")["statement_exports"] = {}
    _fails(ps, "no lean4export sha256")


# (b) every part checked ----------------------------------------------------------------------

def test_b_non_whitelisted_axiom_in_any_part():
    ps = _parts(); _by(ps, "seg:h7000")["inspect"]["axioms"].append("sorryAx")
    _fails(ps, "non-whitelisted")


def test_b_part_without_a_comparator_pass():
    ps = _parts(); _by(ps, "seg:h2000")["comparator"] = "FAIL"
    _fails(ps, "did not PASS")


def test_b_missing_and_duplicate_and_foreign_parts():
    ps = [p for p in _parts() if p["part"] != "seg:h8000"]
    _fails(ps, "missing part")
    ps = _parts(); ps.append(copy.deepcopy(_by(ps, "seg:h1000")))
    _fails(ps, "appears twice")
    ps = _parts(); x = copy.deepcopy(_by(ps, "seg:h1000")); x["part"] = "seg:h9000"; ps.append(x)
    _fails(ps, "unexpected part")


def test_b_parts_from_two_runs():
    ps = _parts(); _by(ps, "seg:h4000")["run_id"] = "999"
    _fails(ps, "different runs")


def test_b_inspected_theorem_must_be_the_judged_bridge():
    ps = _parts(); _by(ps, "seg:h6000")["inspect"]["theorem"] = "Arb4_h6000.hbands"
    _fails(ps, "judged bridge")


# (c) the implication does not depend on the segment proofs ------------------------------------

def test_c_implication_closure_contains_a_certificate_module():
    """Real NC 2 / 3b: the implication imported Arb4_h1000 and used its hbands."""
    ps = _parts(); _by(ps, "compose")["inspect"]["closure_modules"].append("Arb4_H1000Edges_0")
    _fails(ps, "certificate module")


def test_c_missing_closure_report_is_not_a_pass():
    ps = _parts(); _by(ps, "compose")["inspect"]["closure_modules"] = []
    _fails(ps, "no closure-module report")


def test_c_forbidden_regex_must_bite_on_the_segments():
    import dataclasses
    vacuous = dataclasses.replace(SPEC, forbidden_modules=r"^NoSuchModule$")
    errs = compose.verify(NODE, vacuous, _parts())
    assert any("would be vacuous" in e for e in errs), errs


# (d) the verdict says what it is ---------------------------------------------------------------

def test_d_verdict_line_is_parsed_as_compositional():
    line = compose.verdict_line(island="zeta_reflection", node=NODE, spec=SPEC, run_id="1",
                                kernel="lean-kernel-only")
    v = judge_log.parse_verdicts(line)[NODE]
    assert (v.judge, v.parts, v.theorem, v.kernel) == \
        ("compositional", 9, SPEC.theorem, "lean-kernel-only")
    # and an ordinary PASS line still parses, with no judge mode
    v2 = judge_log.parse_verdicts("COMPARATOR PASS island=x node=n theorem=t run=1 kernel=nanoda")["n"]
    assert (v2.judge, v2.parts) == ("", 0)


def test_d_compose_fail_line_is_a_fail_for_the_record():
    assert judge_log.failed_nodes(
        f"COMPARATOR FAIL island=zeta_reflection node={NODE} (compositional)") == [NODE]


def test_d_record_requires_parts_exactly_when_compositional():
    base = dict(run_id="1", date="2026-09-27", artifact_sha256="a" * 64, theorem="t")
    with pytest.raises(SchemaError):
        ComparatorRecord(**base, judge_mode="compositional")
    with pytest.raises(SchemaError):
        ComparatorRecord(**base, parts=("part=compose",))
    with pytest.raises(SchemaError):
        ComparatorRecord(**base, judge_mode="sometimes", parts=("x",))
    assert ComparatorRecord(**base, judge_mode="compositional", parts=["p"]).parts == ("p",)


def test_d_weak_record_reason_says_compositional():
    from telperion.missions.provenance import ProvenanceRow, weak_record_reasons
    row = ProvenanceRow(campaign="anduril", slug=NODE, status="proved", independence="unverified",
                        self_audit=False, comparator_run="1", comparator_stale=False,
                        lean_kernel_only=True, log_check="verified", head_check="matched",
                        has_grant=True, judge_via="heavy", judge_mode="compositional", parts=9)
    (r,) = weak_record_reasons(row)
    assert "not replayed as one closure" in r and "8 Comparator-checked segment" in r


def test_d_staleness_tracks_every_part_module(tmp_path):
    """A compositional record pins each PART module; editing any one makes it stale."""
    import dataclasses
    from telperion.missions.provenance import comparator_staleness, sha256_file
    node = load_node(T / "missions" / "anduril" / "nodes" / f"{NODE}.toml")
    isl = tmp_path / "examples" / "isl" / "lean"; isl.mkdir(parents=True)
    camp = tmp_path / "missions" / "anduril"; camp.mkdir(parents=True)
    art = isl / "Arb4_h8000.lean"; art.write_text("capstone")
    mods = {"compose": SPEC.module, **{f"seg:{n}": m for n, _s, _t, m in SPEC.segments}}
    for m in mods.values():
        (isl / f"{m}.lean").write_text(f"-- {m}")
    parts = tuple(f"part={k} module={m} sha256={sha256_file(isl / f'{m}.lean')} job=1"
                  for k, m in sorted(mods.items()))
    rec = ComparatorRecord(run_id="1", date="d", artifact_sha256=sha256_file(art), theorem="t",
                           judge_mode="compositional", parts=parts)
    proof = dataclasses.replace(node.proof, artifact="../../examples/isl/lean/Arb4_h8000.lean")
    n2 = dataclasses.replace(node, comparator=rec, proof=proof)
    assert comparator_staleness(camp, n2) == ""
    (isl / "Arb4_h3000.lean").write_text("-- edited")
    assert "stale" in comparator_staleness(camp, n2)


# schema ---------------------------------------------------------------------------------------

def test_schema_compose_needs_judge_via_heavy_and_round_trips(tmp_path):
    import dataclasses
    from telperion.missions.schema import save_node
    node = load_node(T / "missions" / "anduril" / "nodes" / f"{NODE}.toml")
    assert node.compose is not None and len(node.compose.segments) == 8
    p = tmp_path / "n.toml"; save_node(node, p)
    assert load_node(p).compose == node.compose
    with pytest.raises(SchemaError, match="judge_via"):
        dataclasses.replace(node, judge_via="")


def test_schema_compose_spec_validation():
    ok = dict(module="M", theorem="M.t", forbidden_modules="^X$", segment_names=("a",),
              segment_statements=("S",), segment_theorems=("T",), segment_modules=("Mod",))
    ComposeSpec(**ok)
    for bad in (dict(segment_names=("a", "b")), dict(forbidden_modules="("),
                dict(segment_names=("a b",)), dict(segment_names=()), dict(theorem=" ")):
        with pytest.raises(SchemaError):
            ComposeSpec(**{**ok, **bad})
    with pytest.raises(SchemaError):
        ComposeSpec(**{**ok, "segment_names": ("a", "b"), "segment_statements": ("S", "S"),
                       "segment_theorems": ("T", "U"), "segment_modules": ("M1", "M2")})


# rendering ------------------------------------------------------------------------------------

def test_render_parts_and_exports():
    from telperion.missions import judge
    b = judge.build_bundle(T, "zeta_reflection", heavy=True, only=[NODE])
    parts = {c.part: c for c in b.challenges}
    assert set(parts) == set(compose.expected_parts(NODE, SPEC))
    comp = parts["compose"]
    assert comp.exports == SPEC.segment_statements and comp.solution_module == SPEC.module
    for nm, stmt, thm, mod in SPEC.segments:
        c = parts[f"seg:{nm}"]
        assert c.exports == (stmt,) and c.solution_module == mod and c.theorem == thm
        assert f": _root_.{stmt} :=\n  {thm}\n" in c.challenge_text
        assert f"(b_{nm} : _root_.{stmt})" in comp.challenge_text
    # the implication's proof applies every hypothesis, in order
    assert (f"{SPEC.theorem} " + " ".join(f"b_{n}" for n in SPEC.segment_names)) in comp.challenge_text


def test_implication_module_imports_no_certificate_module():
    """Cheap static twin of check (c): the island's implication module imports nothing the
    forbidden regex names (the judge's closure check is the authority; this catches it at PR time)."""
    import re
    src = (T / "examples" / "zeta_reflection" / "lean" / f"{SPEC.module}.lean").read_text()
    imports = re.findall(r"(?m)^import\s+(\S+)", src)
    assert imports and not [m for m in imports if re.match(SPEC.forbidden_modules, m)]


# comparator-record: every part located in the run, every part module pinned ---------------------

@pytest.fixture
def record_env(tmp_path, monkeypatch):
    """A throwaway git repo holding the capstone and every part module, a compositional verdict
    log, and a stub for the per-part job lookup (no network)."""
    import dataclasses
    import shutil
    import subprocess
    if shutil.which("git") is None:  # pragma: no cover
        pytest.skip("git is not available")
    from telperion import cli
    from telperion.missions.judge_log import JobVerdict, Verdict
    d = tmp_path / "r"; isl = d / "lean"; isl.mkdir(parents=True)
    git = lambda *a: subprocess.run(["git", *a], cwd=d, capture_output=True, text=True, check=True).stdout.strip()
    git("init", "-q"); git("config", "user.email", "t@example.com"); git("config", "user.name", "t")
    art = isl / "Arb4_h8000.lean"; art.write_text("capstone\n")
    mods = {"compose": SPEC.module, **{f"seg:{n}": m for n, _s, _t, m in SPEC.segments}}
    for m in mods.values():
        (isl / f"{m}.lean").write_text(f"-- {m}\n")
    git("add", "-A"); git("commit", "-q", "-m", "c"); head = git("rev-parse", "HEAD")
    node = load_node(T / "missions" / "anduril" / "nodes" / f"{NODE}.toml")
    want = compose.expected_parts(NODE, SPEC)
    log = "\n".join(
        f"COMPOSE PART node={NODE} part={k} slug={s} theorem={compose.bridge(s)} "
        f"axioms=Classical.choice,Quot.sound,propext closure=1 comparator=PASS job=judge"
        for k, s in sorted(want.items()))
    log += "\n" + compose.verdict_line(island="zeta_reflection", node=NODE, spec=SPEC,
                                       run_id="77", kernel="lean-kernel-only")
    calls = []

    def fake_fetch(run_id, slug):
        calls.append(slug)
        v = Verdict("zeta_reflection", slug, "t", str(run_id), "lean-kernel-only")
        return JobVerdict(f"job-{slug}", "", head, v, False, True, ""), []
    monkeypatch.setattr(cli, "_fetch_judge_job", fake_fetch)
    uploaded = {"parts": _parts()}

    def fake_download(run_id, dest):
        for p in uploaded["parts"]:
            (dest / f"{p['slug']}.part.json").write_text(json.dumps(p))
        return bool(uploaded["parts"])
    monkeypatch.setattr(cli, "_download_compose_parts", fake_download)
    verdict = judge_log.parse_verdicts(log)[NODE]
    run = lambda n=node, v=verdict, lg=log, off=False: cli._compositional_parts(
        n, NODE, v, lg, "77", head, art, offline=off)
    return dict(run=run, node=node, verdict=verdict, log=log, isl=isl, calls=calls,
                want=want, dataclasses=dataclasses, uploaded=uploaded)


def test_record_lists_and_pins_every_part(record_env):
    out = record_env["run"]()
    assert isinstance(out, list) and len(out) == 9, out
    assert sorted(record_env["calls"]) == sorted(record_env["want"].values())
    from telperion.missions.provenance import parse_part_entry
    ents = {parse_part_entry(e)["part"]: parse_part_entry(e) for e in out}
    assert ents["compose"]["theorem"] == SPEC.theorem and ents["compose"]["module"] == SPEC.module
    assert ents["seg:h5000"]["theorem"] == "Arb4_h5000.hbands"
    assert all(len(e["sha256"]) == 64 and e["job"].startswith("job-") for e in ents.values())


def test_record_refusals(record_env):
    run, node, v, log = record_env["run"], record_env["node"], record_env["verdict"], record_env["log"]
    dc = record_env["dataclasses"]
    assert "can only be recorded from the judge's own job logs" in run(off=True)
    assert "not the compositional verdict" in run(v=dc.replace(v, judge=""))
    assert "no [compose] table" in run(n=dc.replace(node, compose=None, judge_via="heavy"))
    assert "not the node's implication" in run(v=dc.replace(v, theorem="Arb4_h8000.x"))
    assert "glued 8 part(s)" in run(v=dc.replace(v, parts=8))
    dropped = "\n".join(l for l in log.splitlines() if "part=seg:h4000" not in l)
    assert "verdict job lists parts" in run(lg=dropped)
    tainted = log.replace("part=seg:h6000 slug", "part=seg:h6000 slug", 1).replace(
        "axioms=Classical.choice,Quot.sound,propext closure=1 comparator=PASS job=judge\n"
        f"COMPOSE PART node={NODE} part=seg:h7000",
        "axioms=sorryAx closure=1 comparator=PASS job=judge\n"
        f"COMPOSE PART node={NODE} part=seg:h7000", 1)
    assert "not all whitelisted" in run(lg=tainted)
    (record_env["isl"] / "Arb4_h3000.lean").write_text("-- edited after the judged commit\n")
    assert "differs from the judged commit" in run()


def test_record_rechecks_the_uploaded_parts(record_env):
    """The record does not take the verdict job's word: it re-runs the glue on the artifacts."""
    ps = _parts(); _by(ps, "compose")["inspect"]["closure_modules"].append("Arb4_H2000Edges_1")
    record_env["uploaded"]["parts"] = ps
    assert "re-checking the uploaded parts FAILED" in record_env["run"]()
    record_env["uploaded"]["parts"] = []
    assert "could not download" in record_env["run"]()
