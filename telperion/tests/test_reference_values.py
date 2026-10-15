"""Cross-wiring regression: comparison values come from the referenced artefact, never from a literal.

conjecture1_proved = False.  Reproduces the WALL-3 T bug (545b21697, found by bb): b_twist_real_g.py, a parametrised
copy of b_twist_real.py, compared its gamma0 = 21.02204 residue against the literal 1.0376701213616086, which is
track B's residue for gamma0 = 14.134725.
"""
import json
from pathlib import Path

import pytest

from telperion.reference_values import compare_ball, read_reference, references_in, scan_stale_literals

WALL3 = Path(__file__).resolve().parents[1] / "examples" / "wall3"
CERT_14 = WALL3 / "certs" / "B_twist_REAL.cert.json"
CERT_21 = WALL3 / "certs" / "B_twist_REAL_g21.02204.cert.json"

# The pre-fix tail of b_twist_real_g.py (545b21697^), copied from b_twist_real.py with the literal left in.
STALE_COPY = '''
GS = sys.argv[1] if len(sys.argv) > 1 else "14.134725"
# (5) the residue A at s = 1 (B uses A = 1.0376701213616086 with "no fitting")
out["residue_A"] = {"arb": A.str(25), "B_float": 1.0376701213616086,
                    "contains_B_float": bool(abs(A.real - arb(1.0376701213616086)).upper() < 1e-14)}
'''

FIXED_COPY = '''
GS = sys.argv[1] if len(sys.argv) > 1 else "14.134725"
ref = read_reference(rh(f"wall3/B/out/tw_REAL_b0.85_g{float(GS)}_s0_X1e+09.json"), "A")
out["residue_A"] = compare_ball(A.real, ref)
'''


def _b_refs():
    refs = references_in([CERT_14, CERT_21], "residue_A.B_float", display_root=WALL3)
    audit = json.loads((WALL3 / "certs" / "B_residue_audit.cert.json").read_text())
    refs += [read_reference(WALL3 / "certs" / "B_residue_audit.cert.json", f"rows.{i}.A_B", display_root=WALL3)
             for i in range(len(audit["rows"]))]
    return refs


def test_read_reference_records_provenance(tmp_path):
    p = tmp_path / "art.json"
    p.write_text(json.dumps({"residue_A": {"B_float": 1.25}}))
    r = read_reference(p, "residue_A.B_float", display_root=tmp_path)
    assert r.value == 1.25 and r.path == "art.json" and len(r.sha256) == 64
    with pytest.raises(KeyError):
        read_reference(p, "residue_A.missing")


def test_stale_literal_in_copied_script_is_caught():
    refs = references_in([CERT_14, CERT_21], "residue_A.B_float", display_root=WALL3)
    hits = scan_stale_literals(STALE_COPY, refs)
    assert hits, "the copied literal must be flagged"
    # it names the artefact the literal really belongs to: the gamma0 = 14.13 file, not the 21.02 one
    assert {h["reference"]["path"] for h in hits} == {"certs/B_twist_REAL.cert.json"}
    assert {h["literal"] for h in hits} == {"1.0376701213616086"}
    assert scan_stale_literals(FIXED_COPY, refs) == []


def test_stale_literal_gives_wrong_verdict_and_reference_gives_right_one():
    """Arb residue A for gamma0 = 21.02204: contained in the 21.02 artefact's value, not in the copied 14.13 one."""
    flint = pytest.importorskip("flint")
    from flint import acb, arb, ctx, fmpz
    ctx.prec = 128
    rho = acb(arb("0.85"), arb("21.02204"))
    rhob = rho.conjugate()
    A = 1 / ((2 - rho).zeta() * (2 - rhob).zeta())
    for p in range(2, 102):
        if fmpz(p).is_prime():
            lp = acb(p).log()
            A = A / ((1 - ((rho - 2) * lp).exp()) * (1 - ((rhob - 2) * lp).exp()))
    right = compare_ball(A.real, read_reference(CERT_21, "residue_A.B_float"), slack=1e-14)
    wrong = compare_ball(A.real, read_reference(CERT_14, "residue_A.B_float"), slack=1e-14)
    assert right["contains"] and not wrong["contains"]
    assert flint  # noqa


def test_committed_wall3_scripts_have_no_stale_reference_literals():
    """Every B residue reference value in the committed certificates must be read, not typed, by the scripts."""
    refs = _b_refs()
    assert len(refs) >= 9
    for f in sorted((WALL3 / "scripts").glob("*.py")):
        assert scan_stale_literals(f.read_text(), refs) == [], f.name


def test_no_absolute_home_paths_in_wall3_sources():
    for f in sorted((WALL3 / "scripts").glob("*.py")) + [WALL3 / "TOOLS3.md", WALL3 / "t3tools.py"]:
        assert "/Users/" not in f.read_text(), f.name


def test_compare_ball_uses_the_radius(tmp_path):
    """Regression (bb, PR #744 review): a ball of nonzero radius contains every value within its radius (+ slack),
    and nothing beyond it."""
    pytest.importorskip("flint")
    from flint import arb
    p = tmp_path / "ref.json"
    ball = arb("1", "0.1")                       # [0.9, 1.1]
    for v, slack, want in ((1.05, 0.0, True), (1.09, 0.0, True), (0.95, 0.0, True), (1.25, 0.2, True),
                           (1.11, 0.0, False), (0.85, 0.0, False), (1.35, 0.2, False)):
        p.write_text(json.dumps({"A": v}))
        got = compare_ball(ball, read_reference(p, "A"), slack=slack)["contains"]
        assert got is want, (v, slack)
        if want:
            assert arb(ball.mid(), ball.rad() + slack).contains(arb(repr(v)))
