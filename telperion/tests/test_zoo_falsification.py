"""Required-outcome tests for the MIRRORMERE falsification harness (QC-B1).

These assert the §8 governance matrix outcomes from QC_AXIOMS_DRAFT.md: DH (the
off-line-zero control) must die on every LIVE variant (A/B/D) on its predicted
clause and SURVIVE the dead control C; zeta's certified data passes unconditional
clauses and is CONDITIONAL on RH-clauses; the positive controls (lattice, ksly)
survive; random is killed; and every forged-input negative control flips.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest

_QC = Path(__file__).resolve().parent.parent / "examples" / "quasicrystal"
sys.path.insert(0, str(_QC))

try:
    import zoo  # noqa: E402
    _HAVE = zoo._load_zeta is not None
except Exception:  # pragma: no cover
    _HAVE = False

pytestmark = pytest.mark.skipif(not _HAVE, reason="quasicrystal zoo harness unavailable")


@pytest.fixture(scope="module")
def result():
    r = zoo.build_matrix(100.0)
    r["forged_controls"] = zoo.forged_controls()
    return r


def test_no_governance_failures(result):
    findings, failures = zoo.run_asserts(result)
    assert failures == [], f"governance rails broken: {failures}"


def test_dh_dies_on_every_live_variant(result):
    vk = result["variant_kill"]
    for variant in ("A", "B", "D"):
        assert vk[variant]["dh"]["killed"], f"DH must be killed by live variant {variant}"


def test_dh_killed_on_predicted_clause(result):
    m = result["matrix"]["dh"]
    assert m["weight_positivity"]["verdict"] == zoo.FAIL      # B killer = positivity
    assert m["defect_bounded"]["verdict"] == zoo.FAIL         # D killer = unbounded defect
    assert m["atomic_spectrum"]["verdict"] == zoo.FAIL        # A sep = prime log-lattice


def test_dh_survives_dead_control_C(result):
    vk = result["variant_kill"]
    assert vk["C"]["dh"]["survives"] and not vk["C"]["dh"]["killed"]


def test_positivity_is_the_isolated_killer(result):
    """C(pass)/B(fail) differ only by positivity => DH kill attributable to positivity."""
    m = result["matrix"]["dh"]
    assert m["signed_decay"]["verdict"] in (zoo.PASS, zoo.COND)   # C passes
    assert m["weight_positivity"]["verdict"] == zoo.FAIL          # B fails


def test_zeta_conditional_labels(result):
    m = result["matrix"]["zeta"]
    assert m["support_density"]["verdict"] == zoo.PASS
    assert m["weight_positivity"]["verdict"] == zoo.PASS          # unconditional arithmetic
    assert m["atomic_spectrum"]["verdict"] == zoo.COND            # RH-conditional, never PASS
    assert m["defect_bounded"]["verdict"] == zoo.COND             # k=0 <=> RH


def test_positive_controls_survive(result):
    vk = result["variant_kill"]
    assert vk["B"]["lattice"]["survives"]
    assert vk["B"]["ksly"]["survives"]


def test_random_is_killed(result):
    assert result["matrix"]["random"]["atomic_spectrum"]["verdict"] == zoo.FAIL
    assert result["variant_kill"]["B"]["random"]["killed"]


def test_all_forged_controls_flip(result):
    for fc in result["forged_controls"]:
        assert fc["flipped"], (
            f"forged control {fc['control']} on {fc['clause']} did not flip "
            f"(genuine={fc['genuine']} forged={fc['forged_verdict']})")


def test_dh_fails_bmult_multiplicativity(result):
    """W3a: DH FAILS the B-mult multiplicativity clause -- no Euler product means the
    log-derivative has a nonzero amplitude at the COMPOSITE frequency log 6."""
    m = result["matrix"]["dh"]
    assert m["multiplicativity"]["verdict"] == zoo.FAIL
    assert "COMPOSITE" in m["multiplicativity"]["detail"]
    assert result["variant_kill"]["Bm"]["dh"]["killed"]


def test_zeta_passes_bmult_generation_unconditionally(result):
    """W3a: the multiplicative GENERATION of zeta's amplitudes is unconditional/
    arithmetic (PASS), while pure-pointness of the dual comb stays RH-conditional."""
    m = result["matrix"]["zeta"]
    assert m["multiplicativity"]["verdict"] == zoo.PASS
    assert m["atomic_spectrum"]["verdict"] == zoo.COND   # RH clause unchanged by B-mult
    assert result["variant_kill"]["Bm"]["zeta"]["survives"]


def test_bmult_strictly_sharper_than_b(result):
    """W3a: B-mult excludes generic Lee-Yang FQs that B admitted.  ksly survives B
    (positive-mass FQ) but is killed by B-mult (amplitudes not multiplicatively
    generated) -- the axiom carves out the arithmetic FQs.  This is the FEATURE."""
    vk = result["variant_kill"]
    assert vk["B"]["ksly"]["survives"]
    assert vk["Bm"]["ksly"]["killed"]
    assert result["matrix"]["ksly"]["multiplicativity"]["verdict"] == zoo.FAIL
    assert result["matrix"]["random"]["multiplicativity"]["verdict"] == zoo.FAIL


def test_multiplicativity_implies_positivity(result):
    """W3a dominance: any object passing B-mult also passes (B-iii) positivity --
    the adjudicated primitive dominates the old killer (no object passes mult but
    fails positivity)."""
    m = result["matrix"]
    for name in result["objects"]:
        if m[name]["multiplicativity"]["verdict"] == zoo.PASS:
            assert m[name]["weight_positivity"]["verdict"] in (zoo.PASS, zoo.COND), (
                f"{name} passes B-mult but not positivity")


def test_broken_multiplicativity_forged_control_flips(result):
    """W3a forged negative control: corrupting a single amplitude (a(6)!=a(2)a(3))
    injects a composite atom -> generation FAILS -> verdict flips PASS->FAIL."""
    fc = next(c for c in result["forged_controls"]
              if c["control"] == "broken_multiplicativity")
    assert fc["flipped"]
    assert fc["genuine"] == zoo.PASS and fc["forged_verdict"] == zoo.FAIL


def test_corrupted_certified_input_flips_verdict(result):
    """The load-bearing negative control: corrupting the DH off-line flag must flip
    the defect verdict, proving verdicts are a real function of the certified data."""
    fc = next(c for c in result["forged_controls"]
              if c["control"] == "corrupt_dh_offline_flag")
    assert fc["flipped"]
    assert fc["genuine"] == zoo.FAIL and fc["forged_verdict"] == zoo.PASS
