"""ExpBracketCertificate: reusable rigorous rational bracket of exp(-theta).

Key test is SUBSUMPTION: the certificate reproduces the existing compile-gated
examples/exp_bracket/ artifact byte-for-byte -- so the H2-Bridge exp sites can
migrate to it without changing any emitted Lean.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion import ExpBracketCertificate, suggest_exp_bracket, taylor_exp  # noqa: E402

FROZEN = ROOT / "examples" / "exp_bracket" / "frozen" / "ExpBracket.lean"

# The committed far-constant instance (theta = 0.37167, N=9, tfloor=145015/100000,
# hi=68959/100000) -- values read straight from examples/exp_bracket/generate.py.
THETA = Fr(37167, 100000)
FAR = ExpBracketCertificate(
    theta=THETA, nterms=9, tfloor=Fr(145015, 100000), hi=Fr(68959, 100000))


def test_far_constant_checks():
    assert FAR.check()
    # the bracket really contains exp(-theta): 1-theta <= exp(-theta) <= hi
    assert FAR.lo() == 1 - THETA
    assert FAR.lo() < FAR.hi


def test_subsumes_frozen_artifact_byte_for_byte():
    # the two emitted theorems appear verbatim in the frozen production Lean
    assert FAR.lean() in FROZEN.read_text()


def test_suggest_reproduces_far_constant_values():
    # auto-fill lands on the same clean rationals the bespoke example hand-picked
    tfloor, hi = suggest_exp_bracket(THETA, 9, digits=5)
    assert tfloor == Fr(145015, 100000)
    assert hi == Fr(68959, 100000)


def test_reusable_at_a_fresh_theta():
    # a different exp(-theta) site: theta = 1/2, auto-filled, distinct names
    c = ExpBracketCertificate.build(
        Fr(1, 2), 12, le_name="exp_half_le", ge_name="exp_half_ge")
    assert c.check()
    lean = c.lean()
    assert "theorem exp_half_le" in lean and "theorem exp_half_ge" in lean
    assert "Real.exp (-(1 / 2" in lean
    # the bracket brackets the true value
    assert float(c.lo()) <= 0.60653066 <= float(c.hi)   # exp(-1/2) ~ 0.6065


def test_taylor_is_a_lower_bound_on_exp():
    # Taylor_N(theta) <= exp(theta) for theta>0 (the lemma the upper bound uses)
    import math
    for theta in (Fr(1, 10), Fr(37167, 100000), Fr(1, 2), Fr(1)):
        assert float(taylor_exp(theta, 12)) <= math.exp(float(theta))


def test_bad_tfloor_above_taylor_refused():
    # tfloor must be <= Taylor_N(theta); an inflated one is caught
    T = taylor_exp(THETA, 9)
    bad = ExpBracketCertificate(theta=THETA, nterms=9, tfloor=T + Fr(1, 100),
                                hi=Fr(68959, 100000))
    assert not bad.check()
    with pytest.raises(ValueError, match="refusing to emit"):
        bad.lean()


def test_bad_hi_below_reciprocal_refused():
    # hi must be >= 1/tfloor; a too-small hi is caught
    tfloor = Fr(145015, 100000)
    bad = ExpBracketCertificate(theta=THETA, nterms=9, tfloor=tfloor,
                                hi=1 / tfloor - Fr(1, 1000))
    assert not bad.check()
