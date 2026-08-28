"""Completed in-kernel bracket of the deep transcendental Gamma(1/2) = sqrt(pi)."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import GammaHalfBracketCertificate  # noqa: E402


def test_bracket_is_sound_and_encloses_gamma_half():
    c = GammaHalfBracketCertificate(name="gamma_half_bracket")
    assert c.check()
    lo, hi = c.bracket()
    # the corner inequalities the Lean proof relies on:
    assert lo * lo <= Fr(314, 100)          # lo^2 <= pi-lower  => lo <= sqrt(pi)
    assert Fr(315, 100) <= hi * hi          # pi-upper <= hi^2  => sqrt(pi) <= hi
    # numerically encloses Gamma(1/2) = sqrt(pi) ~ 1.7724539
    assert float(lo) <= 1.7724539 <= float(hi)


def test_lean_uses_gamma_closed_form_and_pi_sqrt_lemmas():
    lean = GammaHalfBracketCertificate(name="gamma_half_bracket").lean()
    assert "Real.Gamma_one_half_eq" in lean      # Gamma(1/2) = sqrt(pi), the Mathlib closed form
    assert "Real.sqrt_sq" in lean and "Real.sqrt_le_sqrt" in lean
    assert "Real.pi_gt_314" in lean and "Real.pi_lt_315" in lean
    assert "Real.Gamma (1/2)" in lean
