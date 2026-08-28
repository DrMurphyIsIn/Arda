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
    assert lo * lo <= Fr(3)              # lo^2 <= pi-lower (3)  => lo <= sqrt(pi)
    assert Fr(4) <= hi * hi              # pi-upper (4) <= hi^2  => sqrt(pi) <= hi
    assert float(lo) <= 1.7724539 <= float(hi)


def test_lean_uses_gamma_closed_form_and_confirmed_pi_lemmas():
    lean = GammaHalfBracketCertificate(name="gamma_half_bracket").lean()
    assert "Real.Gamma_one_half_eq" in lean
    assert "Real.sqrt_sq" in lean and "Real.sqrt_le_sqrt" in lean
    assert "Real.pi_gt_three" in lean and "Real.pi_lt_four" in lean
