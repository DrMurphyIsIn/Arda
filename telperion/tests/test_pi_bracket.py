"""Transcendental pi-bracket certificate (Mathlib-backed, v4.32.0 lemmas)."""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import PiBracketCertificate  # noqa: E402


def test_bracket_encloses_pi():
    c = PiBracketCertificate(name="pi_bracket")
    assert c.check()
    lo, hi = c.bracket()
    assert lo == Fr(3) and hi == Fr(4)
    assert float(lo) < math.pi < float(hi)


def test_lean_uses_confirmed_lemmas():
    lean = PiBracketCertificate(name="pi_bracket").lean()
    assert "(3 : ℝ) < Real.pi" in lean and "Real.pi < (4 : ℝ)" in lean
    assert "⟨Real.pi_gt_three, Real.pi_lt_four⟩" in lean
