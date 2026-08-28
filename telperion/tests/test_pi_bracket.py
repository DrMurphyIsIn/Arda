"""Transcendental pi-bracket certificate (Mathlib-backed)."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import PiBracketCertificate  # noqa: E402


def test_bracket_encloses_pi_rigorously():
    c = PiBracketCertificate(name="pi_bracket")
    assert c.check()                                   # cross-checked vs mpmath iv.pi
    lo, hi = c.bracket()
    assert lo == Fr(314, 100) and hi == Fr(315, 100)
    import math
    assert float(lo) < math.pi < float(hi)


def test_lean_is_name_hedged():
    lean = PiBracketCertificate(name="pi_bracket").lean()
    assert "theorem pi_bracket" in lean
    assert "(314 : ℝ) / 100 < Real.pi" in lean
    # name-hedged across Mathlib versions (v4.32.0 lacks the 314159x names)
    assert "Real.pi_gt_314" in lean and "Real.pi_lt_315" in lean
    assert "first" in lean
