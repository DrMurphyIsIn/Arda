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
    assert lo == Fr(3141592, 1000000) and hi == Fr(3141593, 1000000)
    import math
    assert float(lo) < math.pi < float(hi)


def test_lean_uses_mathlib_lemmas_verbatim():
    lean = PiBracketCertificate(name="pi_bracket").lean()
    assert "theorem pi_bracket" in lean
    assert "Real.pi" in lean
    # decimal literals matching Mathlib's lemma statements (no defeq bridging)
    assert "(3.141592 : ℝ) < Real.pi" in lean
    assert "Real.pi < (3.141593 : ℝ)" in lean
    assert "⟨Real.pi_gt_3141592, Real.pi_lt_3141593⟩" in lean
