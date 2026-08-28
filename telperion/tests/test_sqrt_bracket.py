"""Transcendental sqrt-bracket certificate."""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import SqrtBracketCertificate  # noqa: E402


def test_brackets_sqrt_across_a_range():
    for qn, qd in [(2, 1), (3, 1), (3, 2), (10, 1), (5, 3), (7, 4), (2, 3)]:
        c = SqrtBracketCertificate.build(f"sqrt_{qn}_{qd}", qn, qd)
        assert c.check()
        lo, hi = Fr(c.lo), Fr(c.hi)
        assert lo * lo <= Fr(qn, qd) <= hi * hi        # the exact rational guarantee
        assert float(lo) <= math.sqrt(qn / qd) <= float(hi)


def test_lean_uses_robust_sqrt_lemmas():
    lean = SqrtBracketCertificate.build("sqrt_two", 2, 1).lean()
    assert "theorem sqrt_two" in lean
    assert "Real.sqrt" in lean
    assert "Real.sqrt_sq" in lean and "Real.sqrt_le_sqrt" in lean


def test_bad_bracket_refused():
    bad = SqrtBracketCertificate(name="bad", qn=2, qd=1, lo=Fr(3, 2), hi=Fr(2))  # 1.5^2=2.25 > 2
    assert not bad.check()
    with pytest.raises(ValueError, match="refusing to emit"):
        bad.lean()
