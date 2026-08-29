"""ZetaBoundCertificate: reusable two-sided bounds on zeta(k), k>=2 integer."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import ZetaBoundCertificate  # noqa: E402


def _zeta(k: int) -> float:
    try:
        import mpmath as mp
        return float(mp.zeta(k))
    except Exception:
        return sum(1.0 / n ** k for n in range(1, 100000))  # float partial sum


def test_bracket_contains_zeta_across_k_and_M():
    for k in (2, 3, 4, 5, 6, 7):
        for M in (3, 5, 20):
            c = ZetaBoundCertificate(name=f"z{k}_{M}", k=k, M=M)
            assert c.check()
            lo, hi = c.bracket()
            assert float(lo) <= _zeta(k) <= float(hi)
            assert hi - lo == Fr(1, M - 1)          # tail bound width is exactly 1/(M-1)


def test_tightness_improves_with_M():
    wide = ZetaBoundCertificate(name="w", k=3, M=3)
    tight = ZetaBoundCertificate(name="t", k=3, M=100)
    ww = wide.bracket()[1] - wide.bracket()[0]
    tw = tight.bracket()[1] - tight.bracket()[0]
    assert tw < ww and float(tw) < 0.02          # M=100 -> width 1/99 < 0.02


def test_leading_is_exact_partial_sum():
    c = ZetaBoundCertificate(name="z", k=3, M=4)      # 1 + 1/8 + 1/27
    assert c.leading() == Fr(1) + Fr(1, 8) + Fr(1, 27)


def test_lean_shape():
    lean = ZetaBoundCertificate(name="zeta_five_bound", k=5, M=4).lean()
    assert "theorem zeta_five_bound_eq_ofReal" in lean
    assert "theorem zeta_five_bound" in lean
    assert "riemannZeta 5" in lean
    assert "zeta_eq_tsum_one_div_nat_cpow" in lean
    assert "pow_le_pow_right₀" in lean and "Summable.tsum_le_of_sum_range_le".split(".")[-1] in lean


def test_bad_inputs_refused():
    assert not ZetaBoundCertificate(name="b", k=1, M=3).check()   # k must be >= 2
    assert not ZetaBoundCertificate(name="b", k=3, M=1).check()   # M must be >= 2
    with pytest.raises(ValueError, match="refusing to emit"):
        ZetaBoundCertificate(name="b", k=1, M=3).lean()
