"""TrigNonnegCertificate: nonnegative cosine polynomials (zero-free-region certificate family)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import TrigNonnegCertificate  # noqa: E402
from telperion.trig_nonneg import power_poly  # noqa: E402
import sympy as sp  # noqa: E402


def test_mertens_three_four_one():
    # the classical seed: 3 + 4cos + cos2 = 2(1+cos)^2
    c = TrigNonnegCertificate(name="t", coeffs=(3, 4, 1))
    assert c.check()
    x = sp.Symbol("x", real=True)
    assert sp.expand(power_poly((3, 4, 1)) - 2 * (x + 1) ** 2) == 0


def test_cubic_with_boundary_factor():
    # 6 + 8cos + 4cos2 + 2cos3 -> 2(1+x)(4x^2+1) : needs the -1<=cos bound
    c = TrigNonnegCertificate(name="t", coeffs=(6, 8, 4, 2))
    assert c.check()
    lean = c.lean()
    assert "1 + Real.cos θ" in lean and "mul_nonneg" in lean


def test_refuses_a_non_nonnegative_polynomial():
    # 1 + 2cos is negative near theta=pi (1 + 2(-1) = -1) -> not certifiable
    assert not TrigNonnegCertificate(name="t", coeffs=(1, 2)).check()


def test_refuses_degree_above_three():
    # scope is degree <= 3 (cos_two_mul / cos_three_mul range)
    assert not TrigNonnegCertificate(name="t", coeffs=(8, 12, 6, 2, 1)).check()


def test_emitted_theorem_shape():
    lean = TrigNonnegCertificate(name="trig_nonneg_mertens", coeffs=(3, 4, 1)).lean()
    assert "theorem trig_nonneg_mertens (θ : ℝ) : 0 ≤" in lean
    assert "Real.cos_two_mul" in lean
    assert "sq" in lean or "positivity" in lean or "mul_nonneg" in lean
