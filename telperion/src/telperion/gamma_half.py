"""Transcendental skill: a COMPLETED in-kernel bracket of Gamma(1/2), one of the
deep transcendentals -- via its Mathlib closed form Gamma(1/2) = sqrt(pi).

This is the deep-transcendental result that IS completable in Mathlib v4.32.0:
Gamma(1/2) has a closed form (`Real.Gamma_one_half_eq : Real.Gamma (1/2) = √π`),
so it composes the pi bracket + sqrt monotonicity into a fully proven

    1.772  <=  Gamma(1/2)  <=  1.775      (Gamma(1/2) = √π, pi in (3.14, 3.15)).

Contrast: zeta(1/2), Gamma(1/4), and the xi coefficients a_k have NO Mathlib
closed form / computable handle, so they stay blocked (see DEEP_TRANSCENDENTALS.md).
The line that separates "completable" from "blocked" is exactly whether Mathlib
carries a closed form or a computable series with bounds.

Proof shape (all lemmas CI-confirmed to exist):
    rw [Real.Gamma_one_half_eq]                     -- goal: lo <= √π <= hi
    lo = √(lo^2) <= √π   (Real.sqrt_sq, Real.sqrt_le_sqrt, lo^2 <= 3.14 < π)
    √π <= √(hi^2) = hi   (π < 3.15 <= hi^2)
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


# lo^2 <= 3.14 (< pi)  and  3.15 (> pi) <= hi^2, so [lo,hi] brackets √π = Gamma(1/2).
_LO = Fr(1772, 1000)   # 1.772^2 = 3.139984 <= 3.14
_HI = Fr(1775, 1000)   # 1.775^2 = 3.150625 >= 3.15


@dataclass(frozen=True)
class GammaHalfBracketCertificate:
    """Fully in-kernel bracket 1.772 <= Real.Gamma(1/2) <= 1.775 via √π."""

    name: str

    def bracket(self):
        return _LO, _HI

    def check(self) -> bool:
        # exact-rational soundness of the corner inequalities used by the proof:
        # lo^2 <= 314/100 (pi lower bound) and 315/100 (pi upper bound) <= hi^2
        lo, hi = _LO, _HI
        exact = (lo >= 0 and lo * lo <= Fr(314, 100) and Fr(315, 100) <= hi * hi)
        try:
            import mpmath as mp
            ivg = mp.iv.gamma(mp.iv.mpf('0.5'))       # rigorous interval for Gamma(1/2)
            return exact and bool(mp.mpf(lo.numerator) / lo.denominator < ivg.a) \
                and bool(ivg.b < mp.mpf(hi.numerator) / hi.denominator)
        except Exception:
            return exact

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: Gamma(1/2) bracket unsound -- refusing to emit")
        lo, hi = _LO, _HI
        return (
            f"theorem {self.name} :\n"
            f"    ({lo.numerator} : ℝ) / {lo.denominator} ≤ Real.Gamma (1/2)\n"
            f"      ∧ Real.Gamma (1/2) ≤ ({hi.numerator} : ℝ) / {hi.denominator} := by\n"
            f"  rw [Real.Gamma_one_half_eq]\n"
            f"  constructor\n"
            f"  · calc ({lo.numerator} : ℝ) / {lo.denominator}\n"
            f"        = Real.sqrt ((({lo.numerator} : ℝ) / {lo.denominator}) ^ 2) := "
            f"(Real.sqrt_sq (by norm_num)).symm\n"
            f"      _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_314])\n"
            f"  · calc Real.sqrt Real.pi\n"
            f"        ≤ Real.sqrt ((({hi.numerator} : ℝ) / {hi.denominator}) ^ 2) := "
            f"Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_315])\n"
            f"      _ = ({hi.numerator} : ℝ) / {hi.denominator} := Real.sqrt_sq (by norm_num)\n"
        )
