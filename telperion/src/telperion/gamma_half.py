"""Transcendental skill: a COMPLETED in-kernel bracket of Gamma(1/2), one of the
deep transcendentals -- via its Mathlib closed form Gamma(1/2) = sqrt(pi).

Gamma(1/2) has a closed form (`Real.Gamma_one_half_eq : Real.Gamma (1/2) = √π`),
so it composes the (confirmed) pi bounds Real.pi_gt_three / Real.pi_lt_four with
sqrt monotonicity into a fully proven

    1.7  <=  Gamma(1/2)  <=  2      (Gamma(1/2) = √π, 3 < π < 4).

Loose (the tight version awaits a tighter pi-bound lemma name), but genuinely
kernel-checked.  Contrast: zeta(1/2), Gamma(1/4), and a_k have NO Mathlib closed
form / computable handle (see DEEP_TRANSCENDENTALS.md).

Proof shape (all lemmas CI-confirmed to exist in v4.32.0):
    rw [Real.Gamma_one_half_eq]                     -- goal: lo <= √π <= hi
    lo = √(lo^2) <= √π   (Real.sqrt_sq, Real.sqrt_le_sqrt, lo^2 <= 3 < π)
    √π <= √(hi^2) = hi   (π < 4 <= hi^2)
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


# lo^2 <= 3 (< pi)  and  4 (> pi) <= hi^2, so [lo,hi] brackets √π = Gamma(1/2).
_LO = Fr(17, 10)   # 1.7^2 = 2.89 <= 3
_HI = Fr(2, 1)     # 2^2 = 4 >= 4


@dataclass(frozen=True)
class GammaHalfBracketCertificate:
    """Fully in-kernel bracket 1.7 <= Real.Gamma(1/2) <= 2 via √π and 3 < π < 4."""

    name: str

    def bracket(self):
        return _LO, _HI

    def check(self) -> bool:
        lo, hi = _LO, _HI
        exact = (lo >= 0 and lo * lo <= Fr(3) and Fr(4) <= hi * hi)
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
            f"      ∧ Real.Gamma (1/2) ≤ ({hi.numerator} : ℝ) := by\n"
            f"  rw [Real.Gamma_one_half_eq]\n"
            f"  constructor\n"
            f"  · calc ({lo.numerator} : ℝ) / {lo.denominator}\n"
            f"        = Real.sqrt ((({lo.numerator} : ℝ) / {lo.denominator}) ^ 2) := "
            f"(Real.sqrt_sq (by norm_num)).symm\n"
            f"      _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])\n"
            f"  · calc Real.sqrt Real.pi\n"
            f"        ≤ Real.sqrt (({hi.numerator} : ℝ) ^ 2) := "
            f"Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])\n"
            f"      _ = ({hi.numerator} : ℝ) := Real.sqrt_sq (by norm_num)\n"
        )
