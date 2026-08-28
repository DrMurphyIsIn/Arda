"""Transcendental skill: rigorous rational bracket of Real.pi, in-kernel.

Third transcendental certificate (after exp_bracket, log_bound).  Emits

    3  <  Real.pi  <  4,

proved verbatim by Mathlib's `Real.pi_gt_three` / `Real.pi_lt_four` -- the pi
bounds actually present in v4.32.0 (the decimal names `Real.pi_gt_314` /
`Real.pi_gt_3141592` do NOT exist there, as the CI API probe established).  Loose,
but genuinely kernel-checked; a tighter bracket awaits the correct high-precision
lemma name (not found among the probed candidates).

`check()` cross-checks the bracket against mpmath's RIGOROUS interval iv.pi.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


@dataclass(frozen=True)
class PiBracketCertificate:
    """Rigorous bracket  3 < Real.pi < 4, backed verbatim by Mathlib's
    `Real.pi_gt_three` / `Real.pi_lt_four`."""

    name: str

    def bracket(self):
        return Fr(3), Fr(4)

    def check(self) -> bool:
        lo, hi = self.bracket()
        try:
            import mpmath as mp
            ivpi = mp.iv.pi
            return (lo < hi
                    and bool(mp.mpf(lo.numerator) / lo.denominator < ivpi.a)
                    and bool(ivpi.b < mp.mpf(hi.numerator) / hi.denominator))
        except Exception:
            import math
            return lo < hi and float(lo) < math.pi < float(hi)

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: pi bracket not verified -- refusing to emit")
        return (
            f"theorem {self.name} :\n"
            f"    (3 : ℝ) < Real.pi ∧ Real.pi < (4 : ℝ) :=\n"
            f"  ⟨Real.pi_gt_three, Real.pi_lt_four⟩\n"
        )
