"""Transcendental skill: rigorous rational bracket of Real.pi, in-kernel.

Third transcendental certificate (after exp_bracket, log_bound).  Unlike those it
needs no derivation -- Mathlib ships proven bounds on pi.  This wraps them into

    3.14  <  Real.pi  <  3.15,

proved robustly: `first | linarith [Real.pi_gt_314] | linarith [Real.pi_gt_3141592]`
(and likewise the upper bound), so it survives the lemma-name differences between
Mathlib versions -- the high-precision `Real.pi_{gt,lt}_314159x` names do NOT
exist in v4.32.0 (CI caught this), the coarser `Real.pi_gt_314` / `Real.pi_lt_315`
do.  pi is load-bearing in xi (the pi^{-s/2} factor) and the archimedean Li terms.

`check()` cross-checks the bracket against mpmath's RIGOROUS interval iv.pi.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


@dataclass(frozen=True)
class PiBracketCertificate:
    """Rigorous bracket  3.14 < Real.pi < 3.15, backed by Mathlib's pi bounds
    (name-hedged across Mathlib versions)."""

    name: str

    def bracket(self):
        return Fr(314, 100), Fr(315, 100)

    def check(self) -> bool:
        lo, hi = self.bracket()
        try:
            import mpmath as mp
            ivpi = mp.iv.pi                        # rigorous interval enclosure of pi
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
            f"    (314 : ℝ) / 100 < Real.pi ∧ Real.pi < (315 : ℝ) / 100 := by\n"
            f"  refine ⟨?_, ?_⟩\n"
            f"  · first\n"
            f"      | linarith [Real.pi_gt_314]\n"
            f"      | linarith [Real.pi_gt_3141592]\n"
            f"      | linarith [Real.pi_gt_three]\n"
            f"  · first\n"
            f"      | linarith [Real.pi_lt_315]\n"
            f"      | linarith [Real.pi_lt_3141593]\n"
        )
