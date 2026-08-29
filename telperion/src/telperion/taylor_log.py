"""Transcendental skill: rigorous rational enclosure of `Real.log (1 - 1/k)` via a
truncated Taylor series with an EXPLICIT remainder, in-kernel.

This is the near-1 log residual that `log_bound.py`'s docstring flagged as future work,
and the ingredient BG's `omega_enclosure` (`R3Cert/Sweep.lean`) needs for `log(1-1/24)`.
Backed by Mathlib's `Real.abs_log_sub_add_sum_range_le`:

    | Real.log (1 - x) + sum_{i<n} x^{i+1}/(i+1) |  <=  x^{n+1} / (1 - x)      (|x| < 1)

so with S = sum_{i<n} x^{i+1}/(i+1) and E = x^{n+1}/(1-x),

    -S - E  <=  Real.log (1 - x)  <=  E - S .

For x = 1/k this is an exact rational bracket.  Both S and E are computed exactly (Fraction)
and the emitted Lean discharges the sum by `simp [Finset.sum_range_succ]; norm_num` and the
remainder by `norm_num`, exactly as BG's omega proof does.

HONEST SCOPE.  x = 1/k, k >= 2 integer (so 0 < x <= 1/2, series converges fast).  Not RH
or BG progress; a maintenance/regeneration tool for BG's near-1 log constant.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr


@dataclass
class TaylorLogNear1Certificate:
    """Enclosure `-S-E <= Real.log(1 - 1/k) <= E-S` from the degree-`degree` Taylor sum of
    `log(1-x)` at `x = 1/k`, with Mathlib's explicit series remainder."""

    name: str
    k: int
    degree: int = 4

    def x(self) -> Fr:
        return Fr(1, self.k)

    def taylor_sum(self) -> Fr:
        x = self.x()
        return sum((x ** (i + 1) / (i + 1) for i in range(self.degree)), Fr(0))

    def remainder(self) -> Fr:
        x = self.x()
        return x ** (self.degree + 1) / (1 - x)

    def bracket(self) -> tuple[Fr, Fr]:
        S, E = self.taylor_sum(), self.remainder()
        return (-S - E, E - S)

    def check(self) -> bool:
        if not (self.k >= 2 and self.degree >= 1):
            return False
        lo, hi = self.bracket()
        v = math.log(1 - 1 / self.k)
        return float(lo) <= v <= float(hi) and lo <= hi

    def htay_block(self, hname: str = "htay") -> str:
        """Lean lines establishing `{hname} : -E <= log(1-1/k)+S  &&  log(1-1/k)+S <= E`
        (the two `.1`/`.2` facts a downstream nlinarith consumes)."""
        k, n = self.k, self.degree
        S, E = self.taylor_sum(), self.remainder()
        return (
            f"  have {hname} := Real.abs_log_sub_add_sum_range_le (x := (1 / {k} : ℝ)) (by norm_num) {n}\n"
            f"  have hsum : (∑ i ∈ Finset.range {n}, (1 / {k} : ℝ) ^ (i + 1) / (i + 1))"
            f" = {S.numerator} / {S.denominator} := by\n"
            f"    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num\n"
            f"  have herr : |(1 / {k} : ℝ)| ^ ({n} + 1) / (1 - |1 / {k}|)"
            f" = {E.numerator} / {E.denominator} := by\n"
            f"    rw [show |(1 / {k} : ℝ)| = 1 / {k} by rw [abs_of_pos]; norm_num]; norm_num\n"
            f"  rw [hsum, herr, abs_le] at {hname}\n"
        )

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: invalid Taylor-log bracket -- refusing to emit")
        lo, hi = self.bracket()
        return (
            f"theorem {self.name} :\n"
            f"    ({lo.numerator} : ℝ) / {lo.denominator} ≤ Real.log (1 - 1 / {self.k})\n"
            f"      ∧ Real.log (1 - 1 / {self.k}) ≤ ({hi.numerator} : ℝ) / {hi.denominator} := by\n"
            f"{self.htay_block('htay')}"
            f"  exact ⟨by nlinarith [htay.1, htay.2], by nlinarith [htay.1, htay.2]⟩\n"
        )
