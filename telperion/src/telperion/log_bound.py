"""Transcendental skill: rigorous rational bounds on Real.log q, in-kernel.

Companion to `exp_bracket.py` -- a second *transcendental* certificate (the
theorem's Lean statement contains `Real.log`, and the bound is DERIVED via
Mathlib lemmas, not imported as a hypothesis).  Where `exp_bracket` uses a Taylor
lower bound on exp, this uses the elementary convex bounds

    1 - 1/x  <=  log x  <=  x - 1        (x > 0),

both Mathlib one-liners: `Real.log_le_sub_one_of_pos` for the upper bound, and
the same applied to 1/x (with `Real.log_inv`) for the lower.  For a rational
q = n/d > 0 this gives the exact rational bracket

    1 - d/n  <=  Real.log (n/d)  <=  n/d - 1.

HONEST SCOPE.  This bracket is rigorous but COARSE -- tight only near q = 1
(width ~ (q-1)^2/... ).  Tight bounds need range reduction
(log q = e*log 2 + log(q*2^-e), q*2^-e in [1,2)) with Mathlib's `Real.log_two_*`
decimal bounds plus a near-1 series residual -- a larger build, noted not shipped.

Where it APPLIES to RH: the ARCHIMEDEAN / explicit-formula pieces that carry
log -- the Li-coefficient trend lambda_n^inf ~ (n/2)(log n - 1 - gamma + log 4pi),
zero-free-region constants, the trivial factor of xi.  It does NOT reach the deep
transcendentals (zeta(1/2), Stieltjes constants, the xi Taylor coefficients a_k):
those need in-kernel zeta/Gamma-derivative bounds Mathlib does not have.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr


LOG_BOUND_TEMPLATE = """theorem {name} :
    (1 - ({d} : ℝ) / {n}) ≤ Real.log (({n} : ℝ) / {d})
      ∧ Real.log (({n} : ℝ) / {d}) ≤ ({n} : ℝ) / {d} - 1 := by
  have hpos : (0 : ℝ) < ({n} : ℝ) / {d} := by norm_num
  have hupper : Real.log (({n} : ℝ) / {d}) ≤ ({n} : ℝ) / {d} - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have hinvpos : (0 : ℝ) < ({d} : ℝ) / {n} := by norm_num
  have hlow' : Real.log (({d} : ℝ) / {n}) ≤ ({d} : ℝ) / {n} - 1 :=
    Real.log_le_sub_one_of_pos hinvpos
  have hne : (({n} : ℝ) / {d})⁻¹ = ({d} : ℝ) / {n} := by norm_num
  have hneg : Real.log (({d} : ℝ) / {n}) = - Real.log (({n} : ℝ) / {d}) := by
    rw [← hne, Real.log_inv]
  constructor
  · nlinarith [hlow', hneg]
  · exact hupper"""


@dataclass(frozen=True)
class LogBoundCertificate:
    """The coarse rigorous bracket  1 - d/n <= log(n/d) <= n/d - 1  for a positive
    rational q = n/d, emitted as one Lean theorem backed by Mathlib's convex log
    bounds.  `n`, `d` positive integers."""

    name: str
    n: int
    d: int

    def q(self) -> Fr:
        return Fr(self.n, self.d)

    def bracket(self) -> tuple[Fr, Fr]:
        q = self.q()
        return (1 - Fr(self.d, self.n), q - 1)

    def check(self) -> bool:
        """The bracket really contains log(q) (numeric sanity) and is well-formed."""
        if not (self.n > 0 and self.d > 0):
            return False
        lo, hi = self.bracket()
        v = math.log(self.n / self.d)
        return float(lo) <= v <= float(hi) and lo <= hi

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: invalid log bracket -- refusing to emit")
        return LOG_BOUND_TEMPLATE.format(name=self.name, n=self.n, d=self.d) + "\n"
