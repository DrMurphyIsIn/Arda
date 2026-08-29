"""Transcendental skill: TIGHT rigorous rational enclosures of `Real.log q`, in-kernel.

Where `LogBoundCertificate` emits the COARSE convex bracket `1 - d/n <= log(n/d) <=
n/d - 1` (tight only near q = 1), this emits the TIGHT enclosure BG actually needs --
range-reduced onto Mathlib's decimal constants `Real.log_two_{gt,lt}_d9` and
`Real.log_three_{gt,lt}_d9`, the "larger build, noted not shipped" flagged in
`log_bound.py`'s docstring.

For a rational q = n/d whose numerator and denominator factor over {2, 3}, write
    log(n/d) = c2 * log 2 + c3 * log 3        (c2, c3 integers)
and enclose it by the interval box of the four d9 bounds, rounded OUTWARD to the
requested rational precision.  This regenerates BG's `log_three_half_enclosure`
(405/1000 < log(3/2) < 406/1000) and `log_four_third_enclosure` (287/1000 <
log(4/3) < 288/1000) in `R3Cert/Sweep.lean` EXACTLY -- verified in the example.

HONEST SCOPE.  Basis {2, 3} only (covers BG's sweep constants log(3/2), log(4/3),
and any 2^a 3^b ratio).  Constants needing log 23 or a near-1 Taylor residual
(BG's `omegaVal`) are out of scope here -- a separate emitter.  Not RH or BG
progress; a maintenance/regeneration tool for BG's log cruxes.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr

# Mathlib v4.32.0 decimal constants (strict bounds), as exact rationals.
#   Real.log_two_gt_d9   : 0.6931471803 < Real.log 2
#   Real.log_two_lt_d9   : Real.log 2 < 0.6931471808
#   Real.log_three_gt_d9 : 1.0986122886 < Real.log 3
#   Real.log_three_lt_d9 : Real.log 3 < 1.0986122887
LOG2_LO, LOG2_HI = Fr(6931471803, 10**10), Fr(6931471808, 10**10)
LOG3_LO, LOG3_HI = Fr(10986122886, 10**10), Fr(10986122887, 10**10)


def _factor_23(m: int) -> tuple[int, int]:
    """Return (a2, a3) with m = 2^a2 * 3^a3, or raise if m has any other prime factor."""
    if m <= 0:
        raise ValueError(f"factor_23: need positive int, got {m}")
    a2 = 0
    while m % 2 == 0:
        m //= 2
        a2 += 1
    a3 = 0
    while m % 3 == 0:
        m //= 3
        a3 += 1
    if m != 1:
        raise ValueError(f"factor_23: {m} has a prime factor outside {{2, 3}}")
    return a2, a3


def _log_nat_lemma(name: str, m: int, a2: int, a3: int) -> str:
    # have h<name> : Real.log (m : R) = a2 * Real.log 2 + a3 * Real.log 3
    return (
        f"  have {name} : Real.log ({m} : ℝ) = ({a2} : ℝ) * Real.log 2 + ({a3} : ℝ) * Real.log 3 := by\n"
        f"    rw [show ({m} : ℝ) = (2 : ℝ) ^ ({a2} : ℕ) * (3 : ℝ) ^ ({a3} : ℕ) by norm_num,\n"
        f"      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]\n"
        f"    push_cast; ring\n"
    )


@dataclass
class TightLogCertificate:
    """Tight enclosure `lo < Real.log (n/d) < hi` for q = n/d with n, d factoring over
    {2, 3}, backed by Mathlib's d9 decimal log constants.  `precision` = rounding grid
    denominator (default 1000, matching BG's sweep enclosures)."""

    name: str
    n: int
    d: int
    precision: int = 1000

    def coeffs(self) -> tuple[int, int]:
        a2, a3 = _factor_23(self.n)
        b2, b3 = _factor_23(self.d)
        return a2 - b2, a3 - b3

    def bracket(self) -> tuple[Fr, Fr]:
        c2, c3 = self.coeffs()
        # min / max of c2*log2 + c3*log3 over the d9 interval box
        lo = c2 * (LOG2_LO if c2 > 0 else LOG2_HI) + c3 * (LOG3_LO if c3 > 0 else LOG3_HI)
        hi = c2 * (LOG2_HI if c2 > 0 else LOG2_LO) + c3 * (LOG3_HI if c3 > 0 else LOG3_LO)
        P = self.precision
        return (Fr(math.floor(lo * P), P), Fr(math.ceil(hi * P), P))

    def check(self) -> bool:
        try:
            c2, c3 = self.coeffs()
        except ValueError:
            return False
        lo, hi = self.bracket()
        v = math.log(self.n / self.d)
        # bracket contains the true value AND is strictly provable from the d9 box
        box_lo = c2 * (LOG2_LO if c2 > 0 else LOG2_HI) + c3 * (LOG3_LO if c3 > 0 else LOG3_HI)
        box_hi = c2 * (LOG2_HI if c2 > 0 else LOG2_LO) + c3 * (LOG3_HI if c3 > 0 else LOG3_LO)
        return (float(lo) < v < float(hi)) and (lo < box_lo) and (box_hi < hi)

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: invalid/unprovable tight-log bracket -- refusing to emit")
        c2, c3 = self.coeffs()
        a2, a3 = _factor_23(self.n)
        b2, b3 = _factor_23(self.d)
        # emit over the precision grid (e.g. .../1000), matching BG's sweep enclosures
        # verbatim rather than Fraction's reduced form (81/200).
        P = self.precision
        box_lo = c2 * (LOG2_LO if c2 > 0 else LOG2_HI) + c3 * (LOG3_LO if c3 > 0 else LOG3_HI)
        box_hi = c2 * (LOG2_HI if c2 > 0 else LOG2_LO) + c3 * (LOG3_HI if c3 > 0 else LOG3_LO)
        lo = Fr(math.floor(box_lo * P), 1)  # numerator over P (kept unreduced below)
        hi = Fr(math.ceil(box_hi * P), 1)
        lo_num, lo_den = int(lo), P
        hi_num, hi_den = int(hi), P
        hN = _log_nat_lemma("hN", self.n, a2, a3)
        hD = _log_nat_lemma("hD", self.d, b2, b3)
        return (
            f"theorem {self.name} :\n"
            f"    ({lo_num} : ℝ) / {lo_den} < Real.log (({self.n} : ℝ) / {self.d})\n"
            f"      ∧ Real.log (({self.n} : ℝ) / {self.d}) < ({hi_num} : ℝ) / {hi_den} := by\n"
            f"  have h2lo := Real.log_two_gt_d9\n"
            f"  have h2hi := Real.log_two_lt_d9\n"
            f"  have h3lo := Real.log_three_gt_d9\n"
            f"  have h3hi := Real.log_three_lt_d9\n"
            f"{hN}"
            f"{hD}"
            f"  have e : Real.log (({self.n} : ℝ) / {self.d})"
            f" = ({c2} : ℝ) * Real.log 2 + ({c3} : ℝ) * Real.log 3 := by\n"
            f"    rw [Real.log_div (by norm_num) (by norm_num), hN, hD]; push_cast; ring\n"
            f"  rw [e]\n"
            f"  refine ⟨by nlinarith [h2lo, h2hi, h3lo, h3hi], by nlinarith [h2lo, h2hi, h3lo, h3hi]⟩\n"
        )
