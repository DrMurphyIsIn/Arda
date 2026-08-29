"""Robin's criterion for the Riemann Hypothesis (Robin 1984) -- a genuinely different,
ELEMENTARY ARITHMETIC, RH-EQUIVALENT angle (the hyperbolicity/Jensen family is analytic
and RH-*necessary* only).

    RH  <=>  sigma(n) < e^gamma * n * log log n   for all n >= 5041,

where sigma(n) = sum of divisors of n and gamma is Euler-Mascheroni.  A single
n >= 5041 violating this would DISPROVE RH; the (finitely many) known exceptions are
all <= 5040 (the largest is n = 5040 itself).  The extremal near-boundary cases are
the superabundant numbers, along which sigma(n)/(n log log n) -> e^gamma from below.

RobinCertificate machine-verifies ONE instance.  The left side sigma(n) is an EXACT
integer.  The right side is transcendental, so we lower-bound it by rationals:

    sigma(n)  <  E_lo * n * LL_lo  <=  e^gamma * n * log log n ,

given a rational  E_lo <= e^gamma  and  LL_lo <= log log n.  The arithmetic inequality
sigma(n) < E_lo * n * LL_lo is exact; the two bracket facts (E_lo <= e^gamma, LL_lo <=
log log n) are consumed as hypotheses -- the same consume-a-bracket architecture as
`TuranEnclosureCertificate`.  Their in-kernel provenance:

  * e^gamma:  gamma > 1/2 is `Real.one_half_lt_eulerMascheroniConstant` (Mathlib), and
    e^{1/2} >= E_lo by a positive Taylor partial sum (cf. `ExpBracketCertificate`).  The
    clean gamma>1/2 bound gives e^gamma > 1.6487 -- enough for COMFORTABLE n but NOT the
    tight superabundant n (need e^gamma > ~1.76, i.e. a tighter gamma from
    `eulerMascheroniSeq`, a further build).
  * log log n:  `TightLogCertificate` / the near-1 Taylor-log emitter (`taylor_log.py`)
    range-reduced onto Mathlib's `Real.log_two_*_d9`.  A coarse floor-to-power-of-2
    lower bound (this module's default) suffices for comfortable n; the tight
    superabundant n need the range-reduced tight log.

HONEST SCOPE.  Finite per-n verification of an RH-EQUIVALENT condition -- stronger than
the RH-necessary Jensen ladder, but still evidence on a finite set, never a proof of RH.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr

import sympy as sp

# Mathlib v4.32.0 decimal constant Real.log_two_gt_d9 : 0.6931471803 < Real.log 2
LOG2_LO = Fr(6931471803, 10 ** 10)


def _rat(f: Fr) -> str:
    f = Fr(f)
    return f"({f.numerator} : ℝ)" if f.denominator == 1 else f"(({f.numerator} : ℝ) / {f.denominator})"


def exp_lower(x: Fr, terms: int = 40, grid: int = 10 ** 6) -> Fr:
    """Rational lower bound on e^x for x >= 0: the truncated Taylor sum (all terms
    positive), rounded DOWN to a `grid` denominator so the Lean literal stays clean
    while remaining a valid lower bound.  This is what `ExpBracketCertificate` proves."""
    s, t = Fr(0), Fr(1)
    for k in range(terms):
        if k > 0:
            t *= Fr(x) / k
        s += t
    return Fr(math.floor(s * grid), grid)


def loglog_exponents(n: int) -> tuple[int, int]:
    """(a, c) with 2^a <= n and 2^c <= a*log2_lo, so log n >= a*log2 and
    log log n >= c*log2 -- the exponents the in-kernel loglog chain uses."""
    a = n.bit_length() - 1                       # 2^a <= n < 2^{a+1}
    logn_lo = a * LOG2_LO
    if logn_lo <= 1:
        raise ValueError(f"loglog_exponents: log n too small for n={n} (need n >= 16)")
    c = 0
    while Fr(2) ** (c + 1) <= logn_lo:
        c += 1
    return a, c


def coarse_loglog_lower(n: int) -> Fr:
    """Rational LL_lo <= log log n from log 2 alone: log n >= a*log2 (2^a <= n), then
    log log n >= c*log2 (2^c <= a*log2_lo).  Coarse but purely from Real.log_two_gt_d9."""
    _, c = loglog_exponents(n)
    return c * LOG2_LO


@dataclass
class RobinCertificate:
    """One instance of Robin's inequality sigma(n) < e^gamma n log log n, certified by
    the exact arithmetic sigma(n) < egamma_lo * n * loglog_lo over consumed rational
    lower bounds egamma_lo <= e^gamma and loglog_lo <= log log n."""

    name: str
    n: int
    egamma_lo: Fr
    loglog_lo: Fr
    gamma_lo: Fr | None = None      # provenance for the unconditional emitter
    exp_nterms: int = 12

    @classmethod
    def from_gamma_lower(cls, n: int, gamma_lo: Fr, exp_terms: int = 12,
                         name: str | None = None) -> "RobinCertificate":
        """Build with e^gamma lower bound derived from a rational gamma lower bound
        (Taylor exp) and the coarse log-2 loglog lower bound."""
        return cls(name=name or f"robin_n{n}", n=n,
                   egamma_lo=exp_lower(Fr(gamma_lo), exp_terms),
                   loglog_lo=coarse_loglog_lower(n),
                   gamma_lo=Fr(gamma_lo), exp_nterms=exp_terms)

    def sigma(self) -> int:
        return int(sp.divisor_sigma(self.n))

    def rhs_lo(self) -> Fr:
        return Fr(self.egamma_lo) * self.n * Fr(self.loglog_lo)

    def check(self) -> bool:
        if self.n < 16 or self.egamma_lo <= 0 or self.loglog_lo <= 0:
            return False
        # sanity: the consumed brackets must actually be true lower bounds
        if float(self.egamma_lo) > math.exp(0.5772156649015329) + 1e-9:
            return False
        if float(self.loglog_lo) > math.log(math.log(self.n)) + 1e-12:
            return False
        return self.sigma() < self.rhs_lo()

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: Robin instance not certified "
                             f"(sigma({self.n})={self.sigma()} >= worst-case RHS, "
                             f"or brackets invalid) -- refusing to emit")
        sig = self.sigma()
        E, LL = _rat(self.egamma_lo), _rat(self.loglog_lo)
        return (
            f"/-- Robin's inequality at n={self.n}: sigma({self.n})={sig} < "
            f"e^gamma * {self.n} * log log {self.n}.  Consumes E_lo <= e^gamma and "
            f"LL_lo <= log log n; the arithmetic sigma < E_lo*n*LL_lo is exact. -/\n"
            f"theorem {self.name}\n"
            f"    (hγ : {E} ≤ Real.exp Real.eulerMascheroniConstant)\n"
            f"    (hll : {LL} ≤ Real.log (Real.log ({self.n} : ℝ))) :\n"
            f"    ({sig} : ℝ) < Real.exp Real.eulerMascheroniConstant "
            f"* ({self.n} : ℝ) * Real.log (Real.log ({self.n} : ℝ)) := by\n"
            f"  have hE : (0:ℝ) < {E} := by norm_num\n"
            f"  have hLL : (0:ℝ) < {LL} := by norm_num\n"
            f"  have hn : (0:ℝ) < ({self.n} : ℝ) := by norm_num\n"
            f"  have hg : (0:ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _\n"
            f"  have harith : ({sig} : ℝ) < {E} * ({self.n} : ℝ) * {LL} := by norm_num\n"
            f"  nlinarith [hγ, hll, hE, hLL, hn, hg,\n"
            f"    mul_le_mul hγ (le_refl ({self.n} : ℝ)) (le_of_lt hn) (le_of_lt hg),\n"
            f"    mul_le_mul_of_nonneg_left hll (le_of_lt (mul_pos hg hn))]\n"
        )

    def lean_unconditional(self) -> str:
        """Self-contained Robin theorem for the clean case (gamma>1/2 via Mathlib +
        coarse log-2 loglog): discharges BOTH brackets in-kernel, so there are no free
        hypotheses.  Requires gamma_lo == 1/2 (the clean Mathlib bound) and the coarse
        loglog structure.  e^gamma bound reuses the ExpBracket Taylor pattern
        (Real.sum_le_exp_of_nonneg); loglog bound uses gcongr + Real.log_pow +
        Real.log_two_gt_d9.  Only certifies COMFORTABLE n (see module docstring)."""
        if not self.check():
            raise ValueError(f"{self.name}: not certified -- refusing to emit")
        if self.gamma_lo != Fr(1, 2):
            raise ValueError(f"{self.name}: unconditional emitter needs gamma_lo=1/2 "
                             f"(the clean Mathlib bound), got {self.gamma_lo}")
        a, c = loglog_exponents(self.n)
        if self.loglog_lo != c * LOG2_LO:
            raise ValueError(f"{self.name}: unconditional emitter needs the coarse log-2 loglog bound")
        sig, N = self.sigma(), self.exp_nterms
        E, LL = _rat(self.egamma_lo), _rat(self.loglog_lo)
        aL = _rat(a * LOG2_LO)                       # a * log2_lo (rational)
        return (
            f"/-- Robin's inequality at n={self.n}, UNCONDITIONAL: sigma({self.n})={sig} < "
            f"e^gamma * {self.n} * log log {self.n}.  Both brackets discharged in-kernel "
            f"(gamma>1/2 via Real.one_half_lt_eulerMascheroniConstant; loglog via log-2 d9). -/\n"
            f"theorem {self.name} :\n"
            f"    ({sig} : ℝ) < Real.exp Real.eulerMascheroniConstant "
            f"* ({self.n} : ℝ) * Real.log (Real.log ({self.n} : ℝ)) := by\n"
            f"  -- e^gamma >= e^(1/2) >= E_lo  (Taylor lower bound + gamma>1/2)\n"
            f"  have hexp : ({E}) ≤ Real.exp ((1 : ℝ) / 2) := by\n"
            f"    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) {N})\n"
            f"    norm_num [Finset.sum_range_succ, Nat.factorial]\n"
            f"  have hγ : ({E}) ≤ Real.exp Real.eulerMascheroniConstant :=\n"
            f"    le_trans hexp (Real.exp_le_exp.mpr (le_of_lt Real.one_half_lt_eulerMascheroniConstant))\n"
            f"  -- log n >= a * log 2 >= a * log2_lo\n"
            f"  have hl2 := Real.log_two_gt_d9\n"
            f"  have hlogn : ({a} : ℝ) * Real.log 2 ≤ Real.log ({self.n} : ℝ) := by\n"
            f"    have h : Real.log ((2 : ℝ) ^ ({a} : ℕ)) ≤ Real.log ({self.n} : ℝ) := by\n"
            f"      gcongr\n"
            f"      norm_num\n"
            f"    rw [Real.log_pow] at h\n"
            f"    exact_mod_cast h\n"
            f"  have hlogn_lo : ({aL}) ≤ Real.log ({self.n} : ℝ) := by nlinarith [hlogn, hl2]\n"
            f"  -- log log n >= c * log 2 = LL_lo\n"
            f"  have h2c : ((2 : ℝ) ^ ({c} : ℕ)) ≤ Real.log ({self.n} : ℝ) := by\n"
            f"    have hb : ((2 : ℝ) ^ ({c} : ℕ)) ≤ ({aL}) := by norm_num\n"
            f"    linarith [hlogn_lo, hb]\n"
            f"  have hll : ({c} : ℝ) * Real.log 2 ≤ Real.log (Real.log ({self.n} : ℝ)) := by\n"
            f"    have h : Real.log ((2 : ℝ) ^ ({c} : ℕ)) ≤ Real.log (Real.log ({self.n} : ℝ)) := by\n"
            f"      gcongr\n"
            f"    rw [Real.log_pow] at h\n"
            f"    exact_mod_cast h\n"
            f"  have hLL : ({LL}) ≤ Real.log (Real.log ({self.n} : ℝ)) := by nlinarith [hll, hl2]\n"
            f"  -- positivity + exact arithmetic assembly\n"
            f"  have hE : (0:ℝ) < {E} := by norm_num\n"
            f"  have hLLp : (0:ℝ) < {LL} := by norm_num\n"
            f"  have hn : (0:ℝ) < ({self.n} : ℝ) := by norm_num\n"
            f"  have hg : (0:ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _\n"
            f"  have harith : ({sig} : ℝ) < {E} * ({self.n} : ℝ) * {LL} := by norm_num\n"
            f"  nlinarith [hγ, hLL, hE, hLLp, hn, hg,\n"
            f"    mul_le_mul hγ (le_refl ({self.n} : ℝ)) (le_of_lt hn) (le_of_lt hg),\n"
            f"    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]\n"
        )
