"""Robin's inequality at the RH-TIGHT boundary -- the SUPERABUNDANT regime, where
sigma(n)/(n loglog n) approaches e^gamma from below and the clean gamma>1/2 bound is
too loose.  This is the nucleus of the D3 colossally-abundant program: a self-contained
kernel proof of  sigma(n) < e^gamma n loglog n  for a superabundant n, using a TIGHT
gamma (Real.eulerMascheroniSeq) and a TIGHT loglog (3-smooth floor + taylor_log residual)
instead of the comfortable-regime coarse brackets in `robin.py`.

Currently instantiated (and kernel-verified) at n=25200 (= 2^4 3^2 5^2 7, superabundant,
ratio ~1.71).  The recipe pieces are exact rationals:

  * gamma:  gamma > harmonic m - log(m+1)  (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant).
    Choose m so m+1 = 2^p (clean log(m+1) = p log2); then gamma > H_m - p log2 >= gamma_clean
    (a clean rational), so e^gamma >= e^{gamma_clean} >= E_lo (Taylor exp lower bound).
  * loglog:  log n >= a2 log2 + a3 log3  (2^a2 3^a3 <= n) >= T (an integer);  then
    loglog n >= log T = b3 log3 + log(T/3^b3), with log(T/3^b3) >= taylor_log lower bound.

RH-EQUIVALENT, finite, UNCONDITIONAL (no imported enclosures).  A single instance;
generalizing the recipe to arbitrary colossally-abundant n is D3.  Scope stays honest:
this proves Robin at one hard n, NOT RH (which needs all n).
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr

import sympy as sp

# Mathlib v4.32.0 d9 decimal constants, EXACT rationals (as the lemmas actually state them).
LOG2_LO = Fr(6931471803, 10 ** 10)
LOG2_HI = Fr(6931471808, 10 ** 10)
LOG3_LO = Fr(10986122885, 10 ** 10)   # Real.log_three_gt_d9 states 1.0986122885 (NOT ...886)


def _rat(f: Fr) -> str:
    f = Fr(f)
    return f"({f.numerator} : ℝ)" if f.denominator == 1 else f"(({f.numerator} : ℝ) / {f.denominator})"


def _exp_taylor(x: Fr, n: int) -> Fr:
    s, t = Fr(0), Fr(1)
    for k in range(n):
        if k > 0:
            t *= Fr(x) / k
        s += t
    return s


@dataclass
class TightRobinCertificate:
    """Kernel-checkable  sigma(n) < e^gamma n loglog n  for a superabundant n, via a tight
    eulerMascheroniSeq gamma and a tight 3-smooth+taylor_log loglog.  Fields are the exact
    recipe; `for_n25200()` computes the validated instance."""

    name: str
    n: int
    m: int                 # harmonic index; m+1 must be 2^p
    p: int                 # m + 1 == 2**p
    gamma_clean: Fr        # <= H_m - p*log2_hi, a clean rational lower bound on gamma
    egamma_lo: Fr          # <= e^{gamma_clean}
    exp_nterms: int
    a2: int                # log n >= a2 log2 + a3 log3  (2^a2 3^a3 <= n)
    a3: int
    b2: int                # loglog base B = 2^b2 3^b3 ; log T = b2 log2 + b3 log3 - log(1-1/k)
    b3: int
    tl_k: int              # T = B * k/(k-1); loglog residual via taylor_log(1-1/tl_k)
    tl_deg: int
    T: Fr                  # rational threshold B*k/(k-1) with log n >= T
    loglog_lo: Fr          # <= log log n

    @staticmethod
    def _largest_3smooth(limit) -> tuple[int, int]:
        """(a2, a3) maximizing 2^a2 * 3^a3 <= limit (limit int or Fraction)."""
        best, ba, bb = Fr(0), 0, 0
        a = 0
        while Fr(2) ** a <= limit:
            b = 0
            while (Fr(2) ** a) * (Fr(3) ** b) <= limit:
                v = (Fr(2) ** a) * (Fr(3) ** b)
                if v > best:
                    best, ba, bb = v, a, b
                b += 1
            a += 1
        return ba, bb

    @classmethod
    def for_superabundant(cls, n: int, name: str | None = None,
                          tl_deg: int = 4, grid: int = 10 ** 9) -> "TightRobinCertificate":
        """Compute a tight recipe for a superabundant n: tight gamma via the smallest
        m+1=2^p that closes, tight loglog via log n >= a2 log2 + a3 log3, then
        loglog >= log(B*k/(k-1)) = b2 log2 + b3 log3 + taylor_log(k), B = 2^b2 3^b3."""
        sig = int(sp.divisor_sigma(n))
        a2, a3 = cls._largest_3smooth(n)
        logn_lo = a2 * LOG2_LO + a3 * LOG3_LO
        b2, b3 = cls._largest_3smooth(logn_lo)
        B = (Fr(2) ** b2) * (Fr(3) ** b3)
        r = logn_lo / B                                  # >= 1
        # largest k/(k-1) <= r  ->  smallest k with k >= r/(r-1)
        tl_k = math.ceil(float(r / (r - 1))) if r > 1 else 0
        if tl_k < 2:
            raise ValueError(f"n={n}: loglog residual degenerate (logn_lo hits a 3-smooth exactly)")
        x = Fr(1, tl_k)
        S = sum((x ** (i + 1) / (i + 1) for i in range(tl_deg)), Fr(0))
        E = x ** (tl_deg + 1) / (1 - x)
        T = B * Fr(tl_k, tl_k - 1)
        assert T <= logn_lo, (float(T), float(logn_lo))
        loglog_lo = Fr(math.floor((b2 * LOG2_LO + b3 * LOG3_LO + (S - E)) * grid), grid)
        # smallest p (m+1=2^p) whose clean gamma closes sigma < E_lo * n * loglog_lo
        for p in range(5, 14):
            m = 2 ** p - 1
            Hm = sum((Fr(1, k) for k in range(1, m + 1)), Fr(0))
            gc = Fr(math.floor((Hm - p * LOG2_HI) * 1000), 1000)
            nterms = 14
            E_lo = Fr(math.floor(_exp_taylor(gc, nterms) * 10 ** 6), 10 ** 6)
            if sig < E_lo * n * loglog_lo:
                c = cls(name=name or f"robin_tight_n{n}", n=n, m=m, p=p, gamma_clean=gc,
                        egamma_lo=E_lo, exp_nterms=nterms, a2=a2, a3=a3, b2=b2, b3=b3,
                        tl_k=tl_k, tl_deg=tl_deg, T=T, loglog_lo=loglog_lo)
                if c.check():
                    return c
        raise ValueError(f"n={n}: no tight recipe closes (margin too thin for m<=2^13-1)")

    @classmethod
    def for_n25200(cls) -> "TightRobinCertificate":
        return cls.for_superabundant(25200, name="robin_tight_n25200")

    def sigma(self) -> int:
        return int(sp.divisor_sigma(self.n))

    def _Hm(self) -> Fr:
        return sum((Fr(1, k) for k in range(1, self.m + 1)), Fr(0))

    def check(self) -> bool:
        if self.m + 1 != 2 ** self.p:
            return False
        if not (self.gamma_clean <= self._Hm() - self.p * LOG2_HI):
            return False
        if 2 ** self.a2 * 3 ** self.a3 > self.n:
            return False
        if not (self.a2 * LOG2_LO + self.a3 * LOG3_LO >= self.T):
            return False
        B = (Fr(2) ** self.b2) * (Fr(3) ** self.b3)
        if self.T * (self.tl_k - 1) != B * self.tl_k:                # T == B * tl_k/(tl_k-1)
            return False
        # exact closure
        return self.sigma() < Fr(self.egamma_lo) * self.n * Fr(self.loglog_lo)

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: tight recipe not certified -- refusing to emit")
        sig, N = self.sigma(), self.exp_nterms
        Hm = self._Hm()
        E_lo, LL, Tr = _rat(self.egamma_lo), _rat(self.loglog_lo), _rat(self.T)
        aL = _rat(self.a2 * LOG2_LO + self.a3 * LOG3_LO)
        Bsmooth = f"2 ^ ({self.b2} : ℕ) * 3 ^ ({self.b3} : ℕ)"
        x = Fr(1, self.tl_k)
        S = sum((x ** (i + 1) / (i + 1) for i in range(self.tl_deg)), Fr(0))
        Etl = x ** (self.tl_deg + 1) / (1 - x)
        smooth = f"2 ^ ({self.a2} : ℕ) * 3 ^ ({self.a3} : ℕ)"
        return (
            f"/-- Robin's inequality at n={self.n} (SUPERABUNDANT, RH-tight regime), UNCONDITIONAL:\n"
            f"    sigma({self.n})={sig} < e^gamma * {self.n} * log log {self.n}.  Tight gamma via\n"
            f"    eulerMascheroniSeq {self.m} (harmonic {self.m} - log {2 ** self.p}); tight loglog via\n"
            f"    log {self.n} >= {self.a2}log2+{self.a3}log3 > {self.T}, loglog >= log {self.T}. -/\n"
            f"theorem {self.name} :\n"
            f"    ({sig} : ℝ) < Real.exp Real.eulerMascheroniConstant "
            f"* ({self.n} : ℝ) * Real.log (Real.log ({self.n} : ℝ)) := by\n"
            f"  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant {self.m}\n"
            f"  have hharm : (harmonic {self.m} : ℚ) = {Hm.numerator} / {Hm.denominator} := by\n"
            f"    norm_num [harmonic, Finset.sum_range_succ]\n"
            f"  have hval : Real.eulerMascheroniSeq {self.m} = {_rat(Hm)} - Real.log {2 ** self.p} := by\n"
            f"    unfold Real.eulerMascheroniSeq\n"
            f"    rw [hharm]; push_cast; norm_num\n"
            f"  rw [hval] at hseq\n"
            f"  have hlogp : Real.log ({2 ** self.p} : ℝ) = {self.p} * Real.log 2 := by\n"
            f"    rw [show ({2 ** self.p} : ℝ) = 2 ^ ({self.p} : ℕ) by norm_num, Real.log_pow]; push_cast; ring\n"
            f"  rw [hlogp] at hseq\n"
            f"  have hl2hi := Real.log_two_lt_d9\n"
            f"  have hgl : {_rat(self.gamma_clean)} < Real.eulerMascheroniConstant := by nlinarith [hseq, hl2hi]\n"
            f"  have hE : {E_lo} ≤ Real.exp Real.eulerMascheroniConstant := by\n"
            f"    have hexp : {E_lo} ≤ Real.exp {_rat(self.gamma_clean)} := by\n"
            f"      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) {N})\n"
            f"      norm_num [Finset.sum_range_succ, Nat.factorial]\n"
            f"    exact le_trans hexp (Real.exp_le_exp.mpr (le_of_lt hgl))\n"
            f"  have hl2lo := Real.log_two_gt_d9\n"
            f"  have hl3lo := Real.log_three_gt_d9\n"
            f"  have hlogn : ({self.a2} : ℝ) * Real.log 2 + ({self.a3} : ℝ) * Real.log 3 ≤ Real.log ({self.n} : ℝ) := by\n"
            f"    have h : Real.log (({2 ** self.a2 * 3 ** self.a3} : ℝ)) ≤ Real.log ({self.n} : ℝ) := by\n"
            f"      gcongr\n"
            f"      norm_num\n"
            f"    have e : Real.log (({2 ** self.a2 * 3 ** self.a3} : ℝ)) = "
            f"({self.a2} : ℝ) * Real.log 2 + ({self.a3} : ℝ) * Real.log 3 := by\n"
            f"      rw [show (({2 ** self.a2 * 3 ** self.a3} : ℝ)) = {smooth} by norm_num,\n"
            f"        Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring\n"
            f"    rwa [e] at h\n"
            f"  have hlognT : {Tr} ≤ Real.log ({self.n} : ℝ) := by nlinarith [hlogn, hl2lo, hl3lo]\n"
            f"  have hll1 : Real.log {Tr} ≤ Real.log (Real.log ({self.n} : ℝ)) := by gcongr\n"
            f"  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / {self.tl_k} : ℝ)) (by norm_num) {self.tl_deg}\n"
            f"  have hsum : (∑ i ∈ Finset.range {self.tl_deg}, (1 / {self.tl_k} : ℝ) ^ (i + 1) / (i + 1)) = "
            f"{S.numerator} / {S.denominator} := by\n"
            f"    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num\n"
            f"  have herr : |(1 / {self.tl_k} : ℝ)| ^ ({self.tl_deg} + 1) / (1 - |1 / {self.tl_k}|) = "
            f"{Etl.numerator} / {Etl.denominator} := by\n"
            f"    rw [show |(1 / {self.tl_k} : ℝ)| = 1 / {self.tl_k} by rw [abs_of_pos]; norm_num]; norm_num\n"
            f"  rw [hsum, herr, abs_le] at htay\n"
            f"  have hlogT : {LL} ≤ Real.log {Tr} := by\n"
            f"    have e : Real.log {Tr} = ({self.b2} : ℝ) * Real.log 2 + ({self.b3} : ℝ) * Real.log 3 "
            f"- Real.log (1 - 1 / {self.tl_k} : ℝ) := by\n"
            f"      rw [show {Tr} = {Bsmooth} * (1 - 1 / {self.tl_k})⁻¹ by norm_num,\n"
            f"        Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num),\n"
            f"        Real.log_pow, Real.log_pow, Real.log_inv]; push_cast; ring\n"
            f"    rw [e]; nlinarith [htay.2, hl2lo, hl3lo]\n"
            f"  have hLL : {LL} ≤ Real.log (Real.log ({self.n} : ℝ)) := le_trans hlogT hll1\n"
            f"  have hEpos : (0 : ℝ) < {E_lo} := by norm_num\n"
            f"  have hLLpos : (0 : ℝ) < {LL} := by norm_num\n"
            f"  have hn : (0 : ℝ) < ({self.n} : ℝ) := by norm_num\n"
            f"  have hg : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _\n"
            f"  have harith : ({sig} : ℝ) < {E_lo} * ({self.n} : ℝ) * {LL} := by norm_num\n"
            f"  nlinarith [hE, hLL, hEpos, hLLpos, hn, hg,\n"
            f"    mul_le_mul hE (le_refl ({self.n} : ℝ)) (le_of_lt hn) (le_of_lt hg),\n"
            f"    mul_le_mul_of_nonneg_left hLL (le_of_lt (mul_pos hg hn))]\n"
        )
