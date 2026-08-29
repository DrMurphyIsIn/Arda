"""Reusable emitter: kernel-verified two-sided bounds on the Riemann zeta at an
integer k >= 2,  zeta(k) = sum_{n>=1} 1/n^k, via the Dirichlet series
(`zeta_eq_tsum_one_div_nat_cpow`) plus a GENERAL square-telescoping tail

    1/n^k  <=  1/n^2  <=  1/((n-1) n)  =  1/(n-1) - 1/n ,

so the tail from the M-th term telescopes to <= 1/(M-1).  Tightness is controlled
by the split index M (number of leading terms summed exactly): the emitted bound is

    S_M  <=  zeta(k)  <=  S_M + 1/(M-1),      S_M = sum_{n=1}^{M-1} 1/n^k.

This turns the bespoke zeta(2)/zeta(3)/zeta(4) hand-proofs (see ZetaNumerics.lean)
into a one-line emitter call for any k >= 2, any precision M.

HONEST SCOPE.  Re(s) > 1 (convergent series) only -- a numeric-bounds tool, NOT
progress on RH.  The RH-relevant zeta(1/2) needs the analytic continuation and is
out of scope.  The generator is untrusted; the Lean kernel is the arbiter.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


@dataclass
class ZetaBoundCertificate:
    """Two-sided bound  S_M <= zeta(k) <= S_M + 1/(M-1)  for integer k >= 2 and
    split index M >= 2, emitted as kernel-checkable Lean over Mathlib v4.32.0."""

    name: str
    k: int
    M: int = 3

    def leading(self) -> Fr:
        # sum_{i in range M} 1/i^k  =  sum_{n=1}^{M-1} 1/n^k  (the i = 0 term is 0)
        return sum((Fr(1, n ** self.k) for n in range(1, self.M)), Fr(0))

    def bracket(self) -> tuple[Fr, Fr]:
        lo = self.leading()
        return lo, lo + Fr(1, self.M - 1)

    def check(self) -> bool:
        if not (self.k >= 2 and self.M >= 2):
            return False
        lo, hi = self.bracket()
        try:
            import mpmath as mp
            v = float(mp.zeta(self.k))
        except Exception:
            # crude fallback: a long partial sum
            v = float(sum(Fr(1, n ** self.k) for n in range(1, 100000)))
        return float(lo) <= v <= float(hi) and lo <= hi

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: invalid zeta bound -- refusing to emit")
        k, M = self.k, self.M
        lo, hi = self.bracket()
        eqname = f"{self.name}_eq_ofReal"
        # leading-sum unfolding: range M -> (M-1) x sum_range_succ + sum_range_one
        succs = ", ".join(["Finset.sum_range_succ"] * (M - 1) + ["Finset.sum_range_one"])
        return (
            f"/-- zeta({k}) as a real Dirichlet series (each complex term a nonneg real cast). -/\n"
            f"theorem {eqname} :\n"
            f"    riemannZeta {k} = ((∑' n : ℕ, 1 / (n : ℝ) ^ {k} : ℝ) : ℂ) := by\n"
            f"  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), Complex.ofReal_tsum]\n"
            f"  refine tsum_congr (fun n => ?_)\n"
            f"  rw [show ({k} : ℂ) = (({k} : ℕ) : ℂ) by norm_cast, Complex.cpow_natCast]\n"
            f"  push_cast; ring\n\n"
            f"/-- Two-sided bound  {lo} <= zeta({k}) <= {hi}  (square-telescoping tail). -/\n"
            f"theorem {self.name} :\n"
            f"    ({lo.numerator} : ℝ) / {lo.denominator} ≤ (riemannZeta {k}).re\n"
            f"      ∧ (riemannZeta {k}).re ≤ ({hi.numerator} : ℝ) / {hi.denominator} := by\n"
            f"  rw [{eqname}, Complex.ofReal_re]\n"
            f"  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ {k}) :=\n"
            f"    Real.summable_one_div_nat_pow.mpr (by norm_num)\n"
            f"  have hsplit := hf.sum_add_tsum_nat_add {M}\n"
            f"  have hlead : (∑ i ∈ Finset.range {M}, 1 / (i : ℝ) ^ {k})"
            f" = ({lo.numerator} : ℝ) / {lo.denominator} := by\n"
            f"    rw [{succs}]; norm_num\n"
            f"  set g : ℕ → ℝ := fun i => 1 / ((i : ℝ) + {M - 1}) with hg\n"
            f"  have hts : Summable (fun i : ℕ => 1 / (((i + {M} : ℕ)) : ℝ) ^ {k}) :=\n"
            f"    (summable_nat_add_iff {M}).mpr hf\n"
            f"  have hterm : ∀ i : ℕ, (1 / (((i + {M} : ℕ)) : ℝ) ^ {k}) ≤ g i - g (i + 1) := by\n"
            f"    intro i\n"
            f"    have hfi : (1 / (((i + {M} : ℕ)) : ℝ) ^ {k}) = 1 / ((i : ℝ) + {M}) ^ {k} := by\n"
            f"      push_cast; ring\n"
            f"    have e : g i - g (i + 1) = 1 / (((i : ℝ) + {M - 1}) * ((i : ℝ) + {M})) := by\n"
            f"      simp only [hg]; push_cast; field_simp; ring\n"
            f"    rw [hfi, e]\n"
            f"    have hb : (1 : ℝ) ≤ (i : ℝ) + {M} := by\n"
            f"      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i\n"
            f"      linarith\n"
            f"    have step1 : 1 / ((i : ℝ) + {M}) ^ {k} ≤ 1 / ((i : ℝ) + {M}) ^ 2 :=\n"
            f"      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hb (by norm_num))\n"
            f"    have step2 : 1 / ((i : ℝ) + {M}) ^ 2"
            f" ≤ 1 / (((i : ℝ) + {M - 1}) * ((i : ℝ) + {M})) :=\n"
            f"      one_div_le_one_div_of_le (by positivity)"
            f" (by nlinarith [(by positivity : (0 : ℝ) ≤ (i : ℝ) + {M - 1})])\n"
            f"    exact le_trans step1 step2\n"
            f"  have htail : (∑' i : ℕ, 1 / (((i + {M} : ℕ)) : ℝ) ^ {k}) ≤ 1 / {M - 1} := by\n"
            f"    apply hts.tsum_le_of_sum_range_le\n"
            f"    intro N\n"
            f"    calc ∑ i ∈ Finset.range N, 1 / (((i + {M} : ℕ)) : ℝ) ^ {k}\n"
            f"        ≤ ∑ i ∈ Finset.range N, (g i - g (i + 1)) :="
            f" Finset.sum_le_sum (fun i _ => hterm i)\n"
            f"      _ = g 0 - g N := Finset.sum_range_sub' g N\n"
            f"      _ ≤ 1 / {M - 1} := by\n"
            f"          have hg0 : g 0 = 1 / {M - 1} := by simp only [hg]; norm_num\n"
            f"          have hgN : (0 : ℝ) ≤ g N := by simp only [hg]; positivity\n"
            f"          rw [hg0]; linarith [hgN]\n"
            f"  refine ⟨?_, ?_⟩\n"
            f"  · calc ({lo.numerator} : ℝ) / {lo.denominator}"
            f" = ∑ i ∈ Finset.range {M}, 1 / (i : ℝ) ^ {k} := hlead.symm\n"
            f"      _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ {k} :="
            f" hf.sum_le_tsum (Finset.range {M}) (fun i _ => by positivity)\n"
            f"  · rw [← hsplit, hlead]; linarith [htail]\n"
        )
