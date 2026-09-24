/-
CruxFQ_ZeroSideFejer.lean -- crux-fq workflow, KERNEL seat, zero-side companion of
CruxFQ_PoissonRigidity.lean (li_positivity island).

conjecture1_proved = False. Nothing here bears on where the zeros of `riemannZeta` lie.

Checked by: `cd telperion/examples/rvm_bridge/lean && lake env lean Crux/CruxFQ_ZeroSideFejer.lean`
(Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 fbdc36bb). No `sorry`, `admit`, `native_decide`,
new `axiom`, or `opaque`.

WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked): the zero-side transport of Theorem A's Fejer
step. Theorem A forces the support of a self-dual measure by a test pair whose dual half lives in the
dual gap, so that every dual atom drops out. The Guinand-Weil pair of zeta has a dual (prime-side)
gap `(-log 2, log 2)`: no prime power has `log n < log 2`. For every Weil test supported in that gap
the prime side vanishes (`primeSide_eq_zero_of_gap`), so the zero-side sum equals the archimedean
side (`zero_side_fejer`), and the Weil form is purely archimedean (`weilForm_eq_archSide_of_gap`).
`archSide` is defined from the Gamma factor and the two pole terms alone: no arithmetic input.
Consequence (paper-level, recorded, not a theorem here): any certificate built from tests in the
prime gap is uniform over every function sharing zeta's archimedean data and pole terms, so it cannot
be the step that separates zeta from the program's fakes (golden-fake Gaussian-layer barrier,
Crux_meta_barriers.lean on this island).
-/
import E6Bridge5

open Complex MeasureTheory

noncomputable section

namespace CruxFQZeroSide

open WeilExplicit

/-- **The prime-side gap (kernel).** If `g` vanishes on `|u| ≥ log 2`, the prime side is `0`. -/
theorem primeSide_eq_zero_of_gap {g : ℝ → ℂ} (hg : ∀ u : ℝ, Real.log 2 ≤ |u| → g u = 0) :
    primeSide g = 0 := by
  unfold primeSide
  have hterm : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (g (Real.log n) + g (-Real.log n)) = 0 := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hpos : 0 ≤ Real.log n := le_trans (Real.log_nonneg (by norm_num)) hlog
      have h1 : g (Real.log n) = 0 := hg _ (by rw [abs_of_nonneg hpos]; exact hlog)
      have h2 : g (-Real.log n) = 0 := hg _ (by rw [abs_neg, abs_of_nonneg hpos]; exact hlog)
      rw [h1, h2]; simp
  simp only [hterm, tsum_zero]

/-- **Zero-side Fejer identity (kernel).** For a Weil test supported in the prime gap, the
multiplicity-weighted zero sum (over all zeros, off-line ones included) equals the archimedean side. -/
theorem zero_side_fejer {g : ℝ → ℂ} (hg : IsWeilTest g)
    (hgap : ∀ u : ℝ, Real.log 2 ≤ |u| → g u = 0) :
    HasSum (fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel g ρ) (archSide g) := by
  have h := (RvMBridge4.limit_explicit_formula g hg).2
  rwa [primeSide_eq_zero_of_gap hgap, sub_zero] at h

/-- **The Weil form in the prime gap is archimedean (kernel).** -/
theorem weilForm_eq_archSide_of_gap {f : ℝ → ℂ} (hgap : ∀ u : ℝ, Real.log 2 ≤ |u| → f u = 0) :
    weilForm f = archSide f := by
  unfold weilForm
  rw [primeSide_eq_zero_of_gap hgap, sub_zero]

/-- The gap is sharp: the prime `2` sits exactly at its edge (`Λ(2) = log 2 > 0`). -/
theorem prime_gap_edge : Real.log (2 : ℕ) = Real.log 2 ∧ 0 < ArithmeticFunction.vonMangoldt 2 := by
  refine ⟨by norm_num, ?_⟩
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact Real.log_pos (by norm_num)

end CruxFQZeroSide

#print axioms CruxFQZeroSide.primeSide_eq_zero_of_gap
#print axioms CruxFQZeroSide.zero_side_fejer
#print axioms CruxFQZeroSide.weilForm_eq_archSide_of_gap
#print axioms CruxFQZeroSide.prime_gap_edge
