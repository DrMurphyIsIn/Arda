/-
RvMArchElemBound — Arc B (archimedean Li growth), PR B1b part 1: compact form, bound, convergence.

Three stones toward extracting Taylor coefficients from the elementary series (B1a):

  * `archSummand_eq_compact` — the two pieces of `archSummand` collapse over a common denominator:
      `archSummand j z = M² / (2(j+1) · D_j)`,  `D_j = 2(j+1)(1−z) + 1`,  `M = (1−z)⁻¹`
    (the key cancellation is `(1−z)·M = 1`).  This makes the `O(1/j²)` pairing decay MANIFEST.
  * `archSummand_norm_le` — on `‖z‖ ≤ 1/4`:  `‖archSummand j z‖ ≤ 2/(j+1)²`
    (from `‖M‖ ≤ 4/3` and `‖D_j‖ ≥ (j+1)/2`).
  * `tendstoUniformlyOn_archSummand` — the partial sums of `∑' j, archSummand j` converge
    UNIFORMLY on `closedBall 0 (1/4)`.  This single 0-th-order fact is all the convergence input
    the iterated-derivative extraction (part 2) needs: iterating the locally-uniform-limit
    derivative theorem trades per-order summable bounds for this one bound.

conjecture1_proved = False: Γ-function calculus; nothing here approaches RH.
-/
import Mathlib
import RvMArchElemSeries

open Complex

namespace RvMWeierstrass

/-- **The compact form of the elementary summand**: `archSummand j z = M²/(2(j+1)·D_j)` with
`D_j = 2(j+1)(1−z)+1`.  The pairing cancellation, made into a single fraction. -/
theorem archSummand_eq_compact (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    archSummand j z
      = ((1 - z)⁻¹) ^ 2 / (2 * ((j : ℂ) + 1) * (2 * ((j : ℂ) + 1) * (1 - z) + 1)) := by
  have hzre : z.re < 1 / 2 :=
    lt_of_le_of_lt ((le_abs_self _).trans (abs_re_le_norm z)) hz
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro hc
    have h1 : z.re = 1 := by
      have h := sub_eq_zero.mp hc; rw [← h]; simp
    rw [h1] at hzre; norm_num at hzre
  have hj1 : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
  have hDrw : (2 * ((j : ℂ) + 1) * (1 - z) + 1) = ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z) := by
    ring
  have hDne : ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z) ≠ 0 := by
    intro hc
    have h1 : (2 * (j : ℂ) + 3) = (2 * (j : ℂ) + 2) * z := by linear_combination hc
    have h4 := congrArg norm h1
    rw [show (2 * (j : ℂ) + 3) = ((2 * j + 3 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast, norm_mul,
      show (2 * (j : ℂ) + 2) = ((2 * j + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast] at h4
    have h6 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    push_cast at h4
    nlinarith [hz, norm_nonneg z]
  have hDne2 : (2 * ((j : ℂ) + 1) * (1 - z) + 1) ≠ 0 := by rw [hDrw]; exact hDne
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hj1) hDne2)]
  unfold archSummand
  rw [show ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z) = 2 * ((j : ℂ) + 1) * (1 - z) + 1
    from hDrw.symm]
  set D : ℂ := 2 * ((j : ℂ) + 1) * (1 - z) + 1 with hDdef
  field_simp
  rw [hDdef]
  ring

/-- **The uniform summable bound**: on `‖z‖ ≤ 1/4`, `‖archSummand j z‖ ≤ 2/(j+1)²`. -/
theorem archSummand_norm_le (j : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖archSummand j z‖ ≤ 2 / ((j : ℝ) + 1) ^ 2 := by
  have hz2 : ‖z‖ < 1 / 2 := lt_of_le_of_lt hz (by norm_num)
  rw [archSummand_eq_compact j hz2]
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro hc
    have h1 : (1 : ℝ) ≤ ‖z‖ := by
      have := congrArg norm hc
      simp only [norm_zero] at this
      have h2 : ‖(1 : ℂ)‖ - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := norm_sub_norm_le _ _
      rw [this, norm_one] at h2
      linarith
    linarith
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  -- `‖1 − z‖ ≥ 3/4`, hence `‖M‖ ≤ 4/3`
  have h1z : (3 / 4 : ℝ) ≤ ‖(1 : ℂ) - z‖ := by
    have h2 : ‖(1 : ℂ)‖ - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := norm_sub_norm_le _ _
    rw [norm_one] at h2
    linarith
  have hM : ‖(1 - z)⁻¹‖ ≤ 4 / 3 := by
    rw [norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  -- `‖D_j‖ ≥ (j+1)/2`
  have hD : ((j : ℝ) + 1) / 2 ≤ ‖2 * ((j : ℂ) + 1) * (1 - z) + 1‖ := by
    have h2 : ‖2 * ((j : ℂ) + 1) * (1 - z)‖ - ‖2 * ((j : ℂ) + 1) * (1 - z) + 1‖ ≤ 1 := by
      have h := norm_sub_norm_le (2 * ((j : ℂ) + 1) * (1 - z))
        (2 * ((j : ℂ) + 1) * (1 - z) + 1)
      simpa using h
    have h3 : ‖2 * ((j : ℂ) + 1) * (1 - z)‖ = 2 * ((j : ℝ) + 1) * ‖(1 : ℂ) - z‖ := by
      rw [norm_mul, norm_mul]
      have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have ej : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
        rw [show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        push_cast; ring
      rw [e2, ej]
    rw [h3] at h2
    nlinarith [h1z, hj0]
  -- assemble
  rw [norm_div, norm_pow, norm_mul, norm_mul]
  have hnn : (0 : ℝ) ≤ ‖(1 - z)⁻¹‖ := norm_nonneg _
  have h2j : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hjc : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
    rw [show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [h2j, hjc]
  have hden : ((j : ℝ) + 1) ^ 2 ≤ 2 * ((j : ℝ) + 1) * ‖2 * ((j : ℂ) + 1) * (1 - z) + 1‖ := by
    nlinarith [hD, hj0]
  have hnum : ‖(1 - z)⁻¹‖ ^ 2 ≤ 2 := by nlinarith [hM, hnn]
  have hdpos : (0 : ℝ) < 2 * ((j : ℝ) + 1) * ‖2 * ((j : ℂ) + 1) * (1 - z) + 1‖ := by
    have := hD; nlinarith [hj0]
  calc ‖(1 - z)⁻¹‖ ^ 2 / (2 * ((j : ℝ) + 1) * ‖2 * ((j : ℂ) + 1) * (1 - z) + 1‖)
      ≤ 2 / ((j : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ hdpos (by positivity)]
        nlinarith [hnum, hden, hj0, hdpos, sq_nonneg ((j : ℝ) + 1),
          norm_nonneg (2 * ((j : ℂ) + 1) * (1 - z) + 1)]

/-- The dominating sequence is summable. -/
theorem summable_archBound : Summable (fun j : ℕ => 2 / ((j : ℝ) + 1) ^ 2) := by
  have h := Real.summable_one_div_nat_pow.mpr (le_refl 2)
  have h2 := (summable_nat_add_iff 1).mpr h
  simpa [div_eq_mul_inv, mul_comm] using h2.mul_left 2

/-- **Uniform convergence of the elementary series on `closedBall 0 (1/4)`**: the partial sums of
`∑' j, archSummand j` converge uniformly.  The single convergence input for the coefficient
extraction. -/
theorem tendstoUniformlyOn_archSummand :
    TendstoUniformlyOn (fun (t : Finset ℕ) (z : ℂ) => ∑ j ∈ t, archSummand j z)
      (fun z => ∑' j : ℕ, archSummand j z) Filter.atTop (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  refine tendstoUniformlyOn_tsum summable_archBound ?_
  intro j z hzball
  have hz : ‖z‖ ≤ 1 / 4 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hzball
    exact hzball
  exact archSummand_norm_le j hz

end RvMWeierstrass
