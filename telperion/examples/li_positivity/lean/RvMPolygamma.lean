/-
RvMPolygamma — Phase 4a foundation: the general trigamma series.

Generalises `deriv_digamma_one_half` (Phase 3) to arbitrary `s` off the poles:
  `deriv Complex.digamma s = ∑'_k 1/(s+k)²`  (the trigamma function), valid on the pole-free
neighbourhood.  This is the base case for the polygamma induction (higher `iteratedDeriv m` at 1/2).

The reindex `1/s² + ∑'_n 1/(s+(n+1))² = ∑'_k 1/(s+k)²` and the summability come for free from the
term-by-term differentiation HasSum; the one new ingredient vs. the `s = 1/2` case is a case-split
uniform `O(1/n²)` bound on the ball (the poles are no longer at a fixed clean distance).

conjecture1_proved = False.
-/
import Mathlib
import RvMTrigamma

open Complex Filter Topology

namespace RvMWeierstrass

set_option maxHeartbeats 4000000 in
/-- **The trigamma series** (Phase 4a foundation).  For `s` off the non-positive integers,
    `deriv Complex.digamma s = ∑'_k 1/(s+k)²`. -/
theorem deriv_digamma_eq_tsum {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    deriv Complex.digamma s = ∑' k : ℕ, 1 / (s + (k : ℂ)) ^ 2 := by
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_norm_add hs
  have hsne : s ≠ 0 := hs 0 |>.imp (by intro h; simpa using h)
  set A : ℝ := ‖s‖ + ε / 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set C : ℝ := max (2 * A) (4 * A ^ 2 / ε) with hC
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set g : ℕ → ℂ := fun k => 1 / (s + (k : ℂ)) ^ 2 with hg
  have hg0 : g 0 = 1 / s ^ 2 := by rw [hg]; norm_num
  set F : ℕ → ℂ → ℂ := fun n z => 1 / (z + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1) with hF
  set U : Set ℂ := Metric.ball s (ε / 2) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hsU : s ∈ U := by rw [hU, Metric.mem_ball, dist_self]; positivity
  have hnb : ∀ n : ℕ, ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    intro n
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ)) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  have hbnd' : ∀ n : ℕ, ε ≤ ‖s + ((n : ℂ) + 1)‖ := by
    intro n
    have := hbound (n + 1)
    rwa [show s + (((n + 1 : ℕ)) : ℂ) = s + ((n : ℂ) + 1) by push_cast; ring] at this
  -- two lower bounds on ‖w + (n+1)‖ for w ∈ U
  have hlow_eps : ∀ n : ℕ, ∀ w ∈ U, ε / 2 ≤ ‖w + ((n : ℂ) + 1)‖ := by
    intro n w hw
    rw [hU, Metric.mem_ball, dist_eq_norm] at hw
    have h3 := norm_sub_norm_le (s + ((n : ℂ) + 1)) (s - w)
    have heq : (s + ((n : ℂ) + 1)) - (s - w) = w + ((n : ℂ) + 1) := by ring
    rw [heq, norm_sub_rev] at h3
    linarith [hbnd' n]
  have hwle : ∀ w ∈ U, ‖w‖ ≤ A := by
    intro w hw
    rw [hU, Metric.mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le w s
    rw [hA]; linarith
  have hlow_grow : ∀ n : ℕ, ∀ w ∈ U, ((n : ℝ) + 1) - A ≤ ‖w + ((n : ℂ) + 1)‖ := by
    intro n w hw
    have h3 := norm_sub_norm_le ((n : ℂ) + 1) (-w)
    have heq : ((n : ℂ) + 1) - (-w) = w + ((n : ℂ) + 1) := by ring
    rw [norm_neg, heq, hnb n] at h3
    linarith [hwle w hw]
  -- 4A² ≤ Cε (no division, for nlinarith)
  have hCeps : 4 * A ^ 2 ≤ C * ε := by
    have h : 4 * A ^ 2 / ε ≤ C := hC ▸ le_max_right _ _
    rw [show 4 * A ^ 2 = 4 * A ^ 2 / ε * ε by field_simp]
    exact mul_le_mul_of_nonneg_right h hε.le
  -- uniform O(1/n²) bound (case split on n)
  have hFle : ∀ n : ℕ, ∀ w ∈ U, ‖F n w‖ ≤ C / ((n : ℝ) + 1) ^ 2 := by
    intro n w hw
    have hcn : ((n : ℂ) + 1) ≠ 0 := natCast_add_one_ne_zero n
    have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hanorm : (0 : ℝ) < ‖w + ((n : ℂ) + 1)‖ :=
      lt_of_lt_of_le (by positivity) (hlow_eps n w hw)
    have hwn : w + ((n : ℂ) + 1) ≠ 0 := norm_pos_iff.mp hanorm
    have hkey : A * ((n : ℝ) + 1) ≤ C * ‖w + ((n : ℂ) + 1)‖ := by
      rcases lt_or_ge ((n : ℝ) + 1) (2 * A) with hn | hn
      · have hep := hlow_eps n w hw
        nlinarith [mul_le_mul_of_nonneg_left hep hCpos.le,
          mul_lt_mul_of_pos_left hn hApos, hCeps, hε, hApos]
      · have hCge : 2 * A ≤ C := le_max_left _ _
        have hhalf : ((n : ℝ) + 1) / 2 ≤ ‖w + ((n : ℂ) + 1)‖ := by
          linarith [hlow_grow n w hw]
        nlinarith [mul_le_mul hCge hhalf (by linarith) hCpos.le]
    have hFval : F n w = -w / ((w + ((n : ℂ) + 1)) * ((n : ℂ) + 1)) := by
      simp only [hF]; rw [div_sub_div _ _ hwn hcn]; congr 1; ring
    rw [hFval, norm_div, norm_neg, norm_mul, hnb n,
      div_le_div_iff₀ (mul_pos hanorm hpos1) (by positivity)]
    nlinarith [hwle w hw, hkey, hpos1, hanorm, norm_nonneg w,
      mul_le_mul_of_nonneg_right hkey (le_of_lt hpos1),
      mul_le_mul_of_nonneg_right (hwle w hw) (sq_nonneg ((n : ℝ) + 1))]
  have hu : Summable (fun n : ℕ => C / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_pow_div_add C 2 1 (by norm_num)).of_norm
    simpa [Nat.cast_one] using h
  have hfdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) U := by
    intro n w hw
    have hwn : w + ((n : ℂ) + 1) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hlow_eps n w hw))
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => (z + ((n : ℂ) + 1))⁻¹) w :=
      (differentiableAt_id.add_const _).inv hwn
    have hd2 : DifferentiableAt ℂ (F n) w := by
      simp only [hF, one_div]; exact hd1.sub_const _
    exact hd2.differentiableWithinAt
  have hSderiv : HasSum (fun n : ℕ => deriv (F n) s) (deriv (fun z => ∑' n : ℕ, F n z) s) :=
    hasSum_deriv_of_summable_norm hu hfdiff hUopen hFle hsU
  have hSdiff : DifferentiableOn ℂ (fun z => ∑' n : ℕ, F n z) U :=
    differentiableOn_tsum_of_summable_norm hu hfdiff hUopen hFle
  have hFderiv : ∀ n : ℕ, deriv (F n) s = -(1 / (s + ((n : ℂ) + 1)) ^ 2) := by
    intro n
    have hne : s + ((n : ℂ) + 1) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hlow_eps n s hsU))
    have hinner : HasDerivAt (fun z : ℂ => z + ((n : ℂ) + 1)) 1 s := by
      simpa using (hasDerivAt_id s).add_const ((n : ℂ) + 1)
    have hd : HasDerivAt (F n) (-(1 : ℂ) / (s + ((n : ℂ) + 1)) ^ 2) s := by
      simpa [hF, one_div] using (hinner.inv hne).sub_const (1 / ((n : ℂ) + 1))
    rw [hd.deriv]; ring
  have hSderivAt : HasDerivAt (fun z => ∑' n : ℕ, F n z) (deriv (fun z => ∑' n : ℕ, F n z) s) s :=
    (hSdiff.differentiableAt (hUopen.mem_nhds hsU)).hasDerivAt
  have hdinv : HasDerivAt (fun z : ℂ => -(1 / z)) (1 / s ^ 2) s := by
    have h := HasDerivAt.const_mul (-1 : ℂ) (hasDerivAt_inv hsne)
    simpa [neg_one_mul, one_div] using h
  have hEq : Complex.digamma =ᶠ[𝓝 s] (fun z => -(1 / z) - (Real.eulerMascheroniConstant : ℂ)
      - ∑' n : ℕ, F n z) := by
    filter_upwards [poleCompl_mem_nhds hs] with z hz
    exact digamma_series hz
  have hdRHS : HasDerivAt (fun z => -(1 / z) - (Real.eulerMascheroniConstant : ℂ)
      - ∑' n : ℕ, F n z) (1 / s ^ 2 - deriv (fun z => ∑' n : ℕ, F n z) s) s :=
    (hdinv.sub_const _).sub hSderivAt
  rw [(hEq.hasDerivAt_iff.mpr hdRHS).deriv]
  -- reindex the derivative sum
  have hfeq : (fun n : ℕ => deriv (F n) s) = fun n => -(g (n + 1)) := by
    funext n; rw [hFderiv n]; simp only [hg]; push_cast; ring
  rw [hfeq] at hSderiv
  have hshift : Summable (fun n : ℕ => g (n + 1)) := by
    have := hSderiv.summable.neg
    simpa using this
  have hsumg : Summable g := (summable_nat_add_iff 1).mp hshift
  have hns : ∑' n : ℕ, g (n + 1) = -(deriv (fun z => ∑' n : ℕ, F n z) s) := by
    have hneg := hSderiv.neg
    simp only [neg_neg] at hneg
    exact hneg.tsum_eq
  have hpeel : (∑' k : ℕ, g k) = g 0 + ∑' n : ℕ, g (n + 1) := by
    have h := hsumg.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h; exact h.symm
  have hgoal : (∑' k : ℕ, 1 / (s + (k : ℂ)) ^ 2) = 1 / s ^ 2 - deriv (fun z => ∑' n : ℕ, F n z) s := by
    have : (∑' k : ℕ, 1 / (s + (k : ℂ)) ^ 2) = ∑' k : ℕ, g k := by rw [hg]
    rw [this, hpeel, hns, hg0]; ring
  rw [hgoal]

end RvMWeierstrass
