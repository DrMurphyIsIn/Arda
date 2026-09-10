/-
RvMTrigamma — Phase 3: differentiate the digamma series → the trigamma series and its value at 1/2.

From `digamma_series` (Phase 2, b4): `digamma s = −1/s − γ − ∑'ₙ (1/(s+(n+1)) − 1/(n+1))` off the
poles.  Differentiating term-by-term (valid on the pole-free open neighbourhood) gives the trigamma
series `deriv digamma s = ∑'ₖ 1/(s+k)²`, and at `s = 1/2` this is `π²/2` (Phase 1).

  * `poleCompl_mem_nhds` — the pole complement `{z | ∀ j, z+j ≠ 0}` is a neighbourhood of any `s` off
    the poles (the reusable open-set foundation).

conjecture1_proved = False.
-/
import Mathlib
import RvMDigammaComplete
import RvMDigammaSeries

open Complex Filter Topology

namespace RvMWeierstrass

/-- **Uniform positive lower bound on the distances to the poles.**  For `s` off the non-positive
    integers there is `ε > 0` with `ε ≤ ‖s + j‖` for every `j : ℕ` (the poles `−j` recede to `∞`, so
    the infimum of the finitely many close ones is positive). -/
theorem exists_pos_le_norm_add {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    ∃ ε > 0, ∀ j : ℕ, ε ≤ ‖s + (j : ℂ)‖ := by
  set K : ℕ := Nat.ceil ‖s‖ + 1 with hK
  have hne : (Finset.range K).Nonempty := Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _)
  set δ : ℝ := (Finset.range K).inf' hne (fun j => ‖s + (j : ℂ)‖) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    exact fun j _ => norm_pos_iff.mpr (hs j)
  refine ⟨min δ 1, lt_min hδpos one_pos, fun j => ?_⟩
  have hjnorm : (j : ℝ) - ‖s‖ ≤ ‖s + (j : ℂ)‖ := by
    have h2 := norm_sub_norm_le ((j : ℂ)) (-s)
    rw [norm_neg, sub_neg_eq_add, add_comm ((j : ℂ)) s, Complex.norm_natCast] at h2
    exact h2
  rcases lt_or_ge j K with hj | hj
  · calc min δ 1 ≤ δ := min_le_left _ _
      _ ≤ ‖s + (j : ℂ)‖ := Finset.inf'_le _ (Finset.mem_range.mpr hj)
  · have hK1 : ‖s‖ + 1 ≤ (j : ℝ) := by
      have := Nat.le_ceil ‖s‖
      have hjK : (K : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      rw [hK] at hjK; push_cast at hjK; linarith
    calc min δ 1 ≤ 1 := min_le_right _ _
      _ ≤ (j : ℝ) - ‖s‖ := by linarith
      _ ≤ ‖s + (j : ℂ)‖ := hjnorm

/-- **The pole complement is a neighbourhood.**  For `s` off the non-positive integers, the set
    `{z | ∀ j : ℕ, z + j ≠ 0}` is a neighbourhood of `s`. -/
theorem poleCompl_mem_nhds {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    {z : ℂ | ∀ j : ℕ, z + (j : ℂ) ≠ 0} ∈ 𝓝 s := by
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_norm_add hs
  refine Filter.mem_of_superset (Metric.ball_mem_nhds s hε) (fun z hz j hcon => ?_)
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hzj : z = -(j : ℂ) := by linear_combination hcon
  have : ‖s + (j : ℂ)‖ < ε := by
    calc ‖s + (j : ℂ)‖ = ‖z - s‖ := by rw [hzj, norm_sub_rev, sub_neg_eq_add]
      _ < ε := hz
  linarith [hbound j]

set_option maxHeartbeats 2000000 in
/-- **The trigamma value** `ψ'(1/2) = π²/2` (Phase 3).  Differentiating `digamma_series`
    term-by-term on the ball `B(1/2, 1/4)` (where the poles are avoided and the terms are
    `O(1/n²)`-bounded) and summing via Phase 1's `hasSum_one_div_add_half_sq`. -/
theorem deriv_digamma_one_half :
    deriv Complex.digamma (1 / 2 : ℂ) = ((Real.pi ^ 2 / 2 : ℝ) : ℂ) := by
  set s : ℂ := 1 / 2 with hsdef
  have hsne : s ≠ 0 := by rw [hsdef]; norm_num
  have hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0 := by
    intro j hj
    have hre : (s + (j : ℂ)).re = 1 / 2 + (j : ℝ) := by rw [hsdef]; simp
    rw [hj, Complex.zero_re] at hre
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  set g : ℕ → ℂ := fun k => 1 / (s + (k : ℂ)) ^ 2 with hg
  have hg0 : g 0 = 1 / s ^ 2 := by rw [hg]; norm_num
  have hgcx : HasSum g ((Real.pi ^ 2 / 2 : ℝ) : ℂ) := by
    have hfg : g = (fun k : ℕ => ((1 / ((k : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ)) := by
      funext k; rw [hg, hsdef]; push_cast; ring
    rw [hfg]
    exact Complex.hasSum_ofReal.mpr RvMDigammaSeries.hasSum_one_div_add_half_sq
  set F : ℕ → ℂ → ℂ := fun n z => 1 / (z + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1) with hF
  set U : Set ℂ := Metric.ball s (1 / 4) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hsU : s ∈ U := by rw [hU, Metric.mem_ball, dist_self]; norm_num
  have hnb : ∀ n : ℕ, ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    intro n
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ)) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  -- lower bound ‖w + (n+1)‖ ≥ n+1 for w ∈ U (s = 1/2, radius 1/4)
  have hwlow : ∀ n : ℕ, ∀ w ∈ U, ((n : ℝ) + 1) ≤ ‖w + ((n : ℂ) + 1)‖ := by
    intro n w hw
    rw [hU, Metric.mem_ball, dist_eq_norm] at hw
    have hbase : ‖s + ((n : ℂ) + 1)‖ = (n : ℝ) + 3 / 2 := by
      rw [hsdef, show (1 / 2 : ℂ) + ((n : ℂ) + 1) = (((n : ℝ) + 3 / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h2 : ‖s + ((n : ℂ) + 1)‖ - ‖w - s‖ ≤ ‖w + ((n : ℂ) + 1)‖ := by
      have h3 := norm_sub_norm_le (s + ((n : ℂ) + 1)) (s - w)
      have heq : (s + ((n : ℂ) + 1)) - (s - w) = w + ((n : ℂ) + 1) := by ring
      rw [heq, norm_sub_rev] at h3; linarith
    rw [hbase] at h2; linarith
  have hwne : ∀ n : ℕ, ∀ w ∈ U, w + ((n : ℂ) + 1) ≠ 0 := by
    intro n w hw
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact norm_pos_iff.mp (lt_of_lt_of_le hp (hwlow n w hw))
  have hwb : ∀ w ∈ U, ‖w‖ ≤ 3 / 4 := by
    intro w hw
    rw [hU, Metric.mem_ball, dist_eq_norm] at hw
    have h4 : ‖w‖ - ‖s‖ ≤ ‖w - s‖ := norm_sub_norm_le w s
    have hsn : ‖s‖ = 1 / 2 := by
      rw [hsdef, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by norm_num)]
    rw [hsn] at h4; linarith
  -- uniform O(1/n²) bound on ‖F n w‖, w ∈ U
  have hFle : ∀ n : ℕ, ∀ w ∈ U, ‖F n w‖ ≤ (3 / 4 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    intro n w hw
    have hwn := hwne n w hw
    have hcn : ((n : ℂ) + 1) ≠ 0 := natCast_add_one_ne_zero n
    have hlow := hwlow n w hw
    have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hanorm : (0 : ℝ) < ‖w + ((n : ℂ) + 1)‖ := lt_of_lt_of_le hpos1 hlow
    have hwbw := hwb w hw
    have hFval : F n w = -w / ((w + ((n : ℂ) + 1)) * ((n : ℂ) + 1)) := by
      simp only [hF]; rw [div_sub_div _ _ hwn hcn]; congr 1; ring
    rw [hFval, norm_div, norm_neg, norm_mul, hnb n,
      div_le_div_iff₀ (mul_pos hanorm hpos1) (by positivity)]
    nlinarith [hwbw, hlow, hpos1, norm_nonneg w,
      mul_le_mul_of_nonneg_right hlow (le_of_lt hpos1),
      mul_le_mul_of_nonneg_right hwbw (sq_nonneg ((n : ℝ) + 1))]
  have hu : Summable (fun n : ℕ => (3 / 4 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_pow_div_add (3 / 4 : ℝ) 2 1 (by norm_num)).of_norm
    simpa [Nat.cast_one] using h
  have hfdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) U := by
    intro n w hw
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => (z + ((n : ℂ) + 1))⁻¹) w :=
      (differentiableAt_id.add_const _).inv (hwne n w hw)
    have hd2 : DifferentiableAt ℂ (F n) w := by
      simp only [hF, one_div]; exact hd1.sub_const _
    exact hd2.differentiableWithinAt
  -- term-by-term differentiation
  have hSderiv : HasSum (fun n : ℕ => deriv (F n) s) (deriv (fun z => ∑' n : ℕ, F n z) s) :=
    hasSum_deriv_of_summable_norm hu hfdiff hUopen hFle hsU
  have hSdiff : DifferentiableOn ℂ (fun z => ∑' n : ℕ, F n z) U :=
    differentiableOn_tsum_of_summable_norm hu hfdiff hUopen hFle
  -- deriv (F n) s = -(g (n+1)) = -1/(s+(n+1))^2
  have hFderiv : ∀ n : ℕ, deriv (F n) s = -(1 / (s + ((n : ℂ) + 1)) ^ 2) := by
    intro n
    have hne : s + ((n : ℂ) + 1) ≠ 0 := hwne n s hsU
    have hinner : HasDerivAt (fun z : ℂ => z + ((n : ℂ) + 1)) 1 s := by
      simpa using (hasDerivAt_id s).add_const ((n : ℂ) + 1)
    have hd : HasDerivAt (F n) (-(1 : ℂ) / (s + ((n : ℂ) + 1)) ^ 2) s := by
      simpa [hF, one_div] using (hinner.inv hne).sub_const (1 / ((n : ℂ) + 1))
    rw [hd.deriv]; ring
  -- transfer differentiation to digamma via digamma_series
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
  -- evaluate: 1/s² − deriv S s = π²/2
  have hfeq : (fun n : ℕ => deriv (F n) s) = fun n => -(g (n + 1)) := by
    funext n; rw [hFderiv n]; simp only [hg]; push_cast; ring
  rw [hfeq] at hSderiv
  have hns : ∑' n : ℕ, g (n + 1) = -(deriv (fun z => ∑' n : ℕ, F n z) s) := by
    have hneg := hSderiv.neg
    simp only [neg_neg] at hneg
    exact hneg.tsum_eq
  have hpeel : g 0 + ∑' n : ℕ, g (n + 1) = ((Real.pi ^ 2 / 2 : ℝ) : ℂ) := by
    have h := hgcx.summable.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    rw [h, hgcx.tsum_eq]
  rw [hns, hg0] at hpeel
  linear_combination hpeel

end RvMWeierstrass
