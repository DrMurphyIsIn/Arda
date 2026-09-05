/- telperion 0.1.6 | family BCDerivRe | input-hash bfaa1a7c5f05d721
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace BCDerivRe

open Complex Metric

/-- Real-part → derivative bound on `ball c (3 / 2)`: `h` holomorphic with
    `(h z).re - (h c).re ≤ 6` throughout implies `‖deriv h c‖ ≤ 2·6/((3 / 2) - (1 / 2))`
    (Borel-Caratheodory + Cauchy).  A concrete copy of `norm_deriv_le_of_re_le`. -/
theorem bc_deriv_re_a (h : ℂ → ℂ) (c : ℂ)
    (hana : DifferentiableOn ℂ h (ball c ((3 / 2) : ℝ)))
    (hbound : ∀ z ∈ ball c ((3 / 2) : ℝ), (h z).re - (h c).re ≤ (6 : ℝ)) :
    ‖deriv h c‖ ≤ 2 * (6 : ℝ) / (((3 / 2) : ℝ) - (1 / 2)) := by
  have hr : (0 : ℝ) < (1 / 2) := by norm_num
  have hrR : ((1 / 2) : ℝ) < (3 / 2) := by norm_num
  have hM' : (0 : ℝ) < 6 := by norm_num
  have hR : (0 : ℝ) < (3 / 2) := by norm_num
  have hRr : (0 : ℝ) < ((3 / 2) - (1 / 2)) := by norm_num
  set f : ℂ → ℂ := fun w => h (c + w) - h c with hf_def
  have hcball : c ∈ ball c ((3 / 2) : ℝ) := mem_ball_self hR
  have hhc : DifferentiableAt ℂ h c :=
    (hana c hcball).differentiableAt (isOpen_ball.mem_nhds hcball)
  have hmaps : ∀ w ∈ ball (0 : ℂ) ((3 / 2) : ℝ), c + w ∈ ball c ((3 / 2) : ℝ) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball_iff_norm]
    simpa using hw
  have hf_deriv0 : HasDerivAt f (deriv h c) 0 := by
    have hbase : HasDerivAt h (deriv h c) (c + 0) := by simpa using hhc.hasDerivAt
    exact (hbase.comp_const_add c 0).sub_const (h c)
  have hf_diffR : DifferentiableOn ℂ f (ball 0 ((3 / 2) : ℝ)) := by
    intro w hw
    have hcw : DifferentiableAt ℂ h (c + w) :=
      (hana _ (hmaps w hw)).differentiableAt (isOpen_ball.mem_nhds (hmaps w hw))
    have h1 : DifferentiableAt ℂ (fun w => h (c + w)) w := hcw.comp w (by fun_prop)
    exact (h1.sub_const (h c)).differentiableWithinAt
  have hf0 : f 0 = 0 := by simp [hf_def]
  have hmaps_re : Set.MapsTo f (ball 0 ((3 / 2) : ℝ)) {z | z.re ≤ (6 : ℝ)} := by
    intro w hw
    simp only [Set.mem_setOf_eq, hf_def, Complex.sub_re]
    exact hbound _ (hmaps w hw)
  have hsphere : ∀ z ∈ sphere (0 : ℂ) ((1 / 2) : ℝ),
      ‖f z‖ ≤ 2 * (6 : ℝ) * (1 / 2) / ((3 / 2) - (1 / 2)) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hzball : z ∈ ball (0 : ℂ) ((3 / 2) : ℝ) := by
      rw [mem_ball_zero_iff, hz]; exact hrR
    have := Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hzball hf0
    rwa [hz] at this
  have hdcc : DiffContOnCl ℂ f (ball 0 ((1 / 2) : ℝ)) := by
    refine ⟨hf_diffR.mono (ball_subset_ball hrR.le), ?_⟩
    rw [closure_ball 0 hr.ne']
    exact hf_diffR.continuousOn.mono (closedBall_subset_ball hrR)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsphere
  rw [hf_deriv0.deriv] at hcauchy
  calc ‖deriv h c‖ ≤ 2 * (6 : ℝ) * (1 / 2) / ((3 / 2) - (1 / 2)) / (1 / 2) := hcauchy
    _ = 2 * (6 : ℝ) / (((3 / 2) : ℝ) - (1 / 2)) := by field_simp
/-- Real-part → derivative bound on `ball c 1`: `h` holomorphic with
    `(h z).re - (h c).re ≤ 2` throughout implies `‖deriv h c‖ ≤ 2·2/(1 - (1 / 4))`
    (Borel-Caratheodory + Cauchy).  A concrete copy of `norm_deriv_le_of_re_le`. -/
theorem bc_deriv_re_b (h : ℂ → ℂ) (c : ℂ)
    (hana : DifferentiableOn ℂ h (ball c (1 : ℝ)))
    (hbound : ∀ z ∈ ball c (1 : ℝ), (h z).re - (h c).re ≤ (2 : ℝ)) :
    ‖deriv h c‖ ≤ 2 * (2 : ℝ) / ((1 : ℝ) - (1 / 4)) := by
  have hr : (0 : ℝ) < (1 / 4) := by norm_num
  have hrR : ((1 / 4) : ℝ) < 1 := by norm_num
  have hM' : (0 : ℝ) < 2 := by norm_num
  have hR : (0 : ℝ) < 1 := by norm_num
  have hRr : (0 : ℝ) < (1 - (1 / 4)) := by norm_num
  set f : ℂ → ℂ := fun w => h (c + w) - h c with hf_def
  have hcball : c ∈ ball c (1 : ℝ) := mem_ball_self hR
  have hhc : DifferentiableAt ℂ h c :=
    (hana c hcball).differentiableAt (isOpen_ball.mem_nhds hcball)
  have hmaps : ∀ w ∈ ball (0 : ℂ) (1 : ℝ), c + w ∈ ball c (1 : ℝ) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball_iff_norm]
    simpa using hw
  have hf_deriv0 : HasDerivAt f (deriv h c) 0 := by
    have hbase : HasDerivAt h (deriv h c) (c + 0) := by simpa using hhc.hasDerivAt
    exact (hbase.comp_const_add c 0).sub_const (h c)
  have hf_diffR : DifferentiableOn ℂ f (ball 0 (1 : ℝ)) := by
    intro w hw
    have hcw : DifferentiableAt ℂ h (c + w) :=
      (hana _ (hmaps w hw)).differentiableAt (isOpen_ball.mem_nhds (hmaps w hw))
    have h1 : DifferentiableAt ℂ (fun w => h (c + w)) w := hcw.comp w (by fun_prop)
    exact (h1.sub_const (h c)).differentiableWithinAt
  have hf0 : f 0 = 0 := by simp [hf_def]
  have hmaps_re : Set.MapsTo f (ball 0 (1 : ℝ)) {z | z.re ≤ (2 : ℝ)} := by
    intro w hw
    simp only [Set.mem_setOf_eq, hf_def, Complex.sub_re]
    exact hbound _ (hmaps w hw)
  have hsphere : ∀ z ∈ sphere (0 : ℂ) ((1 / 4) : ℝ),
      ‖f z‖ ≤ 2 * (2 : ℝ) * (1 / 4) / (1 - (1 / 4)) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hzball : z ∈ ball (0 : ℂ) (1 : ℝ) := by
      rw [mem_ball_zero_iff, hz]; exact hrR
    have := Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hzball hf0
    rwa [hz] at this
  have hdcc : DiffContOnCl ℂ f (ball 0 ((1 / 4) : ℝ)) := by
    refine ⟨hf_diffR.mono (ball_subset_ball hrR.le), ?_⟩
    rw [closure_ball 0 hr.ne']
    exact hf_diffR.continuousOn.mono (closedBall_subset_ball hrR)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsphere
  rw [hf_deriv0.deriv] at hcauchy
  calc ‖deriv h c‖ ≤ 2 * (2 : ℝ) * (1 / 4) / (1 - (1 / 4)) / (1 / 4) := hcauchy
    _ = 2 * (2 : ℝ) / ((1 : ℝ) - (1 / 4)) := by field_simp

end BCDerivRe
