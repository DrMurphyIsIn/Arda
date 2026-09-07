/- telperion 0.1.6 | family FullArgumentPrinciple | input-hash f73c14c64a64975c
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace FullArgumentPrinciple

open Complex Metric Real

/-- FULL argument principle on the circle of radius `(3 / 2)` about `c`.
    For `f = Σ_ρ (m ρ)(z-ρ)⁻¹ + E` with `E` holomorphic on the closed disk,
    `∮_(C(c,(3 / 2))) f = 2πi · Σ_ρ (m ρ)`.  The analytic part `E` vanishes (Cauchy);
    the pole terms give `2πi` each — the winding number = the zero count. -/
theorem full_arg_principle_3half {c : ℂ} (m : ℂ → ℤ) (s : Finset ℂ) (E : ℂ → ℂ) (f : ℂ → ℂ)
    (hmem : ∀ ρ ∈ s, ρ ∈ ball c ((3 / 2) : ℝ))
    (hE : DiffContOnCl ℂ E (ball c ((3 / 2) : ℝ)))
    (hf : ∀ z, f z = (∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) + E z) :
    (∮ z in C(c, ((3 / 2) : ℝ)), f z) = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  have hR : (0 : ℝ) < (3 / 2) := by norm_num
  have hint : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ((3 / 2) : ℝ) := by
    intro ρ hρ
    have hd : dist ρ c < ((3 / 2) : ℝ) := by rw [← mem_ball]; exact hmem ρ hρ
    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ((3 / 2) : ℝ) := by
      rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_
      rw [mem_sphere, abs_of_pos hR]; exact fun h => absurd h (by linarith)
    exact hbase.const_mul _
  have hsum_int : CircleIntegrable (fun z => ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) c ((3 / 2) : ℝ) := by
    have h := CircleIntegrable.sum s hint
    have heq : (∑ ρ ∈ s, fun z => (m ρ : ℂ) * (z - ρ)⁻¹)
        = (fun z => ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) := by
      funext z; exact Finset.sum_apply z s _
    rwa [heq] at h
  have hsub : sphere c ((3 / 2) : ℝ) ⊆ closure (ball c ((3 / 2) : ℝ)) := by
    rw [closure_ball c (by norm_num : ((3 / 2) : ℝ) ≠ 0)]; exact sphere_subset_closedBall
  have hEint : CircleIntegrable E c ((3 / 2) : ℝ) :=
    (hE.continuousOn.mono hsub).circleIntegrable hR.le
  simp only [hf]
  rw [circleIntegral.integral_add hsum_int hEint, hE.circleIntegral_eq_zero hR.le,
    add_zero, circleIntegral.integral_fun_sum hint]
  have hcong : ∀ ρ ∈ s,
      (∮ z in C(c, ((3 / 2) : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by
    intro ρ hρ
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hmem ρ hρ)]
  rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]
/-- FULL argument principle on the circle of radius `2` about `c`.
    For `f = Σ_ρ (m ρ)(z-ρ)⁻¹ + E` with `E` holomorphic on the closed disk,
    `∮_(C(c,2)) f = 2πi · Σ_ρ (m ρ)`.  The analytic part `E` vanishes (Cauchy);
    the pole terms give `2πi` each — the winding number = the zero count. -/
theorem full_arg_principle_two {c : ℂ} (m : ℂ → ℤ) (s : Finset ℂ) (E : ℂ → ℂ) (f : ℂ → ℂ)
    (hmem : ∀ ρ ∈ s, ρ ∈ ball c (2 : ℝ))
    (hE : DiffContOnCl ℂ E (ball c (2 : ℝ)))
    (hf : ∀ z, f z = (∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) + E z) :
    (∮ z in C(c, (2 : ℝ)), f z) = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hint : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c (2 : ℝ) := by
    intro ρ hρ
    have hd : dist ρ c < (2 : ℝ) := by rw [← mem_ball]; exact hmem ρ hρ
    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c (2 : ℝ) := by
      rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_
      rw [mem_sphere, abs_of_pos hR]; exact fun h => absurd h (by linarith)
    exact hbase.const_mul _
  have hsum_int : CircleIntegrable (fun z => ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) c (2 : ℝ) := by
    have h := CircleIntegrable.sum s hint
    have heq : (∑ ρ ∈ s, fun z => (m ρ : ℂ) * (z - ρ)⁻¹)
        = (fun z => ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) := by
      funext z; exact Finset.sum_apply z s _
    rwa [heq] at h
  have hsub : sphere c (2 : ℝ) ⊆ closure (ball c (2 : ℝ)) := by
    rw [closure_ball c (by norm_num : (2 : ℝ) ≠ 0)]; exact sphere_subset_closedBall
  have hEint : CircleIntegrable E c (2 : ℝ) :=
    (hE.continuousOn.mono hsub).circleIntegrable hR.le
  simp only [hf]
  rw [circleIntegral.integral_add hsum_int hEint, hE.circleIntegral_eq_zero hR.le,
    add_zero, circleIntegral.integral_fun_sum hint]
  have hcong : ∀ ρ ∈ s,
      (∮ z in C(c, (2 : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by
    intro ρ hρ
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hmem ρ hρ)]
  rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]

end FullArgumentPrinciple
