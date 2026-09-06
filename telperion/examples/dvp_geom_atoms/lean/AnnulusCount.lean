/- telperion 0.1.6 | family AnnulusCount | input-hash b8bba902d37b7a74
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace AnnulusCount

open Complex Metric Real

/-- Annulus count on the shell `1 < |z-c| < 2`: outer circle integral minus
    inner circle integral isolates the poles in the shell,
    `∮_(C(c,2)) Σ_ρ (m ρ)(z-ρ)⁻¹ - ∮_(C(c,1)) Σ_ρ (m ρ)(z-ρ)⁻¹ = 2πi · Σ_ρ (m ρ)`.
    Outer counts all inside; inner = 0 (poles outside ⟹ analytic ⟹ Cauchy). -/
theorem annulus_count_one_two {c : ℂ} (m : ℂ → ℤ) (s : Finset ℂ)
    (hin : ∀ ρ ∈ s, ρ ∈ ball c ((2) : ℝ))
    (hout : ∀ ρ ∈ s, ((1) : ℝ) < dist ρ c) :
    (∮ z in C(c, (2 : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
        - (∮ z in C(c, (1 : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  have hRout : (0 : ℝ) < 2 := by norm_num
  have houter_int : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c (2 : ℝ) := by
    intro ρ hρ
    have hd : dist ρ c < (2 : ℝ) := by rw [← mem_ball]; exact hin ρ hρ
    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c (2 : ℝ) := by
      rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_
      rw [mem_sphere, abs_of_pos hRout]; exact fun h => absurd h (by linarith)
    exact hbase.const_mul _
  have houter : (∮ z in C(c, (2 : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
    rw [circleIntegral.integral_fun_sum houter_int]
    have hcong : ∀ ρ ∈ s,
        (∮ z in C(c, (2 : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by
      intro ρ hρ
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (hin ρ hρ)]
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]
  have hinner : (∮ z in C(c, (1 : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) = 0 := by
    have hzero : ∀ ρ ∈ s, (∮ z in C(c, (1 : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = 0 := by
      intro ρ hρ
      rw [circleIntegral.integral_const_mul]
      have hbody : (∮ z in C(c, (1 : ℝ)), (z - ρ)⁻¹) = 0 := by
        apply DiffContOnCl.circleIntegral_eq_zero (by norm_num : (0 : ℝ) ≤ 1)
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball c (by norm_num : (1 : ℝ) ≠ 0)]
        intro z hz
        have hzr : dist z c ≤ 1 := by rwa [mem_closedBall] at hz
        have hne : z - ρ ≠ 0 := by
          intro h; rw [sub_eq_zero] at h
          have hd2 := hout ρ hρ; rw [← h] at hd2; linarith
        exact ((differentiableAt_id.sub_const ρ).inv hne).differentiableWithinAt
      rw [hbody, mul_zero]
    have hinner_int : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c (1 : ℝ) := by
      intro ρ hρ
      have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c (1 : ℝ) := by
        rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_
        rw [mem_sphere]; intro h
        have hd2 := hout ρ hρ; rw [h] at hd2; norm_num at hd2
      exact hbase.const_mul _
    rw [circleIntegral.integral_fun_sum hinner_int, Finset.sum_congr rfl hzero,
      Finset.sum_const_zero]
  rw [houter, hinner, sub_zero]
/-- Annulus count on the shell `(1 / 2) < |z-c| < (3 / 2)`: outer circle integral minus
    inner circle integral isolates the poles in the shell,
    `∮_(C(c,(3 / 2))) Σ_ρ (m ρ)(z-ρ)⁻¹ - ∮_(C(c,(1 / 2))) Σ_ρ (m ρ)(z-ρ)⁻¹ = 2πi · Σ_ρ (m ρ)`.
    Outer counts all inside; inner = 0 (poles outside ⟹ analytic ⟹ Cauchy). -/
theorem annulus_count_half_3half {c : ℂ} (m : ℂ → ℤ) (s : Finset ℂ)
    (hin : ∀ ρ ∈ s, ρ ∈ ball c (((3 / 2)) : ℝ))
    (hout : ∀ ρ ∈ s, (((1 / 2)) : ℝ) < dist ρ c) :
    (∮ z in C(c, ((3 / 2) : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
        - (∮ z in C(c, ((1 / 2) : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  have hRout : (0 : ℝ) < (3 / 2) := by norm_num
  have houter_int : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ((3 / 2) : ℝ) := by
    intro ρ hρ
    have hd : dist ρ c < ((3 / 2) : ℝ) := by rw [← mem_ball]; exact hin ρ hρ
    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ((3 / 2) : ℝ) := by
      rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_
      rw [mem_sphere, abs_of_pos hRout]; exact fun h => absurd h (by linarith)
    exact hbase.const_mul _
  have houter : (∮ z in C(c, ((3 / 2) : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
    rw [circleIntegral.integral_fun_sum houter_int]
    have hcong : ∀ ρ ∈ s,
        (∮ z in C(c, ((3 / 2) : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by
      intro ρ hρ
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (hin ρ hρ)]
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]
  have hinner : (∮ z in C(c, ((1 / 2) : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) = 0 := by
    have hzero : ∀ ρ ∈ s, (∮ z in C(c, ((1 / 2) : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = 0 := by
      intro ρ hρ
      rw [circleIntegral.integral_const_mul]
      have hbody : (∮ z in C(c, ((1 / 2) : ℝ)), (z - ρ)⁻¹) = 0 := by
        apply DiffContOnCl.circleIntegral_eq_zero (by norm_num : (0 : ℝ) ≤ (1 / 2))
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball c (by norm_num : ((1 / 2) : ℝ) ≠ 0)]
        intro z hz
        have hzr : dist z c ≤ (1 / 2) := by rwa [mem_closedBall] at hz
        have hne : z - ρ ≠ 0 := by
          intro h; rw [sub_eq_zero] at h
          have hd2 := hout ρ hρ; rw [← h] at hd2; linarith
        exact ((differentiableAt_id.sub_const ρ).inv hne).differentiableWithinAt
      rw [hbody, mul_zero]
    have hinner_int : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ((1 / 2) : ℝ) := by
      intro ρ hρ
      have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ((1 / 2) : ℝ) := by
        rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_
        rw [mem_sphere]; intro h
        have hd2 := hout ρ hρ; rw [h] at hd2; norm_num at hd2
      exact hbase.const_mul _
    rw [circleIntegral.integral_fun_sum hinner_int, Finset.sum_congr rfl hzero,
      Finset.sum_const_zero]
  rw [houter, hinner, sub_zero]

end AnnulusCount
