/- telperion 0.1.6 | family ArgumentPrinciple | input-hash 6c879751e5ddd4dd
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace ArgumentPrinciple

open Complex Metric Real

/-- Argument principle (residue-sum) on the circle of radius `(3 / 2)` about `c`:
    `∮_(C(c,(3 / 2))) Σ_ρ (m ρ)(z-ρ)⁻¹ = 2πi · Σ_ρ (m ρ)` for zeros `ρ` inside the disk.
    The winding/residue bridge — `(2πi)⁻¹ ∮ ζ'/ζ = Σ divisor` = the zero count. -/
theorem arg_principle_3half {c : ℂ} (m : ℂ → ℤ) (s : Finset ℂ)
    (hmem : ∀ ρ ∈ s, ρ ∈ ball c ((3 / 2) : ℝ)) :
    (∮ z in C(c, ((3 / 2) : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  have hR : (0 : ℝ) < (3 / 2) := by norm_num
  have hint : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ((3 / 2) : ℝ) := by
    intro ρ hρ
    have hd : dist ρ c < ((3 / 2) : ℝ) := by rw [← mem_ball]; exact hmem ρ hρ
    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ((3 / 2) : ℝ) := by
      rw [circleIntegrable_sub_inv_iff]
      refine Or.inr ?_
      rw [mem_sphere, abs_of_pos hR]
      exact fun h => absurd h (by linarith)
    exact hbase.const_mul _
  rw [circleIntegral.integral_fun_sum hint]
  have hcong : ∀ ρ ∈ s,
      (∮ z in C(c, ((3 / 2) : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by
    intro ρ hρ
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hmem ρ hρ)]
  rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]
/-- Argument principle (residue-sum) on the circle of radius `1` about `c`:
    `∮_(C(c,1)) Σ_ρ (m ρ)(z-ρ)⁻¹ = 2πi · Σ_ρ (m ρ)` for zeros `ρ` inside the disk.
    The winding/residue bridge — `(2πi)⁻¹ ∮ ζ'/ζ = Σ divisor` = the zero count. -/
theorem arg_principle_one {c : ℂ} (m : ℂ → ℤ) (s : Finset ℂ)
    (hmem : ∀ ρ ∈ s, ρ ∈ ball c (1 : ℝ)) :
    (∮ z in C(c, (1 : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  have hR : (0 : ℝ) < 1 := by norm_num
  have hint : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c (1 : ℝ) := by
    intro ρ hρ
    have hd : dist ρ c < (1 : ℝ) := by rw [← mem_ball]; exact hmem ρ hρ
    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c (1 : ℝ) := by
      rw [circleIntegrable_sub_inv_iff]
      refine Or.inr ?_
      rw [mem_sphere, abs_of_pos hR]
      exact fun h => absurd h (by linarith)
    exact hbase.const_mul _
  rw [circleIntegral.integral_fun_sum hint]
  have hcong : ∀ ρ ∈ s,
      (∮ z in C(c, (1 : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by
    intro ρ hρ
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hmem ρ hρ)]
  rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]

end ArgumentPrinciple
