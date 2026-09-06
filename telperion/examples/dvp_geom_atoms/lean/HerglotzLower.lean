/- telperion 0.1.6 | family HerglotzLower | input-hash 7e49218eabc49e14
   3 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace HerglotzLower

open Complex

/-- Equal-height contribution (helper): the zero at the same height has a real term. -/
private theorem re_smul_inv_sub_at_equal_height (σ γ β : ℝ) (k : ℝ) :
    (((k : ℂ)) / (((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I))).re = k / (σ - β) := by
  have hsub : ((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I) = ((σ - β : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Droppable zero (helper): a zero with `Re ρ < Re s` contributes a nonnegative real part. -/
private theorem re_inv_sub_nonneg_of_re_lt (s ρ : ℂ) (h : ρ.re < s.re) :
    0 ≤ (1 / (s - ρ)).re := by
  have hz : 0 < (s - ρ).re := by rw [Complex.sub_re]; linarith
  rw [one_div, Complex.inv_re]
  exact div_nonneg hz.le (Complex.normSq_nonneg _)

/-- Herglotz lower bound (kept term `1/(σ−β)`, e.g. σ=3/2, β=1/2):
    keep the equal-height zero `ρ₀ = β+γI`, drop the nonnegative rest. -/
theorem herglotz_lower_a {s : Finset ℂ} (m : ℂ → ℤ) (σ γ β : ℝ) (k : ℤ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I) (hmρ₀ : m ρ₀ = k)
    (hother : ∀ ρ ∈ s, ρ ≠ ρ₀ → ρ.re < σ) :
    (k : ℝ) / (σ - β)
      ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ)).re := by
  set z : ℂ := (σ : ℂ) + (γ : ℂ) * I with hz
  rw [Complex.re_sum, ← Finset.add_sum_erase _ _ hρ₀]
  have hterm₀ : ((m ρ₀ : ℂ) / (z - ρ₀)).re = (k : ℝ) / (σ - β) := by
    rw [hmρ₀, hρ₀_eq, hz]
    exact_mod_cast re_smul_inv_sub_at_equal_height σ γ β (k : ℝ)
  have hrest : 0 ≤ ∑ ρ ∈ s.erase ρ₀, ((m ρ : ℂ) / (z - ρ)).re := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρs : ρ ∈ s := Finset.mem_of_mem_erase hρ
    have hρne : ρ ≠ ρ₀ := Finset.ne_of_mem_erase hρ
    have hlt : ρ.re < z.re := by rw [hz]; simpa using hother ρ hρs hρne
    have hdiv : (m ρ : ℂ) / (z - ρ) = (m ρ : ℂ) * (1 / (z - ρ)) := by rw [mul_one_div]
    rw [hdiv, ← Complex.ofReal_intCast, Complex.re_ofReal_mul]
    exact mul_nonneg (by exact_mod_cast hm ρ hρs) (re_inv_sub_nonneg_of_re_lt z ρ hlt)
  rw [hterm₀]
  linarith

end HerglotzLower
