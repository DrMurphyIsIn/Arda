/- PHASE 4 (dVP frontier, BLASCHKE → skeleton bridge): the Herglotz lower bound.

   `DlvpBCSumBlaschke.bc_sum_blaschke` gives `-Re(ζ'/ζ) ≤ A·L − Re(Z)` with `Z = Σ_ρ (divisor ρ)/(z−ρ)`.
   To reach the skeleton's `hzero` shape `-Re(ζ'/ζ) ≤ A·L − k/(σ−β)`, one needs `Re(Z) ≥ k/(σ−β)`:
   keep the zero `ρ₀ = β+γI` at the SAME height as `z = σ+γI` (its real part is exactly `k/(σ−β)`,
   rung 1 `re_smul_inv_sub_at_equal_height`) and DROP the other zeros (each `Re ≥ 0` since their real
   part is `< σ`, rung 1 `re_inv_sub_nonneg_of_re_lt`, times the nonnegative multiplicity).

     `herglotz_re_ge` :  ρ₀ ∈ s with `ρ₀ = β+γI`, `m ρ₀ = k`, `m ≥ 0`, other zeros `Re < σ`
       ⟹  `k/(σ−β) ≤ Re(Σ_ρ (m ρ)/((σ+γI) − ρ))`.

   Combined with `bc_sum_blaschke` (a `linarith`) this yields the `hzero`/`htwo` inputs the reduction
   skeleton `DlvpPole.dlvp_region_of_bc_inputs` consumes.  conjecture1_proved = False (NOT RH).
-/
import DlvpZeroSum

open Complex

namespace ZeroFreeBridge

/-- **Herglotz lower bound.**  At `z = σ+γI`, keeping the equal-height zero `ρ₀ = β+γI` (multiplicity
    `k`) and dropping the other (nonnegative-multiplicity, `Re < σ`) zeros,
    `k/(σ−β) ≤ Re(Σ_ρ (m ρ)/(z−ρ))`. -/
theorem herglotz_re_ge {s : Finset ℂ} (m : ℂ → ℤ) (σ γ β : ℝ) (k : ℤ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I) (hmρ₀ : m ρ₀ = k)
    (hother : ∀ ρ ∈ s, ρ ≠ ρ₀ → ρ.re < σ) :
    (k : ℝ) / (σ - β)
      ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ)).re := by
  set z : ℂ := (σ : ℂ) + (γ : ℂ) * I with hz
  rw [Complex.re_sum, ← Finset.add_sum_erase _ _ hρ₀]
  -- the distinguished term equals `k/(σ-β)`.
  have hterm₀ : ((m ρ₀ : ℂ) / (z - ρ₀)).re = (k : ℝ) / (σ - β) := by
    rw [hmρ₀, hρ₀_eq, hz]
    exact_mod_cast re_smul_inv_sub_at_equal_height σ γ β (k : ℝ)
  -- the remaining terms are nonnegative.
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