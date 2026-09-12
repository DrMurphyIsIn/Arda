/- PHASE 4 (dVP frontier, Blaschke → skeleton GLUE): combine the Blaschke BC-SUM with the Herglotz
   lower bound to produce the reduction skeleton's `hzero` / `htwo` shapes.

   `DlvpBCSumBlaschke.bc_sum_blaschke` gives `-Re(ζ'/ζ)(z) ≤ AL - Re(Z)`, `Z = Σ_ρ (m ρ)/(z-ρ)`.
   `DlvpHerglotzLower.herglotz_re_ge` gives `Re(Z) ≥ k/(σ-β)` (keep the equal-height zero, drop the
   rest).  A `linarith` combines them into `-Re(ζ'/ζ)(z) ≤ AL - k/(σ-β)` — the exact `hzero` input of
   `DlvpPole.dlvp_region_of_bc_inputs`.  Dropping ALL zeros (`Re(Z) ≥ 0`, `weighted_sum_re_nonneg`)
   instead gives the `htwo` shape `-Re(ζ'/ζ)(z) ≤ AL`.  Abstract in the function `f` (composes with the
   ζ recentering).  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpHerglotzLower

open Complex

namespace ZeroFreeBridge

/-- **Weighted Herglotz nonnegativity.**  If every zero `ρ` has `Re ρ < Re z` and the multiplicities
    are nonnegative, the weighted Herglotz sum has nonnegative real part. -/
theorem weighted_sum_re_nonneg (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hlt : ∀ ρ ∈ s, ρ.re < z.re) :
    0 ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ)).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro ρ hρ
  have hzr : 0 < (z - ρ).re := by rw [Complex.sub_re]; linarith [hlt ρ hρ]
  have hre : ((m ρ : ℂ) / (z - ρ)).re = (m ρ : ℝ) * ((z - ρ)⁻¹).re := by
    rw [div_eq_mul_inv, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
    ring
  rw [hre]
  apply mul_nonneg (by exact_mod_cast hm ρ hρ)
  rw [Complex.inv_re]
  exact div_nonneg hzr.le (Complex.normSq_nonneg _)

/-- **`hzero` glue.**  BC-SUM + Herglotz lower bound ⟹ `-Re(ζ'/ζ)(σ+γI) ≤ AL - k/(σ-β)`. -/
theorem hzero_of_blaschke {f : ℂ → ℂ} (s : Finset ℂ) (m : ℂ → ℤ) (σ γ β AL : ℝ) (k : ℤ)
    (hbc : (-(logDeriv f ((σ : ℂ) + (γ : ℂ) * I))).re
             ≤ AL - (∑ ρ ∈ s, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ)).re)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I)
    (hmρ₀ : m ρ₀ = k) (hother : ∀ ρ ∈ s, ρ ≠ ρ₀ → ρ.re < σ) :
    (-(logDeriv f ((σ : ℂ) + (γ : ℂ) * I))).re ≤ AL - (k : ℝ) / (σ - β) := by
  have hherg := herglotz_re_ge m σ γ β k hm ρ₀ hρ₀ hρ₀_eq hmρ₀ hother
  linarith

/-- **`htwo` glue.**  BC-SUM + weighted Herglotz nonnegativity ⟹ `-Re(ζ'/ζ)(z) ≤ AL`. -/
theorem htwo_of_blaschke {f : ℂ → ℂ} (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ) (AL : ℝ)
    (hbc : (-(logDeriv f z)).re ≤ AL - (∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ)).re)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hlt : ∀ ρ ∈ s, ρ.re < z.re) :
    (-(logDeriv f z)).re ≤ AL := by
  have hnn := weighted_sum_re_nonneg s m z hm hlt
  linarith

end ZeroFreeBridge
