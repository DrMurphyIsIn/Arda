/- PHASE 4 (dVP frontier, obligation (i) CORE): the partial-fraction SPLIT of a
   log-derivative into its Herglotz zero-sum plus the entire part.

   BC-SUM (`DlvpBCSum.bc_sum_of_split`) reduces the region to `w = Z + E, ‖E‖ ≤ B`.  The
   split ITSELF — obligation (i) — comes from the canonical factorization of `f` on a disk
   (Mathlib `MeromorphicOn.extract_zeros_poles`: `f = (∏_ρ (·-ρ)^{m_ρ}) · g` with `g` the
   zero-free part).  Taking log-derivatives, `logDeriv` is additive over the product and the
   zero factor's log-derivative is EXACTLY the Herglotz sum:

       f'/f(z) = Σ_ρ m(ρ)/(z-ρ) + g'/g(z)      (= Z + E).

   This file proves that split, function-agnostically and kernel-clean, given the factored
   form:
     * `logDeriv_sub_zpow`      — one zero factor `(w-ρ)^n` contributes `n/(z-ρ)`;
     * `logDeriv_prod_sub_zpow` — a finite product gives the Herglotz sum `Σ_ρ m(ρ)/(z-ρ)`
       (the `Z`-identification);
     * `herglotz_split`         — the full `f'/f = Z + logDeriv g` for `f = (∏..) · g`.

   This reduces obligation (i) to: (i-a) the factorization `f = (∏..) · g` on the disk
   (`extract_zeros_poles` on ζ, the codiscrete step), and (i-b) `g` zero-free ⟹ `logDeriv g`
   analytic (the entire part `E`, then bounded by Borel-Caratheodory).  Emitted certificates
   `emit_bc_split`/`emit_jensen_zero_count`/`emit_sphere_bound` cover the surrounding atoms.
   Improves the region-rate chain only; NOT a proof of RH.  conjecture1_proved = False.
-/
import Mathlib

open Complex

namespace ZeroFreeBridge

/-- One zero factor: `logDeriv ((·-ρ)^n)` at `z ≠ ρ` is the Herglotz term `n/(z-ρ)`. -/
theorem logDeriv_sub_zpow (ρ z : ℂ) (n : ℤ) (hz : z ≠ ρ) :
    logDeriv (fun w => (w - ρ) ^ n) z = (n : ℂ) / (z - ρ) := by
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - ρ) z := by fun_prop
  have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hz
  have hd : deriv (fun w : ℂ => w - ρ) z = 1 := ((hasDerivAt_id z).sub_const ρ).deriv
  have hld : logDeriv (fun w : ℂ => w - ρ) z = 1 / (z - ρ) := by rw [logDeriv_apply, hd]
  rw [logDeriv_fun_zpow hsub n, hld, mul_one_div]

/-- Differentiability of a single zero factor `(w-ρ)^n` at `z ≠ ρ` (negative `n` too). -/
theorem differentiableAt_sub_zpow (ρ z : ℂ) (n : ℤ) (hz : z ≠ ρ) :
    DifferentiableAt ℂ (fun w : ℂ => (w - ρ) ^ n) z := by
  apply DifferentiableAt.zpow
  · fun_prop
  · exact Or.inl (sub_ne_zero.mpr hz)

/-- **The `Z`-identification.**  `logDeriv` of the finite product of zero factors is the
    Herglotz sum `Σ_ρ m(ρ)/(z-ρ)` — the zero-sum half of the partial-fraction split. -/
theorem logDeriv_prod_sub_zpow (Z : Finset ℂ) (m : ℂ → ℤ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ (m ρ)) z
      = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_prod (f := fun ρ => fun w : ℂ => (w - ρ) ^ (m ρ))
        (fun ρ hρ => zpow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
        (fun ρ hρ => differentiableAt_sub_zpow ρ z (m ρ) (hz ρ hρ))]
  exact Finset.sum_congr rfl (fun ρ hρ => logDeriv_sub_zpow ρ z (m ρ) (hz ρ hρ))

/-- **The partial-fraction split (obligation (i) core).**  For `f = (∏_ρ (·-ρ)^{m(ρ)}) · g`
    with the zero factors and `g` the zero-free part (`g z ≠ 0`, differentiable), the
    log-derivative splits as the Herglotz zero-sum `Z` plus the entire part `E = logDeriv g`:
    `f'/f(z) = Σ_ρ m(ρ)/(z-ρ) + g'/g(z)`. -/
theorem herglotz_split (Z : Finset ℂ) (m : ℂ → ℤ) (g : ℂ → ℂ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z ≠ ρ) (hg : g z ≠ 0) (hgd : DifferentiableAt ℂ g z) :
    logDeriv (fun w => (∏ ρ ∈ Z, (w - ρ) ^ (m ρ)) * g w) z
      = (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) + logDeriv g z := by
  have hprod : (fun w => ∏ ρ ∈ Z, (w - ρ) ^ (m ρ)) z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun ρ hρ => zpow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
  have hpd : DifferentiableAt ℂ (fun w => ∏ ρ ∈ Z, (w - ρ) ^ (m ρ)) z :=
    DifferentiableAt.fun_finsetProd
      (fun ρ hρ => differentiableAt_sub_zpow ρ z (m ρ) (hz ρ hρ))
  rw [logDeriv_mul z hprod hg hpd hgd, logDeriv_prod_sub_zpow Z m z hz]

end ZeroFreeBridge
