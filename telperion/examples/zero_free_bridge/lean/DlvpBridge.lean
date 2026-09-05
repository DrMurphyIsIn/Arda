/- PHASE 4 (dVP frontier, obligation (i-a''') BRIDGE): connecting the `extract_zeros_poles`
   FINPROD factorization to the `herglotz_split` FINSET Herglotz sum.

   `DlvpEntire.zeta_extract_zeros_poles` produces the zero part as a FINPROD
   `∏ᶠ u, (·-u)^{divisor u}`; `DlvpHerglotz.herglotz_split` works with a FINSET product.  This
   file bridges them (the finprod over a finite-support divisor is the Finset product over the
   support) and assembles the split in the exact form the ζ factorization feeds:

     * `finprod_sub_zpow_eq`       — `∏ᶠ u, (·-u)^{D u} = ∏ u ∈ support, (·-u)^{D u}`;
     * `logDeriv_finprod_sub_zpow` — `logDeriv (∏ᶠ..) z = Σ_{ρ∈support} D(ρ)/(z-ρ)` (the Herglotz sum);
     * `herglotz_split_finprod`    — `logDeriv ((∏ᶠ..) * g) z = Σ_{ρ} D(ρ)/(z-ρ) + logDeriv g z`.

   With the ζ factorization (i-a), the entire-part analyticity (i-b), and the germ/identity
   transfer (i-a', `DlvpTransfer`), the remaining gaps are: (i-a'') the codiscrete→nhds filter
   step (a non-exceptional point has a neighborhood of agreement), and (i-b') the
   Borel-Caratheodory bound `‖E‖ ≤ A·L`.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpHerglotz

open Complex

namespace ZeroFreeBridge

/-- The `extract_zeros_poles` zero-part finprod equals the Finset product over the (finite)
    divisor support (as functions). -/
theorem finprod_sub_zpow_eq (D : ℂ → ℤ) (hD : (Function.support D).Finite) :
    (∏ᶠ u, (fun w : ℂ => (w - u) ^ (D u)))
      = fun w => ∏ u ∈ hD.toFinset, (w - u) ^ (D u) := by
  have hsub : Function.mulSupport (fun u => (fun w : ℂ => (w - u) ^ (D u))) ⊆ hD.toFinset := by
    intro u hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hDu
    apply hu
    funext w
    simp [hDu, Pi.one_apply]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  funext w
  exact Finset.prod_apply w hD.toFinset _

/-- (i-a''') `logDeriv` of the zero-part finprod is the Herglotz sum over the divisor support. -/
theorem logDeriv_finprod_sub_zpow (D : ℂ → ℤ) (hD : (Function.support D).Finite) (z : ℂ)
    (hz : ∀ ρ ∈ hD.toFinset, z ≠ ρ) :
    logDeriv (∏ᶠ u, (fun w : ℂ => (w - u) ^ (D u))) z
      = ∑ ρ ∈ hD.toFinset, (D ρ : ℂ) / (z - ρ) := by
  rw [finprod_sub_zpow_eq D hD]
  exact logDeriv_prod_sub_zpow hD.toFinset D z hz

/-- **The split in `extract_zeros_poles` form.**  For the factorization `(∏ᶠ_ρ (·-ρ)^{D ρ}) * g`
    (zero part times zero-free `g`), the log-derivative splits as the Herglotz zero-sum plus the
    entire part — the exact shape the ζ factorization feeds into. -/
theorem herglotz_split_finprod (D : ℂ → ℤ) (hD : (Function.support D).Finite) (g : ℂ → ℂ) (z : ℂ)
    (hz : ∀ ρ ∈ hD.toFinset, z ≠ ρ) (hg : g z ≠ 0) (hgd : DifferentiableAt ℂ g z) :
    logDeriv ((∏ᶠ u, (fun w : ℂ => (w - u) ^ (D u))) * g) z
      = (∑ ρ ∈ hD.toFinset, (D ρ : ℂ) / (z - ρ)) + logDeriv g z := by
  have hFeq := finprod_sub_zpow_eq D hD
  have hF : (∏ᶠ u, (fun w : ℂ => (w - u) ^ (D u))) z ≠ 0 := by
    rw [hFeq]
    exact Finset.prod_ne_zero_iff.mpr (fun ρ hρ => zpow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
  have hFd : DifferentiableAt ℂ (∏ᶠ u, (fun w : ℂ => (w - u) ^ (D u))) z := by
    rw [hFeq]
    exact DifferentiableAt.fun_finsetProd
      (fun ρ hρ => differentiableAt_sub_zpow ρ z (D ρ) (hz ρ hρ))
  have hmul := logDeriv_mul z hF hg hFd hgd
  show logDeriv (fun w => (∏ᶠ u, (fun w' : ℂ => (w' - u) ^ (D u))) w * g w) z = _
  rw [hmul, logDeriv_finprod_sub_zpow D hD z hz]

end ZeroFreeBridge
