/- PHASE 4 (dVP frontier, obligation (i-a') CORE): transferring a factorization equality to a
   POINTWISE log-derivative equality — the germ / identity-principle machinery.

   `DlvpEntire.zeta_extract_zeros_poles` gives the factorization only up to CODISCRETE equality
   `ζ =ᶠ[codiscreteWithin U] (∏ᶠ..)·g`; `DlvpHerglotz.herglotz_split` computes `logDeriv` of the
   FACTORED form.  To connect them one needs `logDeriv ζ z = logDeriv ((∏ᶠ..)·g) z` POINTWISE.
   `logDeriv` depends only on the germ (value + derivative at `z`), so it agrees wherever the
   functions agree on a NEIGHBORHOOD — and two analytic functions agreeing near one point agree
   on the whole connected set (the identity principle):

     * `logDeriv_congr_nhds`        — germ equality ⟹ equal log-derivatives;
     * `logDeriv_congr_eqOn_open`   — agreement on an OPEN set ⟹ equal log-derivatives there;
     * `logDeriv_congr_of_analytic` — two analytic functions on a preconnected open `U` agreeing
       on a NEIGHBORHOOD of some `z₀ ∈ U` have equal log-derivatives at EVERY `z ∈ U`.

   This reduces obligation (i-a') to the single filter step: the codiscrete factorization's
   DISAGREEMENT set is discrete, so a non-exceptional point `z₀` has a neighborhood of agreement,
   feeding `logDeriv_congr_of_analytic` (+ the finprod↔Finset bridge to `herglotz_split`).
   Function-agnostic.  conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

open Complex

namespace ZeroFreeBridge

/-- Log-derivatives agree wherever the functions agree on a NEIGHBORHOOD: `logDeriv` is a
    germ invariant (value + derivative at the point). -/
theorem logDeriv_congr_nhds {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[nhds z] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- Log-derivatives agree at any point of an OPEN set on which the functions agree. -/
theorem logDeriv_congr_eqOn_open {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (h : Set.EqOn f₁ f₂ U) :
    logDeriv f₁ z = logDeriv f₂ z :=
  logDeriv_congr_nhds (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h)

/-- **Identity-principle transfer.**  Two analytic functions on a preconnected open `U` that
    agree on a NEIGHBORHOOD of some `z₀ ∈ U` have equal log-derivatives at EVERY `z ∈ U`.  For
    the ζ factorization the neighborhood agreement comes from the codiscrete factorization at a
    non-exceptional point (the disagreement set is discrete). -/
theorem logDeriv_congr_of_analytic {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z₀ z : ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ U) (hf₂ : AnalyticOnNhd ℂ f₂ U)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U) (hz : z ∈ U)
    (h : f₁ =ᶠ[nhds z₀] f₂) :
    logDeriv f₁ z = logDeriv f₂ z :=
  logDeriv_congr_eqOn_open hU hz
    (hf₁.eqOn_of_preconnected_of_eventuallyEq hf₂ hUc hz₀ h)

open scoped Topology in
/-- (i-a'') **codiscrete transfer.**  Two analytic functions on a preconnected open `U` agreeing
    CODISCRETELY (off a discrete set, `=ᶠ[codiscreteWithin U]`) have equal log-derivatives at
    EVERY `z ∈ U`.  This is the exact shape `MeromorphicOn.extract_zeros_poles` produces, so it
    connects the ζ factorization to a pointwise `logDeriv` equality: codiscrete membership gives
    punctured-neighborhood agreement (drop `Uᶜ`, since `U ∈ 𝓝 z₀`), hence a `∃ᶠ` (`𝓝[≠]` is
    NeBot on ℂ), hence `EqOn` by the analytic identity principle. -/
theorem logDeriv_congr_of_codiscrete {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z₀ z : ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ U) (hf₂ : AnalyticOnNhd ℂ f₂ U)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U) (hz : z ∈ U)
    (h : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  have hmem : {x | f₁ x = f₂ x} ∪ Uᶜ ∈ 𝓝[≠] z₀ :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h) z₀ hz₀
  have hU_nhds : U ∈ 𝓝[≠] z₀ := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz₀)
  have hev : ∀ᶠ x in 𝓝[≠] z₀, f₁ x = f₂ x := by
    filter_upwards [hmem, hU_nhds] with x hx hxU
    rcases hx with h1 | h2
    · exact h1
    · exact absurd hxU h2
  exact logDeriv_congr_eqOn_open hU hz
    (hf₁.eqOn_of_preconnected_of_frequently_eq hf₂ hUc hz₀ hev.frequently)

end ZeroFreeBridge
