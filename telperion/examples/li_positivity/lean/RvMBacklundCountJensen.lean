/-
RvMBacklundCountJensen — Backlund S(T)=O(log T), PR 5 step 3: the explicit O(log T) horizontal bound.

Combines the ζ horizontal bound (PR 5, in terms of the zero COUNT) with the Jensen count (PR 3b) to make
the bound literally `O(log T)`:

  * `zeta_argChangeHoriz_abs_le_log` — `|argChangeHoriz ζ T (1/2) 2| ≤ (log((4T+19)/‖F_T 2‖)/log(7/6) + 1)·π`.

The count step: the real zeros of `F_T` inject (via `Complex.ofReal`) into the support of `F_T`'s divisor
on `closedBall 2 (3/2)` (each has positive analytic order — the PR 4c-finiteness argument), so their count
is at most `card(support) ≤ ∑ᶠ divisor` (divisor `≥ 1` on its support), which PR 3b bounds by the Jensen
`O(log T)`.  conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundZeta
import RvMBacklundJensen
import RvMBacklundFinite

open Complex MeasureTheory

namespace Backlund

/-- **Explicit `O(log T)` horizontal argument bound for `ζ`.** -/
theorem zeta_argChangeHoriz_abs_le_log {T : ℝ} (hT : 4 ≤ T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hlogcont : ContinuousOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2)) :
    |DiffractionCore.argChangeHoriz riemannZeta T (1 / 2) 2|
      ≤ (Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2)) + 1)
        * Real.pi := by
  set D := MeromorphicOn.divisor (backlundAux T) (Metric.closedBall (2 : ℂ) (3 / 2)) with hD
  have hana74 : AnalyticOnNhd ℂ (backlundAux T) (Metric.closedBall (2 : ℂ) (7 / 4)) :=
    backlundAux_analyticOnNhd_ball hT
  have hpre : IsPreconnected (Metric.closedBall (2 : ℂ) (7 / 4)) :=
    (convex_closedBall _ _).isPreconnected
  have hF2ne : backlundAux T (2 : ℂ) ≠ 0 := by
    have hge := backlundAux_two_norm_ge T
    have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    rw [h2] at hge; intro hz; rw [hz, norm_zero] at hge; nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hsub : Metric.closedBall (2 : ℂ) (3 / 2) ⊆ Metric.closedBall (2 : ℂ) (7 / 4) :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hana32 : AnalyticOnNhd ℂ (backlundAux T) (Metric.closedBall (2 : ℂ) (3 / 2)) := hana74.mono hsub
  have hsupp : (Function.support D).Finite :=
    hana74.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall _ _) hsub
  -- each real zero of F_T lands in the divisor support
  have hmem : ∀ σ ∈ (backlundAux_real_zeros_finite hT).toFinset, (σ : ℂ) ∈ Function.support D := by
    intro σ hσ
    obtain ⟨hσIcc, hσ0⟩ := (backlundAux_real_zeros_finite hT).mem_toFinset.mp hσ
    obtain ⟨hσ1, hσ2⟩ := hσIcc
    have hmem32 : (σ : ℂ) ∈ Metric.closedBall (2 : ℂ) (3 / 2) := by
      rw [Metric.mem_closedBall, Complex.dist_eq,
        show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    have hAA : AnalyticAt ℂ (backlundAux T) (σ : ℂ) := hana32 _ hmem32
    have ho_ne0 : analyticOrderAt (backlundAux T) (σ : ℂ) ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hAA, hσ0⟩
    have ho_neTop : analyticOrderAt (backlundAux T) (σ : ℂ) ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      exact hF2ne ((hana74.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre (hsub hmem32) htop)
        (Metric.mem_closedBall_self (by norm_num)))
    rw [Function.mem_support, hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hana32 hmem32]
    lift analyticOrderAt (backlundAux T) (σ : ℂ) to ℕ using ho_neTop with k
    rw [ENat.map_natCast]; simpa using ho_ne0
  -- so the zero count is at most the divisor-support cardinality
  have hcard1 : (backlundAux_real_zeros_finite hT).toFinset.card ≤ hsupp.toFinset.card := by
    rw [← Finset.card_image_of_injOn (Complex.ofReal_injective.injOn)]
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨σ, hσ, rfl⟩ := hz
    exact hsupp.mem_toFinset.mpr (hmem σ hσ)
  -- support card ≤ ∑ᶠ divisor (divisor ≥ 1 on its support)
  have hDnn : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana32 u
  have hsum_supp : ∑ᶠ u, D u = ∑ u ∈ hsupp.toFinset, D u := by
    apply finsum_eq_finsetSum_of_support_subset
    intro x hx
    exact Finset.mem_coe.mpr (hsupp.mem_toFinset.mpr hx)
  have hcard2 : (hsupp.toFinset.card : ℤ) ≤ ∑ᶠ u, D u := by
    rw [hsum_supp]
    have h1 : ∀ u ∈ hsupp.toFinset, (1 : ℤ) ≤ D u := by
      intro u hu
      have hne : D u ≠ 0 := Function.mem_support.mp (hsupp.mem_toFinset.mp hu)
      have := hDnn u
      omega
    calc (hsupp.toFinset.card : ℤ) = ∑ _u ∈ hsupp.toFinset, (1 : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ u ∈ hsupp.toFinset, D u := Finset.sum_le_sum h1
  -- chain PR 5 with PR 3b Jensen
  have h5 := zeta_argChangeHoriz_abs_le hT hζne hlogcont
  have h487 := backlundAux_zero_count_le hT
  have hZle : ((backlundAux_real_zeros_finite hT).toFinset.card : ℝ)
      ≤ Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2)) := by
    have hstep : ((backlundAux_real_zeros_finite hT).toFinset.card : ℤ) ≤ ∑ᶠ u, D u :=
      le_trans (by exact_mod_cast hcard1) hcard2
    calc ((backlundAux_real_zeros_finite hT).toFinset.card : ℝ)
        ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by exact_mod_cast hstep
      _ ≤ _ := h487
  calc |DiffractionCore.argChangeHoriz riemannZeta T (1 / 2) 2|
      ≤ ((backlundAux_real_zeros_finite hT).toFinset.card + 1) * Real.pi := h5
    _ ≤ (Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2)) + 1)
          * Real.pi := by
        apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
        linarith [hZle]

end Backlund
