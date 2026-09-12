/- PHASE 4 (dVP frontier, item 2(i) — the count RECONCILIATION core): bound the recentred divisor
   sum (the Herglotz-sum zero count over `ball 0 R`) by the ζ finsum over `closedBall c₀ R`, which
   `zeta_zero_count_strip` then bounds by an O(log|c₀.im|) Jensen quantity.

   The gap `hAL` faces: its sum is `∑ over toFinset` of the RECENTRED divisor on `ball 0 R`, while
   the Jensen count is a finsum of `divisor ζ` on a `closedBall`.  This file bridges them (the hard
   discrete part; `finsum_le_finsum` is absent in Mathlib, so it is assembled from lower-level pieces):
     * `sum_divisor_recenter_eq_image` — pointwise translate (`divisor_comp_const_add_apply`) +
       shift-reindex (`Finset.sum_image`, `add_left_cancel` injective) ⟹ recentred sum = ζ sum over
       the shifted image `{c₀+u}`;
     * `sum_divisor_recenter_le_finsum` — `ball c₀ R = closedBall c₀ R` divisor on interior points
       (`divisor_apply` both sides = same order), then `image ⊆ finiteSupport` (compact-domain
       `locallyFinsuppWithin.finiteSupport`) + `Finset.sum_le_sum_of_subset_of_nonneg` (`divisor ≥ 0`)
       + `finsum_eq_finset_sum_of_support_subset` ⟹ `∑ ≤ ∑ᶠ divisor ζ (closedBall c₀ R)`.
   Chaining with `zeta_zero_count_strip` (inner `R`, outer `R' > R`) gives the O(L) `hcount` that
   `hAL_concrete` consumes.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpDivisorTranslate
import DlvpZetaCountStrip
open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

theorem sum_divisor_recenter_eq_image {c₀ : ℂ} {R : ℝ}
    (hf_mero : MeromorphicOn riemannZeta (ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite) :
    (∑ u ∈ hfin.toFinset, (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℤ))
      = ∑ ρ ∈ hfin.toFinset.image (fun u => c₀ + u),
          (divisor riemannZeta (ball c₀ R) ρ : ℤ) := by
  rw [Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hune : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0 := by
    rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
  have huball : u ∈ ball (0 : ℂ) R :=
    (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
      (Function.mem_support.mpr hune)
  have hcuball : c₀ + u ∈ ball c₀ R := by
    rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
  exact divisor_comp_const_add_apply c₀ hf_mero hf'_mero huball hcuball

/-- **Count reconciliation.**  The recentred divisor sum over the support (= the Herglotz-sum zero
    count in `ball 0 R`) is bounded by the strip Jensen count `zeta_zero_count_strip` (inner `R`,
    outer `R'`), as an O(log|c₀.im|) quantity. -/
theorem sum_divisor_recenter_le_finsum {c₀ : ℂ} {R : ℝ}
    (hf_mero : MeromorphicOn riemannZeta (ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hf_ana_cl : AnalyticOnNhd ℂ riemannZeta (closedBall c₀ R))
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite) :
    (∑ u ∈ hfin.toFinset, (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℤ))
      ≤ ∑ᶠ ρ, divisor riemannZeta (closedBall c₀ R) ρ := by
  rw [sum_divisor_recenter_eq_image hf_mero hf'_mero hfin]
  -- step 1: ball = closedBall divisor on image points
  have hf_mero_cl := hf_ana_cl.meromorphicOn
  have hstep1 : ∀ ρ ∈ hfin.toFinset.image (fun u => c₀ + u),
      divisor riemannZeta (ball c₀ R) ρ = divisor riemannZeta (closedBall c₀ R) ρ := by
    intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    have hune : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    have hcuball : c₀ + u ∈ ball c₀ R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    have hcucl : c₀ + u ∈ closedBall c₀ R := ball_subset_closedBall hcuball
    rw [hf_mero.divisor_apply hcuball, hf_mero_cl.divisor_apply hcucl]
  rw [Finset.sum_congr rfl (fun ρ hρ => by rw [hstep1 ρ hρ])]
  -- step 2+3: image ⊆ finiteSupport, nonneg
  have hDnn : (0 : _) ≤ divisor riemannZeta (closedBall c₀ R) := hf_ana_cl.divisor_nonneg
  have hDfin : Set.Finite (Function.support ((divisor riemannZeta (closedBall c₀ R) : ℂ → ℤ))) :=
    (divisor riemannZeta (closedBall c₀ R)).finiteSupport (isCompact_closedBall c₀ R)
  have hfinsum : ∑ᶠ ρ, divisor riemannZeta (closedBall c₀ R) ρ
      = ∑ ρ ∈ hDfin.toFinset, divisor riemannZeta (closedBall c₀ R) ρ :=
    finsum_eq_finset_sum_of_support_subset _ (by
      intro ρ hρ; rw [Set.Finite.coe_toFinset]; exact hρ)
  rw [hfinsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    rw [← hstep1 (c₀ + u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)]
    have hune : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    have hcuball : c₀ + u ∈ ball c₀ R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    rwa [← divisor_comp_const_add_apply c₀ hf_mero hf'_mero huball hcuball]
  · intro ρ _ _; exact hDnn ρ

/-- **The count as an explicit O(log|c₀.im|) bound.**  Chains `sum_divisor_recenter_le_finsum` with
    `zeta_zero_count_strip` (inner `R`, outer `R' > R`) + the ℤ→ℝ cast: the recentred divisor sum
    `≤ log(U''(R')/‖ζ c₀‖)/log(R'/R)`.  This is the concrete `hcount` for `hAL_concrete` (identify
    the RHS with `Ccount·L`, `L = log|c₀.im|`). -/
theorem sum_divisor_recenter_le_jensen {c₀ : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R')
    (hc1 : 1 < c₀.re) (hR'lt : R' < c₀.re - 1/2) (himc : R' + 2 ≤ |c₀.im|)
    (hf_mero : MeromorphicOn riemannZeta (ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hf_ana_cl : AnalyticOnNhd ℂ riemannZeta (closedBall c₀ R))
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite) :
    (∑ u ∈ hfin.toFinset, (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℝ))
      ≤ Real.log (((‖c₀‖ + R') / (|c₀.im| - R') + (‖c₀‖ + R') / (c₀.re - R'))
          / ‖riemannZeta c₀‖) / Real.log (R' / R) := by
  have hR'0 : 0 < R' := lt_trans hR hRR'
  have hZ := sum_divisor_recenter_le_finsum hf_mero hf'_mero hf_ana_cl hfin
  have hcount := zeta_zero_count_strip c₀ R R'
    (by rw [abs_of_pos hR]; exact hR)
    (by rw [abs_of_pos hR, abs_of_pos hR'0]; exact hRR')
    hc1 (by rw [abs_of_pos hR'0]; exact hR'lt) (by rw [abs_of_pos hR'0]; exact himc)
  rw [abs_of_pos hR, abs_of_pos hR'0] at hcount
  calc (∑ u ∈ hfin.toFinset, (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℝ))
      = ((∑ u ∈ hfin.toFinset, divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℤ) : ℝ) := by
        push_cast; ring
    _ ≤ ((∑ᶠ ρ, divisor riemannZeta (closedBall c₀ R) ρ : ℤ) : ℝ) := by exact_mod_cast hZ
    _ ≤ _ := hcount

end ZeroFreeBridge
