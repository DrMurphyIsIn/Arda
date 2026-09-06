/- PHASE 4 (dVP frontier, BLASCHKE item (d4) capstone): the BC-SUM for the Blaschke split.

   Combines the explicit formula `ζ'/ζ = Z + E` (`DlvpBlaschkeSplitExpand`) with the entire-part
   bound `‖E‖ ≤ A·L` (correction via `DlvpCorrectionBound` (d3) + `‖logDeriv g‖` via item (c)) through
   the rung-2 combine `DlvpBCSum.bc_sum_of_split`, yielding the de la Vallee Poussin BC-SUM:

     `-Re(ζ'/ζ)(z) ≤ A·L − Re(Σ_ρ (divisor ρ)/(z−ρ))`,

   with `Z = Σ_ρ (divisor ρ)/(z−ρ)` the Herglotz zero-sum whose `Re` is `≥ 0` near the line (rung 1),
   hence droppable.  This is the `hzero`/`htwo` input the reduction skeleton (`DlvpZeroSum`/`DlvpPole`/
   `DlvpBCSum` → `ZeroFreeRegion`) consumes to reach `β ≤ 1 − c/log|t|`.  conjecture1_proved = False.
-/
import DlvpBlaschkeSplitExpand
import DlvpCorrectionBound
import DlvpBCSum

open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

/-- **(d4) capstone: the Blaschke BC-SUM.**  Given the canonical decomposition and a bound `Bg` on
    `‖logDeriv g z‖`, with `A·L` dominating the correction + `Bg`, the de la Vallee Poussin BC-SUM
    `-Re(logDeriv f z) ≤ A·L − Re(Herglotz zero-sum)` holds. -/
theorem bc_sum_blaschke {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R)
    (hf_ana : AnalyticOnNhd ℂ f (ball 0 R)) (hg_ana : AnalyticOnNhd ℂ g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hzne : ∀ u ∈ hfin.toFinset, z ≠ u)
    {Bg AL : ℝ} (hg_bound : ‖logDeriv g z‖ ≤ Bg)
    (hAL : (∑ u ∈ hfin.toFinset, |(divisor f (ball 0 R) u : ℝ)|) / (R - ‖z‖) + Bg ≤ AL) :
    (-(logDeriv f z)).re
      ≤ AL - (∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u)).re := by
  have hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) R := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hdu : divisor f (ball 0 R) u ≠ 0 := fun h => hu (by simp [h])
    exact (divisor f (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hdu)
  have hzR : ‖z‖ < R := by rw [← mem_ball_zero_iff]; exact hz
  set Z : ℂ := ∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u) with hZ
  set Corr : ℂ := ∑ u ∈ hfin.toFinset,
    (divisor f (ball 0 R) u : ℂ) * (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z) with hCorr
  have hw : logDeriv f z = Z + (Corr + logDeriv g z) :=
    logDeriv_eq_herglotz_add_entire hR D hf_ana hg_ana hg_ne hfin hz hzne
  have hCorr_bound :
      ‖Corr‖ ≤ (∑ u ∈ hfin.toFinset, |(divisor f (ball 0 R) u : ℝ)|) / (R - ‖z‖) :=
    norm_correction_sum_le hR (fun u => divisor f (ball 0 R) u) hfin.toFinset hsupp hzR
  have hE : ‖Corr + logDeriv g z‖ ≤ AL :=
    le_trans (norm_add_le _ _) (le_trans (add_le_add hCorr_bound hg_bound) hAL)
  exact bc_sum_of_split (logDeriv f z) Z (Corr + logDeriv g z) AL hw hE

end ZeroFreeBridge
