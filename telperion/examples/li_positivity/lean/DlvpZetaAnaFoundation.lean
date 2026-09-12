/- PHASE 4 (dVP frontier, final-assembly foundation atoms): reusable helpers that cut the boilerplate
   of the capstone `dlvp_zeta_region_of_bc_sums` instantiation for c₀=2+iγ (and c₁=2+2iγ).

   Every downstream analyticity hypothesis derives from ONE atom, `zeta_recenter_ana_closedBall`
   (recentred ζ analytic on `closedBall 0 R`): `hf_ana` = `.mono ball_subset_closedBall`, sphere
   continuity = `.mono sphere_subset_closedBall |>.continuousOn`, `hf'_mero` = `.meromorphicOn`; and
   `hf_ana_cl`/`hf_mero` on the physical disk = `zeta_analyticOnNhd_disk` directly.  The `1∉closedBall`
   precondition is `one_notMem_closedBall_of_himc` (from `R+2 ≤ |c₀.im|`).  conjecture1_proved = False.
-/
import DlvpZetaDisk
open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- `1 ∉ closedBall c₀ R` from `R + 2 ≤ |c₀.im|` (the height dominates the radius). -/
theorem one_notMem_closedBall_of_himc {c₀ : ℂ} {R : ℝ} (himc : R + 2 ≤ |c₀.im|) :
    (1 : ℂ) ∉ closedBall c₀ R := by
  rw [mem_closedBall, Complex.dist_eq]
  intro hle
  have h3 : |((1 : ℂ) - c₀).im| = |c₀.im| := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have h4 : |((1 : ℂ) - c₀).im| ≤ ‖(1 : ℂ) - c₀‖ := Complex.abs_im_le_norm _
  rw [h3] at h4; linarith

/-- **The recentred-ζ closed-ball analyticity atom.**  `fun w => ζ(c₀+w)` is `AnalyticOnNhd` on
    `closedBall 0 R` when `1 ∉ closedBall c₀ R`.  Foundation from which every downstream analyticity
    (`hf_ana` on the ball, sphere continuity, `hf'_mero`) derives by `.mono`/`.meromorphicOn`. -/
theorem zeta_recenter_ana_closedBall (c₀ : ℂ) (R : ℝ) (h1 : (1 : ℂ) ∉ closedBall c₀ R) :
    AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (closedBall 0 R) := by
  have hshift : AnalyticOnNhd ℂ (fun w => c₀ + w) (closedBall 0 R) :=
    fun z _ => analyticAt_const.add analyticAt_id
  have hmaps : Set.MapsTo (fun w => c₀ + w) (closedBall (0 : ℂ) R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    rw [mem_closedBall, Complex.dist_eq, add_sub_cancel_left]; simpa using hw
  exact (zeta_analyticOnNhd_disk c₀ R h1).comp hshift hmaps

end ZeroFreeBridge
