/- PHASE 4 (dVP frontier, item 1 COMPLETE — hg_bound fully wired): the entire-part bound
   `‖logDeriv g z₀‖ ≤ 4·Aζ''·(R+‖z₀‖)/(R-‖z₀‖)² = O(L)` for the recentred-ζ Blaschke quotient g,
   from JUST a `CanonicalDecomp` + the disk geometry — every sub-input discharged internally.

   `norm_logDeriv_g_le_strip` needs 4 inputs beyond D/geometry: hf_cont, hg_cont, hg_dcc, hfg0.
   This wrapper discharges all four (general in c₀, so reusable for the height-γ disk c₀=2+iγ AND
   the height-2γ disk c₁=2+2iγ):
     * hf_cont  = `zeta_recenter_cont_sphere` (ζ(c₀+·) cont on sphere);
     * hg_cont  = `canonicalDecomp_contOn_sphere`, hg_dcc = `canonicalDecomp_diffContOnCl`
                  (g analytic up to the sphere, PR #289, needs f analytic on the sphere);
     * hfg0     = `zeta_norm_le_g_zero` (‖ζ c₀‖≤‖g 0‖ from ‖B 0‖≤1), fed by the centre factorization
                  `zeta_center_factorization` ← `continuousAt_blaschke_smul_g_zero` (B·g cont at 0) +
                  the divisor-support facts (u≠0 since ζ(c₀)≠0 ⟹ divisor 0 =0; ‖u‖<R; divisor ≥0).
   `1∉closedBall c₀ R` is derived from `|c₀.im| ≥ R+2`; the recentred ζ analyticity on closedBall 0 R
   is the standard `zeta_analyticOnNhd_disk ∘ shift`.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaSphereLogStrip
import DlvpZetaContSphere
import DlvpCanonicalClosedBall
import DlvpZetaCentreRel
import DlvpZetaCentreFac
import DlvpBlaschkeCont
import DlvpBlaschkeAnalytic
open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

theorem norm_logDeriv_g_le_wired {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hRlt : R < c₀.re - 1/2) (himc : R + 2 ≤ |c₀.im|)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * (Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
              - Real.log (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by
  have hc : 1 < c₀.re := by linarith
  -- 1 ∉ closedBall c₀ R (from |c₀.im| ≥ R+2)
  have h1 : (1 : ℂ) ∉ closedBall c₀ R := by
    rw [mem_closedBall, Complex.dist_eq]
    intro hle
    have h3 : |((1 : ℂ) - c₀).im| = |c₀.im| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    have h4 : |((1 : ℂ) - c₀).im| ≤ ‖(1 : ℂ) - c₀‖ := Complex.abs_im_le_norm _
    rw [h3] at h4; linarith
  -- recentred ζ analytic on closedBall 0 R
  have hana : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (closedBall 0 R) := by
    have hshift_ana : AnalyticOnNhd ℂ (fun w => c₀ + w) (closedBall 0 R) :=
      fun z _ => analyticAt_const.add analyticAt_id
    have hmaps : Set.MapsTo (fun w => c₀ + w) (closedBall (0 : ℂ) R) (closedBall c₀ R) := by
      intro w hw
      rw [mem_closedBall, Complex.dist_eq] at hw
      rw [mem_closedBall, Complex.dist_eq, add_sub_cancel_left]; simpa using hw
    exact (zeta_analyticOnNhd_disk c₀ R h1).comp hshift_ana hmaps
  have hf_sphere := hana.mono sphere_subset_closedBall
  have hf_cont := zeta_recenter_cont_sphere h1
  have hg_cont := canonicalDecomp_contOn_sphere hR D hf_sphere
  have hg_dcc := canonicalDecomp_diffContOnCl hR D hf_sphere
  have hg_ne := canonicalDecomp_ne_zero D
  have hg_ana := canonicalDecomp_analyticOnNhd D
  -- divisor support finite
  have hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D.meromorphicOn.divisor_ball_support_finite
  set m : ℂ → ℤ := fun u => divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u with hm_def
  -- support facts
  have hfb : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (ball 0 R) :=
    hana.mono ball_subset_closedBall
  have hsupp0 : ∀ u ∈ hfin.toFinset, u ≠ 0 := by
    intro u hu h0
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    subst h0
    apply hu
    rw [neg_eq_zero]
    show divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) 0 = 0
    rw [hfb.divisor_apply (mem_ball_self hR)]
    have hf0 : (fun w => riemannZeta (c₀ + w)) 0 ≠ 0 := by
      simp only [add_zero]; exact zeta_ne_zero_of_one_lt_re c₀ hc
    rw [(hfb 0 (mem_ball_self hR)).analyticOrderAt_eq_zero.mpr hf0]
    simp
  have hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0 ∧ ‖u‖ < R := by
    intro u hu
    refine ⟨hsupp0 u hu, ?_⟩
    rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu
    have := (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
      (Function.mem_support.mpr hu)
    rwa [mem_ball_zero_iff] at this
  have hm : ∀ u ∈ hfin.toFinset, 0 ≤ m u := fun u _ =>
    hfb.divisor_nonneg u
  -- centre factorization → hfg0
  have hf_cont0 : ContinuousAt (fun w => riemannZeta (c₀ + w)) 0 :=
    (hfb 0 (mem_ball_self hR)).continuousAt
  have hg_cont0 : ContinuousAt g 0 := (hg_ana 0 (mem_ball_self hR)).continuousAt
  have hBg_cont0 := continuousAt_blaschke_smul_g_zero hR m hfin hsupp0 hg_cont0
  have hfac0 := zeta_center_factorization hR D hf_cont0 hBg_cont0
  have hfg0 := zeta_norm_le_g_zero hR m hfin hsupp hm hfac0
  exact norm_logDeriv_g_le_strip hR hc2 hRlt himc D hf_cont hg_cont hg_dcc hg_ne hfg0 hz₀

end ZeroFreeBridge
