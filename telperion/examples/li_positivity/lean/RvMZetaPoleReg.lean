/-
RvMZetaPoleReg — the ζ-pole regularization of the coefficient-level split, made explicit.

The coefficient split `taylorCoeff_riemannXi_split` groups the naive frontier-(a) pieces `1/(s−1)` and
`logDeriv ζ` — each SINGULAR at `s = 1 = M 0` — into the single companion `H = (s−1)·ζ`, analytic at 1.
This file proves that grouping is exactly the ζ-pole regularization:

  * `logDeriv_phi_zetaPoleCompanion_regularizes` — on the punctured neighbourhood of `0`, the companion
    pullback equals the sum of the pole pullback `logDeriv(phi (·−1))` and the ζ pullback
    `logDeriv(phi ζ)` (both singular at 0);
  * `analyticAt_logDeriv_phi_zetaPoleCompanion` — yet the companion pullback is analytic at `0`,

so the companion coefficient `taylorCoeff zetaPoleCompanion n` is finite and captures the pole+ζ
combination with the `s = 1` pole cancelled.  conjecture1_proved = False.
-/
import Mathlib
import RvMLiConnection

open Complex Filter Topology

namespace RvMWeierstrass

/-- **The companion pullback is analytic at 0** — the ζ-pole is regularized away, so
    `taylorCoeff zetaPoleCompanion n` is a finite Taylor datum. -/
theorem analyticAt_logDeriv_phi_zetaPoleCompanion :
    AnalyticAt ℂ (logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion)) 0 := by
  have hMana : AnalyticAt ℂ (fun z : ℂ => (1 - z)⁻¹) 0 :=
    (analyticAt_const.sub analyticAt_id).inv (by norm_num)
  have hphi : LiCriterion.phi DiffractionCore.zetaPoleCompanion
      = fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹) := by
    rw [LiCriterion.phi_eq]; funext z; rw [one_div]
  rw [hphi]
  have hcomp : AnalyticAt ℂ (fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹)) 0 := by
    have h := AnalyticAt.comp (g := DiffractionCore.zetaPoleCompanion)
      (f := fun z : ℂ => (1 - z)⁻¹) (x := 0)
      (by simpa using DiffractionCore.analyticAt_zetaPoleCompanion 1) hMana
    simpa [Function.comp_def] using h
  have hval : (fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹)) 0 ≠ 0 := by
    simp [DiffractionCore.zetaPoleCompanion_one]
  have hlogeq : logDeriv (fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹))
      = fun z => deriv (fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹)) z
          / (fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹)) z := by
    funext z; rw [logDeriv_apply]
  rw [hlogeq]; exact hcomp.deriv.div hcomp hval

/-- **The ζ-pole regularization, explicit.**  On the punctured neighbourhood of `0`, the analytic
    companion pullback equals the sum of the (individually singular-at-0) pole pullback and ζ pullback:
    `logDeriv(phi H) = logDeriv(phi (·−1)) + logDeriv(phi ζ)`. -/
theorem logDeriv_phi_zetaPoleCompanion_regularizes :
    logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun z => logDeriv (LiCriterion.phi (fun s : ℂ => s - 1)) z
          + logDeriv (LiCriterion.phi riemannZeta) z := by
  have hphi_eq : ∀ f : ℂ → ℂ, LiCriterion.phi f = fun z => f ((1 - z)⁻¹) := by
    intro f; rw [LiCriterion.phi_eq]; funext z; rw [one_div]
  have hMana : AnalyticAt ℂ (fun z : ℂ => (1 - z)⁻¹) 0 :=
    (analyticAt_const.sub analyticAt_id).inv (by norm_num)
  have hMcont : ContinuousAt (fun z : ℂ => (1 - z)⁻¹) 0 := hMana.continuousAt
  have hHev : ∀ᶠ z in 𝓝 (0 : ℂ), DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹) ≠ 0 := by
    have hc : ContinuousAt (fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹)) 0 := by
      have h := ContinuousAt.comp (g := DiffractionCore.zetaPoleCompanion)
        (f := fun z : ℂ => (1 - z)⁻¹) (x := 0)
        (by simpa using (DiffractionCore.analyticAt_zetaPoleCompanion 1).continuousAt) hMcont
      simpa [Function.comp_def] using h
    exact hc.eventually_ne (by simp [DiffractionCore.zetaPoleCompanion_one])
  have hz1ev : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 1 := continuousAt_id.eventually_ne (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hHev.filter_mono nhdsWithin_le_nhds,
    hz1ev.filter_mono nhdsWithin_le_nhds] with z hz0 hHz hz1'
  have hzne0 : z ≠ 0 := hz0
  have hMz1 : (1 - z)⁻¹ ≠ 1 := by rw [ne_eq, inv_eq_one, sub_eq_self]; exact hzne0
  have hζz : riemannZeta ((1 - z)⁻¹) ≠ 0 := by
    intro hc; apply hHz
    rw [DiffractionCore.zetaPoleCompanion_apply_of_ne hMz1, hc]; ring
  rw [hphi_eq DiffractionCore.zetaPoleCompanion, hphi_eq (fun s : ℂ => s - 1), hphi_eq riemannZeta,
    logDeriv_phi hz1' (DiffractionCore.differentiable_zetaPoleCompanion _),
    logDeriv_phi hz1' (show DifferentiableAt ℂ (fun s : ℂ => s - 1) ((1 - z)⁻¹) by fun_prop),
    logDeriv_phi hz1' (differentiableAt_riemannZeta hMz1),
    DiffractionCore.logDeriv_sub_const,
    DiffractionCore.logDeriv_zeta_eq_companion_sub_pole hMz1 hζz]
  ring

end RvMWeierstrass
