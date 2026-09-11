/-
RvMLiCoeffSplit — the coefficient-level connection to the upstream Li machinery.

Regrouping the frontier-(a) split via the analytic ζ-pole companion `H = (·−1)·ζ` turns
`logDeriv ξ = 1/s + 1/(s−1) + logDeriv ζ + logDeriv Γℝ` into `logDeriv ξ = 1/s + logDeriv H +
logDeriv Γℝ` — three summands each analytic at `s = 1 = M 0`, so the Möbius pullbacks are analytic at
`z = 0` and `taylorCoeff` (an `n`-th derivative at `0`) splits additively:

  * `taylorCoeff_riemannXi_split` —
      `taylorCoeff riemannXi n = taylorCoeff id n + taylorCoeff zetaPoleCompanion n + taylorCoeff Γℝ n`.

The last summand is the archimedean coefficient reduced to exact polygamma data
(`taylorCoeff_Gammaℝ_leibniz`).  conjecture1_proved = False.
-/
import Mathlib
import RvMLiConnection

open Complex Filter Topology

namespace RvMWeierstrass

set_option maxHeartbeats 1600000 in
/-- **The coefficient-level split of the Li coefficient.** -/
theorem taylorCoeff_riemannXi_split (n : ℕ) :
    LiCriterion.taylorCoeff LiCriterion.riemannXi n
      = LiCriterion.taylorCoeff (fun s : ℂ => s) n
        + LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n
        + LiCriterion.taylorCoeff Complex.Gammaℝ n := by
  have hMana : AnalyticAt ℂ (fun z : ℂ => (1 - z)⁻¹) 0 :=
    (analyticAt_const.sub analyticAt_id).inv (by norm_num)
  have hphi_eq : ∀ f : ℂ → ℂ, LiCriterion.phi f = fun z => f ((1 - z)⁻¹) := by
    intro f; rw [LiCriterion.phi_eq]; funext z; rw [one_div]
  -- `logDeriv (phi f)` is analytic at 0 when `f` is analytic and non-zero at 1
  have hnice : ∀ f : ℂ → ℂ, AnalyticAt ℂ f 1 → f 1 ≠ 0 →
      AnalyticAt ℂ (logDeriv (LiCriterion.phi f)) 0 := by
    intro f hf hf1
    rw [hphi_eq f]
    have hcomp : AnalyticAt ℂ (fun z => f ((1 - z)⁻¹)) 0 := by
      have h := AnalyticAt.comp (g := f) (f := fun z : ℂ => (1 - z)⁻¹) (x := 0)
        (by simpa using hf) hMana
      simpa [Function.comp_def] using h
    have hval : (fun z => f ((1 - z)⁻¹)) 0 ≠ 0 := by simpa using hf1
    have hlogeq : logDeriv (fun z => f ((1 - z)⁻¹))
        = fun z => deriv (fun z => f ((1 - z)⁻¹)) z / (fun z => f ((1 - z)⁻¹)) z := by
      funext z; rw [logDeriv_apply]
    rw [hlogeq]; exact hcomp.deriv.div hcomp hval
  -- base functions analytic and non-zero at 1
  have hxi_ana : AnalyticAt ℂ LiCriterion.riemannXi 1 := by
    rw [← RvMLiUnified.xiTele_eq_riemannXi]; exact DiffractionCore.analyticAt_xiTele 1
  have hxi1 : LiCriterion.riemannXi 1 ≠ 0 := by
    rw [← RvMLiUnified.xiTele_eq_riemannXi,
      show DiffractionCore.xiTele 1 = 1 / 2 by unfold DiffractionCore.xiTele; ring]; norm_num
  have hH_ana : AnalyticAt ℂ DiffractionCore.zetaPoleCompanion 1 :=
    DiffractionCore.analyticAt_zetaPoleCompanion 1
  have hH1 : DiffractionCore.zetaPoleCompanion 1 ≠ 0 := by
    rw [DiffractionCore.zetaPoleCompanion_one]; norm_num
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG_ana : AnalyticAt ℂ Complex.Gammaℝ 1 := by
    have hne_m : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
      intro z hz m h
      rw [div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)] at h
      have hz2 : z = -(2 * (m : ℂ)) := by linear_combination h
      have hpos : (0 : ℝ) < z.re := hz
      rw [hz2] at hpos
      simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.natCast_re, Complex.natCast_im] at hpos
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hGRdiff : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} := by
      rw [show Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) from by
        funext s; rw [Complex.Gammaℝ_def]]
      intro z hz
      refine (DifferentiableAt.mul ?_ ?_).differentiableWithinAt
      · exact (differentiableAt_id.neg.div_const 2).const_cpow
          (Or.inl (by exact_mod_cast Real.pi_ne_zero))
      · exact (Complex.differentiableAt_Gamma _ (hne_m z hz)).comp z (differentiableAt_id.div_const 2)
    exact (hGRdiff.analyticOnNhd hUopen) 1 (by show (0 : ℝ) < (1 : ℂ).re; simp)
  have hG1 : Complex.Gammaℝ 1 ≠ 0 := by rw [Complex.Gammaℝ_one]; norm_num
  have hMcont : ContinuousAt (fun z : ℂ => (1 - z)⁻¹) 0 := hMana.continuousAt
  -- neighbourhood nonvanishing
  have hGev : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.Gammaℝ ((1 - z)⁻¹) ≠ 0 := by
    have hc : ContinuousAt (fun z => Complex.Gammaℝ ((1 - z)⁻¹)) 0 := by
      have h := ContinuousAt.comp (g := Complex.Gammaℝ) (f := fun z : ℂ => (1 - z)⁻¹) (x := 0)
        (by simpa using hG_ana.continuousAt) hMcont
      simpa [Function.comp_def] using h
    exact hc.eventually_ne (by simpa using hG1)
  have hHev : ∀ᶠ z in 𝓝 (0 : ℂ), DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹) ≠ 0 := by
    have hc : ContinuousAt (fun z => DiffractionCore.zetaPoleCompanion ((1 - z)⁻¹)) 0 := by
      have h := ContinuousAt.comp (g := DiffractionCore.zetaPoleCompanion)
        (f := fun z : ℂ => (1 - z)⁻¹) (x := 0) (by simpa using hH_ana.continuousAt) hMcont
      simpa [Function.comp_def] using h
    exact hc.eventually_ne (by simpa using hH1)
  have hz1ev : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 1 := continuousAt_id.eventually_ne (by norm_num)
  -- punctured split
  have hpunc : logDeriv (LiCriterion.phi LiCriterion.riemannXi)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun z => logDeriv (LiCriterion.phi (fun s : ℂ => s)) z
          + logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion) z
          + logDeriv (LiCriterion.phi Complex.Gammaℝ) z := by
    filter_upwards [self_mem_nhdsWithin, hGev.filter_mono nhdsWithin_le_nhds,
      hHev.filter_mono nhdsWithin_le_nhds, hz1ev.filter_mono nhdsWithin_le_nhds]
      with z hz0 hGz hHz hz1'
    have hzne0 : z ≠ 0 := hz0
    have hMz1 : (1 - z)⁻¹ ≠ 1 := by rw [ne_eq, inv_eq_one, sub_eq_self]; exact hzne0
    have hMz0 : (1 - z)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr fun h => hz1' h.symm)
    have hζz : riemannZeta ((1 - z)⁻¹) ≠ 0 := by
      intro hc
      apply hHz
      rw [DiffractionCore.zetaPoleCompanion_apply_of_ne hMz1, hc]; ring
    have hidM : logDeriv (LiCriterion.phi (fun s : ℂ => s)) z
        = ((1 - z)⁻¹)⁻¹ * deriv (fun w : ℂ => (1 - w)⁻¹) z := by
      rw [hphi_eq, logDeriv_phi (f := fun s : ℂ => s) hz1' differentiableAt_id, logDeriv_id', one_div]
    have hHM : logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion) z
        = (logDeriv riemannZeta ((1 - z)⁻¹) + ((1 - z)⁻¹ - 1)⁻¹)
            * deriv (fun w : ℂ => (1 - w)⁻¹) z := by
      rw [hphi_eq, logDeriv_phi hz1' (DiffractionCore.differentiable_zetaPoleCompanion _),
        DiffractionCore.logDeriv_zeta_eq_companion_sub_pole hMz1 hζz]; ring
    rw [logDeriv_phi_riemannXi_split hz1' hMz0 hMz1 hζz hGz, hidM, hHM]; ring
  -- value at 0 and full-neighbourhood equality
  have hpt : logDeriv (LiCriterion.phi LiCriterion.riemannXi) 0
      = logDeriv (LiCriterion.phi (fun s : ℂ => s)) 0
        + logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion) 0
        + logDeriv (LiCriterion.phi Complex.Gammaℝ) 0 :=
    tendsto_nhds_unique
      ((hnice _ hxi_ana hxi1).continuousAt.continuousWithinAt.tendsto.congr' hpunc)
      (((hnice _ analyticAt_id (by norm_num)).continuousAt.add
        (hnice _ hH_ana hH1).continuousAt).add
        (hnice _ hG_ana hG1).continuousAt).continuousWithinAt.tendsto
  have hfull := eventuallyEq_nhds_of_eventuallyEq_nhdsNE hpunc hpt
  -- distribute deriv^[n]
  have hcd_id : ContDiffAt ℂ n (logDeriv (LiCriterion.phi (fun s : ℂ => s))) 0 :=
    (hnice _ analyticAt_id (by norm_num)).contDiffAt
  have hcd_H : ContDiffAt ℂ n (logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion)) 0 :=
    (hnice _ hH_ana hH1).contDiffAt
  have hcd_G : ContDiffAt ℂ n (logDeriv (LiCriterion.phi Complex.Gammaℝ)) 0 :=
    (hnice _ hG_ana hG1).contDiffAt
  have hkey : iteratedDeriv n (logDeriv (LiCriterion.phi LiCriterion.riemannXi)) 0
      = iteratedDeriv n (logDeriv (LiCriterion.phi (fun s : ℂ => s))) 0
        + iteratedDeriv n (logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion)) 0
        + iteratedDeriv n (logDeriv (LiCriterion.phi Complex.Gammaℝ)) 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq n hfull,
      show (fun z => logDeriv (LiCriterion.phi (fun s : ℂ => s)) z
          + logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion) z
          + logDeriv (LiCriterion.phi Complex.Gammaℝ) z)
        = (fun z => logDeriv (LiCriterion.phi (fun s : ℂ => s)) z
            + logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion) z)
          + logDeriv (LiCriterion.phi Complex.Gammaℝ) from rfl,
      iteratedDeriv_add (hcd_id.add hcd_H) hcd_G,
      show (fun z => logDeriv (LiCriterion.phi (fun s : ℂ => s)) z
            + logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion) z)
          = logDeriv (LiCriterion.phi (fun s : ℂ => s))
            + logDeriv (LiCriterion.phi DiffractionCore.zetaPoleCompanion) from rfl,
      iteratedDeriv_add hcd_id hcd_H]
  simp only [LiCriterion.taylorCoeff, ← iteratedDeriv_eq_iterate, LiCriterion.logDeriv_eq_rootLogDeriv,
    hkey]
  ring

end RvMWeierstrass
