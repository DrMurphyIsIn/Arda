/-
RvMArchimedeanCoeff — Phase 4c capstone: the archimedean Li coefficient as a Leibniz sum.

The archimedean part of the Li Taylor data is `LiCriterion.taylorCoeff Γℝ n` (since `logDeriv(phi f)`
is additive in `logDeriv f` and `phi Γℝ = Γℝ∘M`).  Assembling all Phase-4 pieces — `logDeriv_phi`
(the composition factors as `logDeriv Γℝ(M z)·M'(z)`), the Leibniz product rule, the Faà di Bruno
composition formula, and the Möbius derivatives — gives it as an explicit finite combination:

  * `taylorCoeff_Gammaℝ_leibniz` —
      `taylorCoeff Γℝ n = (∑_{k≤n} C(n,k)·iteratedDeriv k (logDeriv Γℝ∘M) 0 · (n−k+1)!) / n!`,
    whose composition-derivatives are the Phase-4c Faà di Bruno sums of Phase-4b polygamma values.

conjecture1_proved = False.
-/
import Mathlib
import RvMLeibniz
import RvMMobius
import RvMPhiChain
import Lc.LiCriterion.Basic

open Complex

namespace RvMWeierstrass

set_option maxHeartbeats 1000000 in
/-- **The archimedean Li coefficient, as a Leibniz sum.** -/
theorem taylorCoeff_Gammaℝ_leibniz (n : ℕ) :
    LiCriterion.taylorCoeff Complex.Gammaℝ n
      = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
          (iteratedDeriv k (fun z => logDeriv Complex.Gammaℝ ((1 - z)⁻¹)) 0
            * (((n - k + 1).factorial : ℕ) : ℂ))) / ((n.factorial : ℕ) : ℂ) := by
  -- open right half-plane and pole-free ball
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set W : Set ℂ := Metric.ball (0 : ℂ) (1 / 2) with hWdef
  have hWopen : IsOpen W := Metric.isOpen_ball
  have h0W : (0 : ℂ) ∈ W := by rw [hWdef, Metric.mem_ball, dist_self]; norm_num
  have hWre : ∀ z ∈ W, z.re < 1 / 2 := by
    intro z hz
    rw [hWdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    exact lt_of_le_of_lt ((le_abs_self _).trans (abs_re_le_norm z)) hz
  have hWne : ∀ z ∈ W, (1 : ℂ) - z ≠ 0 := by
    intro z hz hc
    have hz1 : z.re = 1 := by have h := sub_eq_zero.mp hc; rw [← h]; simp
    have := hWre z hz; rw [hz1] at this; norm_num at this
  have hMre : ∀ z ∈ W, (0 : ℝ) < ((1 - z)⁻¹).re := by
    intro z hz
    rw [Complex.inv_re]
    apply div_pos
    · rw [Complex.sub_re, Complex.one_re]; linarith [hWre z hz]
    · exact Complex.normSq_pos.mpr (hWne z hz)
  have hMmaps : Set.MapsTo (fun z => (1 - z)⁻¹) W U := fun z hz => hMre z hz
  -- Γℝ analytic and non-zero on U, so `logDeriv Γℝ` is analytic there
  have hne_m : ∀ z ∈ U, ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro z hz m h
    rw [div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)] at h
    have hz2 : z = -(2 * (m : ℂ)) := by linear_combination h
    have hpos : (0 : ℝ) < z.re := hz
    rw [hz2] at hpos
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.natCast_re, Complex.natCast_im] at hpos
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hGReq : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hGRdiff : DifferentiableOn ℂ Complex.Gammaℝ U := by
    rw [hGReq]
    intro z hz
    refine (DifferentiableAt.mul ?_ ?_).differentiableWithinAt
    · exact (differentiableAt_id.neg.div_const 2).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (Complex.differentiableAt_Gamma _ (hne_m z hz)).comp z (differentiableAt_id.div_const 2)
  have hGRana : AnalyticOnNhd ℂ Complex.Gammaℝ U := hGRdiff.analyticOnNhd hUopen
  have hGRne : ∀ z ∈ U, Complex.Gammaℝ z ≠ 0 := fun z hz => Complex.Gammaℝ_ne_zero_of_re_pos hz
  have hlogeq : logDeriv Complex.Gammaℝ = fun z => deriv Complex.Gammaℝ z / Complex.Gammaℝ z := by
    funext z; rw [logDeriv_apply]
  have hlogΓana : AnalyticOnNhd ℂ (logDeriv Complex.Gammaℝ) U := by
    rw [hlogeq]; exact (hGRana.deriv).div hGRana hGRne
  -- the inner map is analytic on W
  have hMana : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z)⁻¹) W := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hWopen
    exact (((differentiableAt_const 1).sub differentiableAt_id).inv (hWne z hz)).differentiableWithinAt
  -- the two factors of the archimedean log-derivative are smooth on W
  have hPcd : ContDiffOn ℂ ⊤ (fun z => logDeriv Complex.Gammaℝ ((1 - z)⁻¹)) W :=
    (hlogΓana.contDiffOn hUopen.uniqueDiffOn).comp (hMana.contDiffOn hWopen.uniqueDiffOn) hMmaps
  have hQcd : ContDiffOn ℂ ⊤ (deriv (fun z : ℂ => (1 - z)⁻¹)) W :=
    hMana.deriv.contDiffOn hWopen.uniqueDiffOn
  -- `logDeriv (phi Γℝ) = P·Q` on W (chain rule for the Möbius pullback)
  have hEq : logDeriv (fun w : ℂ => Complex.Gammaℝ ((1 - w)⁻¹))
      =ᶠ[nhds 0] fun z => logDeriv Complex.Gammaℝ ((1 - z)⁻¹)
          * deriv (fun w : ℂ => (1 - w)⁻¹) z := by
    filter_upwards [hWopen.mem_nhds h0W] with z hz
    have hz1 : z ≠ 1 := fun h => hWne z hz (by rw [h]; ring)
    exact logDeriv_phi hz1 (hGRdiff.differentiableAt (hUopen.mem_nhds (hMre z hz)))
  -- unfold `taylorCoeff` and apply Leibniz
  rw [LiCriterion.taylorCoeff, ← iteratedDeriv_eq_iterate, LiCriterion.logDeriv_eq_rootLogDeriv,
    show LiCriterion.phi Complex.Gammaℝ = fun w : ℂ => Complex.Gammaℝ ((1 - w)⁻¹) by
      funext w; rw [LiCriterion.phi, one_div],
    Filter.EventuallyEq.iteratedDeriv_eq n hEq,
    iteratedDeriv_mul_of_isOpen hWopen hPcd hQcd h0W]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 2
  rw [← iteratedDeriv_succ', iteratedDeriv_mobius_zero]

end RvMWeierstrass
