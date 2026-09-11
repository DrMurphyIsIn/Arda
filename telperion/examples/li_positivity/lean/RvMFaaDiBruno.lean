/-
RvMFaaDiBruno — Phase 4c core: Faà di Bruno on the archimedean composition.

The archimedean part of the Li Taylor data is built from `(logDeriv Γℝ) ∘ M` with `M(z) = (1−z)⁻¹`.
Faà di Bruno (`iteratedDeriv_scomp_eq_sum_orderedFinpartition`), with the inner Möbius derivatives
`iteratedDeriv k M 0 = k!` and the outer derivatives `iteratedDeriv ℓ (logDeriv Γℝ) 1` (Phase 4b),
gives the composition's `n`-th derivative at `0` as an explicit finite `OrderedFinpartition` sum:

  * `iteratedDeriv_logDerivGammaℝ_comp_mobius` —
      `iteratedDeriv i ((logDeriv Γℝ) ∘ M) 0
         = ∑_{c : OrderedFinpartition i} (∏_j (c.partSize j)!) • iteratedDeriv c.length (logDeriv Γℝ) 1`.

conjecture1_proved = False.
-/
import Mathlib
import RvMMobius

open Complex

namespace RvMWeierstrass

/-- **Faà di Bruno on the archimedean composition.**  `iteratedDeriv i ((logDeriv Γℝ)∘(1−·)⁻¹) 0`
    is the finite `OrderedFinpartition` sum of `(∏ (partSize)!) • iteratedDeriv (length) (logDeriv Γℝ) 1`. -/
theorem iteratedDeriv_logDerivGammaℝ_comp_mobius (i : ℕ) :
    iteratedDeriv i (fun z : ℂ => logDeriv Complex.Gammaℝ ((1 - z)⁻¹)) 0
      = ∑ c : OrderedFinpartition i,
          (∏ j, ((c.partSize j).factorial : ℂ)) • iteratedDeriv c.length (logDeriv Complex.Gammaℝ) 1 := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hUdef
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h1U : (1 : ℂ) ∈ U := by show (0 : ℝ) < (1 : ℂ).re; simp
  -- s/2 stays off the non-positive integers on the right half-plane
  have hne_m : ∀ z ∈ U, ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro z hz m h
    rw [div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)] at h
    have hz2 : z = -(2 * (m : ℂ)) := by linear_combination h
    have hpos : (0 : ℝ) < z.re := hz
    rw [hz2] at hpos
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.natCast_re, Complex.natCast_im] at hpos
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  -- Γℝ is analytic and non-zero on U, so its log-derivative is analytic there
  have hGReq : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hGRdiff : DifferentiableOn ℂ Complex.Gammaℝ U := by
    rw [hGReq]
    intro z hz
    refine (DifferentiableAt.mul ?_ ?_).differentiableWithinAt
    · exact (differentiableAt_id.neg.div_const 2).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (Complex.differentiableAt_Gamma _ (hne_m z hz)).comp z (differentiableAt_id.div_const 2)
  have hGRana : AnalyticOnNhd ℂ Complex.Gammaℝ U := hGRdiff.analyticOnNhd hopen
  have hGRne : ∀ z ∈ U, Complex.Gammaℝ z ≠ 0 := fun z hz => Complex.Gammaℝ_ne_zero_of_re_pos hz
  have hlogeq : logDeriv Complex.Gammaℝ = fun z => deriv Complex.Gammaℝ z / Complex.Gammaℝ z := by
    funext z; rw [logDeriv_apply]
  have hlogana : AnalyticOnNhd ℂ (logDeriv Complex.Gammaℝ) U := by
    rw [hlogeq]; exact (hGRana.deriv).div hGRana hGRne
  have hg : ContDiffAt ℂ i (logDeriv Complex.Gammaℝ) 1 := (hlogana 1 h1U).contDiffAt
  -- inner Möbius map is smooth at 0, with M 0 = 1
  have hM : ContDiffAt ℂ i (fun w : ℂ => (1 - w)⁻¹) 0 :=
    (contDiffAt_const.sub contDiffAt_id).inv (by norm_num)
  -- Faà di Bruno, then substitute the Möbius derivatives
  have hcomp := iteratedDeriv_scomp_eq_sum_orderedFinpartition (𝕜 := ℂ)
    (g := logDeriv Complex.Gammaℝ) (f := fun w : ℂ => (1 - w)⁻¹) (x := 0) (n := i) (i := i)
    (by simp only [sub_zero, inv_one]; exact hg) hM le_rfl
  rw [show (fun z : ℂ => logDeriv Complex.Gammaℝ ((1 - z)⁻¹))
      = (logDeriv Complex.Gammaℝ) ∘ (fun w : ℂ => (1 - w)⁻¹) from rfl, hcomp]
  simp only [sub_zero, inv_one]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  exact Finset.prod_congr rfl (fun j _ => iteratedDeriv_mobius_zero _)

end RvMWeierstrass
