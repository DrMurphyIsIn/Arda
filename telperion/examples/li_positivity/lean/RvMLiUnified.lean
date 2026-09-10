/-
RvMLiUnified — the RvM count and Li's criterion, unified about ONE `riemannXi`.

With the RvM count now ported onto the v4.34 island (`RvMDiffractionCore`), this
file closes the loop: it proves our development's `xiTele` is DEFINITIONALLY the
upstream `LiCriterion.riemannXi`, and restates the RvM counting formula for that
upstream object.  So on a single toolchain:

  * `xiTele_eq_riemannXi`      : the two developments are about ONE function.
  * `riemannXi_winding_eq_RvM` : N(T) = 1 + θ(T)/π + S(T)  — the RvM count, for
                                 `LiCriterion.riemannXi`.
  * upstream `li_criterion_rh_iff` : RH ⟺ ∀ n, 0 ≤ (taylorCoeff riemannXi n).re.

All three now name the SAME `riemannXi`.

HONEST SCOPE.  This is a genuine kernel-level UNIFICATION of the two formalizations
(same object, same toolchain, both importable here).  It is NOT a link between the
zero COUNT `N(T)` and the Li COEFFICIENTS `λ_n = taylorCoeff riemannXi n`: that is
the explicit-formula / Guinand–Weil mathematics (`λ_n = Σ_ρ [1−(1−1/ρ)^n]`), which
neither development contains.  `RiemannHypothesis` is neither proved nor approached.
conjecture1_proved = False.
-/
import RvMDiffractionCore
import LiPositivity
import Lc.LiCriterion.Fidelity

namespace RvMLiUnified

open Complex Real

/-- **The shared object.**  Our RvM development's `xiTele` is the upstream
    `LiCriterion.riemannXi` — both are `½·s·(s−1)·completedRiemannZeta₀ s + ½`,
    equal by `ring`.  So the RvM count and Li's criterion are about ONE function. -/
theorem xiTele_eq_riemannXi : DiffractionCore.xiTele = LiCriterion.riemannXi := by
  funext s
  unfold DiffractionCore.xiTele LiCriterion.riemannXi
  ring

/-- **The Riemann–von Mangoldt count, for the upstream `riemannXi`.**  Verbatim
    the ported `xiTele_winding_eq_RvM`, restated for `LiCriterion.riemannXi` via
    the shared-object equality — so the count literally names the function whose
    Li coefficients determine RH.  `conjecture1_proved = False`. -/
theorem riemannXi_winding_eq_RvM (T : ℝ) (hT : 0 < T) (N : ℤ)
    (hnzBot : ∀ x ∈ Set.Icc (-1:ℝ) 2, LiCriterion.riemannXi ((x : ℂ)) ≠ 0)
    (hnzTop : ∀ x ∈ Set.Icc (-1:ℝ) 2, LiCriterion.riemannXi ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hnzL : ∀ y ∈ Set.Icc (0:ℝ) T, LiCriterion.riemannXi (((-1:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hnzR : ∀ y ∈ Set.Icc (0:ℝ) T, LiCriterion.riemannXi (((2:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hζT : ∀ x ∈ Set.uIcc (2:ℝ) (1/2), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hwind : (∫ x in (-1:ℝ)..2, logDeriv LiCriterion.riemannXi (↑x + ((0:ℝ) : ℂ) * I))
        - (∫ x in (-1:ℝ)..2, logDeriv LiCriterion.riemannXi (↑x + ((T:ℝ) : ℂ) * I))
        + I • (∫ y in (0:ℝ)..T, logDeriv LiCriterion.riemannXi (((2:ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (0:ℝ)..T, logDeriv LiCriterion.riemannXi (((-1:ℝ) : ℂ) + ↑y * I))
      = 2 * ↑π * I * (N : ℂ)) :
    (N : ℝ) = 1 + ZeroFreeBridge.riemannSiegelTheta T / π + DiffractionCore.riemannS T := by
  have e := xiTele_eq_riemannXi
  exact DiffractionCore.xiTele_winding_eq_RvM T hT N
    (by rw [e]; exact hnzBot) (by rw [e]; exact hnzTop) (by rw [e]; exact hnzL)
    (by rw [e]; exact hnzR) hζT (by rw [e]; exact hwind)

/-- **The unification, stated.**  `LiCriterion.riemannXi` is simultaneously (i) the
    function whose box zero-count the RvM formula computes
    (`riemannXi_winding_eq_RvM`), and (ii) the function whose Li coefficients
    characterise RH (`LiCriterion.li_criterion_rh_iff`).  Recorded as the
    conjunction of the two upstream/ported facts about the one object. -/
theorem rvm_and_li_share_riemannXi :
    (RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re)
      ∧ DiffractionCore.xiTele = LiCriterion.riemannXi :=
  ⟨LiCriterion.li_criterion_rh_iff, xiTele_eq_riemannXi⟩

end RvMLiUnified
