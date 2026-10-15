/-  RS_BridgeSharp.lean -- lane RS, brick B3 part 4 SHARPENED (RSC0 Phase 2): the Riemann-Siegel
    formula for Hardy's Z with the C0 term and the SHARPENED explicit remainders of `RS_B3Sharp`,
    phase discharged hypothesis-free exactly as in `RS_Bridge` / `RSSeam_Bridge` (imports
    `RS_B3Sharp`, `RS_Bridge`; all read-only, nothing existing is edited).

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_Z_C0'` : for t >= 4250, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= (3/5) t^(-3/4).
      `RSSeam.rs_Z_C0_seam'` : the same for t >= 509 with (21/25) t^(-3/4).
      Same statement shape as `RSInt.rs_Z_C0` (2 t^(-3/4), t >= 10000) and `RSSeam.rs_Z_C0_seam`
      ((13/5) t^(-3/4), t >= 509); those two statements are re-derived here from the sharpened
      remainders as `RSInt.rs_Z_C0_of_sharp` and `RSSeam.rs_Z_C0_seam_of_sharp`.

    `rs_Z_of_remainder` is the proof of `RSInt.rs_Z_C0` with the remainder constant abstracted:
    any bound C on the C0-corrected remainder, valid for every phase within 1/t of thetaMain, is a
    bound on the Z formula with the island's branch-correct theta.

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/
import RS_B3Sharp
import RS_Bridge

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-- **From a remainder bound to the Z formula.**  If every phase `phi` with
    `|phi - rsThetaMain t| <= 1/t` has C0-corrected remainder at most `C`, then the Riemann-Siegel
    formula for `Re Lambda(1/2+it)/M` holds with remainder at most `C`, for the island's theta. -/
theorem rs_Z_of_remainder {t C : ℝ} (ht0 : 0 < t)
    (hrem : ∀ φ : ℝ, |φ - rsThetaMain t| ≤ 1 / t →
      |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤ C) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤ C := by
  have hGne : Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    linarith
  obtain ⟨Λ, hΛtend, hbranch⟩ :=
    ThetaConverge.convergence_obligation (1 / 4) (t / 2) (by norm_num) hGne
  obtain ⟨M, hM, hpolar⟩ := ZeroSignDecomp.gamma_r_polar_t t ht0.ne' Λ hbranch
  have hθ := RSDesignTheta.theta_sub_thetaMain t ht0 Λ hΛtend
  set φ : ℝ := Λ - t / 2 * Real.log Real.pi with hφ
  have hφb : |φ - rsThetaMain t| ≤ 1 / t := by
    rw [rsThetaMain_eq_thetaMain]; exact hθ
  refine ⟨M, φ, hM, hpolar, hφb, ?_⟩
  have hN : ((rsNn t : ℕ) : ℝ) < (rsNn t : ℝ) + 1 / 2 := by linarith
  have hN' : (rsNn t : ℝ) + 1 / 2 < (rsNn t : ℝ) + 1 := by linarith
  have hre := completed_re_eq_rs_cos t (rsNn t) hN hN' hpolar
  have hrem' : -lineUp ((rsNn t : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))) =
      rsRem t := rfl
  rw [hrem'] at hre
  rw [hre]
  have hC0 := hrem φ hφb
  have e : 2 * M * ((∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.cos (φ - t * Real.log n)) + (cexp (I * φ) * rsRem t).re) / M -
      (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)) =
      2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t) := by
    field_simp
    ring
  rw [e]
  exact hC0

/-- **The Riemann-Siegel formula with the C0 term, sharpened remainder, t >= 4250.**  Same shape
    as `rs_Z_C0`; remainder `(3/5) t^(-3/4)` instead of `2 t^(-3/4)`, from t >= 4250 instead of
    t >= 10000. -/
theorem rs_Z_C0' {t : ℝ} (ht : 4250 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        3 / 5 * t ^ (-(3 / 4 : ℝ)) :=
  rs_Z_of_remainder (by linarith) fun _ hφ => rs_remainder_C0' ht hp hcos hφ

/-- `rs_Z_C0`'s statement (2 t^(-3/4), t >= 10000), re-derived from the sharpened remainder. -/
theorem rs_Z_C0_of_sharp {t : ℝ} (ht : 10000 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        2 * t ^ (-(3 / 4 : ℝ)) :=
  rs_Z_of_remainder (by linarith) fun _ hφ => rs_remainder_C0_of_sharp ht hp hcos hφ

end RSInt

namespace RSSeam

open RSInt

/-- **SEAM: the Riemann-Siegel formula with the C0 term, sharpened remainder, t >= 509.**  Same
    shape as `rs_Z_C0_seam`; remainder `(21/25) t^(-3/4)` instead of `(13/5) t^(-3/4)`. -/
theorem rs_Z_C0_seam' {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        21 / 25 * t ^ (-(3 / 4 : ℝ)) :=
  rs_Z_of_remainder (by linarith) fun _ hφ => rs_remainder_C0_seam' ht hp hcos hφ

/-- `rs_Z_C0_seam`'s statement ((13/5) t^(-3/4), t >= 509), re-derived from the sharpened seam. -/
theorem rs_Z_C0_seam_of_sharp {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        13 / 5 * t ^ (-(3 / 4 : ℝ)) :=
  rs_Z_of_remainder (by linarith) fun _ hφ => rs_remainder_C0_seam_of_sharp ht hp hcos hφ

end RSSeam
