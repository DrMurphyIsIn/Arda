/-  RSSeam_Bridge.lean -- lane SEAM: the Riemann-Siegel formula for Hardy's Z with the C0 term and an
    explicit remainder from t >= 509, phase discharged HYPOTHESIS-FREE exactly as in `RS_Bridge`
    (imports `RSSeam_B3Bound`, `RS_Bridge`, the island's `RSTheta` and `ZeroSignDecomp_t14`;
    all read-only).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_Z_C0_seam` : for t >= 509, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= (13/5) t^(-3/4),
      N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p).

    This is `RSInt.rs_Z_C0` with the range lowered from t >= 10000 to t >= 509 (constant 2 -> 13/5),
    so the Riemann-Siegel range now overlaps the Euler-Maclaurin kernel ladder (which reaches 1000 on
    this branch and 8000 via `AND.ladder_h8000_kernel`).

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/
import RSSeam_B3Bound
import RS_Bridge

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSSeam

open RSInt

/-- **SEAM: the Riemann-Siegel formula with the C0 term and an explicit remainder, t >= 509.**
    For `t >= 509` with `0 < p = rsFrac t` and `cos(2 pi p) ≠ 0` there are `M > 0` and a phase `phi`
    (the Riemann-Siegel theta, hypothesis-free from the island's `ThetaConverge` branch and `RSTheta`
    Stirling bracket) with `Gammaℝ(1/2+it) = M e^{i phi}`, `|phi - thetaMain t| <= 1/t`, and
        | Re completedRiemannZeta(1/2+it) / M
            - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
          <= (13/5) t^(-3/4). -/
theorem rs_Z_C0_seam {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        13 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
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
  have hrem : -lineUp ((rsNn t : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))) =
      rsRem t := rfl
  rw [hrem] at hre
  rw [hre]
  have hC0 := rs_remainder_C0_seam ht hp hcos hφb
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


end RSSeam
