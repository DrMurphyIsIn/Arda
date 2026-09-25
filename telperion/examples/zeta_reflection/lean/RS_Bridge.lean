/-  RS_Bridge.lean -- lane RS, brick B3 part 4: the Riemann-Siegel formula for Hardy's Z with the
    C0 term and an explicit remainder, HYPOTHESIS-FREE on the phase (imports `RS_B3Bound`, the
    island's `RSTheta` Stirling bracket and `ZeroSignDecomp_t14` polar form; all read-only).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_Z_C0` : for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= 2 t^(-3/4),
      N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p).

    The phase phi = Lam - (t/2) log pi is the island's branch-correct Riemann-Siegel theta
    (`ThetaConverge.convergence_obligation` + `ZeroSignDecomp.gamma_r_polar_t`), and the bound
    |phi - thetaMain t| <= 1/t is `RSDesignTheta.theta_sub_thetaMain`.  The quotient on the left is
    Hardy's Z(t) (Re Lambda(1/2+it) = M Z(t), M = |Gammaℝ(1/2+it)| > 0): its sign is the sign of the
    island's `gLine t`, so a sign certificate for gLine at height t >= 10000 now needs only the
    finite main sum, one Psi value and the margin 2 t^(-3/4).

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/
import RS_B3Bound
import RSTheta
import ZeroSignDecomp_t14

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

theorem rsThetaMain_eq_thetaMain (t : ℝ) : rsThetaMain t = ZeroFreeBridge.thetaMain t := rfl

/-- **The Riemann-Siegel formula with the C0 term and an explicit remainder, on the critical line.**
    For `t >= 10000` with `0 < p = rsFrac t` and `cos(2 pi p) ≠ 0` there are `M > 0` and a phase `phi`
    (the Riemann-Siegel theta, delivered hypothesis-free by the island's `ThetaConverge` branch and
    `RSTheta` Stirling bracket) with `Gammaℝ(1/2+it) = M e^{i phi}`, `|phi - thetaMain t| <= 1/t`, and
        | Re completedRiemannZeta(1/2+it) / M
            - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
          <= 2 t^(-3/4).
    The left quotient is Hardy's `Z(t)` (`Re Lambda(1/2+it) = M Z(t)`, `M = |Gammaℝ(1/2+it)| > 0`), so
    its SIGN is the sign of `gLine t` (`ZeroSignDecomp.gLine_sign_decomp_t`). -/
theorem rs_Z_C0 {t : ℝ} (ht : 10000 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        2 * t ^ (-(3 / 4 : ℝ)) := by
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
  have hC0 := rs_remainder_C0 ht hp hcos hφb
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

end RSInt
