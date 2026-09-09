/- TURING RUNG T2, brick 1: the Riemann–Siegel theta function, defined BRANCH-CUT-FREE as the
   integral of an explicit real integrand (TURING_METHOD_SCOPING §3, rung T2).

   Classically `θ(t) = Im logΓ(1/4 + it/2) − (t/2)·log π` with a continuously-tracked branch of
   `logΓ` — awkward to formalize.  Instead we DEFINE

     `θ(t) := ∫_0^t ( (1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π ) du`,

   where `ψ = Complex.digamma = logDeriv Γ` (Mathlib).  This agrees with the classical `θ`
   (both vanish at `0` and have the same derivative `θ'(u) = (1/2)·Re ψ(1/4 + iu/2) − (1/2)·log π`)
   and needs NO branch tracking: the integrand is a plain continuous real function of `u`.

   This brick: the ray `1/4 + (u/2)·i` avoids all Γ-poles (`Re = 1/4 > 0`), Γ is ANALYTIC there
   (differentiable on the open right half-plane ⟹ analytic), `ψ` is continuous on the ray
   (`deriv Γ / Γ`, with `Γ ≠ 0` by `Gamma_ne_zero_of_re_pos`), hence the integrand is continuous,
   `θ` is well-defined with `θ(0) = 0` and `θ' = integrand` (FTC for continuous integrands).

   Later bricks (T2 cont.): effective two-sided bounds `θ(t) = (t/2)log(t/2π) − t/2 − π/8 +
   O*(explicit/t)` via Binet-type digamma estimates; then T3 wires `θ` into the rectangle
   argument identity `N(T) = θ(T)/π + 1 + S(T)`.

   conjecture1_proved = False. -/
import Mathlib

open Complex

namespace ZeroFreeBridge

/-- The digamma ray for the Riemann–Siegel theta: `u ↦ 1/4 + (u/2)·i`. -/
noncomputable def thetaRay (u : ℝ) : ℂ := 1 / 4 + ((u / 2 : ℝ) : ℂ) * I

theorem thetaRay_re (u : ℝ) : (thetaRay u).re = 1 / 4 := by
  simp only [thetaRay, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

theorem thetaRay_continuous : Continuous thetaRay := by
  have h1 : Continuous fun u : ℝ => ((u / 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_id.div_const 2)
  exact continuous_const.add (h1.mul continuous_const)

/-- `Γ` is analytic at every ray point (the ray lies in the open right half-plane, where `Γ` is
    differentiable, hence analytic). -/
theorem gamma_analyticAt_thetaRay (u : ℝ) : AnalyticAt ℂ Gamma (thetaRay u) := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Gamma {s : ℂ | 0 < s.re} := by
    intro s hs
    refine (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    rw [hm] at hs
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  exact (hdiff.analyticOnNhd hopen) (thetaRay u)
    (by simp only [Set.mem_setOf_eq, thetaRay_re]; norm_num)

/-- `ψ = digamma` is continuous at every ray point (`deriv Γ / Γ`, `Γ ≠ 0` on `Re > 0`, and
    `deriv Γ` is continuous since `Γ` is analytic). -/
theorem digamma_continuousAt_thetaRay (u : ℝ) :
    ContinuousAt Complex.digamma (thetaRay u) := by
  have hana := gamma_analyticAt_thetaRay u
  have hne : Gamma (thetaRay u) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [thetaRay_re]; norm_num)
  have heq : Complex.digamma = fun s => deriv Gamma s / Gamma s := by
    funext s; rw [Complex.digamma_def, logDeriv_apply]
  rw [heq]
  exact (hana.deriv.continuousAt).div hana.continuousAt hne

/-- The θ integrand: `u ↦ (1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π`. -/
noncomputable def thetaIntegrand (u : ℝ) : ℝ :=
  (1 / 2) * (Complex.digamma (thetaRay u)).re - (1 / 2) * Real.log Real.pi

theorem thetaIntegrand_continuous : Continuous thetaIntegrand := by
  have hcomp : Continuous fun u : ℝ => (Complex.digamma (thetaRay u)).re := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (Complex.continuous_re.continuousAt).comp
      ((digamma_continuousAt_thetaRay u).comp thetaRay_continuous.continuousAt)
  exact (continuous_const.mul hcomp).sub continuous_const

/-- **The Riemann–Siegel theta function**, branch-cut-free:
    `θ(t) := ∫_0^t ((1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π) du`. -/
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, thetaIntegrand u

theorem riemannSiegelTheta_zero : riemannSiegelTheta 0 = 0 :=
  intervalIntegral.integral_same

theorem thetaIntegrand_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable thetaIntegrand MeasureTheory.volume a b :=
  thetaIntegrand_continuous.intervalIntegrable a b

/-- FTC: `θ'(t) = (1/2)·Re ψ(1/4 + i·t/2) − (1/2)·log π` (the integrand is continuous). -/
theorem riemannSiegelTheta_deriv (t : ℝ) :
    deriv riemannSiegelTheta t = thetaIntegrand t :=
  Continuous.deriv_integral thetaIntegrand thetaIntegrand_continuous 0 t

end ZeroFreeBridge
