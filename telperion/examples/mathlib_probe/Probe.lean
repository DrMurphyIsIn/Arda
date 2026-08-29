/- Zeta-foundation seed: the Mertens nonnegative trigonometric polynomial, the certificate
   behind the classical zero-free region  zeta(s) != 0 for Re > 1 - c/log|t|. -/
import Mathlib
open scoped Real

/-- `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)^2 >= 0` (Mertens). Applied to
    Re[3 log zeta(σ) + 4 log zeta(σ+it) + log zeta(σ+2it)] this yields the classical
    zero-free region. A nonneg-trig-polynomial certificate; proves nothing about RH. -/
theorem mertens_three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h := Real.cos_two_mul θ
  nlinarith [h, sq_nonneg (Real.cos θ + 1)]
