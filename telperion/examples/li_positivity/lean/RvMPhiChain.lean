/-
RvMPhiChain — Phase 4c foundation: the log-derivative of the Möbius pullback `phi f`.

The upstream Li Taylor coefficients read off `logDeriv (phi f)` with `phi f z = f(1/(1−z))`.  Since
`phi f = f ∘ M` with `M(z) = 1/(1−z) = (1−z)⁻¹`, the log-derivative factors through the chain rule:

  * `logDeriv_phi` — `logDeriv (fun z => f((1−z)⁻¹)) z = logDeriv f ((1−z)⁻¹) · M'(z)`,
    for `z ≠ 1` and `f` differentiable at `(1−z)⁻¹`.

This separates the outer log-derivative `logDeriv f` (which the frontier-(a) split resolves into
`1/s + 1/(s−1) + logDeriv ζ + logDeriv Γℝ`) from the inner Möbius derivative — the two ingredients Faà
di Bruno recombines.  conjecture1_proved = False.
-/
import Mathlib
import RvMMobius

open Complex

namespace RvMWeierstrass

/-- **Log-derivative of the Möbius pullback.**  For `z ≠ 1` and `f` differentiable at `(1−z)⁻¹`,
    `logDeriv (fun w => f((1−w)⁻¹)) z = logDeriv f ((1−z)⁻¹) · deriv (fun w => (1−w)⁻¹) z`. -/
theorem logDeriv_phi {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 1)
    (hf : DifferentiableAt ℂ f ((1 - z)⁻¹)) :
    logDeriv (fun w : ℂ => f ((1 - w)⁻¹)) z
      = logDeriv f ((1 - z)⁻¹) * deriv (fun w : ℂ => (1 - w)⁻¹) z := by
  have hne : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hM : DifferentiableAt ℂ (fun w : ℂ => (1 - w)⁻¹) z :=
    (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).inv hne)
  have h := logDeriv_comp (f := f) (g := fun w : ℂ => (1 - w)⁻¹) hf hM
  simpa [Function.comp_def] using h

end RvMWeierstrass
