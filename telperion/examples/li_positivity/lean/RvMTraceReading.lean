/-
RvMTraceReading — MIRRORMERE Route D, layer D1: the TRACE READING of the Bragg bridge.

`RvMBraggBridge.rect_explicit_formula_bragg` (W3b) is the finite-height explicit formula in
diffraction form,

    2πi · Σ_ρ d(ρ)  =  (bottom edge) − (top edge) − i·Σ'_n braggTerm(σ₁,T0,T1,n) − i·(left edge),

with the zero side the box divisor count of ζ over its ACTUAL divisor.  Route D reads the same
identity as a finite TRACE identity: the divisor count (the "trace" of the counting weight over
the box spectrum) isolated on the left, the diffraction data (edge remainders + Bragg comb) on the
right, divided through by 2πi.  This file is that reading — an algebraic rearrangement of the
bridge (divide by `2πi ≠ 0`), same hypotheses, nothing new about the zeros.

Mirrors the registry node `MM_rect_trace_reading` (telperion/missions/mirrormere) VERBATIM; the
vocabulary (`braggTerm`, `RHInBoxAnalytic.zeroFinset`, `MeromorphicOn.divisor`) is the island's.
No RH progress is claimed; conjecture1_proved = False.
-/
import Mathlib
import RvMBraggBridge

open Complex MeasureTheory Real DiffractionCore
open scoped Topology

namespace DiffractionCore

/-- **The trace reading of the Bragg bridge.**  `rect_explicit_formula_bragg` divided through by
    `2πi`: the box divisor count of ζ (the finite trace) equals `1/(2πi)` times the diffraction
    data — bottom edge minus top edge, minus `i` times the Bragg comb, minus `i` times the left
    edge.  Same hypotheses as the bridge; a dictionary-grade rearrangement. -/
theorem rect_trace_reading
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1) (hσ1 : 1 < sigma1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ)
      = (1 / (2 * ↑π * I)) *
        ((∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
          - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
          - I • (∑' n : ℕ, braggTerm sigma1 T0 T1 n)
          - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))) := by
  -- The bridge, at these hypotheses.
  have hEF := rect_explicit_formula_bragg sigma0 sigma1 T0 T1 hsig hT hσ1 c R hbox_ball hs1
    hnzb hnzt hnzl hins
  -- `2πi ≠ 0`.
  have h2πi : (2 * (π : ℂ) * I) ≠ 0 := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero
  -- Divide the bridge through by `2πi`.
  rw [← hEF, one_div, inv_mul_cancel_left₀ h2πi]

end DiffractionCore
