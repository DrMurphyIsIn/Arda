/-
RvMCompanionBragg — Route P, Brick D2a: the companion right-edge Bragg integrand.

Brick D1 (`RvMCompanionPrime.logDeriv_zetaPoleCompanion_eq_vonMangoldt`) gives
`logDeriv zetaPoleCompanion s = − L(Λ) s + (s−1)⁻¹` for `Re s > 1`.  On the right edge `Re s = σ₁ > 1`
of the explicit-formula rectangle, the weighted integrand therefore reads

    g · logDeriv zetaPoleCompanion = g · (− L(Λ) + (·−1)⁻¹)      (the companion Bragg integrand),

the companion analogue of `DiffractionCore.right_edge_weighted_prime_integrand`.  This is the
integrand the finite explicit formula integrates along the prime edge; it is the edge-level step
toward the finite Bragg identity for the companion coefficient (D2b — see
ROUTEP_D2B_WEIGHT_RECONCILIATION_SPEC_2026-09-11.md, whose crux is reconciling `liWeight` with
`liPairedSummand`).  A direct corollary of D1; a re-coordinatization onto the prime side, NOT
progress toward RH (the von Mangoldt series converges only for `Re s > 1`).  conjecture1_proved = False.
-/
import Mathlib
import RvMCompanionPrime

open Complex

namespace RvMWeierstrass

/-- **Route P, Brick D2a — the companion right-edge Bragg integrand.**  For `1 < σ₁`, pointwise along
    the right edge `Re = σ₁`, `g·logDeriv zetaPoleCompanion = g·(−L(Λ) + (·−1)⁻¹)` — the companion
    analogue of `right_edge_weighted_prime_integrand`, exposing the log-prime Bragg spectrum
    (peaks at `k·log p`) plus the explicit pole on the edge the explicit formula integrates.
    A corollary of Brick D1.  conjecture1_proved = False. -/
theorem companion_right_edge_prime_integrand (sigma1 : ℝ) (hσ : 1 < sigma1) (g : ℂ → ℂ) (y : ℝ) :
    g ((sigma1 : ℂ) + y * I) * logDeriv DiffractionCore.zetaPoleCompanion ((sigma1 : ℂ) + y * I)
      = g ((sigma1 : ℂ) + y * I)
          * (- LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ((sigma1 : ℂ) + y * I)
             + ((sigma1 : ℂ) + y * I - 1)⁻¹) := by
  rw [logDeriv_zetaPoleCompanion_eq_vonMangoldt (by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero]
    exact hσ)]

end RvMWeierstrass
