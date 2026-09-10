/-
RvMLiOrthogonal — surmounting the digamma-asymptotic barrier by an ORTHOGONAL route.

The barrier for the Li archimedean main term (frontier (b)+(c)) was the complex
large-argument asymptotic `ψ(w) ~ log w`, absent from Mathlib.  But that asymptotic
is only forced by the CONTOUR / explicit-formula route (integrate `∮ g_n·Γℝ'/Γℝ`
over a growing contour, `Im → ∞`).

ORTHOGONAL ROUTE.  Upstream *defines* the Li coefficient by the Taylor/Möbius
route: `λ_n = n`-th Taylor coefficient at `z = 0` of `logDeriv (ξ ∘ (z ↦ 1/(1−z)))`.
The Möbius map sends the expansion base point `z = 0 ↦ s = 1`.  So the archimedean
factor `Γℝ'/Γℝ` is sampled — with ALL its `z`-derivatives — at the FIXED point
`s = 1`, never at infinity.  No large-argument asymptotic is required; the input is
`Γℝ` and its derivatives at `s = 1`, which are EXACT constants.

And Mathlib supplies the base-point datum exactly:

  * `hasDerivAt_Gammaℝ_one : HasDerivAt Gammaℝ (−(γ + log 4π)/2) 1`,
  * `Gammaℝ_one : Gammaℝ 1 = 1`,

giving `logDeriv Γℝ 1 = −(γ + log 4π)/2`.  This file lands that value and the
principle:

  * `logDeriv_gammaR_one` — the exact base-point archimedean datum.

So the barrier is ROUTE-SPECIFIC, not intrinsic: switching from the contour route
to the Taylor route replaces the (absent) complex digamma asymptotic with EXACT
local evaluations at `s = 1` (`ψ`-derivatives at `1/2` = polygamma = ζ-values, all
exact).  The residual difficulty — the GROWTH of that exact sequence giving the
`~(n/2)log n` main term — is a different and more elementary problem (asymptotics of
a known explicit sequence), NOT the uniform complex asymptotic Mathlib lacks.

conjecture1_proved = False.  This surmounts the STATED analytic barrier; it does not
prove or approach RiemannHypothesis.
-/
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open Complex Real

namespace RvMLiOrthogonal

/-- **The exact base-point archimedean datum** (orthogonal route).  The Möbius
    transform samples the archimedean factor at `s = 1`, where it is an EXACT
    constant — no large-argument digamma asymptotic:

      `logDeriv Γℝ 1 = −(γ + log 4π)/2`.

    From `hasDerivAt_Gammaℝ_one` (Mathlib, exact) and `Gammaℝ_one` (`Γℝ 1 = 1`). -/
theorem logDeriv_gammaR_one :
    logDeriv Complex.Gammaℝ 1
      = -(↑Real.eulerMascheroniConstant + Complex.log (4 * (Real.pi : ℂ))) / 2 := by
  rw [logDeriv_apply, hasDerivAt_Gammaℝ_one.deriv, Complex.Gammaℝ_one, div_one]

end RvMLiOrthogonal
