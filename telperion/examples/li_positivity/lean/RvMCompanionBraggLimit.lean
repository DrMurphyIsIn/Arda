/-
RvMCompanionBraggLimit — Route P D2b-3 (prime/Bragg side): the CONDITIONAL reduction.

The zero-sum-side isolation (`taylorCoeff_companion_eq_liWeight_paired_tsum`, #479) is unconditional-
modulo-`hgenus`/`hhad`.  Its PRIME/Bragg-side dual — expressing the same companion coefficient through
the finite explicit formula's von-Mangoldt spectrum (`li_finite_explicit_formula` + D1/D2a) — requires
the `T→∞` exhaustion limit AND the archimedean main-term extraction from the boundary integrals.  That
limit + extraction is the NAMED, UNBUILT FRONTIER (`RvMLiStratum3` header: "the research core that
neither this development nor the upstream contains"); the zero density `dN(T) ~ (1/2π)log(T/2π)` becomes
load-bearing there.  It is NOT built here and NOT approached.

This file does the one honest thing available: it REDUCES the prime-side isolation to three explicit,
separable, non-circular analytic PRIMITIVES — carried as hypotheses — and proves the limit-passage is
correct.  It establishes NONE of the three limits (that is the frontier); it only shows that GIVEN them,
the companion coefficient is isolated on the Bragg side.

  * `taylorCoeff_companion_bragg_of_exhaustion_limits`:
      GIVEN a box exhaustion whose finite explicit formulae hold (`hformula`, = `li_finite_explicit_
      formula` along the exhaustion), whose zero-sums capture the coefficient (`hzero`, the Stratum-2
      exhaustion), and whose boundary and Bragg pieces converge (`hboundary`, `hbragg` — the archimedean
      main-term extraction lives in `boundaryLim`), THEN
        `taylorCoeff zetaPoleCompanion n
           = (boundaryLim − braggLim) / (2πi) − 1 − taylorCoeff Γℝ n`.
    Proof = `tendsto_nhds_unique` on `hformula` (real limit-passage) + the split (#463).

The hypotheses are limit primitives about FINITE quantities (`zeroSum`/`boundary`/`bragg : ℕ → ℂ`), NOT
the companion coefficient — the reduction is non-circular.  It is category-(b)→(c) boundary: the passage
is finite-checkable; the three limits are the quarantined research core.  conjecture1_proved = False.
-/
import Mathlib
import RvMLiCoeffId

open Complex Filter Topology

namespace RvMWeierstrass

/-- **Prime/Bragg-side isolation of the companion coefficient — CONDITIONAL reduction.**

    `zeroSum k`, `boundary k`, `bragg k` are the finite Li-weighted zero-sum, the boundary-integral
    part, and the von-Mangoldt (Bragg) part of `li_finite_explicit_formula` on the `k`-th box of an
    exhaustion (kept abstract as `ℕ → ℂ`).

    - `hformula` is `li_finite_explicit_formula` holding along the exhaustion (`2πi·zeroSum = boundary − bragg`);
    - `hzero` is the Stratum-2 exhaustion capturing the coefficient (`2πi·zeroSum → 2πi·taylorCoeff riemannXi n`);
    - `hboundary` / `hbragg` are the boundary / Bragg limits — the archimedean main-term extraction lives in `boundaryLim`.

    These three limits are the NAMED, UNBUILT FRONTIER (`RvMLiStratum3`); none is established here.  This
    theorem only performs the (rigorous, finite-checkable) limit-passage that isolates the companion GIVEN
    them.  conjecture1_proved = False. -/
theorem taylorCoeff_companion_bragg_of_exhaustion_limits
    (n : ℕ)
    (zeroSum boundary bragg : ℕ → ℂ) (boundaryLim braggLim : ℂ)
    (hformula : ∀ k, 2 * (Real.pi : ℂ) * I * zeroSum k = boundary k - bragg k)
    (hzero : Tendsto (fun k => 2 * (Real.pi : ℂ) * I * zeroSum k) atTop
        (𝓝 (2 * (Real.pi : ℂ) * I * LiCriterion.taylorCoeff LiCriterion.riemannXi n)))
    (hboundary : Tendsto boundary atTop (𝓝 boundaryLim))
    (hbragg : Tendsto bragg atTop (𝓝 braggLim)) :
    LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n
      = (boundaryLim - braggLim) / (2 * (Real.pi : ℂ) * I)
        - 1 - LiCriterion.taylorCoeff Complex.Gammaℝ n := by
  -- 2πi ≠ 0
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2πi : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero
  -- the finite formula's LHS and RHS have the SAME limit, read two ways
  have hrhs : Tendsto (fun k => 2 * (Real.pi : ℂ) * I * zeroSum k) atTop (𝓝 (boundaryLim - braggLim)) := by
    have hcongr : (fun k => 2 * (Real.pi : ℂ) * I * zeroSum k) = fun k => boundary k - bragg k := funext hformula
    rw [hcongr]; exact hboundary.sub hbragg
  -- limit uniqueness: 2πi·(coefficient) = boundaryLim − braggLim
  have hkey : 2 * (Real.pi : ℂ) * I * LiCriterion.taylorCoeff LiCriterion.riemannXi n
      = boundaryLim - braggLim := tendsto_nhds_unique hzero hrhs
  -- solve for the ξ coefficient
  have hcoeff : LiCriterion.taylorCoeff LiCriterion.riemannXi n
      = (boundaryLim - braggLim) / (2 * (Real.pi : ℂ) * I) := by
    rw [eq_div_iff h2πi]; linear_combination hkey
  -- subtract the elementary 1 and the archimedean datum via the split (#463)
  have hsplit := taylorCoeff_riemannXi_split_explicit n
  rw [hcoeff] at hsplit
  linear_combination -hsplit

end RvMWeierstrass
