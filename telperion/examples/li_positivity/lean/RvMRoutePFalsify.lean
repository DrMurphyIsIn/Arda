/-
RvMRoutePFalsify — Arc C (Route P diffraction), Brick D3 part 1: the falsifiability atom.

`rh_iff_companion_ge` (Route P) relocates RH onto a single explicit inequality per `n`:

  `RH ↔ ∀ n, -(1 + (taylorCoeff Γℝ n).re) ≤ (taylorCoeff zetaPoleCompanion n).re`,

the right side being the arithmetic companion coefficient, the left an explicit archimedean floor
(the polygamma-at-½ capstone).  Its contrapositive is the falsifiability face of the whole route:
a single `n` at which the companion coefficient drops **below** the explicit floor refutes RH
outright.

  * `companion_below_floor_refutes_rh` — one sub-floor companion value ⟹ ¬RH.

This is the certificate shape the `bragg_floor` emitter (Brick D3 part 2) targets: with the
companion expressed on `Re s > 1` as the von Mangoldt log-prime (Bragg) spectrum
(`logDeriv_zetaPoleCompanion_eq_vonMangoldt`), a *certified* truncated Bragg amplitude sum falling
below the archimedean floor would fire this atom.  It is never expected to fire — RH is expected to
hold — but it makes the ladder an experiment that could have falsified.

Honesty: this PROVES nothing about RH; it is the honest negative face of a relocation.  The uniform
`∀ n` direction IS RH and is untouched.  Kernel-clean `[propext, Classical.choice, Quot.sound]`.
conjecture1_proved = False.
-/
import Mathlib
import RvMRouteP

open Complex

namespace RvMWeierstrass

/-- **The Route P falsifiability atom.**  If the companion Taylor coefficient falls strictly below
the explicit archimedean floor `-(1 + (taylorCoeff Γℝ n).re)` at any single order `n`, then the
Riemann Hypothesis is false.  The contrapositive of `rh_iff_companion_ge`; the negative face of the
companion relocation.  conjecture1_proved = False. -/
theorem companion_below_floor_refutes_rh (n : ℕ)
    (h : (LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n).re
          < -(1 + (LiCriterion.taylorCoeff Complex.Gammaℝ n).re)) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact absurd ((rh_iff_companion_ge.mp hRH) n) (not_le.mpr h)

end RvMWeierstrass
