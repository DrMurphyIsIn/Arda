/-
RvMRouteP — localizing the Riemann Hypothesis onto the companion Taylor coefficient.

Route P (the direct positivity attack).  `li_criterion_rh_iff` (kernel-clean) says
`RH ↔ ∀ n, 0 ≤ (taylorCoeff riemannXi n).re`.  The explicit split (#463) resolves the elementary
`1` and the fully-computed archimedean polygamma datum, leaving the companion term as the sole
arithmetic carrier.  Substituting gives RH as ONE explicit inequality per `n`, on the companion:

  * `rh_iff_companion_ge` —
      `RH ↔ ∀ n, -(1 + (taylorCoeff Γℝ n).re) ≤ (taylorCoeff zetaPoleCompanion n).re`.

This is the sharpest honest reduction: the archimedean side `1 + (taylorCoeff Γℝ n).re` is fully
explicit (the polygamma-at-½ capstone), so RH is now exactly the statement that the companion
coefficient never falls below that explicit archimedean floor.  It PROVES nothing about RH — it
relocates it — and it inherits only `[propext, Classical.choice, Quot.sound]`.  conjecture1_proved = False.
-/
import Mathlib
import RvMLiCoeffId
import Lc.LiCriterion.XiOrderBridge

open Complex

namespace RvMWeierstrass

/-- **RH, localized onto the companion coefficient.**  Equivalent to Li positivity via the explicit
    split: RH holds iff the companion Taylor coefficient never drops below the explicit archimedean
    floor `-(1 + (taylorCoeff Γℝ n).re)`. -/
theorem rh_iff_companion_ge :
    RiemannHypothesis ↔
      ∀ n : ℕ, -(1 + (LiCriterion.taylorCoeff Complex.Gammaℝ n).re)
        ≤ (LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n).re := by
  rw [LiCriterion.li_criterion_rh_iff]
  refine forall_congr' fun n => ?_
  rw [taylorCoeff_riemannXi_split_explicit n, Complex.add_re, Complex.add_re, Complex.one_re]
  constructor <;> intro h <;> linarith

end RvMWeierstrass
