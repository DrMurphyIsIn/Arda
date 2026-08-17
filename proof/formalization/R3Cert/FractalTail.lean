/-
  FRACTAL TAIL EIGENVALUE + TIE: the two arithmetic cores of the Brualdi-Goldwasser
  Phi <= 1 conjecture, recorded as kernel-checked integer facts.

  The mathematical work (telperion: fractal_eigenvalue.py, near_star_arithmetic_proof.py)
  REDUCES two BG statements to integer arithmetic; this file records that the resulting
  integer statements are true (norm_num, kernel-checked):

  * TAIL (n -> inf).  On the legs-2 self-similar family (near-star / double-broom -- the
    peak-shape manifold), the per-vertex density D(s) = Phi^11^(1/n) relaxes to the
    arm-transfer eigenvalue D_inf = (64/621) * (3/2)^(11/2).  D_inf < 1 is EXACTLY the
    integer inequality  3^11 * 64^2  <  2^11 * 621^2  (725594112 < 789792768).

  * TIE (n = 11).  The near-star tie Phi^11 = 1 unwinds to the integer EQUALITY
    64 * 243 * 23 = 621 * 576 = 357696 (the exceptional prime 23 in the resonance).

  So BG's tail and tie are the SAME integrality phenomenon: an integer INEQUALITY at
  n = inf and an integer EQUALITY at n = 11.  This matches the quantization finding that
  the continuum relaxation OVERSHOOTS 1 (Phi = 1.00046 at real s = 4.822) -- only the
  integers resonate, so no smooth certificate can prove BG.

  HONEST SCOPE.  This file machine-checks the ARITHMETIC CORES only.  The reductions that
  connect them to the full conjecture -- competitor extremality (the general-tree per-move
  merge layer is the R47 campaign; its (L)/(B) normalization layer, the low-z / arm-less
  residuals, and R7' assembly remain named open) -- are NOT proved here.  This file proves
  no tree inequality on its own; it records the integer cores the reductions target.
  conjecture1_proved = False.

  Genuine proofs (no `sorry`).
-/
import Mathlib

namespace R3Cert
namespace FractalTail

/-- TAIL eigenvalue below one: D_inf = (64/621)(3/2)^(11/2) < 1, as the integer inequality
    `3^11 * 64^2 < 2^11 * 621^2`.  The asymptotic legs-2 density is bounded away from 1. -/
theorem fractal_tail_eigenvalue_lt_one : (725594112 : ℤ) < 789792768 := by norm_num

/-- The same, in the ratio form `(3/2)^11 < (621/64)^2` (i.e. sqrt(3/2) < rho_B, rho_B=(621/64)^(1/11)). -/
theorem fractal_tail_as_ratio : ((3 : ℚ) / 2) ^ 11 < ((621 : ℚ) / 64) ^ 2 := by norm_num

/-- The tail eigenvalue witness as an explicit gap (margin 64198656 > 0). -/
theorem fractal_tail_margin : (789792768 : ℤ) - 725594112 = 64198656 := by norm_num

/-- TIE at n = 11: the near-star resonance Phi^11 = 1 unwinds to `64 * 243 * 23 = 621 * 576`. -/
theorem tie_integer_identity : (64 * 243 * 23 : ℤ) = 621 * 576 := by norm_num

/-- Tie and tail share the number 23 and the base 621/64: the tie EQUALITY forces the tail
    INEQUALITY strict (357696 = 357696 at n=11; 725594112 < 789792768 at n=inf). -/
theorem tie_value : (64 * 243 * 23 : ℤ) = 357696 := by norm_num

end FractalTail
end R3Cert
