/-
  R3Cert.R47R6StarAmplitude -- the single-star amplitude, exact rational facts (R6 / distribution.py).

  From distribution.py (C): the single star at arm level c=5 has EXACT amplitude
      A_single = 18/23 + (3/2)^10 / (6 * (621/64)^2) = 468/529 = 0.884688...
  This certifies the star-vs-double-star tiebreak constant (the single star strictly exceeds the
  tightest named near-star competitor amplitude ~0.871).  Rational facts, proved by `norm_num`.
  (The de-load/arm-balancing Polya positivity is already in R47ArmBalance.)  Genuine (no `sorry`).
  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- The single-star (arm level c=5) amplitude closed form. -/
noncomputable def aSingle : ℚ := (18 / 23) + (3 / 2 : ℚ) ^ 10 / (6 * (621 / 64 : ℚ) ^ 2)

/-- The closed form evaluates exactly to `468/529`. -/
theorem aSingle_eq : aSingle = 468 / 529 := by unfold aSingle; norm_num

/-- `A_single` strictly exceeds `871/1000`, the tightest named near-star competitor amplitude. -/
theorem aSingle_beats_competitor : (871 / 1000 : ℚ) < aSingle := by rw [aSingle_eq]; norm_num

/-- Two-sided pin `0.884 < A_single < 0.885`. -/
theorem aSingle_bounds : (884 / 1000 : ℚ) < aSingle ∧ aSingle < 885 / 1000 := by
  rw [aSingle_eq]; constructor <;> norm_num

end Step3
end R3Cert
