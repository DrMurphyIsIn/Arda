/-
  R4-R7 campaign, RUNG R6-deload: exact rational + Polya positivity bricks for the
  cherry-distribution step (proof/verification/distribution.py).

  Two independent, self-contained facts are certified here, both machine-extracted
  and sympy-verified (exact Fraction) before transcription:

  (C) STAR AMPLITUDE IDENTITY.  The single star at arm level c=5 has the EXACT
      amplitude
          A_single = 18/23 + (3/2)^10 / (6 * F6^2),   F6 = 621/64,
      and this closed form equals 468/529 exactly (= 414/529 + 54/529).  A strict
      rational lower bound 468/529 > 871/1000 witnesses that A_single exceeds the
      tightest named near-star competitor amplitude (~0.871), resolving the
      star-vs-double-star tiebreak in the single star's favour.

  (A/B) DE-LOAD (ARM-BALANCING) POLYA SURPLUS.  The worst-case single-cherry
      transfer surplus D(a,b) (2-arm hub-3 star, P=1, z0=1/6), after the corner
      shift a = 3+s, b = 5+s+t (s,t >= 0) and factoring the positive (3/2)^{a+b},
      reduces to num(s,t)/den(s,t) with BOTH num and den having all-nonnegative
      coefficients:
          num(s,t) = 4 s t + 4 s + 2 t^2 + 22 t + 20,
          den(s,t) = 9 s^4 + 18 s^3 t + 180 s^3 + 9 s^2 t^2 + 261 s^2 t
                     + 1341 s^2 + 81 s t^2 + 1251 s t + 4410 s + 180 t^2
                     + 1980 t + 5400.
      Both are nonnegative (den strictly positive) for s,t >= 0, hence the ratio
      D >= 0 unconditionally -- the Polya-type de-load certificate that the
      arm-optimal cherry distribution is balanced.

  Genuine proofs (no `sorry`, no `axiom`, no vacuous hypotheses).
  conjecture1_proved stays False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-! ### (C) Single-star amplitude: exact rational identity + strict lower bound -/

/-- The single-star (arm level c = 5) amplitude, as the closed form from
    `distribution.A_SINGLE`: `18/23 + (3/2)^10 / (6 * (621/64)^2)`. -/
noncomputable def aSingle : ℚ := (18 / 23) + (3 / 2 : ℚ) ^ 10 / (6 * (621 / 64 : ℚ) ^ 2)

/-- The closed form evaluates EXACTLY to `468/529`. -/
theorem aSingle_eq : aSingle = 468 / 529 := by
  unfold aSingle
  norm_num

/-- The second summand `(3/2)^10 / (6 * F6^2)` is exactly `54/529`. -/
theorem aSingle_second_term : (3 / 2 : ℚ) ^ 10 / (6 * (621 / 64 : ℚ) ^ 2) = 54 / 529 := by
  norm_num

/-- The first summand `18/23` is `414/529`, so the amplitude splits as `414/529 + 54/529`. -/
theorem aSingle_split : (18 / 23 : ℚ) = 414 / 529 := by norm_num

/-- `A_single` strictly exceeds `871/1000`, the tightest named near-star competitor
    amplitude (~0.871) -- the star-vs-double-star tiebreak in the star's favour. -/
theorem aSingle_beats_competitor : (871 / 1000 : ℚ) < aSingle := by
  rw [aSingle_eq]
  norm_num

/-- Two-sided pin: `0.884 < A_single < 0.885` (`A_single = 0.884688...`). -/
theorem aSingle_bounds : (884 / 1000 : ℚ) < aSingle ∧ aSingle < 885 / 1000 := by
  rw [aSingle_eq]
  constructor <;> norm_num

/-! ### (A/B) De-load Polya certificate: numerator and denominator positivity -/

/-- Polya numerator of the de-load transfer surplus, all-nonnegative coefficients. -/
noncomputable def deloadNum (s t : ℝ) : ℝ :=
  4 * s * t + 4 * s + 2 * t ^ 2 + 22 * t + 20

/-- Polya denominator of the de-load transfer surplus, all-nonnegative coefficients. -/
noncomputable def deloadDen (s t : ℝ) : ℝ :=
  9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
    + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
    + 1980 * t + 5400

/-- The numerator is nonnegative for `s, t >= 0` (Polya nonneg-coefficient certificate). -/
theorem deloadNum_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ deloadNum s t := by
  unfold deloadNum
  positivity

/-- The denominator is strictly positive for `s, t >= 0` (constant term 5400 > 0). -/
theorem deloadDen_pos {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < deloadDen s t := by
  unfold deloadDen
  positivity

/-- The de-load transfer surplus `D = num/den` is nonnegative for `s, t >= 0`.
    This is the machine-extracted Polya-type de-load certificate: the worst-case
    single-cherry arm-transfer surplus never decreases `pi`, so the arm-optimal
    cherry distribution is balanced (arm counts within 1). -/
theorem deload_surplus_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ deloadNum s t / deloadDen s t :=
  div_nonneg (deloadNum_nonneg hs ht) (le_of_lt (deloadDen_pos hs ht))

/-- Sanity anchor: at the corner `s = t = 0` (arms `a = 3, b = 5`) the surplus ratio
    is `20/5400 = 1/270 > 0`. -/
theorem deload_corner : deloadNum 0 0 / deloadDen 0 0 = 1 / 270 := by
  unfold deloadNum deloadDen
  norm_num

/-- This module proves supporting positivity/rational facts only; it does not
    discharge the global conjecture. -/
def conjecture1_proved : Prop := False

end Step3
end R3Cert
