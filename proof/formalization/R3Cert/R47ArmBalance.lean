/-
  R3Cert.R47ArmBalance -- the R6 arm-balancing Polya certificate (single-cherry transfer).

  R6 (cherry distribution) says: on a star hub, spreading arm cherries as evenly as possible
  MAXIMISES the objective -- any two arm counts differ by at most 1 (Schur-concavity).  The proof
  (distribution.py, certify_arm_balancing_symbolic) is the single-cherry transfer (a,b) -> (a+1,b-1)
  for b >= a+2: at the joint minimum (2-arm hub-3 star), the objective change is
      D(a,b) = [G_new - G_old] + (1/6)[G_new S_new - G_old S_old] >= 0.
  After the corner shift a = 3+s, b = 5+s+t (s,t >= 0) and factoring the positive (3/2)^{a+b},
  D = num(s,t) / den(s,t) with num, den ALL-NONNEGATIVE-COEFFICIENT polynomials (a Polya certificate):

      num = 4 s t + 4 s + 2 t^2 + 22 t + 20                       (min coeff 2, constant 20)
      den = 9 s^4 + 18 s^3 t + 180 s^3 + 9 s^2 t^2 + 261 s^2 t + 1341 s^2
            + 81 s t^2 + 1251 s t + 4410 s + 180 t^2 + 1980 t + 5400   (constant 5400)

  This file certifies the positivity core (`num >= 0`, `den > 0`, hence `D >= 0`) via `positivity`.  The
  ALGEBRAIC identity `pi-change = (3/2)^{a+b} * num/den` (that this D IS the transfer's objective change)
  is the next brick; here we bank the certificate.  Genuine proof (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- The transfer-certificate numerator is nonnegative for `s, t ≥ 0`. -/
theorem armBalance_num_nonneg (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ 4 * s * t + 4 * s + 2 * t ^ 2 + 22 * t + 20 := by positivity

/-- The transfer-certificate denominator is strictly positive for `s, t ≥ 0`. -/
theorem armBalance_den_pos (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < 9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
        + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
        + 1980 * t + 5400 := by positivity

/-- **R6 arm-balancing certificate.**  The single-cherry-transfer objective change `D = num/den` is
    nonnegative for all `s, t ≥ 0` -- the Polya core of Schur-concavity (arms spread evenly). -/
theorem armBalance_D_nonneg (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ (4 * s * t + 4 * s + 2 * t ^ 2 + 22 * t + 20)
        / (9 * s ^ 4 + 18 * s ^ 3 * t + 180 * s ^ 3 + 9 * s ^ 2 * t ^ 2 + 261 * s ^ 2 * t
          + 1341 * s ^ 2 + 81 * s * t ^ 2 + 1251 * s * t + 4410 * s + 180 * t ^ 2
          + 1980 * t + 5400) :=
  div_nonneg (armBalance_num_nonneg s t hs ht) (le_of_lt (armBalance_den_pos s t hs ht))

end Step3
end R3Cert
