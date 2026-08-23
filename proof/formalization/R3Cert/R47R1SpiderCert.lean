/-
  R47R1SpiderCert.lean

  RUNG R1-spiders.  Standalone supporting brick for the "branching beats every
  spider (asymptotically)" argument in `proof/verification/spiders.py`.

  The spider transfer-matrix argument bounds every spider on n vertices by
  `pi(spider) <= C * rho_S^n` with `rho_S = sqrt(377/250)`, while the star
  B(k,5) achieves per-vertex rate `rho_B = (621/64)^(1/11)`.  The exponential
  growth-rate comparison `rho_S < rho_B` is the exact rational crux that makes
  the gap `(rho_B/rho_S)^n -> infinity`.  Clearing the 1/2 and 1/11 exponents,
  this is exactly:

        rho_S < rho_B
    <=> rho_S^(2*11) < rho_B^(2*11)
    <=> (377/250)^11 < (621/64)^2.

  Numerically (exact Fraction, verified in Python):
        (377/250)^11 = 21865270389159625050067741673 / 238418579101562500000000000
                     ~ 91.70959...
        (621/64)^2   = 385641 / 4096
                     ~ 94.15063...
  and cross-multiplied over the integers:
        377^11 * 64^2 = 89560147513997824205077469892608
        621^2 * 250^11 = 91943979263305664062500000000000
  so the strict inequality holds.

  This brick states and proves that exact rational crux (and its integer
  cross-multiplied form), which are the machine-checkable rank-0/1 facts of the
  spider argument.  Everything is a closed rational/integer inequality proved by
  `norm_num`; no analytic content, no hypotheses, no `sorry`, no `axiom`.

  conjecture1_proved = False.  This brick certifies a supporting rate-gap fact
  only, not the full Brualdi-Goldwasser conjecture.
-/
import Mathlib

namespace R3Cert.Step3

/-- The exact spider rate-gap crux, cleared of both exponents:
    `rho_S < rho_B  <=>  (377/250)^11 < (621/64)^2`.
    Here `377/250 = rho_S^2` and `621/64 = rho_B^11 = F(6)`. -/
theorem spider_rate_gap : (377 / 250 : ℚ) ^ 11 < (621 / 64 : ℚ) ^ 2 := by
  norm_num

/-- Integer cross-multiplied form of the same crux:
    `377^11 * 64^2 < 621^2 * 250^11`. -/
theorem spider_rate_gap_int :
    (377 : ℤ) ^ 11 * 64 ^ 2 < 621 ^ 2 * 250 ^ 11 := by
  norm_num

/-- Exact value of `rho_S^(2*11) = (377/250)^11`, the spider side of the gap. -/
theorem rho_s_pow11_value :
    (377 / 250 : ℚ) ^ 11
      = 21865270389159625050067741673 / 238418579101562500000000000 := by
  norm_num

/-- Exact value of `rho_B^(2*11) = (621/64)^2`, the branch side of the gap. -/
theorem rho_b_pow2_value : (621 / 64 : ℚ) ^ 2 = 385641 / 4096 := by
  norm_num

/-- The gap is strictly positive: `(621/64)^2 - (377/250)^11 > 0`.
    This is the quantity whose n-th power drives `pi(branch)/pi(spider) -> inf`. -/
theorem spider_rate_gap_pos :
    (0 : ℚ) < (621 / 64 : ℚ) ^ 2 - (377 / 250 : ℚ) ^ 11 := by
  norm_num

/-- Sanity anchor for the branch base `F(6) = 621/64 = 3^3 * 23 / 2^6`. -/
theorem branch_arm_base_factor : (621 / 64 : ℚ) = (3 ^ 3 * 23 : ℚ) / 2 ^ 6 := by
  norm_num


end R3Cert.Step3
