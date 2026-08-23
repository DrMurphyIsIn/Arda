/-
  R47 R6 arm rate-optimality certificate -- the cherry-bundle arm rate is uniquely
  maximised at c = 5.

  SOURCE: proof/verification/arm_bound.py, `certify_rate_optimal` (exact `Fraction`).

  CONTEXT.  In the single-hub objective (`singleHub_Aobj_formula`, R47SingleHubFormula),
  each arm of cherry-count `c` contributes through the per-vertex rate
      rho(c) = F(1,c) ^ (1 / (1 + 2 c)),   F(1,c) = (3/2)^c * (1 + c / (3 (c+1))),
  and the tie base is F(1,5) = 621/64 = rhoB^11.  The arm-level bound of the R6
  hub-de-loading / arm-balancing argument rests on the EXACT rational fact
      F(1,c) ^ 11  <  (621/64) ^ (1 + 2 c)     for every integer c != 5,
  i.e. `rho(c) < rho(5) = rhoB` (raise both sides to the `11 (1+2c)` power; no real
  `rpow` needed).  c = 5 is the strict unique rate-maximiser, with equality
  F(1,5) = 621/64 at the tie.

  This brick certifies the exact `F(1,c)` VALUE IDENTITIES (closed form = rational) for
  c = 1..7 and the rate-suboptimality inequalities for the finite region
  c in {0,1,2,3,4,6,7} -- in particular the load-bearing arm-level BOUNDARY cases c = 4
  and c = 6 (the maximiser's arms lie in {4,5,6}; c=4 and c=6 both strictly lose to c=5),
  plus their cleared-denominator integer forms.  Every fact re-verified in exact
  `fractions.Fraction` before writing.

  HONEST SCOPE.  This is the finite-region rate-optimality certificate feeding the R6
  arm-level bound -- one input to the Hdom single-hub domination.  It is NOT the full
  arm-level bound (which also needs rate unimodality on the c<=3 and c>=7 tails) and NOT
  the conjecture.  Self-contained (`import Mathlib`); genuine proofs (no `sorry`, no
  `axiom`, no vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-! ### `F(1,c)` value identities: `(3/2)^c * (1 + c/(3(c+1))) = F(1,c)` -/

/-- `F(1,1) = 7/4`. -/
theorem armF1_c1 : ((3 / 2 : ℚ) ^ 1 * (1 + 1 / (3 * (1 + 1)))) = 7 / 4 := by norm_num

/-- `F(1,2) = 11/4`. -/
theorem armF1_c2 : ((3 / 2 : ℚ) ^ 2 * (1 + 2 / (3 * (2 + 1)))) = 11 / 4 := by norm_num

/-- `F(1,3) = 135/32`. -/
theorem armF1_c3 : ((3 / 2 : ℚ) ^ 3 * (1 + 3 / (3 * (3 + 1)))) = 135 / 32 := by norm_num

/-- `F(1,4) = 513/80`. -/
theorem armF1_c4 : ((3 / 2 : ℚ) ^ 4 * (1 + 4 / (3 * (4 + 1)))) = 513 / 80 := by norm_num

/-- **`F(1,5) = 621/64 = rhoB^11`** -- the tie base (the unique rate-maximiser value). -/
theorem armF1_c5 : ((3 / 2 : ℚ) ^ 5 * (1 + 5 / (3 * (5 + 1)))) = 621 / 64 := by norm_num

/-- `F(1,6) = 6561/448`. -/
theorem armF1_c6 : ((3 / 2 : ℚ) ^ 6 * (1 + 6 / (3 * (6 + 1)))) = 6561 / 448 := by norm_num

/-- `F(1,7) = 22599/1024`. -/
theorem armF1_c7 : ((3 / 2 : ℚ) ^ 7 * (1 + 7 / (3 * (7 + 1)))) = 22599 / 1024 := by norm_num

/-! ### Rate-suboptimality: `F(1,c)^11 < (621/64)^(1+2c)` for `c != 5` -/

/-- `c = 0`: the bare (no-cherry) arm, `F(1,0)=1`, `1^11 < (621/64)^1`. -/
theorem arm_rate_c0 : (1 / 1 : ℚ) ^ 11 < (621 / 64) ^ 1 := by norm_num

/-- `c = 1`: `(7/4)^11 < (621/64)^3`. -/
theorem arm_rate_c1 : (7 / 4 : ℚ) ^ 11 < (621 / 64) ^ 3 := by norm_num

/-- `c = 2`: `(11/4)^11 < (621/64)^5`. -/
theorem arm_rate_c2 : (11 / 4 : ℚ) ^ 11 < (621 / 64) ^ 5 := by norm_num

/-- `c = 3`: `(135/32)^11 < (621/64)^7`. -/
theorem arm_rate_c3 : (135 / 32 : ℚ) ^ 11 < (621 / 64) ^ 7 := by norm_num

/-- **`c = 4` (arm-level boundary): `(513/80)^11 < (621/64)^9`** -- a 4-cherry arm loses to a
    5-cherry arm.  One of the two load-bearing `{4,5,6}` boundary cases. -/
theorem arm_rate_c4 : (513 / 80 : ℚ) ^ 11 < (621 / 64) ^ 9 := by norm_num

/-- **`c = 6` (arm-level boundary): `(6561/448)^11 < (621/64)^13`** -- a 6-cherry arm loses to a
    5-cherry arm.  The other load-bearing `{4,5,6}` boundary case. -/
theorem arm_rate_c6 : (6561 / 448 : ℚ) ^ 11 < (621 / 64) ^ 13 := by norm_num

/-- `c = 7`: `(22599/1024)^11 < (621/64)^15`. -/
theorem arm_rate_c7 : (22599 / 1024 : ℚ) ^ 11 < (621 / 64) ^ 15 := by norm_num

/-! ### Cleared-denominator integer forms of the two boundary cases -/

/-- `c = 4` integer form (equivalent to `arm_rate_c4`): `513^11 * 64^9 < 621^9 * 80^11`. -/
theorem arm_rate_c4_integer : (513 : ℚ) ^ 11 * 64 ^ 9 < 621 ^ 9 * 80 ^ 11 := by norm_num

/-- `c = 6` integer form (equivalent to `arm_rate_c6`): `6561^11 * 64^13 < 621^13 * 448^11`. -/
theorem arm_rate_c6_integer : (6561 : ℚ) ^ 11 * 64 ^ 13 < 621 ^ 13 * 448 ^ 11 := by norm_num

end Step3
end R3Cert
