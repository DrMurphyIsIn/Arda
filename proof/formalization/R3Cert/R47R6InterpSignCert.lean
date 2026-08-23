/-
  R47 R6 interpolation-lemma sign dichotomy (I2) -- the same-n domination monotonicity.

  SOURCE: proof/verification/interpolation_lemma.py, `verify_I2` (exact).

  CONTEXT.  In the same-n domination of defected stars-of-hubs (R7' Stage II), a load-0
  sub-hub attached to an arm-heavy top contributes, exactly, a rational amplitude
  `B(cav) = 26/(rhoB (23 + 3 cav))` of its cavity alone, and the whole pi-bound is
      pi = rhoB^n * A_top * prod_i B(cav_i) * (1 + z_t (sigma_top + SUM cav_i)).
  The dependence on each sub-hub cavity `c_i` is governed by the derivative of the log
  pi-bound, whose SIGN reduces (exact `ring` identity) to the linear form
      -3 (1 + z_t (c_i + T)) + z_t (23 + 3 c_i)  =  23 z_t - 3 - 3 z_t T,     T >= 0.
  So the pi-bound is monotone DECREASING in every cavity iff `z_t <= 3/23`
  (the top is arm-heavy: `3 dt + 4 cT >= 23`), and monotone INCREASING otherwise.
  Hence the supremum over ALL sub-hub size vectors sits at an ENDPOINT --
  `cav -> 0` (heavy top, top-only limit) or `q_i = 1` (light top, all-spacer stars) --
  which is the finitely-certified case.  This dichotomy is what reduces the infinite
  family of size vectors to the endpoint certificates.

  This brick formalises the exact I2 core: the sign-polynomial `ring` identity, the two
  monotonicity sign lemmas, and the arm-heavy activity threshold
  `z_t = 3/(3 dt + 4 cT) <= 3/23  <=>  3 dt + 4 cT >= 23`.  Verified in exact `sympy`.

  HONEST SCOPE.  This is the exact monotonicity mechanism (I2) of the interpolation lemma
  -- one input to the same-n domination feeding Hdom.  It is NOT the endpoint certificates,
  NOT the full interpolation lemma, and NOT the conjecture.  Self-contained (`import
  Mathlib`); genuine proofs (no `sorry`, no `axiom`, no vacuous hypothesis).
  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- **(I2) sign-polynomial identity.**  The `c`-derivative sign of the log pi-bound
    reduces exactly to `23 z - 3 - 3 z T`. -/
theorem i2_sign_poly_eq (z c T : ℝ) :
    -3 * (1 + z * (c + T)) + z * (23 + 3 * c) = 23 * z - 3 - 3 * z * T := by
  ring

/-- **Arm-heavy top (`z ≤ 3/23`): monotone DECREASING.**  The sign polynomial is `≤ 0`
    for all `T ≥ 0`, so the pi-bound decreases in every sub-hub cavity; the sup is at
    `cav → 0` (the top-only limit). -/
theorem i2_sign_nonpos (z T : ℝ) (hz : 0 ≤ z) (hT : 0 ≤ T) (harm : z ≤ 3 / 23) :
    23 * z - 3 - 3 * z * T ≤ 0 := by
  nlinarith [mul_nonneg hz hT, harm, hz, hT]

/-- **Light top (`3/23 < z`): monotone INCREASING.**  At `T = 0` the sign polynomial is
    `> 0`, so the pi-bound increases in every cavity; the sup is at `q_i = 1` (all-spacer
    stars). -/
theorem i2_sign_pos_light (z : ℝ) (hlight : 3 / 23 < z) : 0 < 23 * z - 3 := by
  linarith

/-- **The arm-heavy activity bound.**  An arm-heavy top (`3 dt + 4 cT ≥ 23`, i.e. the top
    denominator `X ≥ 23`) has activity `z_t = 3/X ≤ 3/23` -- placing it in the DECREASING
    regime of `i2_sign_nonpos`, so its supremum is the top-only (`cav → 0`) limit. -/
theorem zt_le_of_arm_heavy (X : ℝ) (hX : 0 < X) (h : 23 ≤ X) : 3 / X ≤ 3 / 23 := by
  gcongr

end Step3
end R3Cert
