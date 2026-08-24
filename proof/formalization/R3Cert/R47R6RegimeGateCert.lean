/-
  R47 R6 many-arm regime gate -- when the hub activity z0 falls into the certified range.

  SOURCE: proof/verification/distribution.py (arm-balancing part (A)): the transfer surplus
  is affine in z0 and certified nonnegative on z0 in (0, 1/6]; the worst-case corner is the
  "2-arm hub-3 star" with z0 = 1/6.

  CONTEXT.  The hub activity of a `k`-arm hub carrying `c0` cherries is
      z0 = 3 / (3 k + 4 c0)      (degree `k + c0`, so `3 (k + c0) + c0 = 3 k + 4 c0`).
  `R47R6ArmBalanceLiftCert.armBalance_lift` (and the de-loading lift) require `z0 <= 1/6`.
  This brick is the exact GATE for that hypothesis in terms of the concrete arm/cherry
  counts: `z0 <= 1/6` once `3 k + 4 c0 >= 18`.  In particular a hub is inside the certified
  improving regime once it is arm-rich enough (e.g. `k >= 6` for a de-loaded hub, matching
  the asymptotic large-`n` maximizer); small hubs (`z0 > 1/6`) are OUTSIDE the range, where
  the transfers may go the other way (verified: a 2-arm `c0 = 0` hub, `z0 = 1/2`, has an
  all-negative balancing bracket).

  HONEST SCOPE.  The regime gate connecting concrete hub arm-counts to the lift hypothesis
  `z0 <= 1/6`.  It does NOT discharge the transfer induction nor the conjecture.
  Self-contained (`import Mathlib`); genuine proof (no `sorry`, no `axiom`, no vacuous
  hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- **The many-arm regime gate.**  A `k`-arm hub with `c0` cherries has activity
    `z0 = 3/(3k+4c0) ≤ 1/6` once `3k+4c0 ≥ 18` -- the range on which the arm-balancing /
    de-loading transfer surplus is certified nonnegative (`armBalance_lift`, de-loading lift). -/
theorem hub_z0_le (k c0 : ℕ) (h : 18 ≤ 3 * k + 4 * c0) :
    (3 : ℝ) / (3 * (k : ℝ) + 4 * (c0 : ℝ)) ≤ 1 / 6 := by
  rw [show (1 : ℝ) / 6 = 3 / 18 by norm_num]
  have hk : (18 : ℝ) ≤ 3 * (k : ℝ) + 4 * (c0 : ℝ) := by exact_mod_cast h
  gcongr

end Step3
end R3Cert
