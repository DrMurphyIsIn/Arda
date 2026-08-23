/-
  R47 R6 hub de-loading transfer certificate -- moving a hub cherry onto an arm
  strictly increases the objective (the "hub carries 0" mechanism).

  SOURCE: proof/verification/arm_bound.py, `certify_transfer_mixed` (exact, symbolic).

  CONTEXT.  In the R6 single-hub structure, a hub with `c0` cherries and arms in the
  balanced set `{4,5,6}` can shed a cherry: de-load one hub cherry (`c0 -> c0-1`) and
  raise a level-`m` arm to level `m+1`.  The sign of the resulting objective change is
      E(k, c0) = after - before,
  with `k` the hub arm-count and `S = (k-1) s` the total activity of the OTHER arms.
  `E` is AFFINE in `S`, so certifying `E > 0` at the two activity endpoints
      s = z(1,6) = 3/25   (all other arms at level 6)   and
      s = z(1,4) = 3/19   (all other arms at level 4)
  covers every balanced arrangement of the other arms in `{4,5,6}` by interpolation.

  Under the physical-domain shift `k = 33 + mm`, `c0 = 1 + j` (so `mm, j >= 0` over the
  regime `k >= 33`, `c0 >= 1`), the NUMERATOR of `E` over its positive denominator is a
  degree-2 polynomial in `(mm, j)` with ALL-NONNEGATIVE coefficients AND a strictly
  positive constant term -- hence `E > 0` throughout.  This brick certifies the four
  cases `m in {4,5}` x `s in {3/25, 3/19}`.  Each polynomial is the exact
  `sp.Poly(expand(num.subs{k:33+mm, c0:1+j}))` of `certify_transfer_mixed`, re-verified
  in exact `sympy`/`Fraction` before writing (constant terms 13212, 15156, 705, 7275).

  Consequence (with the arm-level bound `R47R6ArmRateCert` + `k = Theta(n) >= 33`): for
  the pi-maximising star of cherry-bundles every hub cherry strictly improves away, so
  the hub carries 0 -- the de-loaded all-arms template.

  HONEST SCOPE.  This is the finite-regime (`k >= 33`, arms in `{4,5,6}`) de-loading
  transfer certificate -- one input to the Hdom single-hub domination.  It is NOT the
  full G5 de-loading schedule and NOT the conjecture.  Self-contained (`import Mathlib`);
  genuine proofs (no `sorry`, no `axiom`, no vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- **De-loading transfer, `m = 4`, other-arms endpoint `s = 3/25` (level 6).**
    The shifted numerator of `E` is strictly positive: a positive constant plus
    nonnegative-coefficient terms in `mm, j >= 0` (`k = 33+mm`, `c0 = 1+j`). -/
theorem deload_transfer_m4_lo (mm j : ℝ) (hm : 0 ≤ mm) (hj : 0 ≤ j) :
    0 < 50 * j ^ 2 + 92 * mm * j + 42 * mm ^ 2 + 2969 * j + 1785 * mm + 13212 := by
  positivity

/-- **De-loading transfer, `m = 4`, other-arms endpoint `s = 3/19` (level 4).** -/
theorem deload_transfer_m4_hi (mm j : ℝ) (hm : 0 ≤ mm) (hj : 0 ≤ j) :
    0 < 38 * j ^ 2 + 71 * mm * j + 33 * mm ^ 2 + 2291 * j + 1551 * mm + 15156 := by
  positivity

/-- **De-loading transfer, `m = 5`, other-arms endpoint `s = 3/25` (level 6).** -/
theorem deload_transfer_m5_lo (mm j : ℝ) (hm : 0 ≤ mm) (hj : 0 ≤ j) :
    0 < 50 * j ^ 2 + 92 * mm * j + 42 * mm ^ 2 + 2969 * j + 1409 * mm + 705 := by
  positivity

/-- **De-loading transfer, `m = 5`, other-arms endpoint `s = 3/19` (level 4).** -/
theorem deload_transfer_m5_hi (mm j : ℝ) (hm : 0 ≤ mm) (hj : 0 ≤ j) :
    0 < 38 * j ^ 2 + 71 * mm * j + 33 * mm ^ 2 + 2291 * j + 1316 * mm + 7275 := by
  positivity

end Step3
end R3Cert
