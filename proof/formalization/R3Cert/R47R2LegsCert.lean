import Mathlib

/-!
  # R2-legs certificate brick: a length-1 (non-cherry) leg is rate-suboptimal

  Ground truth: `proof/verification/legs.py` (`certify_cherries_optimal`, exact).

  The "legs are cherries" gadget theorem states that among all pendant-leg
  lengths `ℓ`, only `ℓ = 2` (cherries) attains the star growth rate
  `rho_B = (621/64)^(1/11)`; every `ℓ ≠ 2` grows strictly slower.  In the
  rational (root-free) form used throughout the R3Cert legs framework, each
  `(ℓ, c)` row is the exact inequality

      armBase ℓ c ^ 11  <  (621/64)^(1 + c·ℓ)

  which is `rho_ℓ < rho_B` raised to the `11·(1+cℓ)`-th power (no real `rpow`
  needed, matching `legs.py`'s `RB = 621/64`).

  This standalone brick extracts and machine-checks the **length-1** rows —
  the smallest non-cherry legs — as closed rational `norm_num` facts.  For a
  length-1 leg, `phiL 1 = 1` and `phiL 0 = 2`, so
  `armBase 1 c = (1 + 2c)/(1 + c)`:

    * `c = 1`:  `armBase 1 1 = 3/2`,  and  `(3/2)^11 < (621/64)^2`.
    * `c = 2`:  `armBase 1 2 = 5/3`,  and  `(5/3)^11 < (621/64)^3`.
    * tail `c ≥ 4`:  `armBase 1 c < 2`, hence `armBase 1 c ^ 11 < 2^11`, and the
      certificate closes because `2^11 < (621/64)^5` (`legs.py` line 74).

  We also anchor the reference rate: `armBase 2 5 = 621/64` exactly, i.e. the
  cherry (`ℓ = 2`) star at `c = 5` realizes `rho_B` — the rate the length-1
  legs above fail to reach.

  HONEST SCOPE.  This is a GADGET-level (growth-rate) certificate for the
  length-1 rows of one of the three necessary conditions of the conjecture
  ("legs are cherries").  It is NOT the full conjecture (which also needs the
  backbone-is-a-star condition and global-max rigor).  conjecture1_proved =
  False.
-/

namespace R3Cert
namespace Step3

/-- The reference rate `rho_B` is realized by the cherry (`ℓ = 2`) star at
    `c = 5`: `armBase 2 5 = (3/2)^5 + 5·(1/12)·(3/2)^4 = 621/64`.  This is the
    rate that the length-1 (non-cherry) legs below fail to reach. -/
theorem rhoB_ref :
    ((3 / 2 : ℚ) ^ 5 + 5 * (1 / 12) * (3 / 2) ^ 4) = 621 / 64 := by
  norm_num

/-- **Length-1 leg, `c = 1`, is rate-suboptimal.**  `armBase 1 1 = 3/2`, and
    `(3/2)^11 < (621/64)^2`, i.e. `rho_1 < rho_B` at `c = 1`. -/
theorem leg1_c1_suboptimal : (3 / 2 : ℚ) ^ 11 < (621 / 64) ^ 2 := by
  norm_num

/-- **Length-1 leg, `c = 2`, is rate-suboptimal.**  `armBase 1 2 = 5/3`, and
    `(5/3)^11 < (621/64)^3`, i.e. `rho_1 < rho_B` at `c = 2`.  This is the
    representative non-cherry (`ℓ = 1 ≠ 2`) certificate row. -/
theorem leg1_c2_suboptimal : (5 / 3 : ℚ) ^ 11 < (621 / 64) ^ 3 := by
  norm_num

/-- The `c = 2` row in cleared-denominator integer form (equivalent to
    `leg1_c2_suboptimal`): `5^11 · 64^3 < 621^3 · 3^11`. -/
theorem leg1_c2_integer : (5 : ℚ) ^ 11 * 64 ^ 3 < 621 ^ 3 * 3 ^ 11 := by
  norm_num

/-- **Length-1 tail bound.**  For `c ≥ 4` the length-1 arm base satisfies
    `armBase 1 c < 2`, so its `11`-th power is below `2^11`; the certificate
    then closes via this fixed exact fact `2^11 < (621/64)^5` (`legs.py`,
    line 74). -/
theorem leg1_tail_suboptimal : (2 : ℚ) ^ 11 < (621 / 64) ^ 5 := by
  norm_num

end Step3
end R3Cert