import Mathlib

/-!
  # R2-legs certificate brick: length-3 and length-4 legs are rate-suboptimal

  Ground truth: `proof/verification/legs.py` (`certify_cherries_optimal`, exact).

  The "legs are cherries" gadget theorem states that among all pendant-leg
  lengths `ℓ`, only `ℓ = 2` (cherries) attains the star growth rate
  `rho_B = (621/64)^(1/11)`; every `ℓ ≠ 2` grows strictly slower.  In the
  rational (root-free) form used throughout the R3Cert legs framework, each
  finite-region `(ℓ, c)` row (with `c·ℓ ≤ 21`) is the exact inequality

      armBase ℓ c ^ 11  <  (621/64)^(1 + c·ℓ)

  which is `rho_ℓ < rho_B` raised to the `11·(1+cℓ)`-th power (no real `rpow`
  needed, matching `legs.py`'s `RB = 621/64`).

  The batch-1 brick (`R47R2LegsCert.lean`) handled the length-1 rows.  This
  DISTINCT standalone brick extracts and machine-checks the **length-3 and
  length-4** rows — the next non-cherry legs — as closed rational `norm_num`
  facts.  The leg matching factors are `phiL 2 = 3/2`, `phiL 3 = 7/4`,
  `phiL 4 = 17/8` (recursion `phiL ℓ = phiL (ℓ-1) + phiL (ℓ-2)/4`), and for
  `ℓ ≥ 2` the first-vertex degree is `δ = 2`, so
  `armBase ℓ c = phiL ℓ ^ c + c·(1/(2(1+c)))·phiL (ℓ-1)·phiL ℓ ^ (c-1)`.

    * `ℓ = 3, c = 1`:  `armBase 3 1 = 7/4 + (1/4)·(3/2) = 17/8`,
      and `(17/8)^11 < (621/64)^4`.
    * `ℓ = 3, c = 2`:  `armBase 3 2 = (7/4)^2 + (2/6)·(3/2)·(7/4) = 63/16`,
      and `(63/16)^11 < (621/64)^7`.
    * `ℓ = 4, c = 1`:  `armBase 4 1 = 17/8 + (1/4)·(7/4) = 41/16`,
      and `(41/16)^11 < (621/64)^5`.
    * `ℓ = 4, c = 2`:  `armBase 4 2 = (17/8)^2 + (2/6)·(7/4)·(17/8) = 1105/192`,
      and `(1105/192)^11 < (621/64)^9`.

  HONEST SCOPE.  This is a GADGET-level (growth-rate) certificate for the
  length-3 and length-4 finite-region rows of one of the three necessary
  conditions of the conjecture ("legs are cherries").  It is NOT the full
  conjecture (which also needs the backbone-is-a-star condition and global-max
  rigor).  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

/-- Leg matching factors satisfy the recursion `phiL ℓ = phiL (ℓ-1) + phiL (ℓ-2)/4`.
    From `phiL 2 = 3/2` and `phiL 3 = 7/4`, the `ℓ = 4` factor is
    `phiL 4 = 17/8`. -/
theorem phiL4_val : ((7 / 4 : ℚ) + (3 / 2) / 4) = 17 / 8 := by
  norm_num

/-- The `ℓ = 3` arm base at `c = 1` equals `17/8`:
    `armBase 3 1 = phiL 3 + (1/4)·phiL 2 = 7/4 + (1/4)·(3/2)`. -/
theorem armBase_3_1_val : ((7 / 4 : ℚ) + (1 / 4) * (3 / 2)) = 17 / 8 := by
  norm_num

/-- The `ℓ = 4` arm base at `c = 1` equals `41/16`:
    `armBase 4 1 = phiL 4 + (1/4)·phiL 3 = 17/8 + (1/4)·(7/4)`. -/
theorem armBase_4_1_val : ((17 / 8 : ℚ) + (1 / 4) * (7 / 4)) = 41 / 16 := by
  norm_num

/-- **Length-3 leg, `c = 1`, is rate-suboptimal.**  `armBase 3 1 = 17/8`, and
    `(17/8)^11 < (621/64)^4`, i.e. `rho_3 < rho_B` at `c = 1`. -/
theorem leg3_c1_suboptimal : (17 / 8 : ℚ) ^ 11 < (621 / 64) ^ 4 := by
  norm_num

/-- **Length-3 leg, `c = 2`, is rate-suboptimal.**  `armBase 3 2 = 63/16`, and
    `(63/16)^11 < (621/64)^7`, i.e. `rho_3 < rho_B` at `c = 2`. -/
theorem leg3_c2_suboptimal : (63 / 16 : ℚ) ^ 11 < (621 / 64) ^ 7 := by
  norm_num

/-- **Length-4 leg, `c = 1`, is rate-suboptimal.**  `armBase 4 1 = 41/16`, and
    `(41/16)^11 < (621/64)^5`, i.e. `rho_4 < rho_B` at `c = 1`. -/
theorem leg4_c1_suboptimal : (41 / 16 : ℚ) ^ 11 < (621 / 64) ^ 5 := by
  norm_num

/-- **Length-4 leg, `c = 2`, is rate-suboptimal.**  `armBase 4 2 = 1105/192`, and
    `(1105/192)^11 < (621/64)^9`, i.e. `rho_4 < rho_B` at `c = 2`. -/
theorem leg4_c2_suboptimal : (1105 / 192 : ℚ) ^ 11 < (621 / 64) ^ 9 := by
  norm_num

/-- The `ℓ = 3, c = 1` row in cleared-denominator integer form (equivalent to
    `leg3_c1_suboptimal`): `17^11 · 64^4 < 621^4 · 8^11`. -/
theorem leg3_c1_integer : (17 : ℚ) ^ 11 * 64 ^ 4 < 621 ^ 4 * 8 ^ 11 := by
  norm_num

/-- The `ℓ = 4, c = 1` row in cleared-denominator integer form (equivalent to
    `leg4_c1_suboptimal`): `41^11 · 64^5 < 621^5 · 16^11`. -/
theorem leg4_c1_integer : (41 : ℚ) ^ 11 * 64 ^ 5 < 621 ^ 5 * 16 ^ 11 := by
  norm_num

end Step3
end R3Cert
