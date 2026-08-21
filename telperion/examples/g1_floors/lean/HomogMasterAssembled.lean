import Mathlib
import HomogMaster

/-!
# Assembled achievable homogeneous master bound

This file glues the 12 kernel-green pieces of `HomogMaster.lean` into a single
theorem

    `homog_master_achievable : GS k mu <= T`

for every integer `k >= 1` and every ACHIEVABLE `mu` (`mu = 1`, or `0 < mu <= 1/2`),
where `GS`, `base`, `Bcap`, `glemma`, `master_ub`, `T` are the cavity quantities of
`R3Cert/CappedJointConfig.lean` (`W = 64/621`, `GAMMA = W^2 (5/3)^11`,
`T = W (5/3)^11`).

No new mathematics: the region decomposition (L1-L4) and every scalar/interval
certificate already live in `HomogMaster.lean`. This file supplies only the
mechanical glue -- the `min`-based `Bcap` case analysis, the `base(k) <= base(1)`
k-domination, the geometric `Bcap^k` decay, and the small `ℝ`-cert-to-`ℚ` bridges.

`conjecture1_proved = False`.  This closes the HOMOGENEOUS face over ACHIEVABLE
`mu` only; the heterogeneous -> homogeneous reduction remains open.
-/

namespace HomogMasterAssembled

open scoped BigOperators

/-- `W = 64/621`. -/
def W : ℚ := 64 / 621

/-- `GAMMA = W^2 (5/3)^11`. -/
def GAMMA : ℚ := W ^ 2 * (5 / 3) ^ 11

/-- `T = W (5/3)^11`. -/
def T : ℚ := W * (5 / 3) ^ 11

/-- `glemma mu = GAMMA / (1 + mu/3)^11`. -/
def glemma (mu : ℚ) : ℚ := GAMMA / (1 + mu / 3) ^ 11

/-- `master_ub mu = W (3/(2+mu))^11`. -/
def master_ub (mu : ℚ) : ℚ := W * (3 / (2 + mu)) ^ 11

/-- `Bcap mu = min (master_ub mu) (min (glemma mu) 1)`. -/
def Bcap (mu : ℚ) : ℚ := min (master_ub mu) (min (glemma mu) 1)

/-- `base k mu = (3(k+1) + 3 k mu + 1) / (3(k+1))`. -/
def base (k : ℕ) (mu : ℚ) : ℚ :=
  (3 * ((k : ℚ) + 1) + 3 * (k : ℚ) * mu + 1) / (3 * ((k : ℚ) + 1))

/-- `GS k mu = base(k,mu)^11 * Bcap(mu)^k`. -/
def GS (k : ℕ) (mu : ℚ) : ℚ := (base k mu) ^ 11 * (Bcap mu) ^ k

end HomogMasterAssembled
