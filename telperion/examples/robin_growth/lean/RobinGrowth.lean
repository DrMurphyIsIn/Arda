/- telperion 0.1.6 | family RobinGrowth | input-hash cf9f87200519d925
   8 theorems, 8 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace RobinGrowth

-- robin_neg_refutes: the falsifiability face.  A certified UPPER bound `hi`
-- on R = e^γ·n·log log n with `hi < σ(n)` (n > 5040) contradicts Robin's
-- inequality at n, hence ¬RH through Robin's equivalence (carried as hRobin :
-- RH → σ(n) < R).  Not expected to fire; makes the ladder falsifiable.
theorem robin_neg_refutes {P : Prop} (sigma_n R hi : ℝ)
    (hRobin : P → sigma_n < R) (hUp : R ≤ hi) (hlt : hi < sigma_n) : ¬P :=
  fun hP => absurd (hRobin hP) (not_lt.mpr (le_trans hUp (le_of_lt hlt)))

-- robin_n5041: Robin rung n=5041 (> 5040) — σ(5041) = 5113 < e^γ·5041·log log 5041 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 192410873467/10000000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n5041 (R : ℝ) (hR : ((192410873467 / 10000000) : ℝ) ≤ R) : ((5113 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

-- robin_n5042: Robin rung n=5042 (> 5040) — σ(5042) = 7566 < e^γ·5042·log log 5042 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 12028195749/625000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n5042 (R : ℝ) (hR : ((12028195749 / 625000) : ℝ) ≤ R) : ((7566 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

-- robin_n5044: Robin rung n=5044 (> 5040) — σ(5044) = 9604 < e^γ·5044·log log 5044 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 96265825057/5000000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n5044 (R : ℝ) (hR : ((96265825057 / 5000000) : ℝ) ≤ R) : ((9604 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

-- robin_n5045: Robin rung n=5045 (> 5040) — σ(5045) = 6060 < e^γ·5045·log log 5045 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 192571909727/10000000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n5045 (R : ℝ) (hR : ((192571909727 / 10000000) : ℝ) ≤ R) : ((6060 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

-- robin_n10080: Robin rung n=10080 (> 5040) — σ(10080) = 39312 < e^γ·10080·log log 10080 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 398775185643/10000000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n10080 (R : ℝ) (hR : ((398775185643 / 10000000) : ℝ) ≤ R) : ((39312 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

-- robin_n15120: Robin rung n=15120 (> 5040) — σ(15120) = 59520 < e^γ·15120·log log 15120 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 152438672169/2500000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n15120 (R : ℝ) (hR : ((152438672169 / 2500000) : ℝ) ≤ R) : ((59520 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

-- robin_n25200: Robin rung n=25200 (> 5040) — σ(25200) = 99944 < e^γ·25200·log log 25200 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 12993384599/125000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n25200 (R : ℝ) (hR : ((12993384599 / 125000) : ℝ) ≤ R) : ((99944 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

-- robin_n55440: Robin rung n=55440 (> 5040) — σ(55440) = 232128 < e^γ·55440·log log 55440 = R.
-- R is the transcendental Robin RHS, carried as hypothesis hR : Llo ≤ R,
-- Llo = 23608142813/100000 the certified Arb lower bound (the trust seam).
-- Kernel proves (σ:ℝ) < Llo (norm_num on exact literals) ≤ R.  A finite rung of
-- Robin's RH-equivalence (RH ⟺ ∀ n > 5040, σ(n) < R(n)); NOT RH.
theorem robin_n55440 (R : ℝ) (hR : ((23608142813 / 100000) : ℝ) ≤ R) : ((232128 : ℝ)) < R :=
  lt_of_lt_of_le (by norm_num) hR

end RobinGrowth
