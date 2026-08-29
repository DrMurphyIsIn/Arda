/- The COLLECTIVE-CANCELLATION obstruction, kernel-gated (PROOF_STATUS "ruled out" #1).
   Per-vertex factorization Phi^11 = prod_v (64/621)a_v^11.  The tie N(0,5) has TWO of its
   three distinct factors > 1 (hub ~1.528, arm-mid ~8.914) yet the full product = 1 --
   so no all-<=1 per-vertex decomposition (no sum of non-positive local terms) can bound
   Phi^11; the <=1 is collective.  Records the obstruction; does NOT prove the crux.
   conjecture1_proved = False. -/
import Mathlib

namespace BGCollectiveCancellation

-- leaf vertex (a=1): sub-unit factor
theorem pvf_leaf_sub_unit : (64 : ℚ) / 621 < 1 := by norm_num

-- hub vertex (a=23/18): factor EXCEEDS 1 (the +0.424 log-defect)
theorem pvf_hub_excess : (41426511213649 : ℚ) / 27113235502176 > 1 := by norm_num

-- arm-mid vertex (a=3/2): factor EXCEEDS 1
theorem pvf_armmid_excess : (6561 : ℚ) / 736 > 1 := by norm_num

-- the tie N(0,5): full per-vertex factorization (5 leaves, 5 arm-mids, 1 hub) = 1 exactly
theorem tie_collective_balance :
    ((64 : ℚ) / 621) ^ 5 * ((6561 : ℚ) / 736) ^ 5 * ((41426511213649 : ℚ) / 27113235502176) = 1 := by norm_num

end BGCollectiveCancellation
