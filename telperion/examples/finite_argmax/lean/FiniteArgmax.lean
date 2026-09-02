/- telperion 0.1.6 | family FiniteArgmax | input-hash b300a3cbd7d2e2ad
   7 theorems, 7 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace FiniteArgmax

-- Finite argmax with strict margin: winner 73039787676416/92354487127101 strictly beats 1 competitor(s).
-- Each fact is the cross-multiplied integer inequality p_i*q_w < p_w*q_i (no division).
theorem fa_nearstar_n5_lt_one : (73039787676416 : ℤ) < 92354487127101 := by norm_num
theorem fa_nearstar_n5_beats_0 : (3123330500020692224 * 92354487127101 : ℤ) < 73039787676416 * 16360320331104560847 := by norm_num
-- Finite argmax with strict margin: winner 1/1 strictly beats 1 competitor(s).
-- Each fact is the cross-multiplied integer inequality p_i*q_w < p_w*q_i (no division).
theorem fa_nearstar_n11_beats_0 : (25804264053054077850709 * 1 : ℤ) < 1 * 46523913960640966796875 := by norm_num
-- Finite argmax with strict margin: winner 3/4 strictly beats 3 competitor(s).
-- Each fact is the cross-multiplied integer inequality p_i*q_w < p_w*q_i (no division).
theorem fa_small_multi_lt_one : (3 : ℤ) < 4 := by norm_num
theorem fa_small_multi_beats_0 : (1 * 4 : ℤ) < 3 * 2 := by norm_num
theorem fa_small_multi_beats_1 : (2 * 4 : ℤ) < 3 * 3 := by norm_num
theorem fa_small_multi_beats_2 : (5 * 4 : ℤ) < 3 * 7 := by norm_num

end FiniteArgmax
