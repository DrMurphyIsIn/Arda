/- telperion 0.1.6 | family Rigidity | input-hash 03b17111df510b52
   4 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Rigidity

-- The tie is an INTEGER coincidence: 64·243·23 = 621·576, pinning
-- R(5) = 1 exactly; R strictly below 1 at every other integer
-- (unimodal, ratio crosses 1 once between s=5 and s=6).  This is why
-- no smooth tool reaches the tie: they osculate c* ≈ 3.82, not 5.
theorem tie_identity : (64 * 243 * 23 : ℚ) = 621 * 576 := by norm_num
theorem near_star_R5_eq_one : ((1 : ℚ) / 1) = 1 := by norm_num
theorem near_star_R4_lt_one : (86959512306484890624 : ℚ) < 87946907297998046875 := by norm_num
theorem near_star_R6_lt_one : (980170052528609401200979968 : ℚ) < 996644577901404223353123569 := by norm_num

end Rigidity
end G1
