/- telperion 0.1.5 | family LatticeBox | input-hash 00b61e138db45157
   18 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace LatticeBox

-- arms_leaves_2d: dimensional-lift certificate in ℤ^2. f <= 1
-- on ℤ^2_{>=0} via finite base box (5, 2) (all integer points,
-- exact) + a monotone tail in each of the 2 directions.  The max
-- lives on the face with coords (1,) pinned to 0 -- the lower-D
-- extremizer (for the crux 2-D family: the 1-D near-star edge).

theorem arms_leaves_2d_box_0_0 : (64:ℚ) < 621 := by norm_num
theorem arms_leaves_2d_box_0_1 : (486:ℚ) < 529 := by norm_num
theorem arms_leaves_2d_box_0_2 : (12800000000000:ℚ) < 42423705806967 := by norm_num
theorem arms_leaves_2d_box_1_0 : (1977326743:ℚ) < 3831728976 := by norm_num
theorem arms_leaves_2d_box_1_1 : (14681377947951104:ℚ) < 26345121306126507 := by norm_num
theorem arms_leaves_2d_box_1_2 : (116490258898219:ℚ) < 738835897016808 := by norm_num
theorem arms_leaves_2d_box_2_0 : (73039787676416:ℚ) < 92354487127101 := by norm_num
theorem arms_leaves_2d_box_2_1 : (34271896307633:ℚ) < 82881149246208 := by norm_num
theorem arms_leaves_2d_box_2_2 : (293434556416:ℚ) < 2883251953125 := by norm_num
theorem arms_leaves_2d_box_3_0 : (25949267578125:ℚ) < 27892330061824 := by norm_num
theorem arms_leaves_2d_box_3_1 : (1275321459751944192:ℚ) < 3823778578173828125 := by norm_num
theorem arms_leaves_2d_box_3_2 : (132239526912:ℚ) < 1801152661463 := by norm_num
theorem arms_leaves_2d_box_4_0 : (86959512306484890624:ℚ) < 87946907297998046875 := by norm_num
theorem arms_leaves_2d_box_4_1 : (76293945312500000:ℚ) < 271799340072751089 := by norm_num
theorem arms_leaves_2d_box_4_2 : (106570876280498368282624:ℚ) < 1884016215314563749249761 := by norm_num
theorem arms_leaves_2d_box_5_0 : ((1:ℚ)/1) = 1 := by norm_num
theorem arms_leaves_2d_box_5_1 : (10491991762245509981011968:ℚ) < 43332372952234966232744503 := by norm_num
theorem arms_leaves_2d_box_5_2 : (23461445241650390625:ℚ) < 516133234622942600192 := by norm_num

end LatticeBox
end G1
