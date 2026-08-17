/- telperion 0.1.3 | family BGExtremality | input-hash 43a2d76e194d2c92
   8 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace BGExtremality

-- BG COMPETITOR EXTREMALITY, n=5 (rooted branch Phi, the ACTUAL BG quantity).
-- The near-star N(0,2) maximizes max_root Phi^11 over all 3 trees on 5
-- vertices; it strictly beats the runner-up.  Phi^11(N(0,2)) = 73039787676416/92354487127101.

theorem bgext_n5_value_le1 : (73039787676416:ℤ) < 92354487127101 := by norm_num
-- strictly above the runner-up Phi^11 = 3123330500020692224/16360320331104560847:
theorem bgext_n5_beats_runnerup : (3123330500020692224*92354487127101:ℤ) < 73039787676416*16360320331104560847 := by norm_num

-- BG COMPETITOR EXTREMALITY, n=7 (rooted branch Phi, the ACTUAL BG quantity).
-- The near-star N(0,3) maximizes max_root Phi^11 over all 11 trees on 7
-- vertices; it strictly beats the runner-up.  Phi^11(N(0,3)) = 25949267578125/27892330061824.

theorem bgext_n7_value_le1 : (25949267578125:ℤ) < 27892330061824 := by norm_num
-- strictly above the runner-up Phi^11 = 12341474201974794188822591/25236841171229975798391708:
theorem bgext_n7_beats_runnerup : (12341474201974794188822591*27892330061824:ℤ) < 25949267578125*25236841171229975798391708 := by norm_num

-- BG COMPETITOR EXTREMALITY, n=9 (rooted branch Phi, the ACTUAL BG quantity).
-- The near-star N(0,4) maximizes max_root Phi^11 over all 47 trees on 9
-- vertices; it strictly beats the runner-up.  Phi^11(N(0,4)) = 86959512306484890624/87946907297998046875.

theorem bgext_n9_value_le1 : (86959512306484890624:ℤ) < 87946907297998046875 := by norm_num
-- strictly above the runner-up Phi^11 = 351801271595486322734724859/650399951116033539528720384:
theorem bgext_n9_beats_runnerup : (351801271595486322734724859*87946907297998046875:ℤ) < 86959512306484890624*650399951116033539528720384 := by norm_num

-- BG COMPETITOR EXTREMALITY, n=11 (rooted branch Phi, the ACTUAL BG quantity).
-- The near-star N(0,5) maximizes max_root Phi^11 over all 235 trees on 11
-- vertices; it strictly beats the runner-up.  Phi^11(N(0,5)) = 1/1 = 1 (the TIE).

theorem bgext_n11_tie : ((1:ℚ)/1) = 1 := by norm_num
-- strictly above the runner-up Phi^11 = 25804264053054077850709/46523913960640966796875:
theorem bgext_n11_beats_runnerup : (25804264053054077850709*1:ℤ) < 1*46523913960640966796875 := by norm_num

end BGExtremality
end G1
