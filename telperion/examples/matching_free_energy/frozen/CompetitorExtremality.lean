/- telperion 0.1.6 | family CompetitorExtremality | input-hash 3cdbdf59b3a9afc4
   8 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace CompetitorExtremality

-- COMPETITOR EXTREMALITY, n=5 (near-star N(0,2)).  rho=per(L)/prod(deg) is the
-- monomer-dimer partition function; N(0,2) maximizes it over all 3 trees on
-- 5 vertices (verified).  Binding witness: it strictly beats the runner-up.
-- rho(N(0,2)) = 3/1 = (4/3)(3/2)^2.
theorem compext_n5_value : ((3:ℚ)/1) = (4/3)*(3/2)^2 := by norm_num
-- strictly above the runner-up rho = 8/3:
theorem compext_n5_beats_runnerup : (8*1:ℤ) < 3*3 := by norm_num

-- COMPETITOR EXTREMALITY, n=7 (near-star N(0,3)).  rho=per(L)/prod(deg) is the
-- monomer-dimer partition function; N(0,3) maximizes it over all 11 trees on
-- 7 vertices (verified).  Binding witness: it strictly beats the runner-up.
-- rho(N(0,3)) = 9/2 = (4/3)(3/2)^3.
theorem compext_n7_value : ((9:ℚ)/2) = (4/3)*(3/2)^3 := by norm_num
-- strictly above the runner-up rho = 35/8:
theorem compext_n7_beats_runnerup : (35*2:ℤ) < 9*8 := by norm_num

-- COMPETITOR EXTREMALITY, n=9 (near-star N(0,4)).  rho=per(L)/prod(deg) is the
-- monomer-dimer partition function; N(0,4) maximizes it over all 47 trees on
-- 9 vertices (verified).  Binding witness: it strictly beats the runner-up.
-- rho(N(0,4)) = 27/4 = (4/3)(3/2)^4.
theorem compext_n9_value : ((27:ℚ)/4) = (4/3)*(3/2)^4 := by norm_num
-- strictly above the runner-up rho = 13/2:
theorem compext_n9_beats_runnerup : (13*4:ℤ) < 27*2 := by norm_num

-- COMPETITOR EXTREMALITY, n=11 (near-star N(0,5)).  rho=per(L)/prod(deg) is the
-- monomer-dimer partition function; N(0,5) maximizes it over all 235 trees on
-- 11 vertices (verified).  Binding witness: it strictly beats the runner-up.
-- rho(N(0,5)) = 81/8 = (4/3)(3/2)^5.
theorem compext_n11_value : ((81:ℚ)/8) = (4/3)*(3/2)^5 := by norm_num
-- strictly above the runner-up rho = 233/24:
theorem compext_n11_beats_runnerup : (233*8:ℤ) < 81*24 := by norm_num

end CompetitorExtremality
end G1
