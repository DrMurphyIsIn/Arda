/- telperion 0.1.3 | family UniformArm | input-hash 88de91b4e6ab2dc5
   3 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace UniformArm

-- uniform_armdom: ARM-DOMINANCE UNIFORM in the hub arm-count k -- adding an
-- arm beats adding competitor X for all real k >= anchor, by the
-- all-nonneg-coefficient numerator (positivity).  Lemma (1) for the key
-- competitors; leaf anchor k>=1 (its k=0 exception BUILDS the arm).

theorem uniform_armdom_arm2 (u : ℝ) (hu : 0 ≤ u) : (0:ℝ) ≤ 6471552874840064*u^11 + 118061063973371904*u^10 + 973689171868385280*u^9 + 4787589363077283840*u^8 + 15575261467140587520*u^7 + 35147072270238179328*u^6 + 56020653810878625792*u^5 + 62887479106354721280*u^4 + 48525557681999280960*u^3 + 24359547774748198320*u^2 + 7087995974538151596*u + 889550875566752661 := by positivity
theorem uniform_armdom_cherry (u : ℝ) (hu : 0 ≤ u) : (0:ℝ) ≤ 153106994167808*u^11 + 2886836498202624*u^10 + 24636190107893760*u^9 + 125481292073533440*u^8 + 423267360036618240*u^7 + 991044226177302528*u^6 + 1639533233615929344*u^5 + 1909764428072878080*u^4 + 1527027632055889920*u^3 + 791754951975102720*u^2 + 236272126917567312*u + 29930852537836191 := by positivity
theorem uniform_armdom_leaf (u : ℝ) (hu : 0 ≤ u) : (0:ℝ) ≤ 48863641600*u^11 + 1444168073216*u^10 + 19305508372480*u^9 + 153890368389120*u^8 + 811426534195200*u^7 + 2964876418301952*u^6 + 7636284000694272*u^5 + 13799372153994240*u^4 + 17023370656195200*u^3 + 13491426541336480*u^2 + 6046620166954136*u + 1105799641735078 := by positivity

end UniformArm
end G1
