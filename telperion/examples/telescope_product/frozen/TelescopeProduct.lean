/- telperion 0.1.5 | family TelescopeProduct | input-hash 76783fb8083cba5c
   22 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace TelescopeProduct

-- PRODUCT-TELESCOPE (integration end of the gauge tower).  The curvature factor
-- 1 - 1/q(t) = P1(t+1) P2(t) / (P1(t) P2(t+1)),  P1=t+1, P2=4t+3, telescopes:
-- PROD_{t<s} (1-1/q(t)) = 3(s+1)/(4s+3), giving the closed form R(s) with R(5)=1.

-- the telescoping key: numerator/denominator of 1-1/q are the shifted potentials.
theorem tele_q_factor (t : ℝ) : (t + 1) * (4*t + 7) = 4*t^2 + 11*t + 7 := by ring
theorem tele_qm1_factor (t : ℝ) : (t + 1) * (4*t + 7) - 1 = (t + 2) * (4*t + 3) := by ring
theorem tele_shift_P1 (t : ℝ) : (t + 1) + 1 = t + 2 := by ring
theorem tele_shift_P2 (t : ℝ) : (4*t + 3) + 4 = 4*t + 7 := by ring
-- per-step factor as the ratio of shifted potentials (q t ≠ 0).
theorem tele_factor (t : ℝ) (hq : (t + 1) * (4*t + 7) ≠ 0) :
    1 - 1 / ((t + 1) * (4*t + 7)) = ((t + 2) * (4*t + 3)) / ((t + 1) * (4*t + 7)) := by
  field_simp; ring
theorem tele_prod_1 : (1 - 1/7) = (6:ℚ)/7 := by norm_num
theorem tele_prod_2 : (1 - 1/7) * (1 - 1/22) = (9:ℚ)/11 := by norm_num
theorem tele_prod_3 : (1 - 1/7) * (1 - 1/22) * (1 - 1/45) = (4:ℚ)/5 := by norm_num
theorem tele_prod_4 : (1 - 1/7) * (1 - 1/22) * (1 - 1/45) * (1 - 1/76) = (15:ℚ)/19 := by norm_num
theorem tele_prod_5 : (1 - 1/7) * (1 - 1/22) * (1 - 1/45) * (1 - 1/76) * (1 - 1/115) = (18:ℚ)/23 := by norm_num
theorem tele_prod_6 : (1 - 1/7) * (1 - 1/22) * (1 - 1/45) * (1 - 1/76) * (1 - 1/115) * (1 - 1/162) = (7:ℚ)/9 := by norm_num
theorem tele_prod_7 : (1 - 1/7) * (1 - 1/22) * (1 - 1/45) * (1 - 1/76) * (1 - 1/115) * (1 - 1/162) * (1 - 1/217) = (24:ℚ)/31 := by norm_num
theorem tele_prod_8 : (1 - 1/7) * (1 - 1/22) * (1 - 1/45) * (1 - 1/76) * (1 - 1/115) * (1 - 1/162) * (1 - 1/217) * (1 - 1/280) = (27:ℚ)/35 := by norm_num
theorem tele_R_0 : (621:ℚ)/64 * (529/486)^0 * ((1:ℚ)/1)^11 = (621:ℚ)/64 := by norm_num
theorem tele_R_1 : (621:ℚ)/64 * (529/486)^1 * ((6:ℚ)/7)^11 = (3831728976:ℚ)/1977326743 := by norm_num
theorem tele_R_2 : (621:ℚ)/64 * (529/486)^2 * ((9:ℚ)/11)^11 = (92354487127101:ℚ)/73039787676416 := by norm_num
theorem tele_R_3 : (621:ℚ)/64 * (529/486)^3 * ((4:ℚ)/5)^11 = (27892330061824:ℚ)/25949267578125 := by norm_num
theorem tele_R_4 : (621:ℚ)/64 * (529/486)^4 * ((15:ℚ)/19)^11 = (87946907297998046875:ℚ)/86959512306484890624 := by norm_num
-- resonance: the integrated value hits 1 at s=5.
theorem tele_R_5 : (621:ℚ)/64 * (529/486)^5 * ((18:ℚ)/23)^11 = 1 := by norm_num
theorem tele_R_6 : (621:ℚ)/64 * (529/486)^6 * ((7:ℚ)/9)^11 = (996644577901404223353123569:ℚ)/980170052528609401200979968 := by norm_num
theorem tele_R_7 : (621:ℚ)/64 * (529/486)^7 * ((24:ℚ)/31)^11 = (279587308662309514753605632:ℚ)/265781642686659773135523693 := by norm_num
-- the meeting point of both tower ends: the lone integer identity.
theorem tele_resonance_id : (64 * 243 * 23 : ℤ) = 621 * 576 := by norm_num

end TelescopeProduct
end G1
