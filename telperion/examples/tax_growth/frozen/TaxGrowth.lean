/- telperion 0.1.3 | family TaxGrowth | input-hash e5ec002935dd0570
   22 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace TaxGrowth

theorem tax_const_c0 : ((3:ℚ)/2)^(11*0) * (64/621)^(1+2*0) = (2^6 : ℚ) / (23^1 * 3^3) := by norm_num
theorem tax_const_c1 : ((3:ℚ)/2)^(11*1) * (64/621)^(1+2*1) = (2^7 * 3^2 : ℚ) / (23^3) := by norm_num
theorem tax_const_c2 : ((3:ℚ)/2)^(11*2) * (64/621)^(1+2*2) = (2^8 * 3^7 : ℚ) / (23^5) := by norm_num
theorem tax_const_c3 : ((3:ℚ)/2)^(11*3) * (64/621)^(1+2*3) = (2^9 * 3^12 : ℚ) / (23^7) := by norm_num
theorem tax_const_c4 : ((3:ℚ)/2)^(11*4) * (64/621)^(1+2*4) = (2^10 * 3^17 : ℚ) / (23^9) := by norm_num
theorem tax_const_c5 : ((3:ℚ)/2)^(11*5) * (64/621)^(1+2*5) = (2^11 * 3^22 : ℚ) / (23^11) := by norm_num
theorem tax_const_c6 : ((3:ℚ)/2)^(11*6) * (64/621)^(1+2*6) = (2^12 * 3^27 : ℚ) / (23^13) := by norm_num
theorem growth_env_c0_r1 : ((9:ℚ)/6)^11 = 177147/2048 := by norm_num
theorem growth_ge_one_c0_r1 (S : ℝ) (h0 : 0 ≤ S) :
    (1:ℝ) ≤ (((6:ℝ) + 3*S)/6)^11 := by
  have hb : (1:ℝ) ≤ ((6:ℝ) + 3*S)/6 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
  calc (1:ℝ) = 1^11 := by norm_num
    _ ≤ (((6:ℝ) + 3*S)/6)^11 := by gcongr
theorem growth_le_env_c0_r1 (S : ℝ) (h0 : 0 ≤ S) (h1 : S ≤ 1) :
    (((6:ℝ) + 3*S)/6)^11 ≤ ((3:ℝ)/2)^11 := by
  have hb : ((6:ℝ) + 3*S)/6 ≤ (3:ℝ)/2 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have hpos : (0:ℝ) ≤ ((6:ℝ) + 3*S)/6 := by positivity
  gcongr
theorem growth_env_c0_r2 : ((15:ℚ)/9)^11 = 48828125/177147 := by norm_num
theorem growth_ge_one_c0_r2 (S : ℝ) (h0 : 0 ≤ S) :
    (1:ℝ) ≤ (((9:ℝ) + 3*S)/9)^11 := by
  have hb : (1:ℝ) ≤ ((9:ℝ) + 3*S)/9 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
  calc (1:ℝ) = 1^11 := by norm_num
    _ ≤ (((9:ℝ) + 3*S)/9)^11 := by gcongr
theorem growth_le_env_c0_r2 (S : ℝ) (h0 : 0 ≤ S) (h1 : S ≤ 2) :
    (((9:ℝ) + 3*S)/9)^11 ≤ ((5:ℝ)/3)^11 := by
  have hb : ((9:ℝ) + 3*S)/9 ≤ (5:ℝ)/3 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have hpos : (0:ℝ) ≤ ((9:ℝ) + 3*S)/9 := by positivity
  gcongr
theorem growth_env_c0_r3 : ((21:ℚ)/12)^11 = 1977326743/4194304 := by norm_num
theorem growth_ge_one_c0_r3 (S : ℝ) (h0 : 0 ≤ S) :
    (1:ℝ) ≤ (((12:ℝ) + 3*S)/12)^11 := by
  have hb : (1:ℝ) ≤ ((12:ℝ) + 3*S)/12 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
  calc (1:ℝ) = 1^11 := by norm_num
    _ ≤ (((12:ℝ) + 3*S)/12)^11 := by gcongr
theorem growth_le_env_c0_r3 (S : ℝ) (h0 : 0 ≤ S) (h1 : S ≤ 3) :
    (((12:ℝ) + 3*S)/12)^11 ≤ ((7:ℝ)/4)^11 := by
  have hb : ((12:ℝ) + 3*S)/12 ≤ (7:ℝ)/4 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have hpos : (0:ℝ) ≤ ((12:ℝ) + 3*S)/12 := by positivity
  gcongr
theorem growth_env_c1_r1 : ((13:ℚ)/9)^11 = 1792160394037/31381059609 := by norm_num
theorem growth_ge_one_c1_r1 (S : ℝ) (h0 : 0 ≤ S) :
    (1:ℝ) ≤ (((10:ℝ) + 3*S)/9)^11 := by
  have hb : (1:ℝ) ≤ ((10:ℝ) + 3*S)/9 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
  calc (1:ℝ) = 1^11 := by norm_num
    _ ≤ (((10:ℝ) + 3*S)/9)^11 := by gcongr
theorem growth_le_env_c1_r1 (S : ℝ) (h0 : 0 ≤ S) (h1 : S ≤ 1) :
    (((10:ℝ) + 3*S)/9)^11 ≤ ((13:ℝ)/9)^11 := by
  have hb : ((10:ℝ) + 3*S)/9 ≤ (13:ℝ)/9 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have hpos : (0:ℝ) ≤ ((10:ℝ) + 3*S)/9 := by positivity
  gcongr
theorem growth_env_c1_r2 : ((19:ℚ)/12)^11 = 116490258898219/743008370688 := by norm_num
theorem growth_ge_one_c1_r2 (S : ℝ) (h0 : 0 ≤ S) :
    (1:ℝ) ≤ (((13:ℝ) + 3*S)/12)^11 := by
  have hb : (1:ℝ) ≤ ((13:ℝ) + 3*S)/12 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
  calc (1:ℝ) = 1^11 := by norm_num
    _ ≤ (((13:ℝ) + 3*S)/12)^11 := by gcongr
theorem growth_le_env_c1_r2 (S : ℝ) (h0 : 0 ≤ S) (h1 : S ≤ 2) :
    (((13:ℝ) + 3*S)/12)^11 ≤ ((19:ℝ)/12)^11 := by
  have hb : ((13:ℝ) + 3*S)/12 ≤ (19:ℝ)/12 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have hpos : (0:ℝ) ≤ ((13:ℝ) + 3*S)/12 := by positivity
  gcongr

end TaxGrowth
end G1
