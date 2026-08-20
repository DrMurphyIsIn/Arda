/- telperion 0.1.6 | family LegsCerts | input-hash 5ce24dd1cf01c61a
   48 theorems, 48 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace L
namespace Legs

theorem legs_ell2_reference : ((621 : ℚ) / 64) = ((621 : ℚ) / 64) := by norm_num

theorem legs_ell1_c1 : ((3 : ℚ) / 2) ^ 11 < ((621 : ℚ) / 64) ^ 2 := by norm_num

theorem legs_ell1_c2 : ((5 : ℚ) / 3) ^ 11 < ((621 : ℚ) / 64) ^ 3 := by norm_num

theorem legs_ell1_c3 : ((7 : ℚ) / 4) ^ 11 < ((621 : ℚ) / 64) ^ 4 := by norm_num

theorem legs_ell1_tail : (2 : ℚ) ^ 11 < ((621 : ℚ) / 64) ^ 5 := by norm_num

theorem legs_beta_step : ((583 : ℚ) / 400) ≤ ((483 : ℚ) / 400) ^ 2 := by norm_num

theorem legs_phi3_base : ((7 : ℚ) / 4) ≤ ((483 : ℚ) / 400) ^ 3 := by norm_num

theorem legs_phi4_base : ((17 : ℚ) / 8) ≤ ((483 : ℚ) / 400) ^ 4 := by norm_num

theorem legs_bignum : ((483 : ℚ) / 400) ^ 253 * (3 / 2) ^ 11 < ((621 : ℚ) / 64) ^ 23 := by norm_num

theorem legs_ell3_c1 : ((17 : ℚ) / 8) ^ 11 < ((621 : ℚ) / 64) ^ 4 := by norm_num

theorem legs_ell3_c2 : ((63 : ℚ) / 16) ^ 11 < ((621 : ℚ) / 64) ^ 7 := by norm_num

theorem legs_ell3_c3 : ((1813 : ℚ) / 256) ^ 11 < ((621 : ℚ) / 64) ^ 10 := by norm_num

theorem legs_ell3_c4 : ((16121 : ℚ) / 1280) ^ 11 < ((621 : ℚ) / 64) ^ 13 := by norm_num

theorem legs_ell3_c5 : ((45619 : ℚ) / 2048) ^ 11 < ((621 : ℚ) / 64) ^ 16 := by norm_num

theorem legs_ell3_c6 : ((160867 : ℚ) / 4096) ^ 11 < ((621 : ℚ) / 64) ^ 19 := by norm_num

theorem legs_ell3_c7 : ((9058973 : ℚ) / 131072) ^ 11 < ((621 : ℚ) / 64) ^ 22 := by norm_num

theorem legs_ell4_c1 : ((41 : ℚ) / 16) ^ 11 < ((621 : ℚ) / 64) ^ 5 := by norm_num

theorem legs_ell4_c2 : ((1105 : ℚ) / 192) ^ 11 < ((621 : ℚ) / 64) ^ 9 := by norm_num

theorem legs_ell4_c3 : ((25721 : ℚ) / 2048) ^ 11 < ((621 : ℚ) / 64) ^ 13 := by norm_num

theorem legs_ell4_c4 : ((555169 : ℚ) / 20480) ^ 11 < ((621 : ℚ) / 64) ^ 17 := by norm_num

theorem legs_ell4_c5 : ((11442377 : ℚ) / 196608) ^ 11 < ((621 : ℚ) / 64) ^ 21 := by norm_num

theorem legs_ell5_c1 : ((99 : ℚ) / 32) ^ 11 < ((621 : ℚ) / 64) ^ 6 := by norm_num

theorem legs_ell5_c2 : ((6437 : ℚ) / 768) ^ 11 < ((621 : ℚ) / 64) ^ 11 := by norm_num

theorem legs_ell5_c3 : ((361415 : ℚ) / 16384) ^ 11 < ((621 : ℚ) / 64) ^ 16 := by norm_num

theorem legs_ell5_c4 : ((18815433 : ℚ) / 327680) ^ 11 < ((621 : ℚ) / 64) ^ 21 := by norm_num

theorem legs_ell6_c1 : ((239 : ℚ) / 64) ^ 11 < ((621 : ℚ) / 64) ^ 7 := by norm_num

theorem legs_ell6_c2 : ((12507 : ℚ) / 1024) ^ 11 < ((621 : ℚ) / 64) ^ 13 := by norm_num

theorem legs_ell6_c3 : ((5086719 : ℚ) / 131072) ^ 11 < ((621 : ℚ) / 64) ^ 19 := by norm_num

theorem legs_ell7_c1 : ((577 : ℚ) / 128) ^ 11 < ((621 : ℚ) / 64) ^ 8 := by norm_num

theorem legs_ell7_c2 : ((72895 : ℚ) / 4096) ^ 11 < ((621 : ℚ) / 64) ^ 15 := by norm_num

theorem legs_ell7_c3 : ((71572613 : ℚ) / 1048576) ^ 11 < ((621 : ℚ) / 64) ^ 22 := by norm_num

theorem legs_ell8_c1 : ((1393 : ℚ) / 256) ^ 11 < ((621 : ℚ) / 64) ^ 9 := by norm_num

theorem legs_ell8_c2 : ((1274593 : ℚ) / 49152) ^ 11 < ((621 : ℚ) / 64) ^ 17 := by norm_num

theorem legs_ell9_c1 : ((3363 : ℚ) / 512) ^ 11 < ((621 : ℚ) / 64) ^ 10 := by norm_num

theorem legs_ell9_c2 : ((7428869 : ℚ) / 196608) ^ 11 < ((621 : ℚ) / 64) ^ 19 := by norm_num

theorem legs_ell10_c1 : ((8119 : ℚ) / 1024) ^ 11 < ((621 : ℚ) / 64) ^ 11 := by norm_num

theorem legs_ell10_c2 : ((14432875 : ℚ) / 262144) ^ 11 < ((621 : ℚ) / 64) ^ 21 := by norm_num

theorem legs_ell11_c1 : ((19601 : ℚ) / 2048) ^ 11 < ((621 : ℚ) / 64) ^ 12 := by norm_num

theorem legs_ell12_c1 : ((47321 : ℚ) / 4096) ^ 11 < ((621 : ℚ) / 64) ^ 13 := by norm_num

theorem legs_ell13_c1 : ((114243 : ℚ) / 8192) ^ 11 < ((621 : ℚ) / 64) ^ 14 := by norm_num

theorem legs_ell14_c1 : ((275807 : ℚ) / 16384) ^ 11 < ((621 : ℚ) / 64) ^ 15 := by norm_num

theorem legs_ell15_c1 : ((665857 : ℚ) / 32768) ^ 11 < ((621 : ℚ) / 64) ^ 16 := by norm_num

theorem legs_ell16_c1 : ((1607521 : ℚ) / 65536) ^ 11 < ((621 : ℚ) / 64) ^ 17 := by norm_num

theorem legs_ell17_c1 : ((3880899 : ℚ) / 131072) ^ 11 < ((621 : ℚ) / 64) ^ 18 := by norm_num

theorem legs_ell18_c1 : ((9369319 : ℚ) / 262144) ^ 11 < ((621 : ℚ) / 64) ^ 19 := by norm_num

theorem legs_ell19_c1 : ((22619537 : ℚ) / 524288) ^ 11 < ((621 : ℚ) / 64) ^ 20 := by norm_num

theorem legs_ell20_c1 : ((54608393 : ℚ) / 1048576) ^ 11 < ((621 : ℚ) / 64) ^ 21 := by norm_num

theorem legs_ell21_c1 : ((131836323 : ℚ) / 2097152) ^ 11 < ((621 : ℚ) / 64) ^ 22 := by norm_num

end Legs
end L
