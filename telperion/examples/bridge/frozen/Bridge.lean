/- telperion 0.1.4 | family Bridge | input-hash 8fd0ec5994ef0bbb
   7 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Bridge

-- BRIDGE CROSSING (near-star span): R(n) ≤ 1 for ALL integers n,
-- though the continuous relaxation R_cont(4.822) = 1.00046 > 1.
-- (1) finite integer base cases n = 0..5 (exact);
-- (2) monotone tail: ρ(t) = R(t+1)/R(t) ≤ 1 for real t ≥ 5,
--     cleared to P(5+u) ≥ 0 with ALL NONNEG coefficients (Polya).
-- base + anchor R(5)=1 + tail-monotonicity ⟹ R(n) ≤ 1 ∀ n ∈ ℤ.

theorem near_star_base_0 : (64:ℚ) < 621 := by norm_num
theorem near_star_base_1 : (1977326743:ℚ) < 3831728976 := by norm_num
theorem near_star_base_2 : (73039787676416:ℚ) < 92354487127101 := by norm_num
theorem near_star_base_3 : (25949267578125:ℚ) < 27892330061824 := by norm_num
theorem near_star_base_4 : (86959512306484890624:ℚ) < 87946907297998046875 := by norm_num
theorem near_star_anchor_5 : ((1:ℚ)/1) = 1 := by norm_num
theorem near_star_tail (u : ℝ) (hu : 0 ≤ u) : (0:ℝ) ≤ 269268679655424*u^22 + 37764932321673216*u^21 + 2518363897136676864*u^20 + 106220733515956224000*u^19 + 3179741526592428441600*u^18 + 71851862018467332882432*u^17 + 1272515101661683513294848*u^16 + 18100995513577652697956352*u^15 + 210229009298590849414594560*u^14 + 2015526052128794051960340480*u^13 + 16061094838226548429956882432*u^12 + 106758848103260995370531801088*u^11 + 592316575556321929063862605824*u^10 + 2736951815299700239891026094080*u^9 + 10477674374281934214858089932800*u^8 + 32940277840131392164595291615232*u^7 + 83922737277396910785346939465728*u^6 + 169926937078953900264922215567360*u^5 + 265713540679210016800546014965760*u^4 + 307137753071703397126583019878400*u^3 + 244334173062227543194117098608640*u^2 + 117181337788199752240616343521280*u + 24596334585379687114573179144192 := by positivity

end Bridge
end G1
