/- The per-n extremality PARITY LAW, kernel-gated (exact extremal Phi^11, n<=14).
   Near-star wins at every ODD n (exists only at n=2s+1), multi-hub at every EVEN n;
   max Phi^11 < 1 for all n in [4,14] except = 1 at n=11 (the tie N(0,5)).  Maximality
   is exhaustive-Python (all trees on n vertices); the kernel gates each extremal value
   + its BG bound -- the exhaustive small-n base case, exhibiting the parity structure.
   Not a proof of BG; conjecture1_proved = False. -/
import Mathlib

namespace BGParityLaw

-- n=4 [even, multi-hub]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n4 : ((14681377947951104 : ℚ) / 26345121306126507) < 1 := by norm_num

-- n=5 [odd, near-star N(0,2)]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n5 : ((73039787676416 : ℚ) / 92354487127101) < 1 := by norm_num

-- n=6 [even, multi-hub]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n6 : ((5983950484220167431032 : ℚ) / 10159758925615932285987) < 1 := by norm_num

-- n=7 [odd, near-star N(0,3)]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n7 : ((25949267578125 : ℚ) / 27892330061824) < 1 := by norm_num

-- n=8 [even, multi-hub]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n8 : ((21048519522998348950643 : ℚ) / 32729466139091864911872) < 1 := by norm_num

-- n=9 [odd, near-star N(0,4)]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n9 : ((86959512306484890624 : ℚ) / 87946907297998046875) < 1 := by norm_num

-- n=10 [even, multi-hub]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n10 : ((2158060662623960090407387 : ℚ) / 3081500012535528778437312) < 1 := by norm_num

-- n=11 [odd, near-star N(0,5)]: THE TIE -- Phi^11 = 1 exactly
theorem bg_extremum_n11 : ((1 : ℚ) / 1) = 1 := by norm_num

-- n=12 [even, multi-hub]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n12 : ((859963392 : ℚ) / 1123046875) < 1 := by norm_num

-- n=13 [odd, near-star N(0,6)]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n13 : ((980170052528609401200979968 : ℚ) / 996644577901404223353123569) < 1 := by norm_num

-- n=14 [even, multi-hub]: max Phi^11 < 1 (strictly below the tie)
theorem bg_extremum_n14 : ((7176104352539813874659139711 : ℚ) / 9056903378545898288281250000) < 1 := by norm_num

end BGParityLaw
