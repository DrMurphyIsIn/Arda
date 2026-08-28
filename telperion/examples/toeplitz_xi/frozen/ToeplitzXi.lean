/- telperion 0.1.3 | family ToeplitzXi | input-hash 638cf0db730c9c0d
   5 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace ToeplitzXi

/-- Worst-corner bridge for the 3x3 Toeplitz minor: a strict rational margin on
    the enclosures forces the minor positive (total-positivity necessary cond.). -/
theorem toeplitz3_pos_of_enclosure
    {g0 g1 g2 g3 g4 lo0 lo1 lo2 lo3 lo4 hi0 hi1 hi2 hi3 hi4 : ℝ}
    (l0 : 0 ≤ lo0) (l1 : 0 ≤ lo1) (l2 : 0 ≤ lo2) (l3 : 0 ≤ lo3) (l4 : 0 ≤ lo4)
    (a0 : lo0 ≤ g0) (a1 : lo1 ≤ g1) (a2 : lo2 ≤ g2) (a3 : lo3 ≤ g3) (a4 : lo4 ≤ g4)
    (b0 : g0 ≤ hi0) (b1 : g1 ≤ hi1) (b2 : g2 ≤ hi2) (b3 : g3 ≤ hi3) (b4 : g4 ≤ hi4)
    (hm : 0 < lo2*lo2*lo2 + lo1*lo1*lo4 + lo0*lo3*lo3
             - 2*hi1*hi2*hi3 - hi0*hi2*hi4) :
    0 < g2*g2*g2 + g1*g1*g4 + g0*g3*g3 - 2*g1*g2*g3 - g0*g2*g4 := by
  have n0 : (0:ℝ) ≤ g0 := le_trans l0 a0
  have n1 : (0:ℝ) ≤ g1 := le_trans l1 a1
  have n2 : (0:ℝ) ≤ g2 := le_trans l2 a2
  have n3 : (0:ℝ) ≤ g3 := le_trans l3 a3
  have n4 : (0:ℝ) ≤ g4 := le_trans l4 a4
  have p1 : lo2*lo2*lo2 ≤ g2*g2*g2 :=
    mul_le_mul (mul_le_mul a2 a2 l2 n2) a2 l2 (mul_nonneg n2 n2)
  have p2 : lo1*lo1*lo4 ≤ g1*g1*g4 :=
    mul_le_mul (mul_le_mul a1 a1 l1 n1) a4 l4 (mul_nonneg n1 n1)
  have p3 : lo0*lo3*lo3 ≤ g0*g3*g3 :=
    mul_le_mul (mul_le_mul a0 a3 l3 n0) a3 l3 (mul_nonneg n0 n3)
  have q1 : g1*g2*g3 ≤ hi1*hi2*hi3 :=
    mul_le_mul (mul_le_mul b1 b2 n2 (le_trans n1 b1)) b3 n3
      (mul_nonneg (le_trans n1 b1) (le_trans n2 b2))
  have q2 : g0*g2*g4 ≤ hi0*hi2*hi4 :=
    mul_le_mul (mul_le_mul b0 b2 n2 (le_trans n0 b0)) b4 n4
      (mul_nonneg (le_trans n0 b0) (le_trans n2 b2))
  nlinarith [p1, p2, p3, q1, q2, hm]



-- m=2: 3x3 Toeplitz minor of a_0..a_4 positive (worst-corner 73523252176464714373638532537384443963608739393857999604982977/500000000000000000000000000000000000000000000000000000000000000000000000000 > 0)
theorem toeplitz3_xi_m2 {g0 g1 g2 g3 g4 : ℝ}
    (a0 : ((4971207781883141099127737 : ℝ) / 10000000000000000000000000) ≤ g0) (b0 : g0 ≤ ((2485603890941570549563869 : ℝ) / 5000000000000000000000000))
    (a1 : ((114859721575727187676249 : ℝ) / 10000000000000000000000000) ≤ g1) (b1 : g1 ≤ ((91887777260581750141 : ℝ) / 8000000000000000000000))
    (a2 : ((1234520180703180068903 : ℝ) / 10000000000000000000000000) ≤ g2) (b2 : g2 ≤ ((154315022587897508613 : ℝ) / 1250000000000000000000000))
    (a3 : ((26011108793297721 : ℝ) / 31250000000000000000000) ≤ g3) (b3 : g3 ≤ ((8323554813855270721 : ℝ) / 10000000000000000000000000))
    (a4 : ((39922265513441371 : ℝ) / 10000000000000000000000000) ≤ g4) (b4 : g4 ≤ ((9980566378360343 : ℝ) / 2500000000000000000000000)) :
    0 < g2*g2*g2 + g1*g1*g4 + g0*g3*g3 - 2*g1*g2*g3 - g0*g2*g4 :=
  toeplitz3_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 (by norm_num)

-- m=3: 3x3 Toeplitz minor of a_1..a_5 positive (worst-corner 11149777074851912484226796828809943072313976221437235197/500000000000000000000000000000000000000000000000000000000000000000000000000 > 0)
theorem toeplitz3_xi_m3 {g0 g1 g2 g3 g4 : ℝ}
    (a0 : ((114859721575727187676249 : ℝ) / 10000000000000000000000000) ≤ g0) (b0 : g0 ≤ ((91887777260581750141 : ℝ) / 8000000000000000000000))
    (a1 : ((1234520180703180068903 : ℝ) / 10000000000000000000000000) ≤ g1) (b1 : g1 ≤ ((154315022587897508613 : ℝ) / 1250000000000000000000000))
    (a2 : ((26011108793297721 : ℝ) / 31250000000000000000000) ≤ g2) (b2 : g2 ≤ ((8323554813855270721 : ℝ) / 10000000000000000000000000))
    (a3 : ((39922265513441371 : ℝ) / 10000000000000000000000000) ≤ g3) (b3 : g3 ≤ ((9980566378360343 : ℝ) / 2500000000000000000000000))
    (a4 : ((146160257601109 : ℝ) / 10000000000000000000000000) ≤ g4) (b4 : g4 ≤ ((14616025760111 : ℝ) / 1000000000000000000000000)) :
    0 < g2*g2*g2 + g1*g1*g4 + g0*g3*g3 - 2*g1*g2*g3 - g0*g2*g4 :=
  toeplitz3_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 (by norm_num)

-- m=4: 3x3 Toeplitz minor of a_2..a_6 positive (worst-corner 705708870796729186573884436093064647847728163681/500000000000000000000000000000000000000000000000000000000000000000000000000 > 0)
theorem toeplitz3_xi_m4 {g0 g1 g2 g3 g4 : ℝ}
    (a0 : ((1234520180703180068903 : ℝ) / 10000000000000000000000000) ≤ g0) (b0 : g0 ≤ ((154315022587897508613 : ℝ) / 1250000000000000000000000))
    (a1 : ((26011108793297721 : ℝ) / 31250000000000000000000) ≤ g1) (b1 : g1 ≤ ((8323554813855270721 : ℝ) / 10000000000000000000000000))
    (a2 : ((39922265513441371 : ℝ) / 10000000000000000000000000) ≤ g2) (b2 : g2 ≤ ((9980566378360343 : ℝ) / 2500000000000000000000000))
    (a3 : ((146160257601109 : ℝ) / 10000000000000000000000000) ≤ g3) (b3 : g3 ≤ ((14616025760111 : ℝ) / 1000000000000000000000000))
    (a4 : ((427454004553 : ℝ) / 10000000000000000000000000) ≤ g4) (b4 : g4 ≤ ((213727002277 : ℝ) / 5000000000000000000000000)) :
    0 < g2*g2*g2 + g1*g1*g4 + g0*g3*g3 - 2*g1*g2*g3 - g0*g2*g4 :=
  toeplitz3_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 (by norm_num)

-- m=5: 3x3 Toeplitz minor of a_3..a_7 positive (worst-corner 21856936476619467416645431254316070683371/500000000000000000000000000000000000000000000000000000000000000000000000000 > 0)
theorem toeplitz3_xi_m5 {g0 g1 g2 g3 g4 : ℝ}
    (a0 : ((26011108793297721 : ℝ) / 31250000000000000000000) ≤ g0) (b0 : g0 ≤ ((8323554813855270721 : ℝ) / 10000000000000000000000000))
    (a1 : ((39922265513441371 : ℝ) / 10000000000000000000000000) ≤ g1) (b1 : g1 ≤ ((9980566378360343 : ℝ) / 2500000000000000000000000))
    (a2 : ((146160257601109 : ℝ) / 10000000000000000000000000) ≤ g2) (b2 : g2 ≤ ((14616025760111 : ℝ) / 1000000000000000000000000))
    (a3 : ((427454004553 : ℝ) / 10000000000000000000000000) ≤ g3) (b3 : g3 ≤ ((213727002277 : ℝ) / 5000000000000000000000000))
    (a4 : ((1030962613 : ℝ) / 10000000000000000000000000) ≤ g4) (b4 : g4 ≤ ((515481307 : ℝ) / 5000000000000000000000000)) :
    0 < g2*g2*g2 + g1*g1*g4 + g0*g3*g3 - 2*g1*g2*g3 - g0*g2*g4 :=
  toeplitz3_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 (by norm_num)

end ToeplitzXi
