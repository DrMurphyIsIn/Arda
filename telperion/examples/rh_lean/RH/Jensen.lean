/- telperion 0.1.3 | family JensenXi | input-hash d022e43bda8657a2
   4 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace JensenXi

/-- Worst-corner bridge for the cubic Jensen discriminant: a strict rational
    margin on the enclosures forces `Delta(g) > 0`, hence three real roots. -/
theorem cubic_jensen_pos_of_enclosure
    {g0 g1 g2 g3 lo0 lo1 lo2 lo3 hi0 hi1 hi2 hi3 : ℝ}
    (l0 : 0 ≤ lo0) (l1 : 0 ≤ lo1) (l2 : 0 ≤ lo2) (l3 : 0 ≤ lo3)
    (a0 : lo0 ≤ g0) (a1 : lo1 ≤ g1) (a2 : lo2 ≤ g2) (a3 : lo3 ≤ g3)
    (b0 : g0 ≤ hi0) (b1 : g1 ≤ hi1) (b2 : g2 ≤ hi2) (b3 : g3 ≤ hi3)
    (hm : 0 < 162*lo0*lo1*lo2*lo3 + 81*lo1*lo1*lo2*lo2
             - 108*hi0*hi2*hi2*hi2 - 108*hi1*hi1*hi1*hi3 - 27*hi0*hi0*hi3*hi3) :
    0 < 162*g0*g1*g2*g3 + 81*g1*g1*g2*g2
        - 108*g0*g2*g2*g2 - 108*g1*g1*g1*g3 - 27*g0*g0*g3*g3 := by
  have n0 : (0:ℝ) ≤ g0 := le_trans l0 a0
  have n1 : (0:ℝ) ≤ g1 := le_trans l1 a1
  have n2 : (0:ℝ) ≤ g2 := le_trans l2 a2
  have n3 : (0:ℝ) ≤ g3 := le_trans l3 a3
  have p1 : lo0*lo1*lo2*lo3 ≤ g0*g1*g2*g3 :=
    mul_le_mul (mul_le_mul (mul_le_mul a0 a1 l1 n0) a2 l2 (mul_nonneg n0 n1)) a3 l3
      (mul_nonneg (mul_nonneg n0 n1) n2)
  have p2 : lo1*lo1*lo2*lo2 ≤ g1*g1*g2*g2 :=
    mul_le_mul (mul_le_mul (mul_le_mul a1 a1 l1 n1) a2 l2 (mul_nonneg n1 n1)) a2 l2
      (mul_nonneg (mul_nonneg n1 n1) n2)
  have q1 : g0*g2*g2*g2 ≤ hi0*hi2*hi2*hi2 :=
    mul_le_mul (mul_le_mul (mul_le_mul b0 b2 n2 (le_trans n0 b0)) b2 n2
      (mul_nonneg (le_trans n0 b0) (le_trans n2 b2))) b2 n2
      (mul_nonneg (mul_nonneg (le_trans n0 b0) (le_trans n2 b2)) (le_trans n2 b2))
  have q2 : g1*g1*g1*g3 ≤ hi1*hi1*hi1*hi3 :=
    mul_le_mul (mul_le_mul (mul_le_mul b1 b1 n1 (le_trans n1 b1)) b1 n1
      (mul_nonneg (le_trans n1 b1) (le_trans n1 b1))) b3 n3
      (mul_nonneg (mul_nonneg (le_trans n1 b1) (le_trans n1 b1)) (le_trans n1 b1))
  have q3 : g0*g0*g3*g3 ≤ hi0*hi0*hi3*hi3 :=
    mul_le_mul (mul_le_mul (mul_le_mul b0 b0 n0 (le_trans n0 b0)) b3 n3
      (mul_nonneg (le_trans n0 b0) (le_trans n0 b0))) b3 n3
      (mul_nonneg (mul_nonneg (le_trans n0 b0) (le_trans n0 b0)) (le_trans n3 b3))
  nlinarith [p1, p2, q1, q2, q3, hm]



-- shift n=0: J^{3,0} hyperbolic (gamma_0..gamma_3); worst-corner Delta_lo = 126059474115809745572529862363759611207360220962031118825426967457394680009127502442641/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 > 0
theorem cubic_jensen_xi_n0 {g0 g1 g2 g3 : ℝ}
    (a0 : ((4971207781883141099127737 : ℝ) / 10000000000000000000000000) ≤ g0) (b0 : g0 ≤ ((2485603890941570549563869 : ℝ) / 5000000000000000000000000))
    (a1 : ((114859721575727187676249 : ℝ) / 10000000000000000000000000) ≤ g1) (b1 : g1 ≤ ((91887777260581750141 : ℝ) / 8000000000000000000000))
    (a2 : ((1234520180703180068903 : ℝ) / 5000000000000000000000000) ≤ g2) (b2 : g2 ≤ ((2469040361406360137807 : ℝ) / 10000000000000000000000000))
    (a3 : ((78033326379893163 : ℝ) / 15625000000000000000000) ≤ g3) (b3 : g3 ≤ ((49941328883131624321 : ℝ) / 10000000000000000000000000)) :
    0 < 162*g0*g1*g2*g3 + 81*g1*g1*g2*g2 - 108*g0*g2*g2*g2 - 108*g1*g1*g1*g3 - 27*g0*g0*g3*g3 :=
  cubic_jensen_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a0 a1 a2 a3 b0 b1 b2 b3 (by norm_num)

-- shift n=1: J^{3,1} hyperbolic (gamma_1..gamma_4); worst-corner Delta_lo = 15556983606634278253042607297279128995455969289157838799362061032035326402483837/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 > 0
theorem cubic_jensen_xi_n1 {g0 g1 g2 g3 : ℝ}
    (a0 : ((114859721575727187676249 : ℝ) / 10000000000000000000000000) ≤ g0) (b0 : g0 ≤ ((91887777260581750141 : ℝ) / 8000000000000000000000))
    (a1 : ((1234520180703180068903 : ℝ) / 5000000000000000000000000) ≤ g1) (b1 : g1 ≤ ((2469040361406360137807 : ℝ) / 10000000000000000000000000))
    (a2 : ((78033326379893163 : ℝ) / 15625000000000000000000) ≤ g2) (b2 : g2 ≤ ((49941328883131624321 : ℝ) / 10000000000000000000000000))
    (a3 : ((958134372322592921 : ℝ) / 10000000000000000000000000) ≤ g3) (b3 : g3 ≤ ((479067186161296461 : ℝ) / 5000000000000000000000000)) :
    0 < 162*g0*g1*g2*g3 + 81*g1*g1*g2*g2 - 108*g0*g2*g2*g2 - 108*g1*g1*g1*g3 - 27*g0*g0*g3*g3 :=
  cubic_jensen_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a0 a1 a2 a3 b0 b1 b2 b3 (by norm_num)

-- shift n=2: J^{3,2} hyperbolic (gamma_2..gamma_5); worst-corner Delta_lo = 6525074675464172323759877243612452003363160790722723185724144088309504903/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 > 0
theorem cubic_jensen_xi_n2 {g0 g1 g2 g3 : ℝ}
    (a0 : ((1234520180703180068903 : ℝ) / 5000000000000000000000000) ≤ g0) (b0 : g0 ≤ ((2469040361406360137807 : ℝ) / 10000000000000000000000000))
    (a1 : ((78033326379893163 : ℝ) / 15625000000000000000000) ≤ g1) (b1 : g1 ≤ ((49941328883131624321 : ℝ) / 10000000000000000000000000))
    (a2 : ((958134372322592921 : ℝ) / 10000000000000000000000000) ≤ g2) (b2 : g2 ≤ ((479067186161296461 : ℝ) / 5000000000000000000000000))
    (a3 : ((17539230912133153 : ℝ) / 10000000000000000000000000) ≤ g3) (b3 : g3 ≤ ((8769615456066577 : ℝ) / 5000000000000000000000000)) :
    0 < 162*g0*g1*g2*g3 + 81*g1*g1*g2*g2 - 108*g0*g2*g2*g2 - 108*g1*g1*g1*g3 - 27*g0*g0*g3*g3 :=
  cubic_jensen_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a0 a1 a2 a3 b0 b1 b2 b3 (by norm_num)

end JensenXi
