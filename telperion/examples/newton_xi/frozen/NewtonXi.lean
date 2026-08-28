/- telperion 0.1.3 | family NewtonXi | input-hash 57bef48e4c60762b
   7 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace NewtonXi

/-- Worst-corner bridge: a strict rational margin `hi0*hi2 < lo1^2` on the
    enclosures forces the Turan inequality `a0*a2 < a1^2` for every real triple
    inside them.  (Monotonicity: `a0*a2 <= hi0*hi2 < lo1^2 <= a1^2`.) -/
theorem turan_from_enclosure {a0 a1 a2 lo1 hi0 hi2 : ℝ}
    (hlo1 : 0 ≤ lo1) (h1 : lo1 ≤ a1)
    (hp0 : 0 ≤ a0) (h0 : a0 ≤ hi0)
    (hp2 : 0 ≤ a2) (h2 : a2 ≤ hi2)
    (hm : hi0 * hi2 < lo1 ^ 2) :
    a0 * a2 < a1 ^ 2 := by
  have hprod : a0 * a2 ≤ hi0 * hi2 := mul_le_mul h0 h2 hp2 (le_trans hp0 h0)
  have hsq : lo1 ^ 2 ≤ a1 ^ 2 := by
    nlinarith [mul_le_mul h1 h1 hlo1 (le_trans hlo1 h1)]
  nlinarith [hprod, hsq, hm]



-- k=1:  a_0 * a_2 < a_1^2  (margin lo_1^2 - hi_0*hi_2 = 183728596409341798032288106203169471852503887/20000000000000000000000000000000000000000000000000 > 0)
theorem newton_xi_k1 {a0 a1 a2 : ℝ}
    (hp0 : 0 ≤ a0) (h0 : a0 ≤ ((2485603890941570549563869 : ℝ) / 5000000000000000000000000))
    (h1 : ((114859721575727187676249 : ℝ) / 10000000000000000000000000) ≤ a1)
    (hp2 : 0 ≤ a2) (h2 : a2 ≤ ((2469040361406360137807 : ℝ) / 10000000000000000000000000)) :
    a0 * a2 < a1 ^ 2 :=
  turan_from_enclosure (by norm_num) h1 hp0 h0 hp2 h2 (by norm_num)

-- k=2:  a_1 * a_3 < a_2^2  (margin lo_2^2 - hi_1*hi_3 = 179956587807664340683640309120917668208693/50000000000000000000000000000000000000000000000000 > 0)
theorem newton_xi_k2 {a1 a2 a3 : ℝ}
    (hp1 : 0 ≤ a1) (h1 : a1 ≤ ((91887777260581750141 : ℝ) / 8000000000000000000000))
    (h2 : ((1234520180703180068903 : ℝ) / 5000000000000000000000000) ≤ a2)
    (hp3 : 0 ≤ a3) (h3 : a3 ≤ ((49941328883131624321 : ℝ) / 10000000000000000000000000)) :
    a1 * a3 < a2 ^ 2 :=
  turan_from_enclosure (by norm_num) h2 hp1 h1 hp3 h3 (by norm_num)

-- k=3:  a_2 * a_4 < a_3^2  (margin lo_3^2 - hi_2*hi_4 = 64231946848943081215851322819066330173/50000000000000000000000000000000000000000000000000 > 0)
theorem newton_xi_k3 {a2 a3 a4 : ℝ}
    (hp2 : 0 ≤ a2) (h2 : a2 ≤ ((2469040361406360137807 : ℝ) / 10000000000000000000000000))
    (h3 : ((78033326379893163 : ℝ) / 15625000000000000000000) ≤ a3)
    (hp4 : 0 ≤ a4) (h4 : a4 ≤ ((479067186161296461 : ℝ) / 5000000000000000000000000)) :
    a2 * a4 < a3 ^ 2 :=
  turan_from_enclosure (by norm_num) h3 hp2 h2 hp4 h4 (by norm_num)

-- k=4:  a_3 * a_5 < a_4^2  (margin lo_4^2 - hi_3*hi_5 = 42088976085978607290268697622473807/100000000000000000000000000000000000000000000000000 > 0)
theorem newton_xi_k4 {a3 a4 a5 : ℝ}
    (hp3 : 0 ≤ a3) (h3 : a3 ≤ ((49941328883131624321 : ℝ) / 10000000000000000000000000))
    (h4 : ((958134372322592921 : ℝ) / 10000000000000000000000000) ≤ a4)
    (hp5 : 0 ≤ a5) (h5 : a5 ≤ ((8769615456066577 : ℝ) / 5000000000000000000000000)) :
    a3 * a5 < a4 ^ 2 :=
  turan_from_enclosure (by norm_num) h4 hp3 h3 hp5 h5 (by norm_num)

-- k=5:  a_4 * a_6 < a_5^2  (margin lo_5^2 - hi_4*hi_6 = 12742591457254242838659190227343/100000000000000000000000000000000000000000000000000 > 0)
theorem newton_xi_k5 {a4 a5 a6 : ℝ}
    (hp4 : 0 ≤ a4) (h4 : a4 ≤ ((479067186161296461 : ℝ) / 5000000000000000000000000))
    (h5 : ((17539230912133153 : ℝ) / 10000000000000000000000000) ≤ a5)
    (hp6 : 0 ≤ a6) (h6 : a6 ≤ ((307766883278653 : ℝ) / 10000000000000000000000000)) :
    a4 * a6 < a5 ^ 2 :=
  turan_from_enclosure (by norm_num) h5 hp4 h4 hp6 h6 (by norm_num)

-- k=6:  a_5 * a_7 < a_6^2  (margin lo_6^2 - hi_5*hi_7 = 3501666106504783617876063/97656250000000000000000000000000000000000000000 > 0)
theorem newton_xi_k6 {a5 a6 a7 : ℝ}
    (hp5 : 0 ≤ a5) (h5 : a5 ≤ ((8769615456066577 : ℝ) / 5000000000000000000000000))
    (h6 : ((76941720819663 : ℝ) / 2500000000000000000000000) ≤ a6)
    (hp7 : 0 ≤ a7) (h7 : a7 ≤ ((649506446481 : ℝ) / 1250000000000000000000000)) :
    a5 * a7 < a6 ^ 2 :=
  turan_from_enclosure (by norm_num) h6 hp5 h5 hp7 h7 (by norm_num)

end NewtonXi
