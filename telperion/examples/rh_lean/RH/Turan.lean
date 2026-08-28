/- telperion 0.1.3 | family RiemannTuran | input-hash 3ec47340b43a2ec2
   4 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace RiemannTuran

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



-- k=1:  a_0 * a_2 < a_1^2  (margin lo_1^2 - hi_0*hi_2 = 7055699311250139309417730442947401319301050849/100000000000000000000000000000000000000000000000000 > 0)
theorem turan_xi_k1 {a0 a1 a2 : ℝ}
    (hp0 : 0 ≤ a0) (h0 : a0 ≤ ((2485603890941570549563869 : ℝ) / 5000000000000000000000000))
    (h1 : ((114859721575727187676249 : ℝ) / 10000000000000000000000000) ≤ a1)
    (hp2 : 0 ≤ a2) (h2 : a2 ≤ ((154315022587897508613 : ℝ) / 1250000000000000000000000)) :
    a0 * a2 < a1 ^ 2 :=
  turan_from_enclosure (by norm_num) h1 hp0 h0 hp2 h2 (by norm_num)

-- k=2:  a_1 * a_3 < a_2^2  (margin lo_2^2 - hi_1*hi_3 = 567998888123692237120013713188009175547159/100000000000000000000000000000000000000000000000000 > 0)
theorem turan_xi_k2 {a1 a2 a3 : ℝ}
    (hp1 : 0 ≤ a1) (h1 : a1 ≤ ((91887777260581750141 : ℝ) / 8000000000000000000000))
    (h2 : ((1234520180703180068903 : ℝ) / 10000000000000000000000000) ≤ a2)
    (hp3 : 0 ≤ a3) (h3 : a3 ≤ ((8323554813855270721 : ℝ) / 10000000000000000000000000)) :
    a1 * a3 < a2 ^ 2 :=
  turan_from_enclosure (by norm_num) h2 hp1 h1 hp3 h3 (by norm_num)

-- k=3:  a_2 * a_4 < a_3^2  (margin lo_3^2 - hi_2*hi_4 = 624897571984977312813968494480156941/3125000000000000000000000000000000000000000000000 > 0)
theorem turan_xi_k3 {a2 a3 a4 : ℝ}
    (hp2 : 0 ≤ a2) (h2 : a2 ≤ ((154315022587897508613 : ℝ) / 1250000000000000000000000))
    (h3 : ((26011108793297721 : ℝ) / 31250000000000000000000) ≤ a3)
    (hp4 : 0 ≤ a4) (h4 : a4 ≤ ((9980566378360343 : ℝ) / 2500000000000000000000000)) :
    a2 * a4 < a3 ^ 2 :=
  turan_from_enclosure (by norm_num) h3 hp2 h2 hp4 h4 (by norm_num)

end RiemannTuran
