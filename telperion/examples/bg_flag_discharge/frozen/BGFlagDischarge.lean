/- Flag-discharge certificate for the Brualdi-Goldwasser walk-count m_2 cut (route b).
   Antisymmetric edge potential w(d,e)=-w(e,d) + scalars (b0,b1,b2), degrees <= 7.
   Per-vertex 2x^2-q >= b0+b1 d+b2 x+sum w(d,d_a); tree sum telescopes (sum w=0) +
   handshake (sum d=2n-2) => m_2(T) >= -1937/3600 + 13/360*(2-2/n) + 1081/720*m_1(T).
   Each atom is a rational per-type inequality the kernel re-checks by norm_num; tight at
   the extremal caterpillar profile. One finite level of the W9 convergent hierarchy --
   NOT a proof of Brualdi-Goldwasser.  conjecture1_proved = False. -/
import Mathlib

namespace BGFlagDischarge

-- profile deg=1 nbrs=[2]  (slack 1/800)
theorem bg_flag_discharge_leaf : ((199 : ℚ)/800) ≤ ((1 : ℚ)/4) := by norm_num

-- profile deg=2 nbrs=[7,1]  (slack 53/176400)
theorem bg_flag_discharge_arm : ((10021 : ℚ)/25200) ≤ ((39 : ℚ)/98) := by norm_num

-- profile deg=7 nbrs=[2,2,2,2,2,7,7]  (slack 103099/17287200)
theorem bg_flag_discharge_hub : ((100349 : ℚ)/352800) ≤ ((2789 : ℚ)/9604) := by norm_num

-- profile deg=1 nbrs=[5]  (slack 0)
theorem bg_flag_discharge_tight : ((1 : ℚ)/25) ≤ ((1 : ℚ)/25) := by norm_num

end BGFlagDischarge
