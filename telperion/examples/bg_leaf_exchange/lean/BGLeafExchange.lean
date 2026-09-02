/- BG extremality assembly leg #5: leaf-exchange (bare leaves excluded from the M_d argmax).
   For hub degree d=3..6, leaf->cherry strictly raises ell; cleared (x11) to the pure rational
   (3(4d-1)/(2(4d+1)))^11 > 621/64. conjecture1_proved = False. -/
import Mathlib

namespace BGLeafExchange

theorem leaf_exch_d3 : ((50542106513726817 : ℚ)/3670344486987776) > ((621 : ℚ)/64) := by norm_num
theorem leaf_exch_d4 : ((1532278301220703125 : ℚ)/70188843638032384) > ((621 : ℚ)/64) := by norm_num
theorem leaf_exch_d5 : ((116490258898219 : ℚ)/4049565169664) > ((621 : ℚ)/64) := by norm_num
theorem leaf_exch_d6 : ((168787390185178426269 : ℚ)/4882812500000000000) > ((621 : ℚ)/64) := by norm_num

end BGLeafExchange
