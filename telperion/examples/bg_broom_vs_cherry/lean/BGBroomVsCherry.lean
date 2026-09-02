/- BG extremality assembly leg #4: broom-vs-cherry on the invariant price interval I=[456/3703,3/7].
   V_mu(B(j)) <= V_mu(cherry) for broom children of degree <= 6 (j=1..5) and all mu in I (linear in mu,
   so both endpoints A,B). Atoms (frozen log-enclosures): 11 L(total B(j))-11 L(3/2)-(2j-1) L(621/64)
   < 11 mu (1/3 - y_Bj). Reference-broom leg of the single-child induction. conjecture1_proved = False. -/
import Mathlib

namespace BGBroomVsCherry

theorem bvc_j1_A : ((-115358104094793112253493315627 : ℚ)/200000000000000000000000000000) < ((-3344 : ℚ)/25921) := by norm_num
theorem bvc_j1_B : ((-115358104094793112253493315627 : ℚ)/200000000000000000000000000000) < ((-22 : ℚ)/49) := by norm_num
theorem bvc_j2_A : ((-149850156447949749723159026049 : ℚ)/1000000000000000000000000000000) < ((304 : ℚ)/3703) := by norm_num
theorem bvc_j2_B : ((-149850156447949749723159026049 : ℚ)/1000000000000000000000000000000) < ((2 : ℚ)/7) := by norm_num
theorem bvc_j3_A : ((12571449966889174500055464489 : ℚ)/1000000000000000000000000000000) < ((3344 : ℚ)/18515) := by norm_num
theorem bvc_j3_B : ((12571449966889174500055464489 : ℚ)/1000000000000000000000000000000) < ((22 : ℚ)/35) := by norm_num
theorem bvc_j4_A : ((73489136259310579994013592667 : ℚ)/1000000000000000000000000000000) < ((880 : ℚ)/3703) := by norm_num
theorem bvc_j4_B : ((73489136259310579994013592667 : ℚ)/1000000000000000000000000000000) < ((110 : ℚ)/133) := by norm_num
theorem bvc_j5_A : ((84779807957805615220047357563 : ℚ)/1000000000000000000000000000000) < ((3344 : ℚ)/12167) := by norm_num
theorem bvc_j5_B : ((84779807957805615220047357563 : ℚ)/1000000000000000000000000000000) < ((22 : ℚ)/23) := by norm_num

end BGBroomVsCherry
