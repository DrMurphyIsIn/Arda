/- BG m=2 arm-balancing (route-b, kernel-gated).
   Two-hub caterpillar T(a,b): Z = (3/2)^(a+b-2)((4a+3)(4b+3)+9)/(4(a+1)(b+1)) (== rho, exact). At fixed
   s=a+b the toward-balance move satisfies g(a-1,b+1)-g(a,b) = 2(a-b-1)(2a+2b-1)/(a(a+1)(b+1)(b+2)) > 0
   for a>=b+2, so moving an arm from the fuller hub to the emptier one strictly increases Z. The one
   monotone move salvaged after the n=16 refutation of local Z-monotone reduction to the family. Atoms:
   Z(T(a,b)) < Z(T(a-1,b+1)) as exact closed-form rationals over a>=b+2 instances. The all-(a,b) lemma is
   the Python-verified arm_balance_delta_g (field_simp;ring + positivity obligation recorded there). NOT
   a proof of Brualdi-Goldwasser (complement reduction + exceptional-spider comparison remain).
   conjecture1_proved = False. -/
import Mathlib

namespace BGArmBalancing

theorem bg_armbal_2_0 : ((7 : ℚ)/2) < ((29 : ℚ)/8) := by norm_num
theorem bg_armbal_3_0 : ((81 : ℚ)/16) < ((43 : ℚ)/8) := by norm_num
theorem bg_armbal_3_1 : ((513 : ℚ)/64) < ((65 : ℚ)/8) := by norm_num
theorem bg_armbal_4_1 : ((1917 : ℚ)/160) < ((783 : ℚ)/64) := by norm_num
theorem bg_armbal_4_2 : ((2943 : ℚ)/160) < ((9477 : ℚ)/512) := by norm_num
theorem bg_armbal_5_2 : ((3537 : ℚ)/128) < ((35721 : ℚ)/1280) := by norm_num
theorem bg_armbal_5_3 : ((43011 : ℚ)/1024) < ((26973 : ℚ)/640) := by norm_num
theorem bg_armbal_6_3 : ((452709 : ℚ)/7168) < ((162567 : ℚ)/2560) := by norm_num
theorem bg_armbal_7_4 : ((5885217 : ℚ)/40960) < ((295245 : ℚ)/2048) := by norm_num
theorem bg_armbal_9_3 : ((17537553 : ℚ)/81920) < ((2211057 : ℚ)/10240) := by norm_num

end BGArmBalancing
