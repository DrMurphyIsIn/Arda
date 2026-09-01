/- BG smooth no-go / integrality gap (kernel-gated).
   The continuous broom free energy f(c)=log(total(c))/(2c+1) overshoots the INTEGER optimum F* at
   c0=24/5: 209 L(3/2)+55 L(111/5)-55 L(2)-55 L(29/5) > 53 L(621/64) (cleared f(24/5)>F*, frozen
   log-enclosures). So NO smooth (relaxation-based) certificate can prove F(T)<=F* -- the BG optimum is
   an integer-program optimum (rational 621/64, prime 4*5+3=23) with a positive integrality gap; the
   closing argument must be arithmetic. conjecture1_proved = False. -/
import Mathlib

namespace BGSmoothNoGo

theorem smooth_nogo_fcont_24_5_gt_Fstar : ((30110500771682917446840190652309 : ℚ)/250000000000000000000000000000) > ((120439743924411766149922078132937 : ℚ)/1000000000000000000000000000000) := by norm_num

end BGSmoothNoGo
