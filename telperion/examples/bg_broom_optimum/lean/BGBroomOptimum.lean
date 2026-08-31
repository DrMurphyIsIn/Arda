/- BG star-of-cherry-brooms c=5 optimum (route-b retarget, kernel-gated).
   S(k,c): central hub + k branch-hubs (deg c+1), each with c length-2 cherries. Asymptotic density
   F(c)=log(total(c))/(2c+1), total(c)=(3/2)^(c-1)(4c+3)/(2(c+1)), total(5)=621/64. Its star core beats
   Pant 2026's path-core caterpillars: F(5)=0.206586 > 0.205098. Atoms: the discrete optimum c*=5 via
   cross-exponentiation rate(5)>rate(c) <=> total(5)^(2c+1) > total(c)^11 (clears the roots -> exact
   rationals). Certifies only the c-argmax among brooms; family-vs-caterpillar dominance and the global
   maximizer (OPEN) are separate. NOT a proof of Brualdi-Goldwasser. conjecture1_proved = False. -/
import Mathlib

namespace BGBroomOptimum

theorem broom_rate_c5_gt_c2 : ((92354487127101 : ℚ)/1073741824) > ((285311670611 : ℚ)/4194304) := by norm_num
theorem broom_rate_c5_gt_c3 : ((35615676770182356741 : ℚ)/4398046511104) > ((271438504226343896484375 : ℚ)/36028797018963968) := by norm_num
theorem broom_rate_c5_gt_c4 : ((13734865205329894235955981 : ℚ)/18014398509481984) > ((647576404628932868625869313537 : ℚ)/858993459200000000000) := by norm_num
theorem broom_rate_c5_gt_c6 : ((2042635155874568680174889641096599261 : ℚ)/302231454903657293676544) > ((969773729787523602876821942164080815560161 : ℚ)/145900961512890638499422666752) := by norm_num
theorem broom_rate_c5_gt_c7 : ((787723864146624540391324616082133635611301 : ℚ)/1237940039285380274899124224) > ((785202084157152429745860160545547063107948448599 : ℚ)/1298074214633706907132624082305024) := by norm_num
theorem broom_rate_c5_gt_c8 : ((303778618693368434381050816270530097370777728941 : ℚ)/5070602400912917605986812821504) > ((16842924327323405614178434756053159228515625 : ℚ)/309485009821345068724781056) := by norm_num

end BGBroomOptimum
