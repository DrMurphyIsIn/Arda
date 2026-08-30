/- BG route-(b) moment-degree-3 no-distant-competitor certificate (kernel-gated).
   F(T) = (1/2) integral log(1+u) dmu_N <= c1 m1 + c2 m2 + c3 m3 for the frozen degree-3 envelope
   P_3(u) = 1/504 + 1219/2520 u + (-947/5040) u^2 + 1/20 u^3 >= (1/2)log(1+u) on [0,1] (min margin ~3.6e-4,
   interval-verified offline; turan/jensen enclosure model).  m_k = (1/n)Tr N^{2k}, exact rationals
   from the verified radius-2 per-vertex integrand.  Atoms: the ~7-arm caterpillar strictly maximizes
   c1 m1 + c2 m2 + c3 m3 over structurally-distinct competitors (2/3/4-regular trees, L=3-arm
   caterpillars, arm counts 3 and 10) -- the distant-competitor directions.  The knife-edge a=6,a=8
   are handled by bg_caterpillar_concavity (piece 2).  NOT a proof of Brualdi-Goldwasser (the
   universal cut needs radius-2 mass-transport).  conjecture1_proved = False. -/
import Mathlib

namespace BGM3MomentCut

theorem bg_m3_cat_beats_path_2reg : ((7541 : ℚ)/40320) < ((36364589 : ℚ)/178564176) := by norm_num
theorem bg_m3_cat_beats_tree_3reg : ((18019 : ℚ)/136080) < ((36364589 : ℚ)/178564176) := by norm_num
theorem bg_m3_cat_beats_tree_4reg : ((4439 : ℚ)/43008) < ((36364589 : ℚ)/178564176) := by norm_num
theorem bg_m3_cat_beats_cat_a7_L3 : ((2492330647 : ℚ)/13094706240) < ((36364589 : ℚ)/178564176) := by norm_num
theorem bg_m3_cat_beats_cat_a5_L3 : ((64773931 : ℚ)/338829120) < ((36364589 : ℚ)/178564176) := by norm_num
theorem bg_m3_cat_beats_cat_a3_L2 : ((22299611 : ℚ)/110250000) < ((36364589 : ℚ)/178564176) := by norm_num
theorem bg_m3_cat_beats_cat_a10_L2 : ((446561837 : ℚ)/2194698240) < ((36364589 : ℚ)/178564176) := by norm_num

end BGM3MomentCut
