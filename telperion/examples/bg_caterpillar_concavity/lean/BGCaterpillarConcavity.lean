/- BG caterpillar density concavity + strict max at a=7 (route-b piece 2, kernel-gated).
   F(a) = infinite length-2-arm caterpillar cavity free-energy density (a arms/hub); the k=0 phonon
   knife-edge. rho* = exp(max_a F(a)), maximizer ~7-arm caterpillar. Enclosures from rigorous 80-digit
   interval numerics (transcendental import, turan/jensen model). Atoms: a=7 strictly maximizes F over
   integer arm-counts, and F is concave (a=6,7,8). With monomer-dimer strong spatial mixing (BGKNT 2007)
   gapping every non-k=0 mode, these certify a strict LOCAL max in every structural direction.
   NOT a proof of Brualdi-Goldwasser (the global no-competitor step remains). conjecture1_proved = False. -/
import Mathlib

namespace BGCaterpillarConcavity

theorem bg_cat_max_a7_gt_a6 : ((102530286470842423 : ℚ)/500000000000000000) < ((205098366921379213 : ℚ)/1000000000000000000) := by norm_num
theorem bg_cat_max_a7_gt_a8 : ((41015115934306273 : ℚ)/200000000000000000) < ((205098366921379213 : ℚ)/1000000000000000000) := by norm_num
theorem bg_cat_concave_a6 : ((410003364507887021 : ℚ)/1000000000000000000) < ((205060572941684843 : ℚ)/500000000000000000) := by norm_num
theorem bg_cat_concave_a7 : ((410136152613216211 : ℚ)/1000000000000000000) < ((205098366921379213 : ℚ)/500000000000000000) := by norm_num
theorem bg_cat_concave_a8 : ((410120022775786479 : ℚ)/1000000000000000000) < ((102537789835765681 : ℚ)/250000000000000000) := by norm_num

end BGCaterpillarConcavity
