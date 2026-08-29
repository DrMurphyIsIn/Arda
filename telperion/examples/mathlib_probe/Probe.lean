/- Does Mathlib ALREADY have the 3-4-1 certificate->zeta bridge (from its non-vanishing
   proof)?  If so, "full effort" should target the FRONTIER (growth bound), not duplicate it. -/
import Mathlib
open scoped Real

-- candidate names for the existing 3-4-1 / real-part-combination machinery
#check @LSeries.re_log_comb_nonneg
#check @norm_LSeries_product_ge_one
#check @riemannZeta_ne_zero_of_one_le_re
#check @DirichletCharacter.re_log_comb_nonneg
#check @LSeries.term_vonMangoldt_re
#check @ArithmeticFunction.LSeries_vonMangoldt_re_nonneg
#check @riemannZeta_ne_zero_of_re_eq_one
