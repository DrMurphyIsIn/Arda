/- Zero-free-region part 1 probe: does Mathlib have the vonMangoldt L-series = -zeta'/zeta,
   its termwise form Lambda(n) n^{-s}, and Re nonneg machinery, so the Mertens 3-4-1
   certificate yields 3 Re(-z'/z)(σ)+4 Re(-z'/z)(σ+it)+Re(-z'/z)(σ+2it) >= 0 ? -/
import Mathlib
open scoped Real

#check @ArithmeticFunction.vonMangoldt
#check @LSeries
#check @LSeries.term
#check @LSeriesSummable
#check @ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
#check @ArithmeticFunction.LSeriesSummable_vonMangoldt
#check @LSeries_vonMangoldt
#check @riemannZeta_eulerProduct_tprod
#check @riemannZeta_eulerProduct
#check @ArithmeticFunction.vonMangoldt_nonneg
