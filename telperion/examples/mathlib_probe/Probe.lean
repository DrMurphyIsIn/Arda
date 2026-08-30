/- PROBE: discover the Mathlib v4.32.0 API linking LSeries(vonMangoldt) to -zeta'/zeta,
   so the ZeroFreeBridge positivity can be restated literally about zeta's log-derivative. -/
import Mathlib
open scoped Real

-- Candidate names for  LSeries Λ s = -ζ'(s)/ζ(s)  (Re s > 1).
#check @ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
#check @riemannZeta_ne_zero_of_one_lt_re

-- What is the exact signature? Try to state the identity and see if it typechecks.
example (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      = - deriv riemannZeta s / riemannZeta s := by
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
