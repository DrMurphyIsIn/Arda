/- API probe for the tighter-gamma path: eulerMascheroniSeq shape + harmonic
   evaluability under norm_num (the two feasibility risks for RH-tight Robin). -/
import Mathlib
open scoped Real

-- 1. the sequence + its bound lemma (shape tells us how to compute gamma_lo)
#check @Real.eulerMascheroniSeq
#check @Real.eulerMascheroniSeq_lt_eulerMascheroniConstant
#check @harmonic

-- 2. can norm_num evaluate harmonic at moderate n?  (feasibility of gamma_lo = H_m - log(m+1))
example : harmonic 10 = 7381/2520 := by norm_num [harmonic, Finset.sum_range_succ]
example : (4 : ℚ) < harmonic 40 := by norm_num [harmonic, Finset.sum_range_succ]

-- 3. is there a definitional/eq lemma exposing seq n = harmonic n - log(...)?
example (n : ℕ) : True := by
  have := @Real.eulerMascheroniSeq_lt_eulerMascheroniConstant
  trivial
