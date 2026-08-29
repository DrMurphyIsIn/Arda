/- Probe 2: reveal eulerMascheroniSeq definition (#print) + harmonic 100 feasibility.
   Decides how to compute gamma_lo and whether m~100 harmonic terms is norm_num-tractable. -/
import Mathlib
open scoped Real

#print Real.eulerMascheroniSeq
#print harmonic

-- harmonic 100 evaluable? (H_100 ~ 5.187 > 5) -- timing shows in build duration
example : (5 : ℚ) < harmonic 100 := by norm_num [harmonic, Finset.sum_range_succ]

-- candidate: does the seq relate to harmonic - log(n+1)?  (guess; error reveals real def)
example (n : ℕ) : Real.eulerMascheroniSeq n = harmonic n - Real.log (n + 1) := by
  rfl
