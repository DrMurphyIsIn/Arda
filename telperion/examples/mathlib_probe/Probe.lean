/- Mathlib v4.32.0 API probe #3: eulerMascheroniConstant internals, to build the
   MISSING lower bound (Mathlib has `_lt_two_thirds` but no lower bound).
   `#print` dumps the definition; `#check` types the surrounding API. -/
import Mathlib
open scoped Real

-- the definition (reveals how to bound it below)
#print Real.eulerMascheroniConstant
#check @Real.eulerMascheroniConstant_lt_two_thirds

-- lower-bound candidates (which, if any, already exist?)
#check @Real.eulerMascheroniConstant_pos
#check @Real.one_half_lt_eulerMascheroniConstant
#check @Real.eulerMascheroniConstant_gt

-- harmonic-minus-log characterization (the standard route to bounds)
#check @harmonic
#check @Real.eulerMascheroniConstant_eq
#check @Real.tendsto_eulerMascheroniSeq
#check @Real.eulerMascheroniSeq
#check @Real.eulerMascheroniSeq'
#check @Real.eulerMascheroniSeq_lt_eulerMascheroniConstant
#check @Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'
