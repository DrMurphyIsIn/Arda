/- telperion 0.1.6 | family CGRound | input-hash 94ce6081f5c9ce1c
   2 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace CGRound

-- cg_cut_3x_ge_2: Chvatal-Gomory derivation (VIPR-style) -- 2 step(s), 1 integer round(s); the integer LHS lets a fractional bound round up.  omega discharges the linear-integer chain.
theorem cg_cut_3x_ge_2 : forall x : Int, 3 * x >= 2 -> x >= 1 := by
  intro x h1
  omega

-- cg_sum_xy_ge_2: Chvatal-Gomory derivation (VIPR-style) -- 1 step(s), 0 integer round(s); the integer LHS lets a fractional bound round up.  omega discharges the linear-integer chain.
theorem cg_sum_xy_ge_2 : forall x y : Int, x >= 1 -> y >= 1 -> x + y >= 2 := by
  intro x y h1 h2
  omega

end CGRound
end G1
