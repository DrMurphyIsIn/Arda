/- telperion 0.1.6 | family Consequence | input-hash 824717a06cac2424
   2 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Consequence

-- consequence_cubes: equational consequence — lhs = rhs follows from the hypotheses (lhs − rhs = Σ c_i·(a_i − b_i)).
theorem consequence_cubes : ∀ x y : ℝ, x = y → x ^ 3 = y ^ 3 := by
  intro x y h
  linear_combination (x ^ 2 + x * y + y ^ 2) * h

-- consequence_sum_of_squares: equational consequence — lhs = rhs follows from the hypotheses (lhs − rhs = Σ c_i·(a_i − b_i)).
theorem consequence_sum_of_squares : ∀ x y : ℝ, x = 1 → y = 1 → x ^ 2 + y ^ 2 = 2 := by
  intro x y hx hy
  linear_combination (1 + x) * hx + (1 + y) * hy

end Consequence
end G1
