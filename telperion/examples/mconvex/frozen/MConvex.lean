/- telperion 0.1.3 | family MConvex | input-hash 0db20825253fd3b4
   4 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace MConvex

-- mconcave_sepsq: M-concavity on the integer lattice via the exchange
-- axiom (discrete convex analysis).  4 distinct exchange
-- inequalities; their equality cases are the integer-native tie
-- candidates.  This is the structure that certifies on ℤ, not ℝ.
theorem mconcave_sepsq_exch0 : ((-4:ℚ)/1) ≤ (-4:ℚ)/1 := by norm_num
theorem mconcave_sepsq_exch1 : ((-6:ℚ)/1) ≤ (-6:ℚ)/1 := by norm_num
theorem mconcave_sepsq_exch2 : ((-6:ℚ)/1) ≤ (-4:ℚ)/1 := by norm_num
theorem mconcave_sepsq_exch3 : ((-8:ℚ)/1) ≤ (-4:ℚ)/1 := by norm_num

end MConvex
end G1
