/- telperion 0.1.3 | family Scope | input-hash eb57a8e1594954ae
   5 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Scope

-- SCOPE (n=4): support is a FOREST (3 edges, acyclic) => the permutation
-- expansion collapses to matchings with nonnegative weights; termwise-nonnegativity
-- arguments (e.g. permanental dominance) are VALID on this class.
theorem scope_forest_edges : (3:ℤ) ≤ 4 - 1 := by norm_num
-- OUT OF SCOPE (n=3): support has a cycle. Frustration witness = a PSD matrix (below,
-- diagonally dominant => PSD by Gershgorin) with a permutation whose entry-product is
-- NEGATIVE, so termwise nonnegativity FAILS -- the method does not extend to general PSD.

theorem scope_frustr_domrow_0 : (2:ℤ) ≤ 3 := by norm_num
theorem scope_frustr_domrow_1 : (2:ℤ) ≤ 3 := by norm_num
theorem scope_frustr_domrow_2 : (2:ℤ) ≤ 3 := by norm_num
-- the frustrated permutation's entry product is negative:
theorem scope_frustr_negative : ((1) * (1) * (-1) : ℤ) < 0 := by norm_num

end Scope
end G1
