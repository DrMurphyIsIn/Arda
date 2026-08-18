/- telperion 0.1.4 | family Entropy | input-hash 4226935c0159b8ab
   2 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Entropy

-- bregman_path3: Bregman permanent bound per(A) ≤ Π(d_v!)^(1/d_v),
-- cleared to integers (^L, L = lcm(d_v) = 6); degree-normalized,
-- equality iff the entropy independence condition (the tie candidate).
-- per(A) = 3, degrees = [2, 3, 2].
theorem bregman_path3 : ((3:ℕ)^6) ≤ (2)^3 * (6)^2 * (2)^3 := by norm_num

-- bregman_c4: Bregman permanent bound per(A) ≤ Π(d_v!)^(1/d_v),
-- cleared to integers (^L, L = lcm(d_v) = 3); degree-normalized,
-- equality iff the entropy independence condition (the tie candidate).
-- per(A) = 9, degrees = [3, 3, 3, 3].
theorem bregman_c4 : ((9:ℕ)^3) ≤ (6)^1 * (6)^1 * (6)^1 * (6)^1 := by norm_num

end Entropy
end G1
