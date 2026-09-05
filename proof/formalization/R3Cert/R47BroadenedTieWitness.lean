/-
  R3Cert.R47BroadenedTieWitness -- the near-star is NOT the fixed-n maximizer (explicit size-56 witness).

  The broadened config (5 load-4 arms + 5 cherries) strictly BEATS the near-star (5 load-5 arms) at the
  SAME size 56.  Hence `conjecture1_of_layers_fixedN` / `SharpRateNF` instantiated with the NEAR-STAR tie is
  FALSE at this n -- the correct tie is the broadened family (see the closed form + m(K) in
  `proof/verification/broadened_tie_family.py`, verified by three independent exact engines).  This matches
  the small-n CHERRY regime already noted qualitatively in `R47NearStarValue.lean`'s docstring; this file
  pins a concrete kernel-checkable witness of it.

  Values (both at usize 56, exact rationals):
    near-star   Aobj(backboneU [(replicate 5 5, 0)]) = (26/23)·(621/64)^5  = 52200362289231/536870912
    broadened   Aobj(backboneU [([4,4,4,4,4], 5)])                          = 10754162441504397/104857600000
  and 52200362289231/536870912 < 10754162441504397/104857600000  (broadened beats near-star by 5.48%).

  Building blocks (all pre-existing, no new axioms): `nearstar_arms_Aobj`, `singleHub_Aobj_formula`,
  `Ztot_armU_four = 513/80`.  Collision-safe `R3Cert.+` leaf, imported by nothing.

  STATUS: faithful transcription of a Python-verified (3 engines) exact inequality.  CI-verification
  pending -- this repo builds Lean on CI only (local Lean builds barred by the hardware constraint), so
  this is NOT yet kernel-confirmed.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47SingleHubFormula
import R3Cert.R47NearStarValue
import R3Cert.R47HeadId

namespace R3Cert
namespace Step3

open RTree

/-- **The near-star is not the fixed-n maximizer at size 56.**  A single hub of 5 load-4 arms plus 5
    cherries has strictly larger `Aobj` than the near-star (5 load-5 arms) of the same size.  Therefore no
    `tie` equal to the near-star family can satisfy `conjecture1`/`SharpRateNF` at this size. -/
theorem nearStar_not_maximal_at_five :
    Aobj (backboneU [(List.replicate 5 5, 0)]) < Aobj (backboneU [([4, 4, 4, 4, 4], 5)]) := by
  rw [nearstar_arms_Aobj 5 (by norm_num),
      singleHub_Aobj_formula [4, 4, 4, 4, 4] 5 (by norm_num)]
  simp only [List.map_cons, List.map_nil, Ztot_armU_four,
             List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil,
             List.length_cons, List.length_nil, Nat.cast_ofNat, Nat.cast_add]
  norm_num

end Step3
end R3Cert
