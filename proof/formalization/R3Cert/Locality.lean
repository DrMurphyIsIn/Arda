/-
  CAVITY-LOCALITY -- the rearrangement primitive behind the depth-collapse lemma.

  The depth-collapse lemma (every tree has `logPhi <= ` the best depth-<=2 bush at its `V`; verified robustly:
  general_children_crux.py + 656 deep random trees, 0 violations) would compose with the bush bound to close
  `Phi <= 1`.  A constructive proof wants a rearrangement that shrinks depth without lowering `logPhi`.  The
  foundation of ANY such argument is this exact locality fact:

  A node's root increment `eroot c ch = log(a(d,c)) + log(1 + z * sum of child cavities)` depends on the child
  list `ch` ONLY through `ch.length` and `cavSum ch` (the sum of child cavities).  Hence:

  * `eroot_congr` : same length + same cavity-sum  =>  same `eroot`.
  * `logPhi_child_replace` : replacing one child `b` by `b'` with `cav b' = cav b` shifts the whole tree's
    `logPhi` by EXACTLY `logPhi b' - logPhi b` -- because every ancestor's `eroot` (and cavity) is unchanged
    (cavity preserved => `cavSum` preserved up the spine), so only the swapped subtree's own amplitude moves.
  * `logPhi_child_mono` : if additionally `logPhi b <= logPhi b'`, the swap does not decrease `logPhi`.

  So `logPhi(C)` is bounded by replacing each subtree with the MAX-amplitude tree of the SAME cavity (the
  value function `Psi(cav)`).  This is exactly why the depth-collapse reduces to bounding `Psi <= 0` -- the
  circular crux.  HONEST STATUS: this primitive is proven; the depth-collapse itself is NOT closed here.  The
  "same V" collapse is obstructed by PARITY (V-parity = node-count parity, so no single leaf<->cherry swap
  preserves V), and the "same cavity" collapse reduces to the circular `Psi <= 0`.  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.Reach

namespace R3Cert

/-- `eroot` sees the child list only through its length and cavity-sum. -/
theorem eroot_congr (c : ℕ) (ch ch' : List Branch)
    (hlen : ch.length = ch'.length) (hcav : cavSum ch = cavSum ch') :
    eroot c ch = eroot c ch' := by
  unfold eroot; rw [hlen, hcav]

/-- **Cavity-locality.**  Replacing a child `b` by `b'` of equal cavity shifts the tree's `logPhi` by exactly
    the child's amplitude change (all ancestors' increments are unchanged). -/
theorem logPhi_child_replace (c : ℕ) (b b' : Branch) (rest : List Branch)
    (hcav : cav b = cav b') :
    logPhi (Branch.node c (b' :: rest)) - logPhi (Branch.node c (b :: rest))
      = logPhi b' - logPhi b := by
  have hlen : (b :: rest).length = (b' :: rest).length := by simp
  have hcs : cavSum (b :: rest) = cavSum (b' :: rest) := by
    simp only [cavSum]; rw [hcav]
  have he : eroot c (b :: rest) = eroot c (b' :: rest) := eroot_congr c _ _ hlen hcs
  simp only [logPhi, logPhiSum]
  rw [he]; ring

/-- **Monotone child replacement.**  A child swap to `b'` of equal cavity and `>=` amplitude does not lower
    `logPhi`.  (The rearrangement primitive for the depth-collapse; the maximiser at a given cavity is `Psi`.) -/
theorem logPhi_child_mono (c : ℕ) (b b' : Branch) (rest : List Branch)
    (hcav : cav b = cav b') (hamp : logPhi b ≤ logPhi b') :
    logPhi (Branch.node c (b :: rest)) ≤ logPhi (Branch.node c (b' :: rest)) := by
  have h := logPhi_child_replace c b b' rest hcav
  linarith

end R3Cert
