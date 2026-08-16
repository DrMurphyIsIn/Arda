/- telperion 0.1.3 | family Telescope | input-hash 829977b2aa0aa66d
   1 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Telescope

/-- Finitely-branching (rose) trees, for telescoping tree inductions. -/
inductive RTree where
  | node : List RTree → RTree

/-- Sum of a node functional over every node of the tree. -/
def RTree.sumOver (loc : RTree → ℝ) : RTree → ℝ
  | .node cs => loc (.node cs) + (cs.map (RTree.sumOver loc)).sum

/-- Telescoping closure: a per-node super-solution `local + Σ_children P ≤ P`
    gives the telescoped global bound `Σ_nodes local ≤ P root`.  Every node's `P`
    cancels between its own term and its parent's child-sum, leaving `P root`. -/
theorem RTree.telescope {loc P : RTree → ℝ}
    (h : ∀ cs : List RTree, loc (.node cs) + (cs.map P).sum ≤ P (.node cs)) :
    ∀ t : RTree, RTree.sumOver loc t ≤ P t
  | .node cs => by
    have hchild : (cs.map (RTree.sumOver loc)).sum ≤ (cs.map P).sum :=
      List.sum_le_sum (by
        intro c hc
        exact RTree.telescope h c)
    have hnode := h cs
    simp only [RTree.sumOver]
    linarith

/-- Number of nodes in the subtree. -/
def RTree.nodeCount : RTree → ℕ
  | .node cs => 1 + (cs.map RTree.nodeCount).sum

/-- Worked telescoping: local ≡ -1, potential P = -(node count).  The per-node
    super-solution holds with equality, so telescoping gives the global bound. -/
theorem telescope_nodecount (t : RTree) :
    RTree.sumOver (fun _ => (-1 : ℝ)) t ≤ (fun s => -(RTree.nodeCount s : ℝ)) t := by
  refine RTree.telescope (loc := fun _ => (-1 : ℝ))
    (P := fun s => -(RTree.nodeCount s : ℝ)) ?_ t
  intro cs
  simp only [RTree.nodeCount, Nat.cast_add, Nat.cast_one, Nat.cast_sum,
             List.map_map, Function.comp]
  push_cast
  ring_nf
  -- -1 + Σ (-(count c)) ≤ -(1 + Σ count c)  holds with equality
  have : (cs.map (fun c => -(RTree.nodeCount c : ℝ))).sum
       = -((cs.map (fun c => (RTree.nodeCount c : ℝ))).sum) := by
    rw [← List.sum_neg]; simp [List.map_map, Function.comp]
  linarith [this]

end Telescope
end G1
