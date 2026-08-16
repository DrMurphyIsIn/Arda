/- telperion 0.1.3 | family Telescope | input-hash 9e64c493f6ebf3d7
   2 theorems, 1 generation-time self-checks passed.
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

/-- Worked telescoping: local ≡ -1, potential P = -(node count), with the node
    count itself expressed as `sumOver (fun _ => 1)` (real-valued, no ℕ casts).
    The per-node super-solution holds with equality, so telescoping gives the
    global bound `Σ (-1) ≤ -(node count)`. -/
theorem telescope_nodecount (t : RTree) :
    RTree.sumOver (fun _ => (-1 : ℝ)) t ≤ -(RTree.sumOver (fun _ => (1 : ℝ)) t) := by
  refine RTree.telescope (loc := fun _ => (-1 : ℝ))
    (P := fun s => -(RTree.sumOver (fun _ => (1 : ℝ)) s)) ?_ t
  intro cs
  simp only [RTree.sumOver]
  have key : ∀ l : List RTree,
      (l.map (fun s => -(RTree.sumOver (fun _ => (1 : ℝ)) s))).sum
        = -((l.map (RTree.sumOver (fun _ => (1 : ℝ)))).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [key]
  linarith

/-- UNIFYING REDUCTION (the pieces, knit together).  The reframed crux
    `Σ_nodes (growth v − tax v) ≤ 0`  (i.e. `Σ growth ≤ Σ tax`, which is EXACTLY
    `Φ¹¹ ≤ 1` by the source-grouped decomposition Φ¹¹ = ∏ const_v·growth_v,
    verified 4130/4130) follows from ONE object: a potential `P` that super-solves
    the per-node ledger and is nonpositive at the root.

    Every OTHER ingredient is discharged and machine-checked:
      • the TAX is exact {2,3,23} arithmetic   (padic + tax_growth: const_v(cr)
        = 2^(6+cr)·3^(5cr−3)/23^(1+2cr));
      • the GROWTH is bounded per node          (tax_growth: 1 ≤ growth ≤ env);
      • the TELESCOPING is `RTree.telescope`    (kernel-verified above).
    The potential `P` is the SOLE open input — no finite closed form exists
    (LP-feasible per-cavity, no finite basis; continuous relaxation > 1).  The
    root-interlacing certificates (Wronskian-SOS) are the candidate source for
    `P` via the matching-polynomial recursion.  conjecture1_proved = False: this
    theorem is the honest reduction, not the conjecture. -/
theorem crux_reduction {growth tax P : RTree → ℝ}
    (hsuper : ∀ cs : List RTree,
        (growth (.node cs) - tax (.node cs)) + (cs.map P).sum ≤ P (.node cs))
    (t : RTree) (hroot : P t ≤ 0) :
    RTree.sumOver (fun v => growth v - tax v) t ≤ 0 := by
  have h := RTree.telescope (loc := fun v => growth v - tax v) (P := P) hsuper t
  linarith

end Telescope
end G1
