/-
  Adjacent leaf StraightStep, structural core: the `nB=0` defect-neutrality (the novel insight behind
  crux (a) of the monomer-dimer / Hnorm-residual program, see
  `proof/verification/AOBJ_MATCHING_POLYNOMIAL_REFORMULATION.md`).

  The adjacent leaf move relocates a leaf `flpLeaf` (child of `par_w`) onto the leaf `flpLeaf` of a
  sibling `par_v = node (flpLeaf :: Bv)`, turning that leaf into a stem: `par_v → node (flpStem :: Bv)`.
  Its `Aobj` increment is `PB·PO·N / den` with `N ≥ N0 = nO(nB·nO + nB + nO − 2)`, sign-indefinite ONLY at
  `nB = 0` (the closed-form analysis). This file proves the STRUCTURAL half of the resolution: when `nB = 0`
  (`Bv = []`) the move is `strDefect`-NEUTRAL — because `par_v = node [flpLeaf]` is a CHERRY (a piece) and
  `par_v' = node [flpStem]` is an ARM (a piece), and the relocated `flpLeaf` is itself a piece, so no
  non-piece count changes in ANY sibling context.  Contrapositive: a `strDefect`-REDUCING adjacent leaf
  move must have `nB ≥ 1`, which lands the closed form in its provably-nonnegative region `N ≥ N0 ≥ 0`.

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7Straighten
import R3Cert.BGSCLRealOblACaseAIdentity

namespace R3Cert
namespace Step3

open RTree

/-! ### Piece facts for the flp atoms (inline, to avoid the heavy `BGSCLFlpStepAt` import). -/

theorem isArm_flpLeaf : isArm flpLeaf = true := rfl
theorem isPiece_flpLeaf : isPiece flpLeaf = true := by rw [isPiece, isArm_flpLeaf, Bool.true_or]
theorem isCherry_flpStem : isCherry flpStem = true := rfl

/-- `node [flpLeaf]` is a CHERRY (its single child is the bare leaf `flpLeaf`), hence a piece. -/
theorem isPiece_node_flpLeaf : isPiece (UTree.node [flpLeaf]) = true := by
  have hc : isCherry (UTree.node [flpLeaf]) = true := rfl
  rw [isPiece, hc, Bool.or_true]

/-- `node [flpStem]` is an ARM (its single child `flpStem` is a cherry), hence a piece. -/
theorem isPiece_node_flpStem : isPiece (UTree.node [flpStem]) = true := by
  have ha : isArm (UTree.node [flpStem]) = true := by
    rw [isArm, List.all_cons, isCherry_flpStem, List.all_nil, Bool.and_true]
  rw [isPiece, ha, Bool.true_or]

/-- **`nB = 0` defect-neutrality.**  With an empty `Bv`, the adjacent leaf move
    `node (pre ++ flpLeaf :: node [flpLeaf] :: post) → node (pre ++ node [flpStem] :: post)`
    leaves `strDefect` unchanged in every sibling context (`par_v = node [flpLeaf]` a cherry-piece,
    `par_v' = node [flpStem]` an arm-piece, and the relocated `flpLeaf` a piece — no non-piece count
    moves). -/
theorem strDefect_adjLeaf_nB0 (pre post : List UTree) :
    strDefect (UTree.node (pre ++ flpLeaf :: UTree.node [flpLeaf] :: post))
      = strDefect (UTree.node (pre ++ UTree.node [flpStem] :: post)) := by
  have hCb : npCount (flpLeaf :: UTree.node [flpLeaf] :: post) = npCount post := by
    rw [npCount, npCount, if_pos isPiece_flpLeaf, if_pos isPiece_node_flpLeaf]; omega
  have hCa : npCount (UTree.node [flpStem] :: post) = npCount post := by
    rw [npCount, if_pos isPiece_node_flpStem]; omega
  have hDb : npDefectSum (flpLeaf :: UTree.node [flpLeaf] :: post) = npDefectSum post := by
    rw [npDefectSum, npDefectSum, if_pos isPiece_flpLeaf, if_pos isPiece_node_flpLeaf]; omega
  have hDa : npDefectSum (UTree.node [flpStem] :: post) = npDefectSum post := by
    rw [npDefectSum, if_pos isPiece_node_flpStem]; omega
  rw [strDefect, strDefect, npCount_append, npCount_append, npDefectSum_append, npDefectSum_append,
    hCb, hCa, hDb, hDa]

/-- **Contrapositive (the usable form):** a `strDefect`-reducing adjacent leaf move at an empty-`Bv`
    site is impossible — so any `strDefect` drop forces `nB ≥ 1`, the provably-`Aobj`-safe region. -/
theorem not_strDefect_lt_adjLeaf_nB0 (pre post : List UTree) :
    ¬ strDefect (UTree.node (pre ++ UTree.node [flpStem] :: post))
        < strDefect (UTree.node (pre ++ flpLeaf :: UTree.node [flpLeaf] :: post)) := by
  rw [strDefect_adjLeaf_nB0]; exact lt_irrefl _

end Step3
end R3Cert
