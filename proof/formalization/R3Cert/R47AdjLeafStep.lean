/-
  Adjacent leaf move: the complete `StraightStep_sized` (the first coverage extension beyond `FlpStepAt`).

  Combines the Aobj half (`R47AdjLeafGains.adjLeaf_Aobj_le`) with the `usize` equality and the `strDefect`
  drop.  The move fires when the extended sibling `par_v = node (flpLeaf :: Bv)` has `Bv` a NONEMPTY list of
  cherries (so `par_v` is non-piece and `par_v' = node (flpStem :: Bv)` is an ARM = piece) and the acted
  node has a non-piece sibling in `Other` (`1 ≤ npCount Other`).  Then

      c  = node (flpLeaf :: par_v :: Other)   →   c' = node (par_v' :: Other)

  drops `strDefect` by exactly 1 (par_v flips non-piece→piece at the acted node), preserves `usize`, and
  does not decrease `Aobj` — a `StraightStep_sized` in any sibling context `pre`/`post`.

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47AdjLeafGains
import R3Cert.R47AdjLeafStruct
import R3Cert.BGSCLHnormPort
import R3Cert.R47R7Sized

namespace R3Cert
namespace Step3

open RTree

/-! ### Piece facts -/

/-- `par_v = node (flpLeaf :: Bv)` with `Bv ≠ []` is non-piece (`flpLeaf` breaks the arm; ≥2 children
    breaks the cherry). -/
theorem isPiece_parv_false {Bv : List UTree} (hBv : Bv ≠ []) :
    isPiece (UTree.node (flpLeaf :: Bv)) = false := by
  obtain ⟨b, Bv', rfl⟩ := List.exists_cons_of_ne_nil hBv
  have ha : isArm (UTree.node (flpLeaf :: b :: Bv')) = false := by
    rw [isArm, List.all_cons, show isCherry flpLeaf = false from rfl, Bool.false_and]
  have hc : isCherry (UTree.node (flpLeaf :: b :: Bv')) = false := rfl
  rw [isPiece, ha, hc, Bool.or_self]

/-- `par_v' = node (flpStem :: Bv)` with `Bv` all cherries is an ARM (piece). -/
theorem isPiece_parv2_true {Bv : List UTree} (hcherry : ∀ x ∈ Bv, isCherry x = true) :
    isPiece (UTree.node (flpStem :: Bv)) = true := by
  have ha : isArm (UTree.node (flpStem :: Bv)) = true := by
    rw [isArm, List.all_cons, isCherry_flpStem, Bool.true_and]
    rw [List.all_eq_true]; intro x hx; exact hcherry x hx
  rw [isPiece, ha, Bool.true_or]

/-- `strDefect (node (flpLeaf :: Bv)) = 0` when `Bv` is all cherries (every child a piece). -/
theorem strDefect_parv_zero {Bv : List UTree} (hcherry : ∀ x ∈ Bv, isCherry x = true) :
    strDefect (UTree.node (flpLeaf :: Bv)) = 0 := by
  have hpieces : ∀ x ∈ flpLeaf :: Bv, isPiece x = true := by
    intro x hx; rw [List.mem_cons] at hx; rcases hx with rfl | hx
    · exact isPiece_flpLeaf
    · rw [isPiece, hcherry x hx, Bool.or_true]
  rw [strDefect, npCount_pieces hpieces, npDefectSum_pieces hpieces]

/-! ### The acted-node piece facts and strDefect drop -/

/-- The pre-move acted node `node (flpLeaf :: par_v :: Other)` is non-piece (≥2 children, `flpLeaf`
    not a cherry). -/
theorem isPiece_actedBefore_false (par_v : UTree) (Other : List UTree) :
    isPiece (UTree.node (flpLeaf :: par_v :: Other)) = false := by
  have ha : isArm (UTree.node (flpLeaf :: par_v :: Other)) = false := by
    rw [isArm, List.all_cons, show isCherry flpLeaf = false from rfl, Bool.false_and]
  have hc : isCherry (UTree.node (flpLeaf :: par_v :: Other)) = false := rfl
  rw [isPiece, ha, hc, Bool.or_self]

/-- The post-move acted node `node (par_v' :: Other)` is non-piece, given `par_v'` non-cherry
    (`Bv ≠ []`). -/
theorem isPiece_actedAfter_false {Bv : List UTree} (Other : List UTree) (hBv : Bv ≠ []) :
    isPiece (UTree.node (UTree.node (flpStem :: Bv) :: Other)) = false := by
  obtain ⟨b, Bv', rfl⟩ := List.exists_cons_of_ne_nil hBv
  have hpvc : isCherry (UTree.node (flpStem :: b :: Bv')) = false := rfl
  have ha : isArm (UTree.node (UTree.node (flpStem :: b :: Bv') :: Other)) = false := by
    rw [isArm, List.all_cons, hpvc, Bool.false_and]
  have hc : isCherry (UTree.node (UTree.node (flpStem :: b :: Bv') :: Other)) = false := by
    cases Other <;> rfl
  rw [isPiece, ha, hc, Bool.or_self]

/-- **The acted-node `strDefect` drop by exactly 1.**  `par_v` (non-piece, defect 0) flips to the
    arm `par_v'` (piece), dropping the acted node's non-piece count while a non-piece sibling in `Other`
    keeps the `-1` from truncating. -/
theorem adjLeaf_strDefect_lt {Bv : List UTree} (Other : List UTree) (hBv : Bv ≠ [])
    (hcherry : ∀ x ∈ Bv, isCherry x = true) (hOther : 1 ≤ npCount Other) :
    strDefect (UTree.node (UTree.node (flpStem :: Bv) :: Other))
      < strDefect (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)) := by
  have hpv : isPiece (UTree.node (flpLeaf :: Bv)) = false := isPiece_parv_false hBv
  have hpv2 : isPiece (UTree.node (flpStem :: Bv)) = true := isPiece_parv2_true hcherry
  have hdpv : strDefect (UTree.node (flpLeaf :: Bv)) = 0 := strDefect_parv_zero hcherry
  rw [strDefect, strDefect]
  rw [show npCount (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)
        = 1 + npCount Other by
        rw [npCount, npCount, if_pos isPiece_flpLeaf, if_neg (by rw [hpv]; simp)]; omega,
      show npDefectSum (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other) = npDefectSum Other by
        rw [npDefectSum, npDefectSum, if_pos isPiece_flpLeaf, if_neg (by rw [hpv]; simp), hdpv]; omega,
      show npCount (UTree.node (flpStem :: Bv) :: Other) = npCount Other by
        rw [npCount, if_pos hpv2]; omega,
      show npDefectSum (UTree.node (flpStem :: Bv) :: Other) = npDefectSum Other by
        rw [npDefectSum, if_pos hpv2]; omega]
  omega

/-! ### usize equality -/

theorem adjLeaf_usize_eq (Bv Other : List UTree) :
    usize (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other))
      = usize (UTree.node (UTree.node (flpStem :: Bv) :: Other)) := by
  simp only [usize_node, usizeList_cons, usize_flpLeaf, usize_flpStem]
  omega

/-! ### The StraightStep -/

/-- **The adjacent leaf move is a `StraightStep_sized`** in any sibling context, given `Bv` a nonempty
    cherry list and a non-piece sibling in `Other`. -/
theorem adjLeaf_straightStep (pre post Bv Other : List UTree) (hBv : Bv ≠ [])
    (hcherry : ∀ x ∈ Bv, isCherry x = true) (hOther : 1 ≤ npCount Other) :
    StraightStep_sized
      (UTree.node (pre ++ UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other) :: post))
      (UTree.node (pre ++ UTree.node (UTree.node (flpStem :: Bv) :: Other) :: post)) := by
  have hnB : 1 ≤ Bv.length := by
    cases Bv with
    | nil => exact absurd rfl hBv
    | cons _ _ => simp
  refine ⟨usize_child_replace pre post (adjLeaf_usize_eq Bv Other),
    adjLeaf_Aobj_le pre post Bv Other hnB,
    strDefect_child_replace_lt pre post
      (isPiece_actedBefore_false _ _) (isPiece_actedAfter_false Other hBv)
      (adjLeaf_strDefect_lt Other hBv hcherry hOther)⟩

end Step3
end R3Cert
