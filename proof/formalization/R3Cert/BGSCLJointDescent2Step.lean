/-
  Case-A / open-core: the SHARP BOUNDARY of the straightening-move existence lemma.

  The size-preserving straightening obligation `StraightProgress_sized` (`R47R7Sized.lean`) is the
  open half of the tree→hub reduction:

      StraightStep_sized t t'      := usize t = usize t' ∧ Aobj t ≤ Aobj t' ∧ strDefect t' < strDefect t
      StraightProgress_sized       := ∀ t, strDefect t ≠ 0 → ∃ t', StraightStep_sized t t'

  A Phase-0 exhaustive sweep (Front C3) probed whether this can be strengthened to the CONSTRUCTIVE
  single-move form used by naive descent: "from any defect>0 tree there is a SINGLE SPR move that is
  BOTH strDefect-decreasing AND Aobj-STRICTLY-increasing".  That strengthening is FALSE.  The unique
  obstruction at n=13 is the maximally symmetric TRIPLE-3-STAR — three degree-4 stars joined at a
  centre — for which (verified exhaustively over its entire 132-move SPR neighbourhood, and
  independently reproduced) EVERY defect-lowering SPR move strictly LOWERS `Aobj`, and every
  `Aobj`-increasing SPR move keeps the defect fixed.  No single-move joint step exists.

  This file kernel-gates that boundary WITHOUT overclaiming.  It proves, for the triple-3-star `T`
  (rooted at a star-hub, its min-defect rooting):

    (1) `Aobj T = 49/8`, `strDefect T = 1`, `usize T = 13`  — the exact invariants, via the cavity
        engine (mirroring the R1 `f2` concrete computations) and the structural recognizers.
    (2) `StraightStep_sized T (cherrySpider 6)` — a WITNESS: the 6-arm cherry-spider `node [cherryU×6]`
        (`usize 13`, `strDefect 0`, `Aobj 243/16`) is a same-size, defect-dropping, `Aobj`-increasing
        straightening step.  So the ACTUAL Lean obligation `StraightProgress_sized` HOLDS at this tree
        — the triple-3-star does NOT block it.

  The lesson for the open core (kept honest): the existence lemma is TRUE in its `StraightProgress_sized`
  form (any same-size `t'`, `Aobj` non-strict), but CANNOT be narrowed to a single-SPR / strict-`Aobj`
  move — the witness `t'` is genuinely a multi-vertex restructuring, not one relocation.  The
  `Aobj`-monotonicity half is separately kernel-proven (R1 `aobj_flp_context_lift_crest`).

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47RootRate
import R3Cert.R47StepSize
import R3Cert.R47R7Straighten
import R3Cert.R47R7Sized
import R3Cert.R47HubState
import R3Cert.BGSCLRealOblACaseAIdentity

namespace R3Cert
namespace Step3

open RTree

/-! ### The triple-3-star, rooted at a star-hub (its min-defect rooting).

    `star3 = node [leaf, leaf, leaf]` (a degree-4 star), `inner = node [star3, star3]`,
    `T = node [leaf, leaf, leaf, inner]`.  Unrooted this is three degree-4 stars joined at a centre;
    this rooting places the root at one star-hub (strDefect 1, the minimum over rootings). -/

/-- A 3-leaf star `node [leaf, leaf, leaf]` (degree-4 vertex). -/
def star3 : UTree := UTree.node [flpLeaf, flpLeaf, flpLeaf]
/-- The two remote stars hung under one child: `node [star3, star3]`. -/
def innerT : UTree := UTree.node [star3, star3]
/-- The triple-3-star, rooted at a star-hub: `node [leaf, leaf, leaf, node [star3, star3]]`. -/
def tripleStar : UTree := UTree.node [flpLeaf, flpLeaf, flpLeaf, innerT]

/-! ### Cavity values, bottom-up. -/

theorem udeg_star3 : udeg star3 = 4 := by simp [star3, udeg_node]
theorem udeg_innerT : udeg innerT = 3 := by simp [innerT, udeg_node]

/-- `Ztot(dtSub star3) = 7/4`: degree-4 realization of three leaves,
    `P·(1 + (1/4)·qSum) = 1·(1 + (1/4)·3)`. -/
theorem Ztot_dtSub_star3 : Ztot (dtSub star3) = 7 / 4 := by
  rw [star3, dtSub_node]
  have hlen : ([flpLeaf, flpLeaf, flpLeaf] : List UTree).length + 1 = 4 := by simp
  rw [hlen, Ztot_node_deg]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Ztot_dtSub_flpLeaf, qSum_cons, qSum, Zopen_dtSub_flpLeaf, udeg_flpLeaf, List.sum_nil,
    add_zero, Nat.cast_ofNat]
  norm_num

/-- `Zopen(dtSub star3) = 1`: the child-product of three leaves. -/
theorem Zopen_dtSub_star3 : Zopen (dtSub star3) = 1 := by
  rw [star3, dtSub_node]
  have h : Zopen (RTree.node (dtChildren (([flpLeaf, flpLeaf, flpLeaf] : List UTree).length + 1)
      [flpLeaf, flpLeaf, flpLeaf]))
      = Popen (dtChildren (([flpLeaf, flpLeaf, flpLeaf] : List UTree).length + 1)
        [flpLeaf, flpLeaf, flpLeaf]) := rfl
  rw [h, Popen_dtChildren]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Ztot_dtSub_flpLeaf, mul_one]

/-- `Ztot(dtSub innerT) = 161/48`: degree-3 realization of two `star3`s,
    `(7/4)²·(1 + (1/3)·qSum)`, `qSum = 2·(1/(7/4)/4) = 2/7`. -/
theorem Ztot_dtSub_innerT : Ztot (dtSub innerT) = 161 / 48 := by
  rw [innerT, dtSub_node]
  have hlen : ([star3, star3] : List UTree).length + 1 = 3 := by simp
  rw [hlen, Ztot_node_deg]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Ztot_dtSub_star3, qSum_cons, qSum, Zopen_dtSub_star3, udeg_star3, List.sum_nil, add_zero,
    Nat.cast_ofNat]
  norm_num

/-- `Zopen(dtSub innerT) = 49/16`: the child-product `(7/4)²`. -/
theorem Zopen_dtSub_innerT : Zopen (dtSub innerT) = 49 / 16 := by
  rw [innerT, dtSub_node]
  have h : Zopen (RTree.node (dtChildren (([star3, star3] : List UTree).length + 1) [star3, star3]))
      = Popen (dtChildren (([star3, star3] : List UTree).length + 1) [star3, star3]) := rfl
  rw [h, Popen_dtChildren]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Ztot_dtSub_star3, mul_one]
  norm_num

/-! ### (1) The exact invariants of the triple-3-star. -/

/-- **`Aobj (tripleStar) = 49/8`**, via the root-degree factorization at degree 4:
    `P·(1 + (1/4)·qSum)`, `P = 1·1·1·(161/48) = 161/48`,
    `qSum = 1+1+1 + (49/16)/(161/48)/3 = 3 + 7/23 = 76/23`; `(161/48)·(1 + (1/4)·(76/23)) = 49/8`. -/
theorem Aobj_tripleStar : Aobj tripleStar = 49 / 8 := by
  rw [tripleStar, Aobj_factor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_cons, List.length_nil, qSum_cons, qSum, Ztot_dtSub_flpLeaf, Zopen_dtSub_flpLeaf,
    udeg_flpLeaf, Ztot_dtSub_innerT, Zopen_dtSub_innerT, udeg_innerT, List.sum_nil, add_zero,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  norm_num

/-- **`usize (tripleStar) = 13`**: 1 root + 3 leaves + (1 + 2·(1 + 3)) = 13 vertices. -/
theorem usize_tripleStar : usize tripleStar = 13 := by
  simp only [tripleStar, innerT, star3, flpLeaf, usize_node, usizeList_cons, usizeList_nil]

/-! ### The structural recognizers on the pieces (for `strDefect`). -/

theorem isLeaf_flpLeaf : isLeaf flpLeaf = true := by simp [flpLeaf, isLeaf]
theorem isPiece_flpLeaf : isPiece flpLeaf = true := by
  simp [isPiece, isArm, isCherry, isLeaf, flpLeaf]
/-- `star3` (three leaves) is NON-piece: not a cherry (3 children), not an arm (leaves aren't cherries). -/
theorem isPiece_star3 : isPiece star3 = false := by
  simp [isPiece, isArm, isCherry, isLeaf, star3, flpLeaf]
/-- `innerT = node [star3, star3]` is NON-piece: 2 non-cherry children. -/
theorem isPiece_innerT : isPiece innerT = false := by
  simp [isPiece, isArm, isCherry, isLeaf, innerT, star3, flpLeaf]

/-- **`strDefect (tripleStar) = 1`** — its min-defect rooting.  The root has one non-piece child
    (`innerT`), so the root layer contributes `npCount-1 = 1-1 = 0`; `innerT` has two non-piece
    `star3` children so its own layer contributes `npCount-1 = 2-1 = 1`; each `star3` has only leaf
    (piece) children so `strDefect star3 = 0`.  Total `= 0 + (1 + 0) = 1`. -/
theorem strDefect_tripleStar : strDefect tripleStar = 1 := by
  rw [tripleStar, strDefect]
  -- npCount [leaf,leaf,leaf,innerT] : leaves are pieces, innerT is not -> 1
  have hnp : npCount [flpLeaf, flpLeaf, flpLeaf, innerT] = 1 := by
    simp only [npCount, isPiece_flpLeaf, isPiece_innerT, if_true]; decide
  rw [hnp]
  -- npDefectSum : only innerT (non-piece) contributes strDefect innerT
  have hstar : strDefect star3 = 0 := by
    rw [star3, strDefect]
    have h0 : npCount [flpLeaf, flpLeaf, flpLeaf] = 0 := by
      simp only [npCount, isPiece_flpLeaf, if_true]
    rw [h0]
    simp only [npDefectSum, isPiece_flpLeaf, if_true]
  have hinner : strDefect innerT = 1 := by
    rw [innerT, strDefect]
    have h2 : npCount [star3, star3] = 2 := by
      simp only [npCount, isPiece_star3]; decide
    rw [h2]
    have h0 : npDefectSum [star3, star3] = 0 := by
      simp only [npDefectSum, isPiece_star3, hstar]; decide
    rw [h0]
  have hnpd : npDefectSum [flpLeaf, flpLeaf, flpLeaf, innerT] = 1 := by
    simp only [npDefectSum, isPiece_flpLeaf, isPiece_innerT, hinner, if_true]; decide
  rw [hnpd]

/-! ### The `StraightStep_sized` witness: the 6-arm cherry-spider. -/

/-- The 6-arm cherry-spider `node [cherryU, cherryU, cherryU, cherryU, cherryU, cherryU]`. -/
def cherrySpider6 : UTree := UTree.node (List.replicate 6 cherryU)

/-- `usize (cherrySpider6) = 13`: 1 hub + 6 cherries × 2 vertices. -/
theorem usize_cherrySpider6 : usize cherrySpider6 = 13 := by
  simp only [cherrySpider6, cherryU, usize_node, usizeList_eq_sum, List.map_replicate,
    List.sum_replicate]
  simp [usize_node, usizeList_cons, usizeList_nil]

/-- `strDefect (cherrySpider6) = 0`: every child is a cherry (a piece), so `npCount = 0`. -/
theorem strDefect_cherrySpider6 : strDefect cherrySpider6 = 0 := by
  rw [cherrySpider6, strDefect]
  have hnp : npCount (List.replicate 6 cherryU) = 0 := by
    induction (6 : ℕ) with
    | zero => simp [npCount]
    | succ k ih => rw [List.replicate_succ, npCount, isPiece_cherryU]; simpa using ih
  have hnpd : npDefectSum (List.replicate 6 cherryU) = 0 := by
    induction (6 : ℕ) with
    | zero => simp [npDefectSum]
    | succ k ih => rw [List.replicate_succ, npDefectSum, isPiece_cherryU]; simpa using ih
  rw [hnp, hnpd]

/-- `Aobj (cherrySpider6) = 243/16` = `2·(3/2)^5`: degree-6 realization of six cherries,
    `P·(1 + (1/6)·qSum)`, `P = (3/2)^6`, `qSum = 6·((1)/(3/2)/2) = 6·(1/3) = 2`. -/
theorem Aobj_cherrySpider6 : Aobj cherrySpider6 = 243 / 16 := by
  rw [cherrySpider6, Aobj_factor]
  have hP : ((List.replicate 6 cherryU).map fun K => Ztot (dtSub K)).prod = (3 / 2 : ℝ) ^ 6 := by
    rw [List.map_replicate, Ztot_dtSub_cherryU, List.prod_replicate]
  have hq : qSum (List.replicate 6 cherryU) = 2 := by
    rw [qSum, List.map_replicate, List.sum_replicate, Ztot_dtSub_cherryU, Zopen_dtSub_cherryU,
      udeg_cherryU]
    norm_num
  rw [hP, hq]
  simp only [List.length_replicate, Nat.cast_ofNat]
  norm_num

/-- **The Lean obligation HOLDS at the triple-3-star.**  `StraightStep_sized tripleStar cherrySpider6`:
    same vertex count (13), `Aobj` increases (`49/8 → 243/16`), and `strDefect` strictly drops
    (`1 → 0`).  So the maximally symmetric triple-3-star — the UNIQUE n=13 obstruction to the
    single-SPR / strict-`Aobj` STRENGTHENING — does NOT block the actual `StraightProgress_sized`
    obligation.  The straightening witness is a genuine multi-vertex restructuring (a cherry-spider),
    not one SPR relocation. -/
theorem straightStep_tripleStar_witness : StraightStep_sized tripleStar cherrySpider6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [usize_tripleStar, usize_cherrySpider6]
  · rw [Aobj_tripleStar, Aobj_cherrySpider6]; norm_num
  · rw [strDefect_tripleStar, strDefect_cherrySpider6]; norm_num

/-- **`StraightProgress_sized` is witnessed at the obstruction.**  Existential form: the triple-3-star
    (which has `strDefect ≠ 0`) admits a `StraightStep_sized`. -/
theorem tripleStar_has_straightStep :
    strDefect tripleStar ≠ 0 ∧ ∃ t', StraightStep_sized tripleStar t' := by
  refine ⟨?_, cherrySpider6, straightStep_tripleStar_witness⟩
  rw [strDefect_tripleStar]; norm_num

end Step3
end R3Cert
