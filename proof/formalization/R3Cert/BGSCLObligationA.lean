/-
  R4-R7 campaign, PHASE 7 (Obligation A — HONEST NEGATIVE RESULT).

  MISSION was to prove **Obligation A**, the general-tree Kelmans cavity relocation inequality

      Aobj (node (A :: B :: rest)) ≤ Aobj (node (pushInto A B :: rest))            (†)

  the `hAobj` hypothesis consumed by `R47R7PushInto.deephub_local_straightStep` and
  `R47R7Debranch.debranch_local_straightStep` (and hence, once per descent level, by the
  `StraightProgress_sized` straightening that feeds the tree→hub reduction).

  RESULT (this file): (†) is **FALSE**, and this file gives a KERNEL-CHECKED counterexample.
  It is not merely hard — the encoded `pushInto` / hub-attach move is the WRONG move.

  WHY (the mathematics, verified numerically in `telperion/scratch/oblA_*.py`).
  `Aobj = per(L)/∏deg` is root-INVARIANT (matches the unrooted graph value) and, on trees,
  is MINIMIZED at the star and MAXIMIZED toward the path: equalizing the degree sequence
  raises `Aobj`, concentrating it lowers `Aobj`.  Phase-0's straightening witness family
  (`PHASE0_STRAIGHTPROGRESS_FINDINGS.md`) is a degree-EQUALIZING SPR (a degree-3 branch
  vertex drops to 2, a degree-1 spine vertex rises to 2, e.g. `[3,3,3,3,1,…] → [3,3,3,2,2,…]`,
  `Aobj 466/81 → 377/54`, UP).  But `pushInto A B` attaches `B` to `A`'s DEEP hub, RAISING an
  already-high-degree vertex — it CONCENTRATES degree (`… → [4,3,3,2,…]`, `Aobj` DOWN).  These
  are OPPOSITE moves.  So (†) cannot hold: the reduction is wired to the star-ward move, not to
  the caterpillar-ward Phase-0 witness.

  The two witnesses proved below (both satisfy every stated hypothesis of (†) —
  `isPiece A = false`, `isPiece B = false`, `strDefect A = 0`):

    * deep-hub form  (`deephub_local_straightStep`):
        A = B = node [node [], node []],  rest = [].
        Aobj (node [A, B]) = 10/3,  Aobj (node [pushInto A B]) = 3;  10/3 > 3.

    * direct-hub form (`debranch_local_straightStep`):
        As = [node []],  B = node [node [], node []],  rest = [].
        Aobj (node [node As, B]) = 19/6,  Aobj (node [node (As ++ [B])]) = 26/9;  19/6 > 26/9.

  CONSEQUENCE.  `deephub_local_straightStep` / `debranch_local_straightStep` are vacuously
  fine as *conditional* lemmas, but their `hAobj` premise is unsatisfiable in general, so they
  cannot discharge `StraightProgress_sized` as intended.  The tree→hub reduction must be
  RE-ENCODED around the degree-EQUALIZING SPR move (the genuine Phase-0 witness), whose local
  `Aobj`-monotone inequality is the *real* Obligation A.  That corrected local inequality is
  stated as `RealObligationA` below (a Prop, not proven here — it is the sharpened target).

  Everything here is `no `sorry``, no `axiom`, no `native_decide`.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47Tree
import R3Cert.R47R7PushInto
import R3Cert.R47HubState

namespace R3Cert
namespace Step3

open RTree

/-! ### A concrete evaluator for `Aobj` on the small witness trees

    `Aobj t = Ztot (dtRealize t)` is a division-free rational recursion, so each concrete tree
    evaluates by unfolding `dtRealize`/`dtChildren`/`Ztot`/`Popen`/`Matched`/`dtSub`/`udeg`.  We
    package the leaf and the "two-leaf node" (`node [leaf, leaf]`) values, which is all the two
    witnesses need. -/

/-- The bare leaf. -/
private def leafU : UTree := UTree.node []

/-- `dtSub leaf` has `Ztot = 1`, `Zopen = 1` (no children). -/
private theorem Ztot_dtSub_leaf : Ztot (dtSub leafU) = 1 := by
  rw [leafU, dtSub_node, dtChildren_nil, Ztot, Popen, Matched]; norm_num

private theorem Zopen_dtSub_leaf : Zopen (dtSub leafU) = 1 := by
  rw [leafU, dtSub_node, dtChildren_nil, Zopen, Popen]

private theorem udeg_leaf : udeg leafU = 1 := by rw [leafU, udeg_node]; rfl

/-- The two-leaf node `V := node [leaf, leaf]` (a "cherry-of-leaves" / degree-3 vertex). -/
private def vee : UTree := UTree.node [leafU, leafU]

private theorem udeg_vee : udeg vee = 3 := by rw [vee, udeg_node]; rfl

/-- `Ztot (dtSub vee)`.  `dtSub vee` = node of degree `udeg vee = 3`, two leaf children each with
    edge weight `1/(3 · udeg leaf) = 1/3`.  `Popen = 1·1 = 1`, `Matched = 1/3·1·1 + 1·(1/3·1·1) =
    2/3`, so `Ztot = 1 + 2/3 = 5/3`. -/
private theorem Ztot_dtSub_vee : Ztot (dtSub vee) = 5 / 3 := by
  rw [vee, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched_cons, Matched, Popen_cons, Popen_cons, Popen,
    Ztot_dtSub_leaf, Zopen_dtSub_leaf, udeg_leaf]
  norm_num

private theorem Zopen_dtSub_vee : Zopen (dtSub vee) = 1 := by
  rw [vee, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Zopen, Popen_cons, Popen_cons, Popen, Ztot_dtSub_leaf]; norm_num

/-! ### The deep-hub witness: `Aobj (node [vee, vee]) = 10/3 > 3 = Aobj (node [pushInto vee vee])` -/

/-- `Before = node [vee, vee]`.  Root degree `2`; two `vee` children, edge weight
    `1/(2 · udeg vee) = 1/6`.  `Popen = (5/3)² = 25/9`,
    `Matched = 1/6 · Zopen(vee) · Ztot(vee) + Ztot(vee) · (1/6 · Zopen(vee) · 1)
             = 1/6·1·5/3 + 5/3·1/6·1 = 5/9`, so `Ztot = 25/9 + 5/9 = 30/9 = 10/3`. -/
private theorem Aobj_before_deephub : Aobj (UTree.node [vee, vee]) = 10 / 3 := by
  rw [Aobj, dtRealize_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched_cons, Matched, Popen_cons, Popen_cons, Popen,
    Ztot_dtSub_vee, Zopen_dtSub_vee, udeg_vee]
  norm_num

/-- `pushInto vee vee = node [leaf, leaf, vee]`: `vee = node [leaf, leaf]` has no non-piece child,
    so `pushIntoList` skips both leaf pieces and appends `vee` at the (reached) hub. -/
private theorem isPiece_leafU : isPiece leafU = true := by rw [leafU, isPiece, isArm, isCherry]; rfl

private theorem pushInto_vee_vee : pushInto vee vee = UTree.node [leafU, leafU, vee] := by
  rw [show vee = UTree.node [leafU, leafU] from rfl, pushInto, pushIntoList,
    if_pos isPiece_leafU, pushIntoList, if_pos isPiece_leafU, pushIntoList]

/-- `After = node [pushInto vee vee] = node [node [leaf, leaf, vee]]`.  Root degree `1`; single
    child `H := node [leaf, leaf, vee]` with edge weight `1/(1 · udeg H) = 1/4`.
    `Ztot(dtSub H)`: `H` at degree `4`, children leaf, leaf, vee with weights `1/4, 1/4,
    1/(4·3)=1/12`.  Direct expansion gives `Ztot(dtSub H) = 12/5` and `Zopen(dtSub H) = 5/3`,
    hence `Aobj(After) = Popen + Matched = 12/5 + 1/4 · 5/3 = 12/5 + 5/12`… computed below by full
    unfolding to `3`. -/
private theorem Aobj_after_deephub : Aobj (UTree.node [pushInto vee vee]) = 3 := by
  rw [pushInto_vee_vee, Aobj, dtRealize_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched, Popen_cons, Popen]
  -- the single child is `dtSub (node [leaf, leaf, vee])`; unfold its Ztot/Zopen
  rw [dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Zopen, Matched_cons, Matched_cons, Matched_cons, Matched,
    Popen_cons, Popen_cons, Popen_cons, Popen,
    Ztot_dtSub_leaf, Zopen_dtSub_leaf, Ztot_dtSub_vee, Zopen_dtSub_vee, udeg_leaf, udeg_vee,
    show udeg (UTree.node [leafU, leafU, vee]) = 4 by rw [udeg_node]; rfl]
  norm_num

/-- **The deep-hub witness satisfies every hypothesis of `deephub_local_straightStep`'s `hAobj`.**
    `A = B = vee` are non-piece with `strDefect vee = 0`. -/
private theorem vee_isPiece_false : isPiece vee = false := by
  rw [vee, isPiece, isArm, isCherry]
  simp only [List.all_cons, List.all_nil, leafU, isCherry, Bool.and_true]
  rfl

private theorem strDefect_vee : strDefect vee = 0 := by
  rw [vee, strDefect, npCount, npCount, npCount, npDefectSum, npDefectSum, npDefectSum]
  simp only [leafU, isPiece, isArm, isCherry, List.all_nil]
  rfl

/-- **KERNEL-CHECKED COUNTEREXAMPLE to the deep-hub Obligation A.**  With `A = B = vee`
    (non-piece, `strDefect = 0`) and `rest = []`, the `hAobj` premise of
    `deephub_local_straightStep` is FALSE: `Aobj` strictly DECREASES under `pushInto`. -/
theorem deephub_obligationA_false :
    ¬ (Aobj (UTree.node (vee :: vee :: ([] : List UTree)))
        ≤ Aobj (UTree.node (pushInto vee vee :: ([] : List UTree)))) := by
  rw [show (vee :: vee :: ([] : List UTree)) = [vee, vee] from rfl,
      show (pushInto vee vee :: ([] : List UTree)) = [pushInto vee vee] from rfl,
      Aobj_before_deephub, Aobj_after_deephub]
  norm_num

/-! ### The direct-hub witness (`debranch_local_straightStep` form)

    `As = [leaf]`, `B = vee`.  `Before = node [node [leaf], vee]`,
    `After = node [node ([leaf] ++ [vee])] = node [node [leaf, vee]]`.
    `Aobj(Before) = 19/6 > 26/9 = Aobj(After)`. -/

/-- The hub `node [leaf]` (a "stem"): `Ztot(dtSub) = 3/2`, `Zopen = 1`. -/
private def stem : UTree := UTree.node [leafU]

private theorem udeg_stem : udeg stem = 2 := by rw [stem, udeg_node]; rfl

private theorem Ztot_dtSub_stem : Ztot (dtSub stem) = 3 / 2 := by
  rw [stem, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched, Popen_cons, Popen, Ztot_dtSub_leaf, Zopen_dtSub_leaf, udeg_leaf]
  norm_num

private theorem Aobj_before_direct : Aobj (UTree.node [stem, vee]) = 19 / 6 := by
  rw [Aobj, dtRealize_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched_cons, Matched, Popen_cons, Popen_cons, Popen,
    Ztot_dtSub_stem, Ztot_dtSub_vee, Zopen_dtSub_vee, udeg_stem, udeg_vee]
  -- Zopen(dtSub stem) still present
  rw [show Zopen (dtSub stem) = 1 by
        rw [stem, dtSub_node]
        simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
        rw [Zopen, Popen_cons, Popen, Ztot_dtSub_leaf]; norm_num]
  norm_num

private theorem Aobj_after_direct : Aobj (UTree.node [UTree.node [leafU, vee]]) = 26 / 9 := by
  rw [Aobj, dtRealize_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched, Popen_cons, Popen, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Zopen, Matched_cons, Matched_cons, Matched, Popen_cons, Popen_cons, Popen,
    Ztot_dtSub_leaf, Zopen_dtSub_leaf, Ztot_dtSub_vee, Zopen_dtSub_vee, udeg_leaf, udeg_vee,
    show udeg (UTree.node [leafU, vee]) = 3 by rw [udeg_node]; rfl]
  norm_num

/-- **KERNEL-CHECKED COUNTEREXAMPLE to the direct-hub Obligation A** (`debranch_local_straightStep`
    form).  `As = [leaf]` (all-piece), `B = vee` (non-piece); the two `isPiece` side conditions
    hold, yet the `hAobj` premise is FALSE: `19/6 > 26/9`. -/
theorem direct_obligationA_false :
    ¬ (Aobj (UTree.node (UTree.node [leafU] :: vee :: ([] : List UTree)))
        ≤ Aobj (UTree.node (UTree.node ([leafU] ++ [vee]) :: ([] : List UTree)))) := by
  rw [show ([leafU] ++ [vee]) = [leafU, vee] from rfl,
      show (UTree.node [leafU] :: vee :: ([] : List UTree)) = [stem, vee] from rfl,
      show (UTree.node [leafU, vee] :: ([] : List UTree)) = [UTree.node [leafU, vee]] from rfl,
      Aobj_before_direct, Aobj_after_direct]
  norm_num

/-! ### The genuine (corrected) local obligation — the REAL Obligation A

    The Phase-0 witness family is a degree-EQUALIZING SPR, not `pushInto`.  Its local
    `Aobj`-monotone inequality — the sharpened target the tree→hub reduction actually needs — is
    the following.  It is stated (not proved) here as the crisp residual obligation; note the
    move `f` must send `t` to a strictly-lower-`strDefect`, same-`usize` tree whose degree
    sequence is EQUALIZED (not concentrated), which the numerics (`telperion/scratch/oblA_*.py`)
    confirm is `Aobj`-monotone on every case up to `n = 12`. -/

/-- **The residual (true) local monotonicity target.**  A straightening move `f` is a
    `RealObligationA` witness at `t` iff it preserves the vertex count, strictly drops the
    off-spine defect, and does NOT decrease `Aobj`.  (The `pushInto` move above fails the third
    clause; the Phase-0 degree-equalizing SPR satisfies all three.  Encoding such an `f` in Lean
    and proving `Aobj`-monotonicity is the corrected, still-open Obligation A.) -/
def RealObligationA (f : UTree → UTree) : Prop :=
  ∀ t : UTree, strDefect t ≠ 0 →
    usize (f t) = usize t ∧ strDefect (f t) < strDefect t ∧ Aobj t ≤ Aobj (f t)

end Step3
end R3Cert
