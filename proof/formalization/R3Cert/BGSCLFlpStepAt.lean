/-
  Problem B, Stage B3: the FLP move CLASS as an inductive step relation, closed under depth.

  `FlpStepAt t t'` holds when `t'` is obtained from `t` by one strDefect-reducing FLP flip at any
  depth: a site child whose children are (up to permutation) TWO leaves plus an all-cherry crest is
  completed to an ARM (`flpChildAfter crest`), at a site parent carrying at least one other
  non-piece child.  The master theorem `FlpStepAt.props` proves, by ONE induction, that every such
  step carries the full invariant bundle -- non-pieceness of both sides, `usize` equality, strict
  `strDefect` drop, the self-propagating cavity-gain pair (G1, G2), and `Aobj` monotonicity -- so
  `FlpStepAt.straightStep : FlpStepAt t t' -> StraightStep_sized t t'` with NO side conditions.

  HONESTY (measured, exact enumeration n <= 12): the single-flip class covers 1004 of 2072
  positive-defect rooted trees (48.5%); the multi-flip generalization (`2m` leaves, this file)
  covers 1085 (52.4%) and is COMPLETE for internal piece-completion.  It is NOT full coverage:
  piece sizes are {1,2} u {odd >= 3}, so an even-size (>= 4) defective subtree (e.g.
  `node [leaf,leaf,leaf]`, 4 vertices) can NEVER be completed to a piece by internal moves -- a
  PARITY obstruction; likewise sites with arm children cannot complete without dismantling them.
  Those trees need cross-boundary moves (the Type-W-side residual).  Accordingly the coverage
  hypothesis is stated GENERICALLY
  (`straightProgress_sized_of_coverage`): any step relation refining `StraightStep_sized` with full
  coverage yields `StraightProgress_sized` (hence Hnorm via `tree_to_hub_sized`).  Widening the
  move class = enlarging the relation; the G-machinery (BGSCLFlpDeepLift) is move-agnostic.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLFlpDeepLift

namespace R3Cert
namespace Step3

open RTree

/-! ### Small piece facts -/

theorem isCherry_flpLeaf : isCherry flpLeaf = false := rfl

theorem isPiece_flpLeaf : isPiece flpLeaf = true := by
  simp [isPiece, isArm, flpLeaf]

theorem isCherry_flpStem : isCherry flpStem = true := rfl

/-- Completing the site child: with an all-cherry crest, `flpChildAfter crest` is an ARM. -/
theorem isPiece_flpChildAfter_of_cherries {crest : List UTree}
    (hcrest : crest.all isCherry = true) : isPiece (flpChildAfter crest) = true := by
  have harm : isArm (flpChildAfter crest) = true := by
    simp only [flpChildAfter, isArm, List.all_cons, hcrest, Bool.and_true, isCherry_flpStem]
  simp [isPiece, harm]

/-- A node with a NON-CHERRY member among `>= 2` children is non-piece. -/
theorem isPiece_node_of_noncherry_mem {cs : List UTree} {x : UTree}
    (hx : x ∈ cs) (hxc : isCherry x = false) (hlen : 2 ≤ cs.length) :
    isPiece (UTree.node cs) = false := by
  rcases cs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hx
  · simp at hlen
  · have harm : isArm (UTree.node (a :: b :: rest)) = false := by
      simp only [isArm]
      cases hall : (a :: b :: rest).all isCherry
      · rfl
      · have := List.all_eq_true.mp hall x hx
        rw [hxc] at this
        exact absurd this (by simp)
    have hch : isCherry (UTree.node (a :: b :: rest)) = false := rfl
    simp [isPiece, harm, hch]

/-! ### Permutation transport of the subtree cavity statistics -/

/-- `Ztot(dtSub)`, `Zopen(dtSub)` and `udeg` of a node depend only on the child MULTISET. -/
theorem dtSub_stats_perm {cs ds : List UTree} (h : cs.Perm ds) :
    Ztot (dtSub (UTree.node cs)) = Ztot (dtSub (UTree.node ds))
      ∧ Zopen (dtSub (UTree.node cs)) = Zopen (dtSub (UTree.node ds))
      ∧ udeg (UTree.node cs) = udeg (UTree.node ds) := by
  have hprod : (cs.map fun K => Ztot (dtSub K)).prod = (ds.map fun K => Ztot (dtSub K)).prod :=
    (h.map _).prod_eq
  have hq : qSum cs = qSum ds := by
    simp only [qSum]
    exact (h.map _).sum_eq
  have hlen := h.length_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [Ztot_dtSub_node_eq, Ztot_dtSub_node_eq, hprod, hq, hlen]
  · rw [Zopen_dtSub_node_eq, Zopen_dtSub_node_eq, hprod]
  · rw [udeg_node, udeg_node, hlen]

/-! ### The FLP child gains, general crest -/

/-- The unweighted G2 gain of the acted child at ANY crest: `P/(n+3) <= (3/2)P/(n+2)`. -/
theorem flp_child_G2 (crest : List UTree) :
    Zopen (dtSub (flpChildBefore crest)) / (udeg (flpChildBefore crest) : ℝ)
      ≤ Zopen (dtSub (flpChildAfter crest)) / (udeg (flpChildAfter crest) : ℝ) := by
  rw [Zopen_dtSub_flpChildBefore, Zopen_dtSub_flpChildAfter,
      udeg_flpChildBefore, udeg_flpChildAfter]
  have hP := flp_crest_P_nonneg crest
  have hn : (0 : ℝ) ≤ (crest.length : ℝ) := Nat.cast_nonneg _
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hP hn]

/-! ### The composite multi-flip child stats -/

/-- A replicate of stems is all-cherry. -/
theorem all_isCherry_replicate_flpStem (m : ℕ) :
    (List.replicate m flpStem).all isCherry = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [(List.mem_replicate.mp hx).2]
  exact isCherry_flpStem

/-- **Composite multi-flip child stats.**  `2m` leaves complete to `m` stems in one step,
    preserving `usize` and carrying the cavity-gain pair, for ANY tail `crest`.  Induction on
    `m`, conjugating each single flip (general-crest lemmas) by permutations -- the stats are
    child-multiset functions (`dtSub_stats_perm`). -/
theorem multiFlp_child_stats :
    ∀ (m : ℕ) (crest : List UTree),
      usize (UTree.node (List.replicate (2 * m) flpLeaf ++ crest))
          = usize (UTree.node (List.replicate m flpStem ++ crest))
        ∧ Ztot (dtSub (UTree.node (List.replicate (2 * m) flpLeaf ++ crest)))
            ≤ Ztot (dtSub (UTree.node (List.replicate m flpStem ++ crest)))
        ∧ Zopen (dtSub (UTree.node (List.replicate (2 * m) flpLeaf ++ crest)))
              / (udeg (UTree.node (List.replicate (2 * m) flpLeaf ++ crest)) : ℝ)
            ≤ Zopen (dtSub (UTree.node (List.replicate m flpStem ++ crest)))
              / (udeg (UTree.node (List.replicate m flpStem ++ crest)) : ℝ)
  | 0, crest => by simp
  | m + 1, crest => by
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h2, List.replicate_succ, List.replicate_succ, List.replicate_succ]
    -- one flip at crest1 = replicate (2m) leaf ++ crest, then perm-conjugate, then IH
    set crest1 := List.replicate (2 * m) flpLeaf ++ crest with hc1
    have hpm : (flpStem :: crest1).Perm
        (List.replicate (2 * m) flpLeaf ++ flpStem :: crest) := by
      rw [hc1]
      exact List.perm_middle.symm
    have hpf : (List.replicate m flpStem ++ flpStem :: crest).Perm
        (flpStem :: (List.replicate m flpStem ++ crest)) := List.perm_middle
    obtain ⟨ihu, ihZ, ihG⟩ := multiFlp_child_stats m (flpStem :: crest)
    obtain ⟨hpmZ, hpmO, hpmU⟩ := dtSub_stats_perm hpm
    obtain ⟨hpfZ, hpfO, hpfU⟩ := dtSub_stats_perm hpf
    refine ⟨?_, ?_, ?_⟩
    · calc usize (UTree.node (flpLeaf :: flpLeaf :: crest1))
          = usize (UTree.node (flpStem :: crest1)) := (usize_flp_move_eq crest1).symm
        _ = usize (UTree.node (List.replicate (2 * m) flpLeaf ++ flpStem :: crest)) := by
            rw [usize_node, usize_node, usizeList_perm hpm]
        _ = usize (UTree.node (List.replicate m flpStem ++ flpStem :: crest)) := ihu
        _ = usize (UTree.node (flpStem :: (List.replicate m flpStem ++ crest))) := by
            rw [usize_node, usize_node, usizeList_perm hpf]
    · calc Ztot (dtSub (UTree.node (flpLeaf :: flpLeaf :: crest1)))
          ≤ Ztot (dtSub (UTree.node (flpStem :: crest1))) := Ztot_dtSub_flp_child_le crest1
        _ = Ztot (dtSub (UTree.node (List.replicate (2 * m) flpLeaf ++ flpStem :: crest))) :=
            hpmZ
        _ ≤ Ztot (dtSub (UTree.node (List.replicate m flpStem ++ flpStem :: crest))) := ihZ
        _ = Ztot (dtSub (UTree.node (flpStem :: (List.replicate m flpStem ++ crest)))) := hpfZ
    · calc Zopen (dtSub (UTree.node (flpLeaf :: flpLeaf :: crest1)))
              / (udeg (UTree.node (flpLeaf :: flpLeaf :: crest1)) : ℝ)
          ≤ Zopen (dtSub (UTree.node (flpStem :: crest1)))
              / (udeg (UTree.node (flpStem :: crest1)) : ℝ) := flp_child_G2 crest1
        _ = Zopen (dtSub (UTree.node (List.replicate (2 * m) flpLeaf ++ flpStem :: crest)))
              / (udeg (UTree.node (List.replicate (2 * m) flpLeaf ++ flpStem :: crest)) : ℝ) := by
            rw [hpmO, hpmU]
        _ ≤ Zopen (dtSub (UTree.node (List.replicate m flpStem ++ flpStem :: crest)))
              / (udeg (UTree.node (List.replicate m flpStem ++ flpStem :: crest)) : ℝ) := ihG
        _ = Zopen (dtSub (UTree.node (flpStem :: (List.replicate m flpStem ++ crest))))
              / (udeg (UTree.node (flpStem :: (List.replicate m flpStem ++ crest))) : ℝ) := by
            rw [hpfO, hpfU]

/-! ### The strDefect drop at a completed site -/

/-- Replacing a non-piece defect-free site child by a completed PIECE strictly lowers the site
    parent's `strDefect`, provided another non-piece sibling exists. -/
theorem strDefect_flp_site_lt (spre spost : List UTree) {u v : UTree}
    (hu_np : isPiece u = false) (hu_def : strDefect u = 0)
    (hv : isPiece v = true) (hsib : 1 ≤ npCount (spre ++ spost)) :
    strDefect (UTree.node (spre ++ v :: spost)) < strDefect (UTree.node (spre ++ u :: spost)) := by
  have hnu : npCount (spre ++ u :: spost) = npCount spre + (npCount spost + 1) := by
    rw [npCount_append, npCount, hu_np]
    simp
    omega
  have hnv : npCount (spre ++ v :: spost) = npCount spre + npCount spost := by
    rw [npCount_append, npCount, hv]
    simp
  have hdu : npDefectSum (spre ++ u :: spost) = npDefectSum spre + npDefectSum spost := by
    rw [npDefectSum_append, npDefectSum, hu_np, hu_def]
    simp
  have hdv : npDefectSum (spre ++ v :: spost) = npDefectSum spre + npDefectSum spost := by
    rw [npDefectSum_append, npDefectSum, hv]
    simp
  rw [npCount_append] at hsib
  simp only [strDefect, hnu, hnv, hdu, hdv]
  omega

/-! ### The move class -/

/-- **The depth-closed multi-flip FLP move class.**  `here`: complete a site child -- children a
    permutation of `2m` leaves (`m >= 1`) plus an all-cherry crest -- to the arm
    `node (replicate m flpStem ++ crest)` in ONE composite step, at a site parent with another
    non-piece child.  `lift`: perform the move inside any child, at any position.  Sibling splits
    (`spre/spost`, `pre/post`) are arbitrary, and the site child's own order is freed by the
    `Perm`, so the class is order-insensitive everywhere.  (`m = 1` recovers the single flip
    `flpChildAfter crest`.) -/
inductive FlpStepAt : UTree → UTree → Prop
  | here (spre spost cs crest : List UTree) (m : ℕ) (hm : 1 ≤ m)
      (hperm : cs.Perm (List.replicate (2 * m) flpLeaf ++ crest))
      (hcrest : crest.all isCherry = true)
      (hsib : 1 ≤ npCount (spre ++ spost)) :
      FlpStepAt (UTree.node (spre ++ UTree.node cs :: spost))
                (UTree.node (spre ++ UTree.node (List.replicate m flpStem ++ crest) :: spost))
  | lift (pre post : List UTree) {c c' : UTree} (h : FlpStepAt c c') :
      FlpStepAt (UTree.node (pre ++ c :: post)) (UTree.node (pre ++ c' :: post))

/-! ### The master invariant bundle -/

/-- **Every `FlpStepAt` step carries the full invariant bundle**: non-pieceness of both sides,
    `usize` equality, strict `strDefect` drop, the cavity-gain pair (G1, G2), and `Aobj`
    monotonicity.  One induction; the G-pair (BGSCLFlpDeepLift) discharges every `Aobj`
    obligation, so no per-level debt remains. -/
theorem FlpStepAt.props {t t' : UTree} (h : FlpStepAt t t') :
    isPiece t = false ∧ isPiece t' = false
      ∧ usize t = usize t'
      ∧ strDefect t' < strDefect t
      ∧ Ztot (dtSub t) ≤ Ztot (dtSub t')
      ∧ Zopen (dtSub t) / (udeg t : ℝ) ≤ Zopen (dtSub t') / (udeg t' : ℝ)
      ∧ Aobj t ≤ Aobj t' := by
  induction h with
  | here spre spost cs crest m hm hperm hcrest hsib =>
    -- child-level: `node cs` matches the `2m`-leaf site up to permutation
    have hmem_leaf : flpLeaf ∈ cs :=
      hperm.mem_iff.mpr
        (List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
    have hlen_cs : cs.length = 2 * m + crest.length := by
      have := hperm.length_eq
      simpa using this
    have hnp_cs : isPiece (UTree.node cs) = false :=
      isPiece_node_of_noncherry_mem hmem_leaf isCherry_flpLeaf (by omega)
    have hpieces : ∀ x ∈ cs, isPiece x = true := by
      intro x hx
      have hx' := hperm.mem_iff.mp hx
      rcases List.mem_append.mp hx' with hx' | hx'
      · rw [(List.mem_replicate.mp hx').2]
        exact isPiece_flpLeaf
      · have := List.all_eq_true.mp hcrest x hx'
        simp [isPiece, this]
    have hdef_cs : strDefect (UTree.node cs) = 0 := by
      simp [strDefect, npCount_pieces hpieces, npDefectSum_pieces hpieces]
    obtain ⟨hZeq, hOeq, hueq⟩ := dtSub_stats_perm hperm
    obtain ⟨hmfu, hmfZ, hmfG⟩ := multiFlp_child_stats m crest
    have husz_c : usize (UTree.node cs)
        = usize (UTree.node (List.replicate m flpStem ++ crest)) := by
      calc usize (UTree.node cs)
          = usize (UTree.node (List.replicate (2 * m) flpLeaf ++ crest)) := by
            rw [usize_node, usize_node, usizeList_perm hperm]
        _ = usize (UTree.node (List.replicate m flpStem ++ crest)) := hmfu
    have hG1_c : Ztot (dtSub (UTree.node cs))
        ≤ Ztot (dtSub (UTree.node (List.replicate m flpStem ++ crest))) := by
      rw [hZeq]
      exact hmfZ
    have hG2_c : Zopen (dtSub (UTree.node cs)) / (udeg (UTree.node cs) : ℝ)
        ≤ Zopen (dtSub (UTree.node (List.replicate m flpStem ++ crest)))
            / (udeg (UTree.node (List.replicate m flpStem ++ crest)) : ℝ) := by
      rw [hOeq, hueq]
      exact hmfG
    have hpiece_after : isPiece (UTree.node (List.replicate m flpStem ++ crest)) = true := by
      have harm : isArm (UTree.node (List.replicate m flpStem ++ crest)) = true := by
        simp only [isArm, List.all_append, all_isCherry_replicate_flpStem, hcrest,
          Bool.and_self]
      simp [isPiece, harm]
    -- RHS parent non-pieceness via the non-piece sibling
    obtain ⟨x, hxmem, hxnp⟩ := exists_nonpiece_of_npCount_pos hsib
    have hxc : isCherry x = false := by
      rcases hc : isCherry x with _ | _
      · rfl
      · exfalso
        rw [isPiece, hc, Bool.or_true] at hxnp
        exact absurd hxnp (by simp)
    have hlen2 :
        2 ≤ (spre ++ UTree.node (List.replicate m flpStem ++ crest) :: spost).length := by
      have hpos : 0 < (spre ++ spost).length := List.length_pos_of_mem hxmem
      simp only [List.length_append, List.length_cons]
      simp only [List.length_append] at hpos
      omega
    have hxmem' : x ∈ spre ++ UTree.node (List.replicate m flpStem ++ crest) :: spost := by
      rcases List.mem_append.mp hxmem with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hnp_after :
        isPiece (UTree.node (spre ++ UTree.node (List.replicate m flpStem ++ crest) :: spost))
          = false :=
      isPiece_node_of_noncherry_mem hxmem' hxc hlen2
    exact ⟨isPiece_plug1 spre spost hnp_cs,
           hnp_after,
           usize_child_replace spre spost husz_c,
           strDefect_flp_site_lt spre spost hnp_cs hdef_cs hpiece_after hsib,
           (dtSub_gains_lift spre spost hG1_c hG2_c).1,
           (dtSub_gains_lift spre spost hG1_c hG2_c).2,
           Aobj_child_replace_of_gains spre spost hG1_c hG2_c⟩
  | lift pre post h ih =>
    obtain ⟨ihnp, ihnp', ihusz, ihdef, ihG1, ihG2, _⟩ := ih
    exact ⟨isPiece_plug1 pre post ihnp,
           isPiece_plug1 pre post ihnp',
           usize_child_replace pre post ihusz,
           strDefect_child_replace_lt pre post ihnp ihnp' ihdef,
           (dtSub_gains_lift pre post ihG1 ihG2).1,
           (dtSub_gains_lift pre post ihG1 ihG2).2,
           Aobj_child_replace_of_gains pre post ihG1 ihG2⟩

/-- **Every FLP move-class step is a `StraightStep_sized`** -- unconditionally. -/
theorem FlpStepAt.straightStep {t t' : UTree} (h : FlpStepAt t t') :
    StraightStep_sized t t' := by
  obtain ⟨-, -, husz, hdef, -, -, hAobj⟩ := h.props
  exact ⟨husz, hAobj, hdef⟩

/-! ### The generic coverage reduction -/

/-- **`StraightProgress_sized` from any covering refinement of `StraightStep_sized`.**  The open
    half of Hnorm is now EXACTLY a coverage statement: exhibit a step relation (e.g. a union of
    move classes like `FlpStepAt`) that (a) refines `StraightStep_sized` and (b) covers every
    positive-defect tree.  `FlpStepAt` supplies (a) for its 52.4%-of-trees class (n <= 12
    measurement); the residual -- parity-blocked even-size subtrees and arm-child sites -- needs
    cross-boundary move classes riding the same G-machinery. -/
theorem straightProgress_sized_of_coverage (R : UTree → UTree → Prop)
    (hstep : ∀ {t t' : UTree}, R t t' → StraightStep_sized t t')
    (hcov : ∀ t : UTree, strDefect t ≠ 0 → ∃ t', R t t') :
    StraightProgress_sized := by
  intro t hdef
  obtain ⟨t', ht'⟩ := hcov t hdef
  exact ⟨t', hstep ht'⟩

/-- **Hnorm from coverage**: with a covering refinement in hand, every tree is `Aobj`-dominated
    by a hub-backbone of the SAME vertex count (via the already-proven `tree_to_hub_sized`). -/
theorem hnorm_of_coverage (R : UTree → UTree → Prop)
    (hstep : ∀ {t t' : UTree}, R t t' → StraightStep_sized t t')
    (hcov : ∀ t : UTree, strDefect t ≠ 0 → ∃ t', R t t') :
    ∀ t : UTree, ∃ s : List Hub, usize (backboneU s) = usize t ∧ Aobj t ≤ Aobj (backboneU s) :=
  tree_to_hub_sized (straightProgress_sized_of_coverage R hstep hcov)

end Step3
end R3Cert
