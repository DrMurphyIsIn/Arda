/-
  A3(2) BRIDGE, stage 2(i): transport from arbitrary Balanced arms to the count form.

  The PairCollapse6 statement quantifies over ARBITRARY `BalancedArms` lists; the closed forms
  (R47PC6Bridge) and the polynomial cells (R47PC6Cells) live in count form
  (`hubArms a b = replicate a 5 ++ replicate b 4`).  This file transports all four compared
  statistics (`Ztot(dtSub)`, `Zopen(dtSub)`, `udeg`, root `Aobj`):

    * `dtSub_stats_child_congr` -- a node's statistics depend on a child only through the child's
      own `(Ztot(dtSub), Zopen(dtSub), udeg)` (immediate from the node closed-form identities);
    * `hub_stats_perm`  -- single-hub statistics are invariant under arm-list permutation;
    * `hub_stats_count` -- a Balanced single hub equals its count form (`balancedArms_perm`);
    * `pair_stats_count` -- a Balanced pair equals its count form (outer perm for hub A,
      child-congruence for the deep hub B).

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47PC6Bridge
import R3Cert.BGSCLFlpStepAt
import R3Cert.R47SharpRate

namespace R3Cert
namespace Step3
namespace PC6

open RTree

/-! ### Node statistics depend on a child only through its own statistics -/

theorem dtSub_stats_child_congr (pre post : List UTree) {c c' : UTree}
    (hZ : Ztot (dtSub c) = Ztot (dtSub c'))
    (hO : Zopen (dtSub c) = Zopen (dtSub c'))
    (hu : udeg c = udeg c') :
    Ztot (dtSub (UTree.node (pre ++ c :: post))) = Ztot (dtSub (UTree.node (pre ++ c' :: post)))
      ∧ Zopen (dtSub (UTree.node (pre ++ c :: post)))
          = Zopen (dtSub (UTree.node (pre ++ c' :: post)))
      ∧ udeg (UTree.node (pre ++ c :: post)) = udeg (UTree.node (pre ++ c' :: post))
      ∧ Aobj (UTree.node (pre ++ c :: post)) = Aobj (UTree.node (pre ++ c' :: post)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Ztot_dtSub_node_eq, Ztot_dtSub_node_eq]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
      qSum_append, qSum_cons, List.length_append, List.length_cons, hZ, hO, hu]
  · rw [Zopen_dtSub_node_eq, Zopen_dtSub_node_eq]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, hZ]
  · rw [udeg_node, udeg_node]
    simp only [List.length_append, List.length_cons]
  · rw [Aobj_factor, Aobj_factor]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
      qSum_append, qSum_cons, List.length_append, List.length_cons, hZ, hO, hu]

/-! ### Single-hub statistics under arm permutation -/

theorem hub_children_general (arms : List ℕ) (c : ℕ) :
    backboneU [(arms, c)] = UTree.node (arms.map armU ++ List.replicate c cherryU) := by
  rw [backboneU_eq, tailU_nil, List.append_nil]

theorem hub_stats_perm (arms arms' : List ℕ) (c : ℕ) (hp : arms.Perm arms') :
    Ztot (dtSub (backboneU [(arms, c)])) = Ztot (dtSub (backboneU [(arms', c)]))
      ∧ Zopen (dtSub (backboneU [(arms, c)])) = Zopen (dtSub (backboneU [(arms', c)]))
      ∧ udeg (backboneU [(arms, c)]) = udeg (backboneU [(arms', c)])
      ∧ Aobj (backboneU [(arms, c)]) = Aobj (backboneU [(arms', c)]) := by
  rw [hub_children_general, hub_children_general]
  have hperm : (arms.map armU ++ List.replicate c cherryU).Perm
      (arms'.map armU ++ List.replicate c cherryU) :=
    (hp.map armU).append_right _
  obtain ⟨hZ, hO, hu⟩ := dtSub_stats_perm hperm
  exact ⟨hZ, hO, hu, Aobj_node_perm hperm⟩

/-- A Balanced single hub carries the statistics of its count form. -/
theorem hub_stats_count (arms : List ℕ) (c : ℕ) (h : BalancedArms arms) :
    Ztot (dtSub (backboneU [(arms, c)]))
        = Ztot (dtSub (backboneU [(hubArms (arms.count 5) (arms.count 4), c)]))
      ∧ Zopen (dtSub (backboneU [(arms, c)]))
          = Zopen (dtSub (backboneU [(hubArms (arms.count 5) (arms.count 4), c)]))
      ∧ udeg (backboneU [(arms, c)])
          = udeg (backboneU [(hubArms (arms.count 5) (arms.count 4), c)])
      ∧ Aobj (backboneU [(arms, c)])
          = Aobj (backboneU [(hubArms (arms.count 5) (arms.count 4), c)]) :=
  hub_stats_perm _ _ c (balancedArms_perm arms h)

/-! ### Pair statistics: outer permutation for hub A, child congruence for hub B -/

theorem pair_children_general (armsA : List ℕ) (cA : ℕ) (armsB : List ℕ) (cb : ℕ) :
    backboneU [(armsA, cA), (armsB, cb)]
      = UTree.node (armsA.map armU ++ List.replicate cA cherryU
          ++ [backboneU [(armsB, cb)]]) := by
  rw [backboneU_eq, tailU_cons]

/-- A Balanced pair carries the statistics of its count form. -/
theorem pair_stats_count (armsA : List ℕ) (cA : ℕ) (armsB : List ℕ) (cb : ℕ)
    (hA : BalancedArms armsA) (hB : BalancedArms armsB) :
    Ztot (dtSub (backboneU [(armsA, cA), (armsB, cb)]))
        = Ztot (dtSub (backboneU [(hubArms (armsA.count 5) (armsA.count 4), cA),
            (hubArms (armsB.count 5) (armsB.count 4), cb)]))
      ∧ Zopen (dtSub (backboneU [(armsA, cA), (armsB, cb)]))
          = Zopen (dtSub (backboneU [(hubArms (armsA.count 5) (armsA.count 4), cA),
              (hubArms (armsB.count 5) (armsB.count 4), cb)]))
      ∧ udeg (backboneU [(armsA, cA), (armsB, cb)])
          = udeg (backboneU [(hubArms (armsA.count 5) (armsA.count 4), cA),
              (hubArms (armsB.count 5) (armsB.count 4), cb)])
      ∧ Aobj (backboneU [(armsA, cA), (armsB, cb)])
          = Aobj (backboneU [(hubArms (armsA.count 5) (armsA.count 4), cA),
              (hubArms (armsB.count 5) (armsB.count 4), cb)]) := by
  -- step 1: canonicalize hub B (the tail child) by child congruence
  obtain ⟨hZB, hOB, huB, -⟩ := hub_stats_count armsB cb hB
  rw [pair_children_general, pair_children_general]
  obtain ⟨h1Z, h1O, h1u, h1A⟩ :=
    dtSub_stats_child_congr (armsA.map armU ++ List.replicate cA cherryU) [] hZB hOB huB
  -- step 2: canonicalize hub A's arm block by an outer permutation
  have hpA : ((armsA.map armU ++ List.replicate cA cherryU)
        ++ [backboneU [(hubArms (armsB.count 5) (armsB.count 4), cb)]]).Perm
      (((hubArms (armsA.count 5) (armsA.count 4)).map armU ++ List.replicate cA cherryU)
        ++ [backboneU [(hubArms (armsB.count 5) (armsB.count 4), cb)]]) :=
    ((((balancedArms_perm armsA hA).map armU).append_right _).append_right _)
  obtain ⟨h2Z, h2O, h2u⟩ := dtSub_stats_perm hpA
  have h2A := Aobj_node_perm hpA
  exact ⟨h1Z.trans h2Z, h1O.trans h2O, h1u.trans h2u, h1A.trans h2A⟩

end PC6
end Step3
end R3Cert
