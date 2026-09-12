/-
  Adjacent leaf StraightStep, the Aobj half: the base cavity GAINS (G1/G2) for the acted node `par_w`.

  The adjacent leaf move relocates `flpLeaf` (child of `par_w`) onto the leaf of a sibling
  `par_v = node (flpLeaf :: Bv)`, extending it: `par_v → par_v' = node (flpStem :: Bv)`, and drops the
  relocated leaf from `par_w`.  The acted node changes
      c  = node (flpLeaf :: par_v :: Other)   →   c' = node (par_v' :: Other).
  With `1 ≤ Bv.length` the acted node satisfies BOTH cavity gains
      G1 : Ztot (dtSub c) ≤ Ztot (dtSub c')          (`adjLeaf_G1`)
      G2 : Zopen (dtSub c)/udeg c ≤ Zopen (dtSub c')/udeg c'   (`adjLeaf_G2`)
  so the move LIFTS through any context via `dtSub_gains_lift` / `Aobj_child_replace_of_gains` (the
  `FlpStepAt` machinery) — NO re-rooting needed.  The gains reduce (via the closed-form cavity stats of
  `par_v`, `par_v'` and the key cancellation `qContrib(par_v) = 1/(nB+3+QB)`) to the real-var inequalities
  `adj_G1_real` (`nlinarith`) and `adj_G2_real` (all-positive coeffs), both proven here.

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLFlpDeepLift
import R3Cert.BGSCLRealOblACaseAIdentity
import R3Cert.R47BackboneAmp

namespace R3Cert
namespace Step3

open RTree

/-! ### `par_v = node (flpLeaf :: Bv)` and `par_v' = node (flpStem :: Bv)` cavity stats -/

theorem parv_Ztot (Bv : List UTree) :
    Ztot (dtSub (UTree.node (flpLeaf :: Bv)))
      = (Bv.map fun K => Ztot (dtSub K)).prod * (1 + (1 + qSum Bv) / ((Bv.length : ℝ) + 2)) := by
  rw [Ztot_dtSub_node_eq, List.map_cons, List.prod_cons, Ztot_dtSub_flpLeaf,
    qSum_cons, Zopen_dtSub_flpLeaf, Ztot_dtSub_flpLeaf, udeg_flpLeaf, List.length_cons]
  push_cast; ring

theorem parv_qContrib (Bv : List UTree) :
    Zopen (dtSub (UTree.node (flpLeaf :: Bv))) / Ztot (dtSub (UTree.node (flpLeaf :: Bv)))
        / (udeg (UTree.node (flpLeaf :: Bv)) : ℝ) = 1 / ((Bv.length : ℝ) + 3 + qSum Bv) := by
  have hPB : 0 < (Bv.map fun K => Ztot (dtSub K)).prod := by
    apply List.prod_pos; intro x hx; rw [List.mem_map] at hx; obtain ⟨K, _, rfl⟩ := hx
    exact Ztot_dt_pos K
  rw [Zopen_dtSub_node_eq, List.map_cons, List.prod_cons, Ztot_dtSub_flpLeaf, one_mul, parv_Ztot,
    udeg_node, List.length_cons]
  have hQB : 0 ≤ qSum Bv := qSum_nonneg Bv
  have hd1 : (0:ℝ) < (Bv.length : ℝ) + 2 := by positivity
  have hd2 : (0:ℝ) < (Bv.length : ℝ) + 3 + qSum Bv := by positivity
  push_cast; field_simp; ring

theorem parv2_Ztot (Bv : List UTree) :
    Ztot (dtSub (UTree.node (flpStem :: Bv)))
      = (3/2) * (Bv.map fun K => Ztot (dtSub K)).prod * (1 + (1/3 + qSum Bv) / ((Bv.length : ℝ) + 2)) := by
  rw [Ztot_dtSub_node_eq, List.map_cons, List.prod_cons, Ztot_dtSub_flpStem,
    qSum_cons, Zopen_dtSub_flpStem, Ztot_dtSub_flpStem, udeg_flpStem, List.length_cons]
  push_cast; ring

theorem parv2_qContrib (Bv : List UTree) :
    Zopen (dtSub (UTree.node (flpStem :: Bv))) / Ztot (dtSub (UTree.node (flpStem :: Bv)))
        / (udeg (UTree.node (flpStem :: Bv)) : ℝ) = 1 / ((Bv.length : ℝ) + 7/3 + qSum Bv) := by
  have hPB : 0 < (Bv.map fun K => Ztot (dtSub K)).prod := by
    apply List.prod_pos; intro x hx; rw [List.mem_map] at hx; obtain ⟨K, _, rfl⟩ := hx
    exact Ztot_dt_pos K
  rw [Zopen_dtSub_node_eq, List.map_cons, List.prod_cons, Ztot_dtSub_flpStem, parv2_Ztot,
    udeg_node, List.length_cons]
  have hQB : 0 ≤ qSum Bv := qSum_nonneg Bv
  have hd1 : (0:ℝ) < (Bv.length : ℝ) + 2 := by positivity
  have hd2 : (0:ℝ) < (Bv.length : ℝ) + 7/3 + qSum Bv := by positivity
  push_cast; field_simp; ring

/-! ### The real-var core inequalities (proven arithmetic) -/

theorem adj_G1_real (PB QB PO QO nB nO : ℝ)
    (hPB : 0 < PB) (hQB : 0 ≤ QB) (hnB : 1 ≤ nB) (hPO : 0 < PO) (hQO : 0 ≤ QO) (hnO : 0 ≤ nO) :
    PB * (1 + (1 + QB)/(nB+2)) * PO * (1 + (1 + 1/(nB+3+QB) + QO)/(nO+3))
      ≤ (3/2) * PB * (1 + (1/3 + QB)/(nB+2)) * PO * (1 + (1/(nB+7/3+QB) + QO)/(nO+2)) := by
  have h2 : (0:ℝ) < nB+3+QB := by linarith
  have h3 : (0:ℝ) < nB+7/3+QB := by linarith
  rw [← sub_nonneg]
  have hh : (3/2) * PB * (1 + (1/3 + QB)/(nB+2)) * PO * (1 + (1/(nB+7/3+QB) + QO)/(nO+2))
      - PB * (1 + (1 + QB)/(nB+2)) * PO * (1 + (1 + 1/(nB+3+QB) + QO)/(nO+3))
      = PB * PO * ((3+nO)*((3*nB+7+3*QB)*(2+nO+QO)+3) - 2*(2+nO)*((nB+3+QB)*(4+nO+QO)+1))
          / (2*(nB+2)*(nO+2)*(nO+3)) := by
    have e1 : nB+2 ≠ 0 := by positivity
    have e2 : nB+3+QB ≠ 0 := by positivity
    have e3 : nB+7/3+QB ≠ 0 := by positivity
    have e4 : nO+2 ≠ 0 := by positivity
    have e5 : nO+3 ≠ 0 := by positivity
    field_simp
    ring
  rw [hh]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (le_of_lt (mul_pos hPB hPO))
  have hm := sub_nonneg.mpr hnB
  nlinarith [mul_nonneg hQB hQO, mul_nonneg hQO hnO, mul_nonneg hQB hnO,
    mul_nonneg hm hnO, mul_nonneg hm hQO, mul_nonneg hm hQB,
    mul_nonneg (mul_nonneg hnO hnO) hm, mul_nonneg hnO hnO,
    mul_nonneg hQB (mul_nonneg hnO hnO), mul_nonneg hQO (mul_nonneg hnO hnO),
    hm, hQB, hQO, hnO, mul_nonneg (mul_nonneg hQB hnO) hnO,
    mul_nonneg (mul_nonneg hQO hnO) hnO, mul_nonneg hm hm]

theorem adj_G2_real (PB QB PO QO nB nO : ℝ)
    (hPB : 0 < PB) (hQB : 0 ≤ QB) (hnB : 1 ≤ nB) (hPO : 0 < PO) (hnO : 0 ≤ nO) :
    PB * (1 + (1 + QB)/(nB+2)) * PO / (nO+3)
      ≤ (3/2) * PB * (1 + (1/3 + QB)/(nB+2)) * PO / (nO+2) := by
  rw [← sub_nonneg]
  have hh : (3/2) * PB * (1 + (1/3 + QB)/(nB+2)) * PO / (nO+2)
      - PB * (1 + (1 + QB)/(nB+2)) * PO / (nO+3)
      = PB * PO * ((3*nB+7+3*QB)*(nO+3) - 2*(nO+2)*(nB+3+QB)) / (2*(nB+2)*(nO+2)*(nO+3)) := by
    have e1 : nB+2 ≠ 0 := by positivity
    have e4 : nO+2 ≠ 0 := by positivity
    have e5 : nO+3 ≠ 0 := by positivity
    field_simp
    ring
  rw [hh]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (le_of_lt (mul_pos hPB hPO))
  nlinarith [mul_nonneg hQB hnO, mul_nonneg (by linarith : (0:ℝ) ≤ nB) hnO, hQB, hnO, hnB]

/-! ### Tree stat → real form (the outer-node expansions) -/

theorem adjLeaf_Ztot_before (Bv Other : List UTree) :
    Ztot (dtSub (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)))
      = (Bv.map fun K => Ztot (dtSub K)).prod * (1 + (1 + qSum Bv)/((Bv.length:ℝ)+2))
        * (Other.map fun K => Ztot (dtSub K)).prod
        * (1 + (1 + 1/((Bv.length:ℝ)+3+qSum Bv) + qSum Other)/((Other.length:ℝ)+3)) := by
  rw [Ztot_dtSub_node_eq, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
    Ztot_dtSub_flpLeaf, qSum_cons, qSum_cons, Zopen_dtSub_flpLeaf, Ztot_dtSub_flpLeaf, udeg_flpLeaf,
    List.length_cons, List.length_cons, parv_qContrib, parv_Ztot]
  push_cast; ring

theorem adjLeaf_Ztot_after (Bv Other : List UTree) :
    Ztot (dtSub (UTree.node (UTree.node (flpStem :: Bv) :: Other)))
      = (3/2) * (Bv.map fun K => Ztot (dtSub K)).prod * (1 + (1/3 + qSum Bv)/((Bv.length:ℝ)+2))
        * (Other.map fun K => Ztot (dtSub K)).prod
        * (1 + (1/((Bv.length:ℝ)+7/3+qSum Bv) + qSum Other)/((Other.length:ℝ)+2)) := by
  rw [Ztot_dtSub_node_eq, List.map_cons, List.prod_cons,
    qSum_cons, List.length_cons, parv2_qContrib, parv2_Ztot]
  push_cast; ring

theorem adjLeaf_Zopen_before (Bv Other : List UTree) :
    Zopen (dtSub (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)))
        / (udeg (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)) : ℝ)
      = (Bv.map fun K => Ztot (dtSub K)).prod * (1 + (1 + qSum Bv)/((Bv.length:ℝ)+2))
        * (Other.map fun K => Ztot (dtSub K)).prod / ((Other.length:ℝ)+3) := by
  rw [Zopen_dtSub_node_eq, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
    Ztot_dtSub_flpLeaf, one_mul, parv_Ztot, udeg_node, List.length_cons, List.length_cons]
  push_cast; ring

theorem adjLeaf_Zopen_after (Bv Other : List UTree) :
    Zopen (dtSub (UTree.node (UTree.node (flpStem :: Bv) :: Other)))
        / (udeg (UTree.node (UTree.node (flpStem :: Bv) :: Other)) : ℝ)
      = (3/2) * (Bv.map fun K => Ztot (dtSub K)).prod * (1 + (1/3 + qSum Bv)/((Bv.length:ℝ)+2))
        * (Other.map fun K => Ztot (dtSub K)).prod / ((Other.length:ℝ)+2) := by
  rw [Zopen_dtSub_node_eq, List.map_cons, List.prod_cons, parv2_Ztot, udeg_node, List.length_cons]
  push_cast; ring

/-! ### The base gains G1, G2 -/

private theorem hPB_pos (Bv : List UTree) : 0 < (Bv.map fun K => Ztot (dtSub K)).prod := by
  apply List.prod_pos; intro x hx; rw [List.mem_map] at hx; obtain ⟨K, _, rfl⟩ := hx; exact Ztot_dt_pos K

/-- **G1**: the acted node's `Ztot(dtSub)` does not decrease under the adjacent leaf move (`1 ≤ nB`). -/
theorem adjLeaf_G1 (Bv Other : List UTree) (hnB : 1 ≤ Bv.length) :
    Ztot (dtSub (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)))
      ≤ Ztot (dtSub (UTree.node (UTree.node (flpStem :: Bv) :: Other))) := by
  rw [adjLeaf_Ztot_before, adjLeaf_Ztot_after]
  exact adj_G1_real _ (qSum Bv) _ (qSum Other) _ _ (hPB_pos Bv) (qSum_nonneg Bv)
    (by exact_mod_cast hnB) (hPB_pos Other) (qSum_nonneg Other) (by positivity)

/-- **G2**: the acted node's weighted `Zopen(dtSub)/udeg` does not decrease (`1 ≤ nB`). -/
theorem adjLeaf_G2 (Bv Other : List UTree) (hnB : 1 ≤ Bv.length) :
    Zopen (dtSub (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)))
        / (udeg (UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other)) : ℝ)
      ≤ Zopen (dtSub (UTree.node (UTree.node (flpStem :: Bv) :: Other)))
        / (udeg (UTree.node (UTree.node (flpStem :: Bv) :: Other)) : ℝ) := by
  rw [adjLeaf_Zopen_before, adjLeaf_Zopen_after]
  exact adj_G2_real _ (qSum Bv) _ (qSum Other) _ _ (hPB_pos Bv) (qSum_nonneg Bv)
    (by exact_mod_cast hnB) (hPB_pos Other) (by positivity)

/-- **The Aobj clause of the adjacent leaf move**, lifted through any sibling context `pre`/`post`
    (via `Aobj_child_replace_of_gains`). -/
theorem adjLeaf_Aobj_le (pre post Bv Other : List UTree) (hnB : 1 ≤ Bv.length) :
    Aobj (UTree.node (pre ++ UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other) :: post))
      ≤ Aobj (UTree.node (pre ++ UTree.node (UTree.node (flpStem :: Bv) :: Other) :: post)) :=
  Aobj_child_replace_of_gains pre post (adjLeaf_G1 Bv Other hnB) (adjLeaf_G2 Bv Other hnB)

end Step3
end R3Cert
