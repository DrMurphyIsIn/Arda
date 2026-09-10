/-
  A3(2) BRIDGE, stage 1: closed-form cavity statistics of the count-form hub and pair.

  The PairCollapse6 clauses compare `Ztot(dtSub)`, `Zopen(dtSub)/udeg` and root `Aobj` of the
  deepest-pair subtree `backboneU [(armsA,cA),(armsB,cb)]` against a single-hub target
  `backboneU [(arms',c')]`.  This file derives the EXACT closed forms of all these quantities for
  count-form arms (`hubState a b c = [(replicate a 5 ++ replicate b 4, c)]`), in the shape the
  emitted polynomial cells (R47PC6Cells) expect:

    hub  :  Zopen = V5^a·V4^b·Vc^c,   Ztot = Zopen·(1 + qSum/(L+1)),   udeg = L+1,
            Aobj  = Zopen·(1 + qSum/L)          with  qSum = a·(3/23) + b·(3/19) + c·(1/3),
                                                       L = a + b + c,
            V5 = 621/64, V4 = 513/80, Vc = 3/2  (the arm/cherry `Ztot(dtSub)` values);
    pair :  the same shape one level up, with the deep hub entering through its
            `Ztot(dtSub)` (product factor) and its dressed cavity `Zopen/(Ztot·udeg)` (qSum term).

  Everything reduces to `backboneU_eq` + the general node identities
  (`Ztot_dtSub_node_eq`/`Zopen_dtSub_node_eq`, R47WPairLift chain) + the component values
  (`Ztot_dtSub_armU`, `Zopen_dtSub_armU`, `udeg_armU`, cherry values) + replicate algebra.
  Stage 2 (separate) will transport to arbitrary `BalancedArms` lists via `balancedArms_perm` and
  reduce the clause inequalities to the R47PC6Cells polynomials.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47WPair6

namespace R3Cert
namespace Step3
namespace PC6

open RTree

/-- Count-form arm list: `a` five-arms then `b` four-arms. -/
abbrev hubArms (a b : ℕ) : List ℕ := List.replicate a 5 ++ List.replicate b 4

/-! ### Component constants -/

theorem Ztot_armU5 : Ztot (dtSub (armU 5)) = 621 / 64 := by
  rw [Ztot_dtSub_armU]
  norm_num

theorem Ztot_armU4 : Ztot (dtSub (armU 4)) = 513 / 80 := by
  rw [Ztot_dtSub_armU]
  norm_num

theorem q_armU5 :
    Zopen (dtSub (armU 5)) / Ztot (dtSub (armU 5)) / (udeg (armU 5) : ℝ) = 3 / 23 := by
  rw [Zopen_dtSub_armU, Ztot_dtSub_armU, udeg_armU]
  norm_num

theorem q_armU4 :
    Zopen (dtSub (armU 4)) / Ztot (dtSub (armU 4)) / (udeg (armU 4) : ℝ) = 3 / 19 := by
  rw [Zopen_dtSub_armU, Ztot_dtSub_armU, udeg_armU]
  norm_num

theorem q_cherryU :
    Zopen (dtSub cherryU) / Ztot (dtSub cherryU) / (udeg cherryU : ℝ) = 1 / 3 := by
  rw [Zopen_dtSub_cherryU, Ztot_dtSub_cherryU, udeg_cherryU]
  norm_num

/-! ### The count-form hub children -/

/-- The realized child list of the count-form single hub. -/
theorem hub_children (a b c : ℕ) :
    backboneU [(hubArms a b, c)]
      = UTree.node ((hubArms a b).map armU ++ List.replicate c cherryU) := by
  rw [backboneU_eq, tailU_nil, List.append_nil]

theorem hub_children_len (a b c : ℕ) :
    ((hubArms a b).map armU ++ List.replicate c cherryU).length = a + b + c := by
  simp [hubArms]
  omega

/-! ### The count-form hub statistics -/

theorem hubU_udeg (a b c : ℕ) :
    udeg (backboneU [(hubArms a b, c)]) = a + b + c + 1 := by
  rw [hub_children, udeg_node, hub_children_len]

theorem hubU_Zopen (a b c : ℕ) :
    Zopen (dtSub (backboneU [(hubArms a b, c)]))
      = (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c := by
  rw [hub_children, Zopen_dtSub_node_eq]
  simp only [hubArms, List.map_append, List.map_replicate, List.map_map, Function.comp_def,
    List.prod_append, List.prod_replicate, Ztot_armU5, Ztot_armU4, Ztot_dtSub_cherryU]

theorem hubU_qSum (a b c : ℕ) :
    qSum ((hubArms a b).map armU ++ List.replicate c cherryU)
      = (a : ℝ) * (3 / 23) + (b : ℝ) * (3 / 19) + (c : ℝ) * (1 / 3) := by
  simp only [qSum, hubArms, List.map_append, List.map_replicate, List.map_map,
    Function.comp_def, List.sum_append, List.sum_replicate, nsmul_eq_mul,
    q_armU5, q_armU4, q_cherryU]

theorem hubU_Ztot (a b c : ℕ) :
    Ztot (dtSub (backboneU [(hubArms a b, c)]))
      = (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c
        * (1 + (1 / (((a : ℝ) + b + c) + 1))
            * ((a : ℝ) * (3 / 23) + (b : ℝ) * (3 / 19) + (c : ℝ) * (1 / 3))) := by
  rw [hub_children, Ztot_dtSub_node_eq, hub_children_len]
  have hprod : (((hubArms a b).map armU ++ List.replicate c cherryU).map
      fun K => Ztot (dtSub K)).prod
      = (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c := by
    simp only [hubArms, List.map_append, List.map_replicate, List.map_map, Function.comp_def,
      List.prod_append, List.prod_replicate, Ztot_armU5, Ztot_armU4, Ztot_dtSub_cherryU]
  rw [hprod, hubU_qSum]
  push_cast
  ring

/-- Root `Aobj` of the count-form hub (`hub_Aobj_eq` restated in this file's shape). -/
theorem hubU_Aobj (a b c : ℕ) (hpos : 0 < a + b + c) :
    Aobj (backboneU [(hubArms a b, c)])
      = (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c
        * (1 + (1 / ((a : ℝ) + b + c))
            * ((a : ℝ) * (3 / 23) + (b : ℝ) * (3 / 19) + (c : ℝ) * (1 / 3))) := by
  rw [hub_children, Aobj_factor, hub_children_len, hubU_qSum]
  have hprod : (((hubArms a b).map armU ++ List.replicate c cherryU).map
      fun K => Ztot (dtSub K)).prod
      = (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c := by
    simp only [hubArms, List.map_append, List.map_replicate, List.map_map, Function.comp_def,
      List.prod_append, List.prod_replicate, Ztot_armU5, Ztot_armU4, Ztot_dtSub_cherryU]
  rw [hprod]
  have hne : ((a : ℝ) + b + c) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) + b + c := by exact_mod_cast hpos
    linarith
  push_cast
  field_simp

/-! ### The count-form pair -/

/-- The realized child list of the pair: hub-A pieces plus the deep hub as tail child. -/
theorem pair_children (a5 a4 cA b5 b4 cb : ℕ) :
    backboneU [(hubArms a5 a4, cA), (hubArms b5 b4, cb)]
      = UTree.node ((hubArms a5 a4).map armU ++ List.replicate cA cherryU
          ++ [backboneU [(hubArms b5 b4, cb)]]) := by
  rw [backboneU_eq, tailU_cons]

theorem pair_children_len (a5 a4 cA b5 b4 cb : ℕ) :
    ((hubArms a5 a4).map armU ++ List.replicate cA cherryU
        ++ [backboneU [(hubArms b5 b4, cb)]]).length = a5 + a4 + cA + 1 := by
  simp [hubArms]
  omega

theorem pairU_udeg (a5 a4 cA b5 b4 cb : ℕ) :
    udeg (backboneU [(hubArms a5 a4, cA), (hubArms b5 b4, cb)]) = a5 + a4 + cA + 2 := by
  rw [pair_children, udeg_node, pair_children_len]

theorem pairU_Zopen (a5 a4 cA b5 b4 cb : ℕ) :
    Zopen (dtSub (backboneU [(hubArms a5 a4, cA), (hubArms b5 b4, cb)]))
      = (621 / 64 : ℝ) ^ a5 * (513 / 80) ^ a4 * (3 / 2) ^ cA
        * Ztot (dtSub (backboneU [(hubArms b5 b4, cb)])) := by
  rw [pair_children, Zopen_dtSub_node_eq]
  simp only [hubArms, List.map_append, List.map_replicate, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, List.prod_append, List.prod_replicate, List.prod_cons,
    List.prod_nil, Ztot_armU5, Ztot_armU4, Ztot_dtSub_cherryU, mul_one]

theorem pairU_Ztot (a5 a4 cA b5 b4 cb : ℕ) :
    Ztot (dtSub (backboneU [(hubArms a5 a4, cA), (hubArms b5 b4, cb)]))
      = (621 / 64 : ℝ) ^ a5 * (513 / 80) ^ a4 * (3 / 2) ^ cA
          * Ztot (dtSub (backboneU [(hubArms b5 b4, cb)]))
        * (1 + (1 / (((a5 : ℝ) + a4 + cA + 1) + 1))
            * ((a5 : ℝ) * (3 / 23) + (a4 : ℝ) * (3 / 19) + (cA : ℝ) * (1 / 3)
               + Zopen (dtSub (backboneU [(hubArms b5 b4, cb)]))
                   / Ztot (dtSub (backboneU [(hubArms b5 b4, cb)]))
                   / (udeg (backboneU [(hubArms b5 b4, cb)]) : ℝ))) := by
  rw [pair_children, Ztot_dtSub_node_eq, pair_children_len]
  have hprod : (((hubArms a5 a4).map armU ++ List.replicate cA cherryU
      ++ [backboneU [(hubArms b5 b4, cb)]]).map fun K => Ztot (dtSub K)).prod
      = (621 / 64 : ℝ) ^ a5 * (513 / 80) ^ a4 * (3 / 2) ^ cA
        * Ztot (dtSub (backboneU [(hubArms b5 b4, cb)])) := by
    simp only [hubArms, List.map_append, List.map_replicate, List.map_map, Function.comp_def,
      List.map_cons, List.map_nil, List.prod_append, List.prod_replicate, List.prod_cons,
      List.prod_nil, Ztot_armU5, Ztot_armU4, Ztot_dtSub_cherryU, mul_one]
  have hq : qSum ((hubArms a5 a4).map armU ++ List.replicate cA cherryU
      ++ [backboneU [(hubArms b5 b4, cb)]])
      = (a5 : ℝ) * (3 / 23) + (a4 : ℝ) * (3 / 19) + (cA : ℝ) * (1 / 3)
        + Zopen (dtSub (backboneU [(hubArms b5 b4, cb)]))
            / Ztot (dtSub (backboneU [(hubArms b5 b4, cb)]))
            / (udeg (backboneU [(hubArms b5 b4, cb)]) : ℝ) := by
    simp only [qSum, hubArms, List.map_append, List.map_replicate, List.map_map,
      Function.comp_def, List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, nsmul_eq_mul, q_armU5, q_armU4, q_cherryU, add_zero]
  rw [hprod, hq]
  push_cast
  ring

/-- Root `Aobj` of the count-form pair, in the same shape at the root weight. -/
theorem pairU_Aobj (a5 a4 cA b5 b4 cb : ℕ) :
    Aobj (backboneU [(hubArms a5 a4, cA), (hubArms b5 b4, cb)])
      = (621 / 64 : ℝ) ^ a5 * (513 / 80) ^ a4 * (3 / 2) ^ cA
          * Ztot (dtSub (backboneU [(hubArms b5 b4, cb)]))
        * (1 + (1 / ((a5 : ℝ) + a4 + cA + 1))
            * ((a5 : ℝ) * (3 / 23) + (a4 : ℝ) * (3 / 19) + (cA : ℝ) * (1 / 3)
               + Zopen (dtSub (backboneU [(hubArms b5 b4, cb)]))
                   / Ztot (dtSub (backboneU [(hubArms b5 b4, cb)]))
                   / (udeg (backboneU [(hubArms b5 b4, cb)]) : ℝ))) := by
  rw [pair_children, Aobj_factor, pair_children_len]
  have hprod : (((hubArms a5 a4).map armU ++ List.replicate cA cherryU
      ++ [backboneU [(hubArms b5 b4, cb)]]).map fun K => Ztot (dtSub K)).prod
      = (621 / 64 : ℝ) ^ a5 * (513 / 80) ^ a4 * (3 / 2) ^ cA
        * Ztot (dtSub (backboneU [(hubArms b5 b4, cb)])) := by
    simp only [hubArms, List.map_append, List.map_replicate, List.map_map, Function.comp_def,
      List.map_cons, List.map_nil, List.prod_append, List.prod_replicate, List.prod_cons,
      List.prod_nil, Ztot_armU5, Ztot_armU4, Ztot_dtSub_cherryU, mul_one]
  have hq : qSum ((hubArms a5 a4).map armU ++ List.replicate cA cherryU
      ++ [backboneU [(hubArms b5 b4, cb)]])
      = (a5 : ℝ) * (3 / 23) + (a4 : ℝ) * (3 / 19) + (cA : ℝ) * (1 / 3)
        + Zopen (dtSub (backboneU [(hubArms b5 b4, cb)]))
            / Ztot (dtSub (backboneU [(hubArms b5 b4, cb)]))
            / (udeg (backboneU [(hubArms b5 b4, cb)]) : ℝ) := by
    simp only [qSum, hubArms, List.map_append, List.map_replicate, List.map_map,
      Function.comp_def, List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, nsmul_eq_mul, q_armU5, q_armU4, q_cherryU, add_zero]
  rw [hprod, hq]
  push_cast
  ring

end PC6
end Step3
end R3Cert
