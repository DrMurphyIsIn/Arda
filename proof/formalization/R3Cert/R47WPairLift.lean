/-
  Problem A, Stage A3(1): the WEAK-pair context lift.

  The strong pair (G1, G2) of BGSCLFlpDeepLift fails for degree-jumping replacements (the
  deepest-pair collapse: pair udeg ~6 vs single-hub udeg ~15 sinks G2, though root-level Hdom
  holds).  The fix: a child enters every ancestor LINEARLY in the weight `w = 1/(len+1) in (0,1]`
  through `Ztot_c·(1+w·Q0) + w·(Zopen_c/udeg_c)`, so by endpoint linearity the sufficient
  self-propagating invariant is the two endpoints:

      W1 : Ztot(dtSub c) <= Ztot(dtSub c')                                     (w = 0)
      W2 : Ztot(dtSub c) + Zopen(dtSub c)/udeg c
             <= Ztot(dtSub c') + Zopen(dtSub c')/udeg c'                        (w = 1)

  Positive-combination identities (the whole proof):
      parent Ztot    = A·B·[ (X - w)·Z + w·(Z + O/u) ]      X = 1 + w·(QP+QQ), X - w >= 0 (w <= 1)
      parent W2-sum  = A·B·[  X     ·Z + w·(Z + O/u) ]
      root Aobj      = A·B·[ (Y - v)·Z + v·(Z + O/u) ]      Y = 1 + v·(QP+QQ), v = 1/len <= 1
  Each is a nonnegative combination of the W1 and W2 quantities, so the pair lifts through any
  ancestor frame (`dtSub_wpair_lift`, `plugFrames_wpair`) and closes at the root
  (`Aobj_child_replace_of_wpair`).  The strong pair implies the weak one, so every B-track use
  remains an instance.  De-risked exactly (15,876 collapse pairs, 0 violations) in
  `proof/verification/A3_WEAK_PAIR_COLLAPSE_FINDINGS.md`.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLFlpDeepLift

namespace R3Cert
namespace Step3

open RTree

/-! ### The weak pair lifts through one ancestor frame -/

/-- **The weak-pair context lift.**  If `c ↦ c'` carries `W1 : Ztot(dtSub) <=` and
    `W2 : Ztot(dtSub) + Zopen(dtSub)/udeg <=`, then so does `node (pre ++ c :: post) ↦
    node (pre ++ c' :: post)` -- with no side conditions.  (Positive combinations; the ancestor
    weight satisfies `w <= 1`.) -/
theorem dtSub_wpair_lift (pre post : List UTree) {c c' : UTree}
    (hW1 : Ztot (dtSub c) ≤ Ztot (dtSub c'))
    (hW2 : Ztot (dtSub c) + Zopen (dtSub c) / (udeg c : ℝ)
        ≤ Ztot (dtSub c') + Zopen (dtSub c') / (udeg c' : ℝ)) :
    Ztot (dtSub (UTree.node (pre ++ c :: post))) ≤ Ztot (dtSub (UTree.node (pre ++ c' :: post)))
      ∧ Ztot (dtSub (UTree.node (pre ++ c :: post)))
            + Zopen (dtSub (UTree.node (pre ++ c :: post)))
              / (udeg (UTree.node (pre ++ c :: post)) : ℝ)
          ≤ Ztot (dtSub (UTree.node (pre ++ c' :: post)))
            + Zopen (dtSub (UTree.node (pre ++ c' :: post)))
              / (udeg (UTree.node (pre ++ c' :: post)) : ℝ) := by
  have hZc := Ztot_dt_pos c
  have hZc' := Ztot_dt_pos c'
  have huc := udeg_cast_pos c
  have huc' := udeg_cast_pos c'
  have hPpre := flp_crest_P_nonneg pre
  have hPpost := flp_crest_P_nonneg post
  have hQpre := qSum_nonneg pre
  have hQpost := qSum_nonneg post
  simp only [Ztot_dtSub_node_eq, Zopen_dtSub_node_eq, udeg_node,
    List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    qSum_append, qSum_cons, List.length_append, List.length_cons]
  push_cast
  set A := (pre.map fun K => Ztot (dtSub K)).prod with hA
  set B := (post.map fun K => Ztot (dtSub K)).prod with hB
  set Zc := Ztot (dtSub c)
  set Zc' := Ztot (dtSub c')
  set Oc := Zopen (dtSub c)
  set Oc' := Zopen (dtSub c')
  set uc := (udeg c : ℝ)
  set uc' := (udeg c' : ℝ)
  set QP := qSum pre
  set QQ := qSum post
  set D : ℝ := (pre.length : ℝ) + ((post.length : ℝ) + 1) + 1 with hD
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hD]
    have h1 : (0 : ℝ) ≤ (pre.length : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (post.length : ℝ) := Nat.cast_nonneg _
    linarith
  have hDpos : (0 : ℝ) < D := by linarith
  -- the two positive-combination identities
  have hidZ : ∀ (Z O u : ℝ), Z ≠ 0 → u ≠ 0 →
      A * (Z * B) * (1 + 1 / D * (QP + (O / Z / u + QQ)))
        = A * B * (1 + 1 / D * (QP + QQ) - 1 / D) * Z + A * B * (1 / D) * (Z + O / u) := by
    intro Z O u hZ hu
    field_simp
    ring
  have hidS : ∀ (Z O u : ℝ), Z ≠ 0 → u ≠ 0 →
      A * (Z * B) * (1 + 1 / D * (QP + (O / Z / u + QQ))) + A * (Z * B) / D
        = A * B * (1 + 1 / D * (QP + QQ)) * Z + A * B * (1 / D) * (Z + O / u) := by
    intro Z O u hZ hu
    field_simp
    ring
  -- nonnegative coefficients
  have hwle : 1 / D ≤ 1 := by
    rw [div_le_one hDpos]
    exact hD1
  have hwnn : (0 : ℝ) ≤ 1 / D := by positivity
  have hcW1 : (0 : ℝ) ≤ A * B * (1 + 1 / D * (QP + QQ) - 1 / D) := by
    have hQ : (0 : ℝ) ≤ 1 / D * (QP + QQ) := by
      apply mul_nonneg hwnn
      linarith
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    linarith
  have hcX : (0 : ℝ) ≤ A * B * (1 + 1 / D * (QP + QQ)) := by
    have hQ : (0 : ℝ) ≤ 1 / D * (QP + QQ) := by
      apply mul_nonneg hwnn
      linarith
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    linarith
  have hcW2 : (0 : ℝ) ≤ A * B * (1 / D) :=
    mul_nonneg (mul_nonneg hPpre hPpost) hwnn
  constructor
  · rw [hidZ Zc Oc uc (ne_of_gt hZc) (ne_of_gt huc),
        hidZ Zc' Oc' uc' (ne_of_gt hZc') (ne_of_gt huc')]
    have h1 := mul_le_mul_of_nonneg_left hW1 hcW1
    have h2 := mul_le_mul_of_nonneg_left hW2 hcW2
    nlinarith [h1, h2]
  · rw [hidS Zc Oc uc (ne_of_gt hZc) (ne_of_gt huc),
        hidS Zc' Oc' uc' (ne_of_gt hZc') (ne_of_gt huc')]
    have h1 := mul_le_mul_of_nonneg_left hW1 hcX
    have h2 := mul_le_mul_of_nonneg_left hW2 hcW2
    nlinarith [h1, h2]

/-! ### The root closure -/

/-- **`Aobj`-monotonicity from the weak pair at the root.**  The root weight is `1/len <= 1`
    (nonempty child list), so the root `Aobj` is the same positive combination. -/
theorem Aobj_child_replace_of_wpair (pre post : List UTree) {c c' : UTree}
    (hW1 : Ztot (dtSub c) ≤ Ztot (dtSub c'))
    (hW2 : Ztot (dtSub c) + Zopen (dtSub c) / (udeg c : ℝ)
        ≤ Ztot (dtSub c') + Zopen (dtSub c') / (udeg c' : ℝ)) :
    Aobj (UTree.node (pre ++ c :: post)) ≤ Aobj (UTree.node (pre ++ c' :: post)) := by
  have hZc := Ztot_dt_pos c
  have hZc' := Ztot_dt_pos c'
  have huc := udeg_cast_pos c
  have huc' := udeg_cast_pos c'
  have hPpre := flp_crest_P_nonneg pre
  have hPpost := flp_crest_P_nonneg post
  have hQpre := qSum_nonneg pre
  have hQpost := qSum_nonneg post
  rw [Aobj_factor, Aobj_factor]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    qSum_append, qSum_cons, List.length_append, List.length_cons]
  push_cast
  set A := (pre.map fun K => Ztot (dtSub K)).prod with hA
  set B := (post.map fun K => Ztot (dtSub K)).prod with hB
  set Zc := Ztot (dtSub c)
  set Zc' := Ztot (dtSub c')
  set Oc := Zopen (dtSub c)
  set Oc' := Zopen (dtSub c')
  set uc := (udeg c : ℝ)
  set uc' := (udeg c' : ℝ)
  set QP := qSum pre
  set QQ := qSum post
  set D : ℝ := (pre.length : ℝ) + ((post.length : ℝ) + 1) with hD
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hD]
    have h1 : (0 : ℝ) ≤ (pre.length : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (post.length : ℝ) := Nat.cast_nonneg _
    linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hidZ : ∀ (Z O u : ℝ), Z ≠ 0 → u ≠ 0 →
      A * (Z * B) * (1 + 1 / D * (QP + (O / Z / u + QQ)))
        = A * B * (1 + 1 / D * (QP + QQ) - 1 / D) * Z + A * B * (1 / D) * (Z + O / u) := by
    intro Z O u hZ hu
    field_simp
    ring
  have hwle : 1 / D ≤ 1 := by
    rw [div_le_one hDpos]
    exact hD1
  have hwnn : (0 : ℝ) ≤ 1 / D := by positivity
  have hcW1 : (0 : ℝ) ≤ A * B * (1 + 1 / D * (QP + QQ) - 1 / D) := by
    have hQ : (0 : ℝ) ≤ 1 / D * (QP + QQ) := by
      apply mul_nonneg hwnn
      linarith
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    linarith
  have hcW2 : (0 : ℝ) ≤ A * B * (1 / D) :=
    mul_nonneg (mul_nonneg hPpre hPpost) hwnn
  rw [hidZ Zc Oc uc (ne_of_gt hZc) (ne_of_gt huc),
      hidZ Zc' Oc' uc' (ne_of_gt hZc') (ne_of_gt huc')]
  have h1 := mul_le_mul_of_nonneg_left hW1 hcW1
  have h2 := mul_le_mul_of_nonneg_left hW2 hcW2
  nlinarith [h1, h2]

/-! ### The weak pair through frame stacks -/

/-- The weak pair lifts through any ancestor frame stack. -/
theorem plugFrames_wpair :
    ∀ (fs : List (List UTree × List UTree)) {c c' : UTree},
      Ztot (dtSub c) ≤ Ztot (dtSub c') →
      Ztot (dtSub c) + Zopen (dtSub c) / (udeg c : ℝ)
          ≤ Ztot (dtSub c') + Zopen (dtSub c') / (udeg c' : ℝ) →
      Ztot (dtSub (plugFrames fs c)) ≤ Ztot (dtSub (plugFrames fs c'))
        ∧ Ztot (dtSub (plugFrames fs c))
              + Zopen (dtSub (plugFrames fs c)) / (udeg (plugFrames fs c) : ℝ)
            ≤ Ztot (dtSub (plugFrames fs c'))
              + Zopen (dtSub (plugFrames fs c')) / (udeg (plugFrames fs c') : ℝ)
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | f :: fs, _, _, h1, h2 =>
    let hlift := dtSub_wpair_lift f.1 f.2 h1 h2
    plugFrames_wpair fs hlift.1 hlift.2

/-- The strong pair implies the weak pair (so every B-track G-result is an instance). -/
theorem wpair_of_gains {c c' : UTree}
    (hG1 : Ztot (dtSub c) ≤ Ztot (dtSub c'))
    (hG2 : Zopen (dtSub c) / (udeg c : ℝ) ≤ Zopen (dtSub c') / (udeg c' : ℝ)) :
    Ztot (dtSub c) + Zopen (dtSub c) / (udeg c : ℝ)
      ≤ Ztot (dtSub c') + Zopen (dtSub c') / (udeg c' : ℝ) :=
  add_le_add hG1 hG2

end Step3
end R3Cert
