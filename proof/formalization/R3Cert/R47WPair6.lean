/-
  Problem A, Stage A3 v2: the 1/6-WEIGHTED weak pair -- the CORRECTED collapse invariant.

  The v1 pair (R47WPairLift / R47MHubTelescope.PairCollapse) used the w = 1 endpoint
  `W2 : Ztot + Zopen/udeg <=`.  The de-risk FALSIFIED v1's PairCollapse: the Balanced+Capped pair
  `(0,5,1 | 47,1,1)` admits NO single-hub target under the w = 1 clause (best deficit 0.2%, while
  W1 and root-Aobj hold) -- see `proof/verification/paircollapse_emitter.py`.

  The fix is structural: `Capped` forces every backbone frame to carry >= 6 children (>= 5 arms
  plus the tail), so the ancestor weights obey `w = 1/D <= 1/6` -- and by the same endpoint
  linearity the invariant only needs the w = 1/6 endpoint:

      W1  : Ztot(dtSub c) <= Ztot(dtSub c')
      W2' : Ztot(dtSub c) + Zopen(dtSub c)/(6·udeg c)
              <= Ztot(dtSub c') + Zopen(dtSub c')/(6·udeg c')

  Positive combinations (proved below):
      parent Ztot    = A·B·[ (X - 6w)·Z       + 6w·(Z + O/(6u)) ]
      parent W2'-sum = A·B·[ (X + w/6 - 6w)·Z + 6w·(Z + O/(6u)) ]
      root  Aobj     = the same shape at the root weight
  with `X = 1 + w·(QP+QQ)`; the coefficients are nonnegative exactly when `w <= 1/6`, i.e. the
  frame carries >= 5 siblings -- guaranteed by `Capped`.  Under (W1, W2', root) the near-collapse
  is UNIVERSAL on all measured grids (11853/11853 dense d<=2, 3953/3953 general; no swap phase).

  Contents: `dtSub_wpair6_lift`, `Aobj_child_replace_of_wpair6`, the Capped backbone transport,
  the corrected `PairCollapse6`, and the telescope `mhub_le_single_of_pairCollapse6` +
  `hdom_of_pairCollapse6_and_singleHubDom`.  `PairCollapse6` remains the named OPEN certificate
  (explicit hypothesis, not an axiom).  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47MHubTelescope

namespace R3Cert
namespace Step3

open RTree

/-! ### The 1/6-weighted pair lifts through one WIDE ancestor frame -/

/-- **The weighted-pair context lift** (frame with `>= 5` siblings, so `w <= 1/6`). -/
theorem dtSub_wpair6_lift (pre post : List UTree) (hlen : 5 ≤ pre.length + post.length)
    {c c' : UTree}
    (hW1 : Ztot (dtSub c) ≤ Ztot (dtSub c'))
    (hW2 : Ztot (dtSub c) + Zopen (dtSub c) / (6 * (udeg c : ℝ))
        ≤ Ztot (dtSub c') + Zopen (dtSub c') / (6 * (udeg c' : ℝ))) :
    Ztot (dtSub (UTree.node (pre ++ c :: post))) ≤ Ztot (dtSub (UTree.node (pre ++ c' :: post)))
      ∧ Ztot (dtSub (UTree.node (pre ++ c :: post)))
            + Zopen (dtSub (UTree.node (pre ++ c :: post)))
              / (6 * (udeg (UTree.node (pre ++ c :: post)) : ℝ))
          ≤ Ztot (dtSub (UTree.node (pre ++ c' :: post)))
            + Zopen (dtSub (UTree.node (pre ++ c' :: post)))
              / (6 * (udeg (UTree.node (pre ++ c' :: post)) : ℝ)) := by
  have hZc := Ztot_dt_pos c
  have hZc' := Ztot_dt_pos c'
  have huc := udeg_cast_pos c
  have huc' := udeg_cast_pos c'
  have hPpre := flp_crest_P_nonneg pre
  have hPpost := flp_crest_P_nonneg post
  have hQpre := qSum_nonneg pre
  have hQpost := qSum_nonneg post
  have hlenR : (5 : ℝ) ≤ (pre.length : ℝ) + (post.length : ℝ) := by exact_mod_cast hlen
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
  have hD7 : (7 : ℝ) ≤ D := by
    rw [hD]
    linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hidZ : ∀ (Z O u : ℝ), Z ≠ 0 → u ≠ 0 →
      A * (Z * B) * (1 + 1 / D * (QP + (O / Z / u + QQ)))
        = A * B * (1 + 1 / D * (QP + QQ) - 6 * (1 / D)) * Z
          + A * B * (6 * (1 / D)) * (Z + O / (6 * u)) := by
    intro Z O u hZ hu
    field_simp
    ring
  have hidS : ∀ (Z O u : ℝ), Z ≠ 0 → u ≠ 0 →
      A * (Z * B) * (1 + 1 / D * (QP + (O / Z / u + QQ))) + A * (Z * B) / (6 * D)
        = A * B * (1 + 1 / D * (QP + QQ) + 1 / D / 6 - 6 * (1 / D)) * Z
          + A * B * (6 * (1 / D)) * (Z + O / (6 * u)) := by
    intro Z O u hZ hu
    field_simp
    ring
  have hwnn : (0 : ℝ) ≤ 1 / D := by positivity
  have hw6 : 6 * (1 / D) ≤ 1 := by
    rw [mul_one_div, div_le_one hDpos]
    linarith
  have hQnn : (0 : ℝ) ≤ 1 / D * (QP + QQ) := by
    apply mul_nonneg hwnn
    linarith
  have hcW1 : (0 : ℝ) ≤ A * B * (1 + 1 / D * (QP + QQ) - 6 * (1 / D)) := by
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    linarith
  have hcS : (0 : ℝ) ≤ A * B * (1 + 1 / D * (QP + QQ) + 1 / D / 6 - 6 * (1 / D)) := by
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    have : (0 : ℝ) ≤ 1 / D / 6 := by positivity
    linarith
  have hc2 : (0 : ℝ) ≤ A * B * (6 * (1 / D)) := by
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    positivity
  constructor
  · rw [hidZ Zc Oc uc (ne_of_gt hZc) (ne_of_gt huc),
        hidZ Zc' Oc' uc' (ne_of_gt hZc') (ne_of_gt huc')]
    have h1 := mul_le_mul_of_nonneg_left hW1 hcW1
    have h2 := mul_le_mul_of_nonneg_left hW2 hc2
    nlinarith [h1, h2]
  · rw [hidS Zc Oc uc (ne_of_gt hZc) (ne_of_gt huc),
        hidS Zc' Oc' uc' (ne_of_gt hZc') (ne_of_gt huc')]
    have h1 := mul_le_mul_of_nonneg_left hW1 hcS
    have h2 := mul_le_mul_of_nonneg_left hW2 hc2
    nlinarith [h1, h2]

/-! ### The root closure at weight 1/6 -/

/-- **`Aobj`-monotonicity from the weighted pair at a WIDE root** (`>= 5` siblings, root weight
    `1/L <= 1/6`). -/
theorem Aobj_child_replace_of_wpair6 (pre post : List UTree)
    (hlen : 5 ≤ pre.length + post.length) {c c' : UTree}
    (hW1 : Ztot (dtSub c) ≤ Ztot (dtSub c'))
    (hW2 : Ztot (dtSub c) + Zopen (dtSub c) / (6 * (udeg c : ℝ))
        ≤ Ztot (dtSub c') + Zopen (dtSub c') / (6 * (udeg c' : ℝ))) :
    Aobj (UTree.node (pre ++ c :: post)) ≤ Aobj (UTree.node (pre ++ c' :: post)) := by
  have hZc := Ztot_dt_pos c
  have hZc' := Ztot_dt_pos c'
  have huc := udeg_cast_pos c
  have huc' := udeg_cast_pos c'
  have hPpre := flp_crest_P_nonneg pre
  have hPpost := flp_crest_P_nonneg post
  have hQpre := qSum_nonneg pre
  have hQpost := qSum_nonneg post
  have hlenR : (5 : ℝ) ≤ (pre.length : ℝ) + (post.length : ℝ) := by exact_mod_cast hlen
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
  have hD6 : (6 : ℝ) ≤ D := by
    rw [hD]
    linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hidZ : ∀ (Z O u : ℝ), Z ≠ 0 → u ≠ 0 →
      A * (Z * B) * (1 + 1 / D * (QP + (O / Z / u + QQ)))
        = A * B * (1 + 1 / D * (QP + QQ) - 6 * (1 / D)) * Z
          + A * B * (6 * (1 / D)) * (Z + O / (6 * u)) := by
    intro Z O u hZ hu
    field_simp
    ring
  have hwnn : (0 : ℝ) ≤ 1 / D := by positivity
  have hw6 : 6 * (1 / D) ≤ 1 := by
    rw [mul_one_div, div_le_one hDpos]
    linarith
  have hQnn : (0 : ℝ) ≤ 1 / D * (QP + QQ) := by
    apply mul_nonneg hwnn
    linarith
  have hcW1 : (0 : ℝ) ≤ A * B * (1 + 1 / D * (QP + QQ) - 6 * (1 / D)) := by
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    linarith
  have hc2 : (0 : ℝ) ≤ A * B * (6 * (1 / D)) := by
    apply mul_nonneg (mul_nonneg hPpre hPpost)
    positivity
  rw [hidZ Zc Oc uc (ne_of_gt hZc) (ne_of_gt huc),
      hidZ Zc' Oc' uc' (ne_of_gt hZc') (ne_of_gt huc')]
  have h1 := mul_le_mul_of_nonneg_left hW1 hcW1
  have h2 := mul_le_mul_of_nonneg_left hW2 hc2
  nlinarith [h1, h2]

/-! ### Weighted transport along a Capped backbone prefix -/

/-- The weighted pair transports from a backbone tail through any CAPPED prefix of hubs (each
    frame carries `>= 5` arms, hence `>= 5` siblings beside the tail child). -/
theorem backbone_tail_wpair6 :
    ∀ (init : List Hub), Capped init → ∀ {r r' : List Hub}, r ≠ [] → r' ≠ [] →
      Ztot (dtSub (backboneU r)) ≤ Ztot (dtSub (backboneU r')) →
      Ztot (dtSub (backboneU r)) + Zopen (dtSub (backboneU r)) / (6 * (udeg (backboneU r) : ℝ))
          ≤ Ztot (dtSub (backboneU r'))
            + Zopen (dtSub (backboneU r')) / (6 * (udeg (backboneU r') : ℝ)) →
      Ztot (dtSub (backboneU (init ++ r))) ≤ Ztot (dtSub (backboneU (init ++ r')))
        ∧ Ztot (dtSub (backboneU (init ++ r)))
              + Zopen (dtSub (backboneU (init ++ r)))
                / (6 * (udeg (backboneU (init ++ r)) : ℝ))
            ≤ Ztot (dtSub (backboneU (init ++ r')))
              + Zopen (dtSub (backboneU (init ++ r')))
                / (6 * (udeg (backboneU (init ++ r')) : ℝ))
  | [], _, r, r', _, _, hW1, hW2 => ⟨hW1, hW2⟩
  | (arms, c) :: init', hcap, r, r', hr, hr', hW1, hW2 => by
    have hne : init' ++ r ≠ [] := fun h => hr (List.append_eq_nil_iff.mp h).2
    have hne' : init' ++ r' ≠ [] := fun h => hr' (List.append_eq_nil_iff.mp h).2
    have hcap' : Capped init' := fun h hh => hcap h (List.mem_cons_of_mem _ hh)
    have harms : 5 ≤ arms.length := hcap (arms, c) (by simp)
    obtain ⟨hZ, hS⟩ := backbone_tail_wpair6 init' hcap' hr hr' hW1 hW2
    rw [List.cons_append, List.cons_append, backboneU_eq, backboneU_eq,
        tailU_of_ne_nil hne, tailU_of_ne_nil hne']
    exact dtSub_wpair6_lift (arms.map armU ++ List.replicate c cherryU) []
      (by simp; omega) hZ hS

/-- Root-level `Aobj` transport at weight 1/6 through a Capped prefix. -/
theorem backbone_tail_aobj6 (init : List Hub) (hcap : Capped init) {r r' : List Hub}
    (hr : r ≠ []) (hr' : r' ≠ [])
    (hW1 : Ztot (dtSub (backboneU r)) ≤ Ztot (dtSub (backboneU r')))
    (hW2 : Ztot (dtSub (backboneU r)) + Zopen (dtSub (backboneU r)) / (6 * (udeg (backboneU r) : ℝ))
        ≤ Ztot (dtSub (backboneU r'))
          + Zopen (dtSub (backboneU r')) / (6 * (udeg (backboneU r') : ℝ)))
    (hroot : Aobj (backboneU r) ≤ Aobj (backboneU r')) :
    Aobj (backboneU (init ++ r)) ≤ Aobj (backboneU (init ++ r')) := by
  cases init with
  | nil => simpa using hroot
  | cons h init' =>
    obtain ⟨arms, c⟩ := h
    have hne : init' ++ r ≠ [] := fun heq => hr (List.append_eq_nil_iff.mp heq).2
    have hne' : init' ++ r' ≠ [] := fun heq => hr' (List.append_eq_nil_iff.mp heq).2
    have hcap' : Capped init' := fun x hx => hcap x (List.mem_cons_of_mem _ hx)
    have harms : 5 ≤ arms.length := hcap (arms, c) (by simp)
    obtain ⟨hZ, hS⟩ := backbone_tail_wpair6 init' hcap' hr hr' hW1 hW2
    rw [List.cons_append, List.cons_append, backboneU_eq, backboneU_eq,
        tailU_of_ne_nil hne, tailU_of_ne_nil hne']
    exact Aobj_child_replace_of_wpair6 (arms.map armU ++ List.replicate c cherryU) []
      (by simp; omega) hZ hS

/-! ### The corrected pair-collapse hypothesis -/

/-- **The corrected pair-collapse certificate** (OPEN -- the A3(2) campaign, v2).  Every
    Balanced+Capped hub pair admits a Balanced+Capped single hub of the summed `hubSize` carrying
    W1, the 1/6-weighted W2', and root-`Aobj`.  The v1 (weight-1) form is FALSE
    (witness `(0,5,1 | 47,1,1)`); this weighted form is measured UNIVERSAL on all grids
    (11853/11853 dense d<=2, 3953/3953 general) with a bounded per-`d` candidate table. -/
def PairCollapse6 : Prop :=
  ∀ (armsA : List ℕ) (cA : ℕ) (armsB : List ℕ) (cb : ℕ),
    BalancedArms armsA → cA ≤ 5 → BalancedArms armsB → cb ≤ 5 →
    5 ≤ armsA.length → 5 ≤ armsB.length →
    ∃ (arms' : List ℕ) (c' : ℕ),
      BalancedArms arms' ∧ c' ≤ 5 ∧ 5 ≤ arms'.length
      ∧ hubSize (arms', c') = hubSize (armsA, cA) + hubSize (armsB, cb)
      ∧ Ztot (dtSub (backboneU [(armsA, cA), (armsB, cb)]))
          ≤ Ztot (dtSub (backboneU [(arms', c')]))
      ∧ Ztot (dtSub (backboneU [(armsA, cA), (armsB, cb)]))
            + Zopen (dtSub (backboneU [(armsA, cA), (armsB, cb)]))
              / (6 * (udeg (backboneU [(armsA, cA), (armsB, cb)]) : ℝ))
          ≤ Ztot (dtSub (backboneU [(arms', c')]))
            + Zopen (dtSub (backboneU [(arms', c')]))
              / (6 * (udeg (backboneU [(arms', c')]) : ℝ))
      ∧ Aobj (backboneU [(armsA, cA), (armsB, cb)]) ≤ Aobj (backboneU [(arms', c')])

/-! ### The corrected telescope -/

/-- The workhorse: strong induction on the state length, collapsing the DEEPEST pair. -/
theorem collapse_aux6 (hcol : PairCollapse6) :
    ∀ (n : ℕ) (s : List Hub), s.length ≤ n → Balanced s → Capped s → s ≠ [] →
      ∃ h : Hub, Balanced [h] ∧ Capped [h] ∧ stateSize [h] = stateSize s ∧
        Aobj (backboneU s) ≤ Aobj (backboneU [h]) := by
  intro n
  induction n with
  | zero =>
    intro s hlen _ _ hne
    cases s with
    | nil => exact absurd rfl hne
    | cons a t => simp at hlen
  | succ n ih =>
    intro s hlen hbal hcap hne
    rcases hrev : s.reverse with _ | ⟨a, ta⟩
    · exact absurd (by simpa using congrArg List.reverse hrev) hne
    rcases ta with _ | ⟨b, tb⟩
    · have hs : s = [a] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst hs
      exact ⟨a, hbal, hcap, rfl, le_refl _⟩
    · have hs : s = tb.reverse ++ [b, a] := by
        have := congrArg List.reverse hrev
        simpa [List.append_assoc] using this
      obtain ⟨armsA', cA'⟩ := b
      obtain ⟨armsB', cb'⟩ := a
      have hmem1 : (armsA', cA') ∈ s := by rw [hs]; simp
      have hmem2 : (armsB', cb') ∈ s := by rw [hs]; simp
      obtain ⟨hbalA, hcAle⟩ := hbal _ hmem1
      obtain ⟨hbalB, hcble⟩ := hbal _ hmem2
      have hcapA := hcap _ hmem1
      have hcapB := hcap _ hmem2
      obtain ⟨arms', c', hbal', hc'le, hcap', hsize', hW1, hW2, hroot⟩ :=
        hcol armsA' cA' armsB' cb' hbalA hcAle hbalB hcble hcapA hcapB
      have hcapInit : Capped tb.reverse := by
        intro h hh
        exact hcap h (by rw [hs]; exact List.mem_append_left _ hh)
      have haobj : Aobj (backboneU s) ≤ Aobj (backboneU (tb.reverse ++ [(arms', c')])) := by
        rw [hs]
        exact backbone_tail_aobj6 tb.reverse hcapInit (by simp) (by simp) hW1 hW2 hroot
      have hbal2 : Balanced (tb.reverse ++ [(arms', c')]) := by
        intro h hh
        rcases List.mem_append.mp hh with h1 | h1
        · exact hbal h (by rw [hs]; exact List.mem_append_left _ h1)
        · simp at h1
          subst h1
          exact ⟨hbal', hc'le⟩
      have hcap2 : Capped (tb.reverse ++ [(arms', c')]) := by
        intro h hh
        rcases List.mem_append.mp hh with h1 | h1
        · exact hcap h (by rw [hs]; exact List.mem_append_left _ h1)
        · simp at h1
          subst h1
          exact hcap'
      have hsize2 : stateSize (tb.reverse ++ [(arms', c')]) = stateSize s := by
        rw [hs]
        simp only [stateSize, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega
      have hlen2 : (tb.reverse ++ [(arms', c')]).length ≤ n := by
        have := congrArg List.length hs
        simp at this ⊢
        omega
      obtain ⟨h, hb1, hc1, hsz1, hle1⟩ :=
        ih (tb.reverse ++ [(arms', c')]) hlen2 hbal2 hcap2 (by simp)
      exact ⟨h, hb1, hc1, by rw [hsz1, hsize2], haobj.trans hle1⟩

/-- **The corrected telescope**: with `PairCollapse6`, every nonempty Balanced+Capped state is
    `Aobj`-dominated by a SINGLE Balanced+Capped hub of the same `stateSize`. -/
theorem mhub_le_single_of_pairCollapse6 (hcol : PairCollapse6) (s : List Hub)
    (hbal : Balanced s) (hcap : Capped s) (hne : s ≠ []) :
    ∃ h : Hub, Balanced [h] ∧ Capped [h] ∧ stateSize [h] = stateSize s ∧
      Aobj (backboneU s) ≤ Aobj (backboneU [h]) :=
  collapse_aux6 hcol s.length s le_rfl hbal hcap hne

/-- **`Hdom` from the corrected collapse certificate + the single-hub tie bound.** -/
theorem hdom_of_pairCollapse6_and_singleHubDom (hcol : PairCollapse6) (tie : ℕ → UTree)
    (hsingle : ∀ h : Hub, Balanced [h] → Capped [h] →
        Aobj (backboneU [h]) ≤ Aobj (tie (stateSize [h]))) :
    ∀ s : List Hub, Balanced s → Capped s → s ≠ [] →
      Aobj (backboneU s) ≤ Aobj (tie (stateSize s)) := by
  intro s hbal hcap hne
  obtain ⟨h, hb, hc, hsz, hle⟩ := mhub_le_single_of_pairCollapse6 hcol s hbal hcap hne
  calc Aobj (backboneU s) ≤ Aobj (backboneU [h]) := hle
    _ ≤ Aobj (tie (stateSize [h])) := hsingle h hb hc
    _ = Aobj (tie (stateSize s)) := by rw [hsz]

end Step3
end R3Cert
