/-
  Problem A, Stage A3(3): the multi-hub TELESCOPE, conditional on the pair-collapse certificate.

  Route (de-risked in `proof/verification/A3_WEAK_PAIR_COLLAPSE_FINDINGS.md`): collapse the
  DEEPEST two hubs of a Balanced+Capped state into a same-size Balanced+Capped single hub carrying
  the three clauses (W1, W2, root-`Aobj`); transport the gain through the remaining hubs via the
  weak-pair machinery (`R47WPairLift`); iterate.  Result: EVERY nonempty Balanced+Capped state is
  `Aobj`-dominated by a SINGLE Balanced+Capped hub of the same `stateSize` -- no stuckness needed.

  The sole open input is `PairCollapse` (the A3(2) certificate campaign): its three clauses are
  exactly the ones measured to hold with a common canonical target on all 15,876 grid pairs.  This
  file pins its Lean statement and consumes it; nothing here hides an axiom -- the hypothesis is
  explicit.  Downstream, `hdom_of_pairCollapse_and_singleHubDom` reduces the whole `Hdom`
  obligation (any length, stuck or not) to the SINGLE-hub tie bound -- whose envelope is already
  proven at every size (R47SingleHubResidue); the remaining assembly there is the non-aligned-n
  tie-representative selection.

  Genuine proofs (no `sorry`); `PairCollapse` is an explicit hypothesis, not an axiom.
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47WPairLift
import R3Cert.R47StepMono

namespace R3Cert
namespace Step3

open RTree

/-! ### Plumbing -/

/-- `tailU` of any nonempty state is the singleton realized backbone. -/
theorem tailU_of_ne_nil {s : List Hub} (h : s ≠ []) : tailU s = [backboneU s] := by
  cases s with
  | nil => exact absurd rfl h
  | cons hd tl => rfl

/-! ### Weak-pair transport along a backbone prefix -/

/-- The dtSub-level weak pair transports from a backbone tail through any prefix of hubs. -/
theorem backbone_tail_wpair :
    ∀ (init : List Hub) {r r' : List Hub}, r ≠ [] → r' ≠ [] →
      Ztot (dtSub (backboneU r)) ≤ Ztot (dtSub (backboneU r')) →
      Ztot (dtSub (backboneU r)) + Zopen (dtSub (backboneU r)) / (udeg (backboneU r) : ℝ)
          ≤ Ztot (dtSub (backboneU r'))
            + Zopen (dtSub (backboneU r')) / (udeg (backboneU r') : ℝ) →
      Ztot (dtSub (backboneU (init ++ r))) ≤ Ztot (dtSub (backboneU (init ++ r')))
        ∧ Ztot (dtSub (backboneU (init ++ r)))
              + Zopen (dtSub (backboneU (init ++ r))) / (udeg (backboneU (init ++ r)) : ℝ)
            ≤ Ztot (dtSub (backboneU (init ++ r')))
              + Zopen (dtSub (backboneU (init ++ r'))) / (udeg (backboneU (init ++ r')) : ℝ)
  | [], r, r', _, _, hW1, hW2 => ⟨hW1, hW2⟩
  | (arms, c) :: init', r, r', hr, hr', hW1, hW2 => by
    have hne : init' ++ r ≠ [] := fun h => hr (List.append_eq_nil_iff.mp h).2
    have hne' : init' ++ r' ≠ [] := fun h => hr' (List.append_eq_nil_iff.mp h).2
    obtain ⟨hZ, hS⟩ := backbone_tail_wpair init' hr hr' hW1 hW2
    rw [List.cons_append, List.cons_append, backboneU_eq, backboneU_eq,
        tailU_of_ne_nil hne, tailU_of_ne_nil hne']
    exact dtSub_wpair_lift (arms.map armU ++ List.replicate c cherryU) [] hZ hS

/-- Root-level `Aobj` transport: the three collapse clauses push a backbone-tail replacement
    through any prefix of hubs to the whole tree. -/
theorem backbone_tail_aobj (init : List Hub) {r r' : List Hub} (hr : r ≠ []) (hr' : r' ≠ [])
    (hW1 : Ztot (dtSub (backboneU r)) ≤ Ztot (dtSub (backboneU r')))
    (hW2 : Ztot (dtSub (backboneU r)) + Zopen (dtSub (backboneU r)) / (udeg (backboneU r) : ℝ)
        ≤ Ztot (dtSub (backboneU r'))
          + Zopen (dtSub (backboneU r')) / (udeg (backboneU r') : ℝ))
    (hroot : Aobj (backboneU r) ≤ Aobj (backboneU r')) :
    Aobj (backboneU (init ++ r)) ≤ Aobj (backboneU (init ++ r')) := by
  cases init with
  | nil => simpa using hroot
  | cons h init' =>
    obtain ⟨arms, c⟩ := h
    have hne : init' ++ r ≠ [] := fun h => hr (List.append_eq_nil_iff.mp h).2
    have hne' : init' ++ r' ≠ [] := fun h => hr' (List.append_eq_nil_iff.mp h).2
    obtain ⟨hZ, hS⟩ := backbone_tail_wpair init' hr hr' hW1 hW2
    rw [List.cons_append, List.cons_append, backboneU_eq, backboneU_eq,
        tailU_of_ne_nil hne, tailU_of_ne_nil hne']
    exact Aobj_child_replace_of_wpair (arms.map armU ++ List.replicate c cherryU) [] hZ hS

/-! ### The pair-collapse hypothesis (the A3(2) certificate target) -/

/-- **The pair-collapse certificate** (OPEN -- the A3(2) campaign): every Balanced+Capped hub
    pair admits a Balanced+Capped single hub of the summed `hubSize` carrying the three clauses
    (W1, W2, root-`Aobj`).  Measured to hold with a common canonical target (`c' = 0`,
    maximal-five arms) on all 15,876 grid pairs; not yet certified symbolically. -/
def PairCollapse : Prop :=
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
              / (udeg (backboneU [(armsA, cA), (armsB, cb)]) : ℝ)
          ≤ Ztot (dtSub (backboneU [(arms', c')]))
            + Zopen (dtSub (backboneU [(arms', c')]))
              / (udeg (backboneU [(arms', c')]) : ℝ)
      ∧ Aobj (backboneU [(armsA, cA), (armsB, cb)]) ≤ Aobj (backboneU [(arms', c')])

/-! ### The telescope -/

/-- The bounded-length workhorse: strong induction on the state length, collapsing the DEEPEST
    pair (the clean subtree) each round. -/
theorem collapse_aux (hcol : PairCollapse) :
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
    · -- singleton state: done
      have hs : s = [a] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst hs
      exact ⟨a, hbal, hcap, rfl, le_refl _⟩
    · -- s = init ++ [b, a] with a the DEEPEST hub
      have hs : s = tb.reverse ++ [b, a] := by
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
      -- the collapsed state and its Aobj gain
      have haobj : Aobj (backboneU s) ≤ Aobj (backboneU (tb.reverse ++ [(arms', c')])) := by
        rw [hs]
        exact backbone_tail_aobj tb.reverse (by simp) (by simp) hW1 hW2 hroot
      -- Balanced / Capped / stateSize / length of the collapsed state
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

/-- **The telescope**: with `PairCollapse`, every nonempty Balanced+Capped state is
    `Aobj`-dominated by a SINGLE Balanced+Capped hub of the same `stateSize`.  No stuckness
    hypothesis -- the collapse is a value comparison, not a rewrite. -/
theorem mhub_le_single_of_pairCollapse (hcol : PairCollapse) (s : List Hub)
    (hbal : Balanced s) (hcap : Capped s) (hne : s ≠ []) :
    ∃ h : Hub, Balanced [h] ∧ Capped [h] ∧ stateSize [h] = stateSize s ∧
      Aobj (backboneU s) ≤ Aobj (backboneU [h]) :=
  collapse_aux hcol s.length s le_rfl hbal hcap hne

/-- **`Hdom` from the collapse certificate + the single-hub tie bound.**  Reduces the whole
    domination obligation (any length, stuck or not) to the single-hub layer, whose envelope is
    proven at every size; the residual assembly there is the non-aligned-n tie-representative
    selection. -/
theorem hdom_of_pairCollapse_and_singleHubDom (hcol : PairCollapse) (tie : ℕ → UTree)
    (hsingle : ∀ h : Hub, Balanced [h] → Capped [h] →
        Aobj (backboneU [h]) ≤ Aobj (tie (stateSize [h]))) :
    ∀ s : List Hub, Balanced s → Capped s → s ≠ [] →
      Aobj (backboneU s) ≤ Aobj (tie (stateSize s)) := by
  intro s hbal hcap hne
  obtain ⟨h, hb, hc, hsz, hle⟩ := mhub_le_single_of_pairCollapse hcol s hbal hcap hne
  calc Aobj (backboneU s) ≤ Aobj (backboneU [h]) := hle
    _ ≤ Aobj (tie (stateSize [h])) := hsingle h hb hc
    _ = Aobj (tie (stateSize s)) := by rw [hsz]

end Step3
end R3Cert
