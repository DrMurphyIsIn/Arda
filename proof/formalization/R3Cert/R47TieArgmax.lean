/-
  The tie-definition layer: a CONCRETE per-size tie family, discharging `Hdom` entirely.

  `hdom_of_pairCollapse6_and_singleHubDom` (R47WPair6, now that `pairCollapse6` is a theorem)
  reduces the whole multi-hub `Hdom` to ONE obligation: some `tie : ℕ → UTree` that dominates
  every Balanced+Capped SINGLE hub at its own size.  The residue envelope (R47SingleHubResidue)
  *characterizes* which hub is the maximizer per residue; but for the DOMINATION bound that
  characterization is unnecessary.  The clean move:

      tie n := the count-form single hub of size n maximizing `Aobj`
               (argmax over the FINITE set `hubTriples n`).

  Then "every single hub of size n is <= tie n" is immediate by construction (`Finset.exists_max_image`)
  -- no residue case analysis, no numerics (the bound is tautological: the hub lies in the set the max
  ranges over).  Composed with the telescope this gives `Hdom` at EVERY length against a concrete tie:

      * `singleHub_le_tieArgmax` -- the single-hub obligation (`hsingle`);
      * `hdom_all`               -- Hdom for every nonempty Balanced+Capped state;
      * `hdom_capstone`          -- the capstone `Hdom` shape (adds the vacuous `s = []` case).

  NET: the tie-definition layer is CLOSED against `tieArgmax`; the single-hub and multi-hub `Hdom`
  residuals are both discharged.  The sole remaining capstone obligation is `Hnorm` (tree->hub).
  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47ArmPerm
import R3Cert.R47SharpRate
import R3Cert.R47Capped
import R3Cert.R47Step
import R3Cert.R47WPair6
import R3Cert.R47PC6Final
import R3Cert.R47TopCapstoneFixedN

namespace R3Cert
namespace Step3

open RTree

/-- Count-form triples `(a,b,c)` of a Balanced+Capped single hub of size `n`:
    `11a + 9b + 2c = n - 1`, `c <= 5`, `5 <= a + b`.  Finite (each coordinate bounded by `n`). -/
def hubTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range 6)).filter
    (fun t => 11 * t.1 + 9 * t.2.1 + 2 * t.2.2 = n - 1 ∧ 5 ≤ t.1 + t.2.1)

theorem mem_hubTriples {n a b c : ℕ} :
    (a, b, c) ∈ hubTriples n ↔ 11 * a + 9 * b + 2 * c = n - 1 ∧ 5 ≤ a + b ∧ c ≤ 5 := by
  simp only [hubTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, _, hc⟩, hsz, hab⟩; exact ⟨hsz, hab, by omega⟩
  · rintro ⟨hsz, hab, hc⟩; exact ⟨⟨by omega, by omega, by omega⟩, hsz, hab⟩

/-- `Aobj` of a count-form single hub, as a function of its `(a,b,c)` triple. -/
noncomputable def tripleAobj (t : ℕ × ℕ × ℕ) : ℝ :=
  Aobj (backboneU (hubState t.1 t.2.1 t.2.2))

/-- **The per-size single-hub tie**: the count-form single hub of size `n` maximizing `Aobj`
    (junk value `backboneU []` when no Balanced+Capped single hub has size `n`). -/
noncomputable def tieArgmax (n : ℕ) : UTree :=
  if h : (hubTriples n).Nonempty then
    let t := (Finset.exists_max_image (hubTriples n) tripleAobj h).choose
    backboneU (hubState t.1 t.2.1 t.2.2)
  else backboneU []

/-- Every count-form hub whose triple is in `hubTriples n` is `Aobj`-dominated by `tieArgmax n`. -/
theorem tie_ge_of_mem {n : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ hubTriples n) :
    Aobj (backboneU (hubState t.1 t.2.1 t.2.2)) ≤ Aobj (tieArgmax n) := by
  have hne : (hubTriples n).Nonempty := ⟨t, ht⟩
  rw [tieArgmax, dif_pos hne]
  obtain ⟨_, hmax⟩ := (Finset.exists_max_image (hubTriples n) tripleAobj hne).choose_spec
  exact hmax t ht

/-- **The single-hub `Hdom` obligation** (`hsingle`): every Balanced+Capped single hub is
    `Aobj`-dominated by the tie at its own size.  Reduce the hub to count form (arm permutation),
    then apply the argmax. -/
theorem singleHub_le_tieArgmax (h : Hub) (hbal : Balanced [h]) (hcap : Capped [h]) :
    Aobj (backboneU [h]) ≤ Aobj (tieArgmax (stateSize [h])) := by
  obtain ⟨arms, c⟩ := h
  have hmem : (arms, c) ∈ [(arms, c)] := by simp
  have hba : BalancedArms arms := (hbal (arms, c) hmem).1
  have hc5 : c ≤ 5 := (hbal (arms, c) hmem).2
  have hlen : 5 ≤ arms.length := hcap (arms, c) hmem
  have hAeq : Aobj (backboneU [(arms, c)])
      = Aobj (backboneU (hubState (arms.count 5) (arms.count 4) c)) := by
    simp only [hubState]
    exact Aobj_backbone_arm_perm c (balancedArms_perm arms hba)
  rw [hAeq]
  have hcount : 5 ≤ arms.count 5 + arms.count 4 := by
    rw [← balancedArms_length arms hba]; exact hlen
  have hsz : stateSize [(arms, c)] = 1 + 11 * arms.count 5 + 9 * arms.count 4 + 2 * c :=
    stateSize_singleHub arms c hba
  have hmemT : (arms.count 5, arms.count 4, c) ∈ hubTriples (stateSize [(arms, c)]) := by
    rw [mem_hubTriples]; exact ⟨by omega, hcount, hc5⟩
  exact tie_ge_of_mem hmemT

/-- **`Hdom` for every nonempty Balanced+Capped state**, against the concrete `tieArgmax`.
    (`pairCollapse6` telescope + the single-hub obligation.) -/
theorem hdom_all : ∀ s : List Hub, Balanced s → Capped s → s ≠ [] →
    Aobj (backboneU s) ≤ Aobj (tieArgmax (stateSize s)) :=
  hdom_of_pairCollapse6_and_singleHubDom PC6.pairCollapse6 tieArgmax singleHub_le_tieArgmax

/-- **The capstone `Hdom` shape**, discharged against `tieArgmax`: every stuck Balanced+Capped
    state is dominated by the tie at its own size.  Nonempty states go through `hdom_all`; the
    empty state is vacuous (`hubTriples 0 = ∅`, so `tieArgmax 0 = backboneU []`, reflexive). -/
theorem hdom_capstone : ∀ s : List Hub, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) →
    Aobj (backboneU s) ≤ Aobj (tieArgmax (stateSize s)) := by
  intro s hbal hcap _
  rcases eq_or_ne s [] with rfl | hne
  · have h0 : ¬ (hubTriples (stateSize ([] : List Hub))).Nonempty := by
      rw [show stateSize ([] : List Hub) = 0 by simp [stateSize]]
      rintro ⟨t, ht⟩
      rw [mem_hubTriples] at ht; omega
    rw [tieArgmax, dif_neg h0]
  · exact hdom_all s hbal hcap hne

/-- **Conjecture 1, reduced to `Hnorm` alone.**  With the concrete tie `tieArgmax`, the domination
    layer `Hdom` is fully discharged (`hdom_capstone`); feeding it to the fixed-n capstone leaves the
    tree->hub normalization `Hnorm` as the SOLE remaining obligation.  Every tree is `Aobj`-dominated
    by the best single hub of its own vertex count -- once `Hnorm` is proven.  conjecture1_proved = False. -/
theorem conjecture1_of_Hnorm
    (Hnorm : ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧
        stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)) :
    ∀ t : UTree, Aobj t ≤ Aobj (tieArgmax (usize t)) :=
  conjecture1_of_layers_fixedN tieArgmax Hnorm hdom_capstone

end Step3
end R3Cert
