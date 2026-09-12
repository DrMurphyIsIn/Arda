/-
  R3Cert.R47HnormMulti -- the BROADENED capstone: reduce every tree to an ARBITRARY multi-hub
  cherry-backbone (`backboneU s` for any `s : List Hub`), not just a Balanced+Capped SINGLE hub.

  Motivation.  `R47HnormFalse52.r47_hnorm_false_at_52` refutes the single-hub normalization `Hnorm`
  at aligned size 52: the four-core witness `T52 = backboneU [([],6),([],6),([],6),([],6)]` strictly
  exceeds every Balanced+Capped state of size 52.  Empirically (exact `fractions.Fraction`,
  `proof/verification/bg_maximizer_family.py`) the TRUE per-size maximizer is always a multi-hub
  cherry-backbone (a caterpillar of cherry-loaded hubs; hub count grows ~n/7..n/11, body hubs of
  degree 5-6 plus one larger head hub), NOT a single hub.

  This file salvages the reduction framework by broadening the normal-form class:
    * `HnormMulti` drops `Balanced ∧ Capped` -- every tree is `Aobj`-dominated by SOME hub-backbone
      of its own size (the tree->backbone straightening).  It is a strict WEAKENING of the
      single-hub `Hnorm` (`hnormMulti_of_hnorm`).
    * `HdomMulti` -- the per-size tie dominates every backbone of its size (tautological for the
      multi-hub backbone argmax, analogous to `tieArgmax`/`tie_ge_of_mem`; left here as a
      hypothesis, dischargeable by a finite multi-hub argmax construction).
    * `conjecture1_of_HnormMulti` -- the broadened reduction: `HnormMulti + HdomMulti => conjecture 1`.

  Crucially the n=52 refutation NO LONGER bites: `T52` is itself a hub-backbone, so it witnesses its
  own `HnormMulti` clause (`hnormMulti_holds_at_T52`).  `singleHub_refuted_but_multiHub_open` pairs
  the two facts: the single-hub target is unprovable, the multi-hub target admits the counterexample.

  The SOLE remaining obligation is `HnormMulti` (the tree->backbone straightening) -- equivalently,
  that the per-size `Aobj`-maximizer over all trees is a multi-hub cherry-backbone.  That is the open
  Brualdi-Goldwasser structural core (Pant 2026); this file does not close it.  conjecture1_proved = False.

  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.R47HnormFalse52
import R3Cert.R47CoverRelation

namespace R3Cert
namespace Step3

open RTree

/-- **The broadened reduction.**  With the multi-hub straightening `HnormMulti` (every tree is
    `Aobj`-dominated by SOME hub-backbone of its own size) and a per-size tie that dominates every
    backbone of its size (`HdomMulti`), every tree is dominated by the tie at its own vertex count.
    This is the `Balanced+Capped`-free analogue of `conjecture1_of_layers_fixedN`. -/
theorem conjecture1_of_HnormMulti (tie : ℕ → UTree)
    (HnormMulti : ∀ t : UTree, ∃ s : List Hub,
        stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s))
    (HdomMulti : ∀ s : List Hub, Aobj (backboneU s) ≤ Aobj (tie (stateSize s))) :
    ∀ t : UTree, Aobj t ≤ Aobj (tie (usize t)) := by
  intro t
  obtain ⟨s, hsz, hle⟩ := HnormMulti t
  calc Aobj t ≤ Aobj (backboneU s) := hle
    _ ≤ Aobj (tie (stateSize s)) := HdomMulti s
    _ = Aobj (tie (usize t)) := by rw [hsz]

/-- **The broadened normal form is a WEAKENING of the single-hub one.**  Dropping `Balanced ∧ Capped`
    can only make the existential easier, so the single-hub `Hnorm` (the hypothesis of
    `conjecture1_of_Hnorm`) implies `HnormMulti`.  Hence broadening loses nothing that was provable
    and gains the room the refutation forces. -/
theorem hnormMulti_of_hnorm
    (Hnorm : ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧
        stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)) :
    ∀ t : UTree, ∃ s : List Hub, stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s) := by
  intro t
  obtain ⟨s, _, _, hsz, hle⟩ := Hnorm t
  exact ⟨s, hsz, hle⟩

/-- **The n=52 refutation does NOT bite `HnormMulti`.**  The counterexample tree
    `T52 = backboneU [([],6),([],6),([],6),([],6)]` is itself a hub-backbone, so it witnesses its own
    `HnormMulti` clause: take `s` to be its own four-core hub-state.  (Contrast `r47_hnorm_false_at_52`,
    which refutes the single-hub clause since `T52` is not Balanced+Capped and exceeds every
    Balanced+Capped state of size 52.) -/
theorem hnormMulti_holds_at_T52 :
    ∃ s : List Hub, stateSize s = usize T52 ∧ Aobj T52 ≤ Aobj (backboneU s) := by
  refine ⟨[([], 6), ([], 6), ([], 6), ([], 6)], ?_, ?_⟩
  · rw [usize_T52]; rfl
  · exact le_refl _

/-- **The broadening is exactly what the refutation forces.**  `T52` refutes the single-hub `Hnorm`
    clause yet satisfies the multi-hub one.  So the single-hub target is unprovable (at 52) while the
    broadened `HnormMulti` remains open -- and is true iff the per-size `Aobj`-maximizer is a multi-hub
    cherry-backbone, the open Brualdi-Goldwasser structural core. -/
theorem singleHub_refuted_but_multiHub_open :
    (¬ ∃ s : List Hub, Balanced s ∧ Capped s ∧ stateSize s = 52 ∧ Aobj T52 ≤ Aobj (backboneU s))
    ∧ (∃ s : List Hub, stateSize s = usize T52 ∧ Aobj T52 ≤ Aobj (backboneU s)) :=
  ⟨r47_hnorm_false_at_52, hnormMulti_holds_at_T52⟩

/-! ### `HnormMulti` is discharged by the pre-existing whole-hub obligation `hwh`

    IMPORTANT CLARIFICATION.  The n=52 refutation (`r47_hnorm_false_at_52`) did NOT kill the whole-hub
    straightening `hwh`.  The repo's `hnorm_of_wholehub` (R47CoverRelation.lean:114) already reduces
    `hwh` to the GENERAL-backbone Hnorm (`∃ s : List Hub, usize (backboneU s) = usize t ∧ ...`) with NO
    `Balanced ∧ Capped` -- which is exactly `HnormMulti`.  What the refutation killed is the FURTHER
    general->Balanced+Capped normalization (the extra step the single-hub `tieArgmax` capstone needed):
    `T52` is a general backbone with no Balanced+Capped dominator of its size.  `hwh` itself feeds only
    the general-backbone straightening and survives -- and is precisely the sole open obligation for the
    BROADENED capstone. -/

/-- `usize (backboneU s) = stateSize s` for a nonempty state (the realization seam). -/
theorem usize_backboneU_of_ne_nil {s : List Hub} (hs : s ≠ []) :
    usize (backboneU s) = stateSize s := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hs
  have h := usizeList_tailU (hd :: tl)
  rw [tailU_cons, usizeList_cons, usizeList_nil, Nat.add_zero] at h
  exact h

/-- **`HnormMulti` follows from the whole-hub obligation `hwh`.**  `hnorm_of_wholehub` produces a
    general backbone dominating `t` at matching `usize`; convert to the `stateSize` form (nonempty via
    the realization seam; the single-leaf `s = []` case uses the size-1 hub `[([],0)]`, whose backbone
    is the same `node []`).  So `hwh` -- unrefuted by the n=52 counterexample -- discharges `HnormMulti`. -/
theorem hnormMulti_of_wholehub
    (hwh : ∀ t : UTree, strDefect t ≠ 0 → RerootMinimal t → (¬ ∃ t', FlpStepAt t t') →
        ∃ t', CoverR t t') :
    ∀ t : UTree, ∃ s : List Hub, stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s) := by
  intro t
  obtain ⟨s, hsz, hle⟩ := hnorm_of_wholehub hwh t
  rcases eq_or_ne s [] with rfl | hne
  · have hb0 : backboneU ([] : List Hub) = UTree.node [] := rfl
    have ht1 : usize t = 1 := by
      rw [hb0, usize_node, usizeList_nil] at hsz; omega
    refine ⟨[([], 0)], ?_, ?_⟩
    · rw [ht1]; rfl
    · rw [show backboneU [([], 0)] = UTree.node [] from rfl, ← hb0]; exact hle
  · exact ⟨s, by rw [← usize_backboneU_of_ne_nil hne]; exact hsz, hle⟩

/-- **The broadened capstone, discharged by `hwh` + `HdomMulti`.**  Conjecture 1 (in the `usize`-tie
    form) follows from the whole-hub straightening `hwh` (the ORIGINAL open object -- unrefuted) together
    with the per-size backbone-dominating tie `HdomMulti` (tautological for the multi-hub argmax).  This
    is the honest state of the salvaged program: `hwh` is the sole open mathematical obligation. -/
theorem conjecture1_of_HnormMulti_of_wholehub (tie : ℕ → UTree)
    (hwh : ∀ t : UTree, strDefect t ≠ 0 → RerootMinimal t → (¬ ∃ t', FlpStepAt t t') →
        ∃ t', CoverR t t')
    (HdomMulti : ∀ s : List Hub, Aobj (backboneU s) ≤ Aobj (tie (stateSize s))) :
    ∀ t : UTree, Aobj t ≤ Aobj (tie (usize t)) :=
  conjecture1_of_HnormMulti tie (hnormMulti_of_wholehub hwh) HdomMulti

end Step3
end R3Cert
