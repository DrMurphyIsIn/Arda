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

end Step3
end R3Cert
