import Mathlib
import R3Cert.R47StepMono
import R3Cert.R47OrderedStep
import R3Cert.R47StepSize

/-!
  # The fixed-n capstone — the size-correct form of `conjecture1_of_layers`

  `R47TopCapstone.conjecture1_of_layers` reduces `∀ t, Aobj t ≤ Aobj tieU` to two open
  layers against a SINGLE fixed tree `tieU`.  That shape is ILL-POSED for the raw
  objective: `Aobj` grows like `rhoB^n` (rhoB = (621/64)^(1/11) > 1), so no fixed
  `tieU : UTree` can dominate `Aobj t` across all sizes `n = usize t`.  Empirically the
  true `per(L)/∏deg` maximizer is a CATERPILLAR whose structure depends on `n` (degree
  sequences `(5,2,2,2,2,2)` at n=11, etc.), and `Aobj/rhoB^n` oscillates rather than
  sitting at a constant — so the comparison is inherently PER-SIZE.

  This file states the well-posed version: the tie is a FAMILY `tie : ℕ → UTree` (one
  maximizer per vertex count), and the conclusion compares each tree to the tie AT ITS
  OWN SIZE, `Aobj t ≤ Aobj (tie (usize t))`.  The reduction stays within one size class
  because the normalization is size-preserving (`Hnorm` carries `stateSize s = usize t`)
  and the ordered-merge chain CONSERVES size (`OrderedStep.stateSize_eq`, lifted to
  chains by `chain_stateSize_eq`).  Everything else is the existing merge capstone
  (`chain_to_normalForm`, `Balanced.chain`, `Capped.chain`).

  This does NOT prove the conjecture: `Hnorm` (size-preserving normalization) and `Hdom`
  (per-size domination by the tie) remain the genuine open layers — now correctly
  quantified.  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

/-- Size is conserved along an ordered-merge chain (each `OrderedStep` conserves
    `stateSize`; lift over the reflexive-transitive closure). -/
theorem chain_stateSize_eq {s s' : List Hub}
    (h : Relation.ReflTransGen OrderedStep s s') : stateSize s' = stateSize s := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [OrderedStep.stateSize_eq hstep]; exact ih

/-- **The fixed-n capstone.**  The size-correct reduction of Conjecture 1: against a
    per-size tie family `tie : ℕ → UTree`, a size-preserving normalization `Hnorm` and a
    per-size domination `Hdom` give `∀ t, Aobj t ≤ Aobj (tie (usize t))`.  The size class
    is preserved end-to-end (Hnorm carries `stateSize s = usize t`; the merge chain
    conserves `stateSize`), so the tie is always evaluated at the tree's own vertex
    count.  Non-vacuous and conditional; `Hnorm`/`Hdom` are the two open layers,
    now correctly quantified.  conjecture1_proved = False. -/
theorem conjecture1_of_layers_fixedN (tie : ℕ → UTree)
    (Hnorm : ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧
        stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s))
    (Hdom : ∀ s : List Hub, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) →
        Aobj (backboneU s) ≤ Aobj (tie (stateSize s))) :
    ∀ t : UTree, Aobj t ≤ Aobj (tie (usize t)) := by
  intro t
  obtain ⟨s, hbal, hcap, hsize, hts⟩ := Hnorm t
  obtain ⟨s', hst, hnf, hmono⟩ := chain_to_normalForm s hbal hcap
  have hbal' : Balanced s' := Balanced.chain hst hbal
  have hcap' : Capped s' := Capped.chain hst hcap
  have hss : stateSize s' = stateSize s := chain_stateSize_eq hst
  calc Aobj t
      ≤ Aobj (backboneU s) := hts
    _ ≤ Aobj (backboneU s') := hmono
    _ ≤ Aobj (tie (stateSize s')) := Hdom s' hbal' hcap' hnf
    _ = Aobj (tie (usize t)) := by rw [hss, hsize]

end Step3
end R3Cert
