/-
  R3Cert.R47TopCapstone -- the R7' top-composition capstone (conditional).

  Reduces the Brualdi-Goldwasser maximizer statement to EXACTLY the two remaining open G7 layers, using
  the DONE merge-layer capstone (`chain_to_normalForm` + `Balanced.chain`/`Capped.chain`, R47StepMono):

    * `Hnorm` -- the (L)/(B) NORMALIZATION layer: every tree's `Aobj` is <= that of some Balanced+Capped
      hub-state (bringing an arbitrary tree into the certified family).  NOT yet a theorem.
    * `Hdom`  -- the R5/R6 + rate DOMINATION layer: every merge-NORMAL Balanced+Capped state's `Aobj` is
      <= the target `tieU`.  NOT yet a theorem.

  Conclusion: `Aobj t <= Aobj tieU` for every rooted tree `t`.  Via `pi_utree` (R47Tree),
  `Aobj u = per(L(realize(dtRealize u)))/prod deg`, so this IS the maximizer statement in the real
  Laplacian permanent ratio -- modulo the two named layers.

  This is NON-VACUOUS (Hnorm, Hdom are the genuine open layers, not `True`) and CONDITIONAL: it makes the
  exact remaining formal obligations explicit as two Lean `Prop`s.  It does NOT prove conjecture1.
  Genuine proof (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47StepMono

namespace R3Cert
namespace Step3

open RTree

/-- **R7' top capstone (conditional on the two open layers).** -/
theorem conjecture1_of_layers (tieU : UTree)
    (Hnorm : ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧ Aobj t ≤ Aobj (backboneU s))
    (Hdom : ∀ s : List Hub, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) →
        Aobj (backboneU s) ≤ Aobj tieU) :
    ∀ t : UTree, Aobj t ≤ Aobj tieU := by
  intro t
  obtain ⟨s, hbal, hcap, hts⟩ := Hnorm t
  obtain ⟨s', hst, hnf, hmono⟩ := chain_to_normalForm s hbal hcap
  have hbal' : Balanced s' := Balanced.chain hst hbal
  have hcap' : Capped s' := Capped.chain hst hcap
  exact le_trans hts (le_trans hmono (Hdom s' hbal' hcap' hnf))

end Step3
end R3Cert
