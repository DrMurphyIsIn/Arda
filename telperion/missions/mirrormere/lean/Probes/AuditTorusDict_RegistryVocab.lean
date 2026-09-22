-- AUDIT PROBE A2 (2026-09-22), node MM_torus_section_dictionary: the REGISTERED statement, proved
-- against the registry's own vocabulary (Statements.MMDefs) with the artifact's one tactic line,
-- and again with the one-rewrite form.  conjecture1_proved = False; nothing here proves RH.
import Mathlib
import Statements.MMDefs
open Quasicrystal

theorem torus_section_dictionary_registry_vocab (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := by
  simp [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two]

theorem torus_section_dictionary_registry_vocab_rw (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := by
  rw [linearTorusForm, Fin.sum_univ_two]; rfl

#print axioms torus_section_dictionary_registry_vocab
#print axioms torus_section_dictionary_registry_vocab_rw
