/-
  R3Cert.R47MergePerL -- the merge-layer capstone, stated in the REAL Laplacian permanent ratio.

  The merge layer (R47StepMono) proves `chain_to_normalForm`: every Balanced+Capped hub-state rewrites,
  by ordered merges, to a normal form with `Aobj (backboneU s) ≤ Aobj (backboneU t)`, where
  `Aobj u = Ztot (dtRealize u)` is the internal rational objective.  `pi_utree` (R47Tree) proves that
  `Aobj u` IS the actual Laplacian permanent ratio `per(L(realize(dtRealize u))) / ∏ deg` for every
  rooted tree `u`.

  This file composes the two: it restates the merge capstone in the target object of the whole program,
  `per(L)/∏deg`, so the merge monotonicity is now expressed in the quantity Brualdi-Goldwasser is about --
  not the internal `Aobj`.  This is the natural next G7 composition step after the merge layer was
  confirmed complete (see docs/design/G7_AUDIT_CORRECTION_20260823.md).

  It does NOT close conjecture1: the (L)/(B) normalization-into-family layer, R5/R6, the stratum-(i) rate
  port, and the top R7' composition remain the open layers.  Genuine proof (no `sorry`).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47StepMono
import R3Cert.R47Tree

namespace R3Cert
namespace Step3

open RTree

/-- **Merge-layer capstone in the Laplacian permanent ratio.**  Every Balanced+Capped hub-state `s`
    ordered-merge-rewrites to a normal form `t` whose `per(L)/∏deg` is at least that of `s`.  (Obtained
    from `chain_to_normalForm` by rewriting both `Aobj` sides through `pi_utree`.) -/
theorem merge_normalForm_perL (s : List Hub) (hbal : Balanced s) (hcap : Capped s) :
    ∃ t, Relation.ReflTransGen OrderedStep s t ∧ (∀ u, ¬ OrderedStep t u) ∧
      (lapl (aGraph (realize (dtRealize (backboneU s))))).permanent
          / (∏ v, ((aGraph (realize (dtRealize (backboneU s)))).degree v : ℝ))
        ≤ (lapl (aGraph (realize (dtRealize (backboneU t))))).permanent
          / (∏ v, ((aGraph (realize (dtRealize (backboneU t)))).degree v : ℝ)) := by
  obtain ⟨t, hst, hnf, hmono⟩ := chain_to_normalForm s hbal hcap
  refine ⟨t, hst, hnf, ?_⟩
  rw [pi_utree (backboneU s), pi_utree (backboneU t)]
  exact hmono

end Step3
end R3Cert
