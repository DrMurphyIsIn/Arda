/-
  R3Cert.R47HwhAssembly -- the ASSEMBLY reduction for `hwh`, packaging the proven move-classes and pinning
  the single remaining open obligation: COVERAGE (exhaustiveness).

  `hwh`/`Hnorm` follows (via the proven `hnorm_of_coverage`, `BGSCLFlpStepAt.lean:328`) once every defective
  tree admits SOME move from a covering set of straightening classes.  This file names three move-classes as
  predicates and reduces `hwh` to their exhaustive coverage:

    * `P_gdom`    -- a g-dominant defect-reducing move exists (interface established by
                    `R47HwhB1Partial.B1_nonneg_of_gdominance`: g-dominance => B1 >= 0 => Aobj-monotone);
    * `P_piece`   -- a piece/sub-star relocation applies (interface: `R47HwhLeafDecomp`/`R47HwhAdjDecomp`/
                    `R47HwhPieceDecomp` + `B2`/`B2adj >= 0`);
    * `P_symstar` -- the tree is a symmetric multi-star and takes the de-branching move (interface FULLY
                    proven, all `k`/hub-sizes: `R47HwhSymStarGenCert.symstar_gen_move_monotone`).

  `hwh_of_extended_coverage` shows: if each class refines to a `StraightStep_sized` (the interface
  hypotheses `hgdom`/`hpiece`/`hsymstar`, discharged by the certificates above modulo the cavity-`Aobj`
  bridge) and every defective tree is covered (`Hcoverage`), then `hwh` holds.  COVERAGE is the SOLE
  genuinely-open input -- and it is the open Brualdi-Goldwasser exhaustiveness, empirically verified to
  n <= 15 (`viable_all`: 1793 defective trees, 0 failures).  No completeness is claimed:
  `conjecture1_proved = False`.

  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.BGSCLFlpStepAt

namespace R3Cert
namespace Step3

open RTree

/-- **The `hwh` assembly reduction.**  Given three named straightening-move classes -- each proven to
    refine to a `StraightStep_sized` (`hgdom`, `hpiece`, `hsymstar`) -- and the COVERAGE hypothesis that
    every defective tree lies in at least one class, every tree is `Aobj`-dominated by a hub-backbone of its
    own vertex count (`hwh`/`Hnorm`).  Coverage (exhaustiveness) is the sole open obligation. -/
theorem hwh_of_extended_coverage
    (P_gdom P_piece P_symstar : UTree → Prop)
    (hgdom    : ∀ t : UTree, P_gdom t    → ∃ t', StraightStep_sized t t')
    (hpiece   : ∀ t : UTree, P_piece t   → ∃ t', StraightStep_sized t t')
    (hsymstar : ∀ t : UTree, P_symstar t → ∃ t', StraightStep_sized t t')
    (Hcoverage : ∀ t : UTree, strDefect t ≠ 0 → P_gdom t ∨ P_piece t ∨ P_symstar t) :
    ∀ t : UTree, ∃ s : List Hub, usize (backboneU s) = usize t ∧ Aobj t ≤ Aobj (backboneU s) := by
  refine hnorm_of_coverage (fun t t' => StraightStep_sized t t') (fun h => h) ?_
  intro t hd
  rcases Hcoverage t hd with h | h | h
  · exact hgdom t h
  · exact hpiece t h
  · exact hsymstar t h

end Step3
end R3Cert
