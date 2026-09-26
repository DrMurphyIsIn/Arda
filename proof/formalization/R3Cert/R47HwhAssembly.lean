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
  hypotheses `hgdom`/`hpiece`/`hsymstar`) and every defective tree is covered (`Hcoverage`), then `hwh`
  holds.  OPEN INPUTS -- all four hypotheses (correction 2026-09-24; an earlier version of this header
  called coverage the sole open input):
    * `hgdom`, `hpiece`, `hsymstar` -- the certificates above prove the `Aobj` inequality on the
      cavity/closed-form models; wiring each class into `StraightStep_sized` (the cavity-to-`Aobj`
      bridge, plus the defect/size clauses) is NOT done, so these remain hypotheses;
    * `Hcoverage` -- the Brualdi-Goldwasser exhaustiveness.  Evidence: exhaustive for n <= 15
      (`viable_all`: 1793 defective trees, 0 failures).  Small-n evidence is weak here: the single-hub
      `Hnorm` also held at small n and first failed at n = 52 (`R47HnormFalse52`).  Larger-n check
      (`proof/docs/BG_HWH_COVERAGE_LARGE_N_2026-09-24.md`): the single-SPR viability test is
      exhaustively clean for n <= 23 but FAILS from n = 25 (exact witness, minDefect 1), so a
      single-SPR move-class family cannot supply `Hcoverage` for all n.  The target itself survives:
      `BGBackboneConjecture` (equivalently `StraightProgress_sized` at each fixed n) holds exhaustively
      and exactly for every n <= 100.
  The pinned consumer is `R47BGConjecture.bgBackbone_of_extended_coverage`.  No completeness is claimed:
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
    own vertex count (`hwh`/`Hnorm`).  All four hypotheses are open for general trees (see the header). -/
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
