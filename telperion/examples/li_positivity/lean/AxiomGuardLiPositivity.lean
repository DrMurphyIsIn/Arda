/-  AxiomGuardLiPositivity -- CI kernel-axiom guard for the Li positivity ladder.

    Mirrors AxiomGuardRHInBox.lean: NOT a `lean_lib`; CI runs it explicitly with

        lake env lean AxiomGuardLiPositivity.lean

    AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * LiPositivity.li_rung_0 / li_rung_19 -- the first and last emitted rungs
        (0 ≤ (taylorCoeff riemannXi n).re from the certified rational lower
        bound hypothesis; the Arb enclosure is the documented trust seam).
      * LiPositivity.li_neg_refutes_rh -- the falsifiability face: a certified
        negative upper bound on any rung refutes RH through the upstream
        equivalence.  Never expected to fire.
      * LiCriterion.li_criterion_rh_iff -- the UPSTREAM reduction itself
        (nicholasbulka/li-criterion-rh-equivalence-lean, pinned in
        lakefile.toml): RiemannHypothesis ↔ ∀ n, 0 ≤ (taylorCoeff riemannXi n).re.
        Guarding it here re-verifies the dependency's axiom hygiene at our pin.

    conjecture1_proved = False: rungs are finite necessary-condition checks;
    the uniform ∀ n IS RH and nothing here approaches it.
-/
import LiPositivity
import LiLadder

#print axioms LiPositivity.li_rung_0
#print axioms LiPositivity.li_rung_19
#print axioms LiPositivity.li_neg_refutes_rh
#print axioms LiCriterion.li_criterion_rh_iff

-- LiLadder (hand-written reduction layer): the ladder as a reduction of RH to
-- its tail. Restates li_criterion_rh_iff relative to a certified prefix; proves
-- neither side of RH. conjecture1_proved = False.
#print axioms LiPositivity.li_rh_iff_tail
#print axioms LiPositivity.li_tail_peel
#print axioms LiPositivity.li_rh_iff_tail_zero
