/-  AxiomGuardSpeiserBoxProbe.lean -- MM_speiser_box_probe kernel-axiom guard.

    Hand-written, NOT generated.  Run explicitly with

        lake env lean AxiomGuardSpeiserBoxProbe.lean

    Prints the axiom set of every headline theorem of the island.  Expected on ALL of
    them: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    SCOPE: the island's capstone `speiser_box_probe_of_numeric` is a *conditional*
    theorem.  It discharges the box claim modulo the two named numeric obligations
    `SecondDerivBoundOnBox` and `GridModulusLowerBound`, which are hypotheses, not
    axioms -- which is exactly why this guard shows no `sorryAx`.  The obligations
    remain OPEN and are not proved anywhere in this repository.

    This island is NOT the Speiser wall and is NOT a step toward RH.
    conjecture1_proved = False.
-/
import SpeiserBoxProbe

open SpeiserBoxProbe

/-! ### The general grid-modulus instrument (unconditional) -/
#print axioms SpeiserBoxProbe.norm_sub_le_of_sq_le
#print axioms SpeiserBoxProbe.nonvanishing_of_grid

/-! ### Box geometry (unconditional) -/
#print axioms SpeiserBoxProbe.mem_box
#print axioms SpeiserBoxProbe.convex_box
#print axioms SpeiserBoxProbe.gridSet_subset_box
#print axioms SpeiserBoxProbe.box_covered
#print axioms SpeiserBoxProbe.box_subset_compl_one

/-! ### Holomorphy of `zeta'` on the box (unconditional, from Mathlib) -/
#print axioms SpeiserBoxProbe.zeta_analyticOnNhd
#print axioms SpeiserBoxProbe.zeta_deriv_analyticOnNhd
#print axioms SpeiserBoxProbe.hasDerivWithinAt_zeta_deriv

/-! ### The capstone (conditional on the two named numeric obligations) -/
#print axioms SpeiserBoxProbe.gridModulusLowerBound_of_points
#print axioms SpeiserBoxProbe.speiser_box_probe_of_numeric

/-! ### The emitted certificate arithmetic (unconditional rational facts) -/
#print axioms SpeiserBoxCert.speiser_box_cert_cover_radius_ok
#print axioms SpeiserBoxCert.speiser_box_cert_gap_ok
#print axioms SpeiserBoxCert.speiser_box_cert_column_span_ok
#print axioms SpeiserBoxCert.speiser_box_cert_row_tiling_ok
#print axioms SpeiserBoxCert.speiser_box_cert
