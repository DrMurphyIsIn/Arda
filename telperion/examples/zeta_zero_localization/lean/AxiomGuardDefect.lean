/-  AxiomGuardDefect -- MIRRORMERE QC-B3 (qc-wedge) kernel-axiom guard.

    Like `AxiomGuardBragg.lean`, this is declared as a `lean_lib` (so `lake build` compiles it and
    all its imports) AND is run explicitly by CI with

        lake env lean AxiomGuardDefect.lean

    AFTER `lake build`, FAILING if any `#print axioms` output mentions `sorryAx` (or `ofReduceBool`).

    Guarded anchors -- the inertia dictionary (DefectDictionary.lean) + the certified perturbation
    experiment (BraggDefect.lean):

    ## Dictionary (deliverable 1)
      * DefectDictionary.defect_ge_one_of_neg_dir  -- row (a) generic: a strictly-negative direction
        forces defect >= 1 (Sylvester subspace bound on -A over span{x0}).
      * DefectDictionary.offline_pair_negIndex     -- row (a) concrete (Prop 4.1): an off-line pair
        block x xT - y yT with <w,x>=0 != <w,y> has defect >= 1 -- the (1,1) signature.
      * DefectDictionary.PairDecomp.defect_le_offline_pairs -- row (c): defect <= p (# off-line pairs),
        the DUAL of the paper's posIndex_blockA_le.
      * DefectDictionary.PairDecomp.defect_zero_iff_onLine  -- row (b) finite iff (RH-hard direction
        carried as an explicit hypothesis).
      * DefectDictionary.PairDecomp.defect_zero_of_no_pairs -- row (b) unconditional <= direction.
      * DefectDictionary.PairDecomp.defect_zero_of_posSemidef -- crystalline snapshot => defect 0.
      * DefectDictionary.pairBlock_hermForm / hermForm_smul_sq -- supporting algebra.

    ## Certified perturbation experiment (deliverable 2)
      * BraggDefect.defect_witness_online  -- the honest (on-line) configuration's finite Weil
        functional is >= 0 in [A,B] (consistent with defect 0).
      * BraggDefect.defect_witness_offline -- the SAME functional with one synthetic off-line pair
        adjoined is < 0 in [A',B'] with B' < 0 <= A: the measured, machine-checked (1,1) leakage.
      * BraggDefect.defect_leakage_gap     -- the two enclosures are separated (B' < A): the defect
        is a kernel-observable, not a rounding artifact.

    Expected on all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    ## The functional-equation quadruple audit (QuadrupleDefect.lean, W2b correction)
      * QuadrupleDefect.offline_quadruple_sigma_pair_count -- a GENUINE off-line zero
        (re != 1/2, im != 0) has a 4-element functional-equation quadruple that splits into
        EXACTLY TWO sigma-orbits: one genuine off-line zero costs p = 2, not p = 1.
      * QuadrupleDefect.quad_real_offline / quad_online -- the two degenerations (p = 1 for a real
        off-line zero; p = 0 for an on-line zero, which is sigma-fixed).
      * QuadrupleDefect.defect_sumPairBlock_le -- row (c) at ARBITRARY ambient dimension, ARBITRARY
        numbers of on-line and off-line channels (answers the "synthetic 2x2" caveat).
      * QuadrupleDefect.defect_sumPairBlock_ge_of_subspace / defect_sumPairBlock_eq -- the rigidity
        direction and the two-sided count at that same arbitrary generality.
      * QuadrupleDefect.defect_parallel_channels_eq_one -- the COUNTEREXAMPLE: two nonzero off-line
        channels that are parallel leak ONE negative direction, so defect = 1 < 2 = p.
      * QuadrupleDefect.quadruple_witness_dimension_not_determined -- the headline correction: same
        ambient dimension, same on-line channel, two nonzero off-line channels in both cases,
        defects 1 and 2.  The witness dimension a quadruple contributes is NOT a function of the
        quadruple.
      * QuadrupleDefect.twoPairBlock_reflection_degenerate_defect_eq_one -- the same read on the
        island's own `twoPairBlock`, the shape `BraggDefect.defect_eq_two` is stated on.

    conjecture1_proved = False.  These are FINITE inertia/diffraction facts about certified data and
    one synthetic pair; they prove NOTHING new about the Riemann Hypothesis.
-/
import DefectDictionary
import R2Rigidity
import BraggDefect
import QuadrupleDefect

/-! ### Dictionary rows (a), (b), (c) + supporting algebra -/
#print axioms DefectDictionary.hermForm_smul_sq
#print axioms DefectDictionary.pairBlock_hermForm
#print axioms DefectDictionary.defect_ge_one_of_neg_dir
#print axioms DefectDictionary.offline_pair_negIndex
#print axioms DefectDictionary.PairDecomp.defect_le_offline_pairs
#print axioms DefectDictionary.PairDecomp.defect_zero_of_posSemidef
#print axioms DefectDictionary.PairDecomp.defect_zero_iff_onLine
#print axioms DefectDictionary.PairDecomp.defect_zero_of_no_pairs

/-! ### The certified perturbation experiment -/
#print axioms BraggDefect.defect_witness_online
#print axioms BraggDefect.defect_witness_offline
#print axioms BraggDefect.defect_leakage_gap

/-! ### The 2-channel signature bridge (29 certified zeros + 1 synthetic pair) -/
#print axioms BraggDefect.defect_two_channel_online
#print axioms BraggDefect.defect_two_channel_offline

/-! ### The R2 rigidity rung (W2b): the instrument COUNTS the off-line pairs

  * DefectDictionary.offline_pairs_le_defect       -- rigidity direction (abstract): a p-dim
    negative-definite subspace forces defect >= p (dual of finrank_le_posIndex_of_posDefOn on -A).
  * DefectDictionary.PairDecomp.defect_eq_offline_pairs -- the two-sided count defect = p (abstract).
  * DefectDictionary.defect_pairBlock_le_one / defect_twoPairBlock_le_two -- rank-one/rank-two
    negative-channel upper bounds.
  * BraggDefect.bragg_defect_eq_one   -- INSTANTIATION: one synthetic pair => defect EXACTLY 1.
  * BraggDefect.defect_eq_two         -- INSTANTIATION: two synthetic pairs => defect EXACTLY 2. -/
#print axioms DefectDictionary.offline_pairs_le_defect
#print axioms DefectDictionary.PairDecomp.defect_eq_offline_pairs
#print axioms DefectDictionary.defect_pairBlock_le_one
#print axioms DefectDictionary.defect_twoPairBlock_le_two
#print axioms BraggDefect.bragg_neg_dir
#print axioms BraggDefect.bragg_defect_eq_one
#print axioms BraggDefect.twoPair_hermForm_neg
#print axioms BraggDefect.defect_eq_two

/-! ### The functional-equation quadruple audit (W2b correction, QuadrupleDefect.lean) -/
#print axioms QuadrupleDefect.sigmaRefl_eq_self_iff
#print axioms QuadrupleDefect.quad_card_eq_four
#print axioms QuadrupleDefect.quad_eq_union
#print axioms QuadrupleDefect.sigmaPair_disjoint
#print axioms QuadrupleDefect.offline_quadruple_sigma_pair_count
#print axioms QuadrupleDefect.quad_real_offline
#print axioms QuadrupleDefect.quad_online
#print axioms QuadrupleDefect.fe_eq_conj_of_online
#print axioms QuadrupleDefect.quad_online_card
#print axioms QuadrupleDefect.defect_sumPairBlock_le_rank
#print axioms QuadrupleDefect.defect_sumPairBlock_le
#print axioms QuadrupleDefect.defect_sumPairBlock_ge_of_subspace
#print axioms QuadrupleDefect.defect_sumPairBlock_eq
#print axioms QuadrupleDefect.degenerate_channels
#print axioms QuadrupleDefect.defect_parallel_channels_eq_one
#print axioms QuadrupleDefect.orthogonality_is_load_bearing
#print axioms QuadrupleDefect.defect_quadruple_block_le
#print axioms QuadrupleDefect.sumPairBlock_two
#print axioms QuadrupleDefect.quadruple_witness_dimension_not_determined
#print axioms QuadrupleDefect.twoPairBlock_reflection_degenerate_defect_eq_one
