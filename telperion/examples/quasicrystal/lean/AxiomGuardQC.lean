/-  AxiomGuardQC.lean -- PROGRAM MIRRORMERE QC-1 kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardQC.lean

    Prints the axiom sets of every completed QC-1 headline theorem.  Expected on
    all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    conjecture1_proved = False (NOT a proof of RH).
-/
import LeeYangCore
import KSConstruction
import BoundaryLemmas
import TwoFreqRigidity
import RationalFreqReduction
import InvolutionDictionary
import OfflineDiscs
import OfflineDiscsInstances

open Quasicrystal

/-! ### increment (i) -- LeeYangCore exponential-sum bridge -/
#print axioms Quasicrystal.norm_exp_arg
#print axioms Quasicrystal.exp_arg_ne_zero
#print axioms Quasicrystal.expPoly_root_iff_eval_zero
#print axioms Quasicrystal.expPoly_root_on_circle
#print axioms Quasicrystal.leeYang_root_norm_one

/-! ### increment (ii) -- KSConstruction crystalline structure + Poisson -/
#print axioms Quasicrystal.preimage_eq_latticeAP
#print axioms Quasicrystal.mem_zeroSet_iff
#print axioms Quasicrystal.latticeAP_mem
#print axioms Quasicrystal.poisson_shifted_lattice

/-! ### increment (iv) -- BoundaryLemmas "where zeta escapes" -/
#print axioms Quasicrystal.not_uniformlyDiscrete_of_dense
#print axioms Quasicrystal.two_pow_ne_three_pow
#print axioms Quasicrystal.log_two_three_incommensurable
#print axioms Quasicrystal.log_two_three_incommensurable_int
#print axioms Quasicrystal.primeLogSpectrum_dense
#print axioms Quasicrystal.primeLogSpectrum_not_uniformlyDiscrete
#print axioms Quasicrystal.not_uniformlyDiscrete_of_gaps_to_zero
#print axioms Quasicrystal.exists_close_of_card_gt
#print axioms Quasicrystal.zeta_ordinates_not_uniformlyDiscrete

/-! ### increment (iv) W2c -- the N(T) brick: discharging the counting hypothesis -/
#print axioms Quasicrystal.exists_close_of_gap_lt
#print axioms Quasicrystal.exists_gap_le_of_window
#print axioms Quasicrystal.windowedDensity_of_unboundedMeanDensity
#print axioms Quasicrystal.not_uniformlyDiscrete_of_windowedDensity
#print axioms Quasicrystal.zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density

/-! ### handoff K1 -- TwoFreqRigidity (Theorem A) -/
#print axioms Quasicrystal.twoFreq_eq_zero_iff
#print axioms Quasicrystal.twoFreq_zero_norm
#print axioms Quasicrystal.twoFreq_realRooted_iff

/-! ### handoff K2 -- RationalFreqReduction (Theorem B bridge) -/
#print axioms Quasicrystal.norm_exp_omega
#print axioms Quasicrystal.im_zero_iff_norm_one
#print axioms Quasicrystal.ratFreq_eq_zero_iff
#print axioms Quasicrystal.ratFreq_realRooted_of_leeYangCircle
#print axioms Quasicrystal.leeYangCircle_reached_of_realRooted

/-! ### Wave-2 handoff W2a -- InvolutionDictionary (functional equation ⟺
    self-inversive symmetry) -/
#print axioms Quasicrystal.intertwiner
#print axioms Quasicrystal.fixed_locus_correspondence
#print axioms Quasicrystal.selfInversive_zeros_symmetric
#print axioms Quasicrystal.inv_conj_exp_real
#print axioms Quasicrystal.selfInversive_circle_identity
#print axioms Quasicrystal.selfInversive_iff_hardyZ_real
#print axioms Quasicrystal.binomialPoly_eval
#print axioms Quasicrystal.binomialPoly_natDegree
#print axioms Quasicrystal.twoFreq_dictionary
#print axioms Quasicrystal.selfInversive_binomial_realRooted
#print axioms Quasicrystal.fixed_locus_dichotomy

/-! ### MIRRORMERE E4b -- OfflineDiscs (registry node MM_offline_disjoint_discs,
    QC_RECURRENCE section 4.3 isolation lemma) -/
#print axioms Quasicrystal.exists_pos_lower_bound_of_finset
#print axioms Quasicrystal.abs_re_sub_le_dist
#print axioms Quasicrystal.offline_disjoint_discs

/-! ### MIRRORMERE E4b instances -- OfflineDiscsInstances (emitted by the Telperion
    `disjoint_discs` kind; the points are INPUT, not a claim about zeta) -/
#print axioms OfflineDiscsInstances.offline_discs_online_pair
#print axioms OfflineDiscsInstances.offline_discs_offline_bank

/-! ### increment (iii) -- CharacterizationStatements

    DELIBERATELY NOT GUARDED HERE.  `CharacterizationStatements.lean` contains only
    `def ... : Prop` STATEMENTS of the published 1-D FQ characterization
    (Kurasov-Sarnak / Olevskii-Ulanovskii / Alon-Cohen-Vinzant Cor 1.4 /
    Lev-Olevskii / AKKV) and the OPEN program conjectures.  Nothing there is a
    theorem, so there are no axioms to print.  It builds green (no sorry) and is
    a defaultTarget; listing its `def`s under `#print axioms` would be a category
    error (they are Props, not proofs). -/
