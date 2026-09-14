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

/-! ### increment (iii) -- CharacterizationStatements

    DELIBERATELY NOT GUARDED HERE.  `CharacterizationStatements.lean` contains only
    `def ... : Prop` STATEMENTS of the published 1-D FQ characterization
    (Kurasov-Sarnak / Olevskii-Ulanovskii / Alon-Cohen-Vinzant Cor 1.4 /
    Lev-Olevskii / AKKV) and the OPEN program conjectures.  Nothing there is a
    theorem, so there are no axioms to print.  It builds green (no sorry) and is
    a defaultTarget; listing its `def`s under `#print axioms` would be a category
    error (they are Props, not proofs). -/
