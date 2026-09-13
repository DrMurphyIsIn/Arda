/-  AxiomGuardQC.lean -- PROGRAM MIRRORMERE QC-1 kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardQC.lean

    Prints the axiom sets of every completed QC-1 headline theorem.  Expected on
    all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    conjecture1_proved = False (NOT a proof of RH).
-/
import LeeYangCore
import KSConstruction

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
