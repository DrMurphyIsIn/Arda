/-  RS5_AxiomGuardSharp.lean -- kernel-axiom guard of the RSC0 Phase 3 modules (RS5_EvalSharp: the
    sharpened band predicate; RS5_ZSharp: its sign lemmas via `RSInt.rs_Z_C0'`; RS5_BandSharp: band
    soundness; RS5_DemoSharp: the read-back controls).

    Not yet a `lean_lib` (lakefile.toml untouched).  Run, after writing the oleans to `.lake/rsc0_side`
    with `lake env lean -o`, as

        LEAN_PATH=$PWD/.lake/rsc0_side lake env lean RS5_AxiomGuardSharp.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`, no
    `Lean.ofReduceBool` (the controls use `decide +kernel`, not `native_decide`), no new axiom.

    conjecture1_proved = False.
-/
import RS5_DemoSharp

/-! ### RS5_EvalSharp (0 theorems; definitions: HeightOK, PosOK', NegOK', sampleOK', bandAux', bandOK') -/

/-! ### RS5_ZSharp (8 theorems; definitions: none) -/
#print axioms RS5.rs5_Z_enclosure'
#print axioms RS5.rs5_Z_enclosure_E'
#print axioms RS5.posOK'_real
#print axioms RS5.negOK'_real
#print axioms RS5.rs5_sign_pos'
#print axioms RS5.rs5_sign_neg'
#print axioms RS5.heightOK_real
#print axioms RS5.sampleOK'_sign

/-! ### RS5_BandSharp (3 theorems; definitions: none) -/
#print axioms RS5.bandOK'_facts
#print axioms RS5.band_sound'
#print axioms RS5.bandZeros_of_ok'

/-! ### RS5_DemoSharp (28 theorems; definitions: knife, knife_Edec, low, at4250, below4250, knife_E35, knife_E35m, negs) -/
#print axioms RS5.DemoSharp.knife_height
#print axioms RS5.DemoSharp.knife_tight
#print axioms RS5.DemoSharp.knife_old_rejected
#print axioms RS5.DemoSharp.knife_old_PosOK_fails
#print axioms RS5.DemoSharp.knife_new_accepted
#print axioms RS5.DemoSharp.knife_pos
#print axioms RS5.DemoSharp.knife_band
#print axioms RS5.DemoSharp.knife_t
#print axioms RS5.DemoSharp.knife_sign
#print axioms RS5.DemoSharp.knife_Edec_rejected
#print axioms RS5.DemoSharp.knife_Edec_margin_fails
#print axioms RS5.DemoSharp.low_old_accepted
#print axioms RS5.DemoSharp.low_height_fails
#print axioms RS5.DemoSharp.low_refused
#print axioms RS5.DemoSharp.at4250_height
#print axioms RS5.DemoSharp.at4250_accepted
#print axioms RS5.DemoSharp.below4250_height_fails
#print axioms RS5.DemoSharp.below4250_old_accepted
#print axioms RS5.DemoSharp.below4250_refused
#print axioms RS5.DemoSharp.knife_E35_margin
#print axioms RS5.DemoSharp.knife_E35_PosOK'_false
#print axioms RS5.DemoSharp.knife_E35_rejected
#print axioms RS5.DemoSharp.knife_E35m_PosOK'_true
#print axioms RS5.DemoSharp.knife_E35m_accepted
#print axioms RS5.DemoSharp.negs_pos
#print axioms RS5.DemoSharp.negs_NegOK'
#print axioms RS5.DemoSharp.negs_accepted
#print axioms RS5.DemoSharp.neg_sign
