/-  AxiomGuardReflection.lean -- A1 correctness-surface kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardReflection.lean

    Prints the axiom sets of EVERY A1 headline (DIntvCorrect op-soundness, TaylorKernels
    remainder brackets, CertVerify certificate soundness).  Expected on all:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    The computable-but-unproven Horner kernel (`TaylorKernels.hornerD`) is EXCLUDED here (it
    carries no headline soundness lemma -- its soundness is `expD_sound_of_endpoints`, which
    IS listed).  Any UNSOUND-pending op would likewise be excluded; A1 shipped none.

    conjecture1_proved = False (NOT a proof of RH).
-/
import DIntvCorrect
import TaylorKernels
import CertVerify

/-! ### DIntvCorrect -- op mem-soundness -/
#print axioms DIntvProd.DIntv.ofInt_sound
#print axioms DIntvProd.DIntv.scale2_sound
#print axioms DIntvProd.DIntv.neg_sound
#print axioms DIntvProd.DIntv.sub_sound
#print axioms DIntvProd.DIntv.abs_sound
#print axioms DIntvProd.DIntv.hull_sound_left
#print axioms DIntvProd.DIntv.hull_sound_right
#print axioms DIntvProd.DIntv.roundTo_sound
#print axioms DIntvProd.DIntv.nonneg_sound
#print axioms DIntvProd.DIntv.nonpos_sound
#print axioms DIntvProd.DIntv.isPos_sound
#print axioms DIntvProd.DIntv.isNeg_sound
#print axioms DIntvProd.DIntv.sign?_pos
#print axioms DIntvProd.DIntv.sign?_neg
#print axioms DIntvProd.DIntv.belowR_sound

/-! ### TaylorKernels -- transcendental remainder brackets -/
#print axioms TaylorKernels.exp_lower
#print axioms TaylorKernels.exp_upper
#print axioms TaylorKernels.exp_encl_of_endpoints
#print axioms TaylorKernels.expD_sound_of_endpoints
#print axioms TaylorKernels.cos_lower
#print axioms TaylorKernels.cos_upper
#print axioms TaylorKernels.sin_lower
#print axioms TaylorKernels.sin_upper
#print axioms TaylorKernels.cosD_sound_of_bracket
#print axioms TaylorKernels.sinD_sound_of_bracket

/-! ### CertVerify -- verify-not-compute certificate soundness -/
#print axioms CertVerify.invSqrt_lower
#print axioms CertVerify.invSqrt_upper
#print axioms CertVerify.inv_lower
#print axioms CertVerify.inv_upper
#print axioms CertVerify.ln_of_exp_bracket
#print axioms CertVerify.ln_of_taylor_bracket
#print axioms CertVerify.pi_bracket
#print axioms CertVerify.piCert
