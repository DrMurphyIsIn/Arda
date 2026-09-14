/-  AxiomGuardThetaValue.lean -- ANDÚRIL θ-value finite-pipeline kernel-axiom guard.

    NOT a `lean_lib`; run via the toolchain lean with a hand-built LEAN_PATH.  Expected on ALL:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      * arg_eq_arctan_of_re_pos  -- the per-factor atom
      * imLn_formula             -- the exact Im L_n formula
      * exp_Ln_eq_gammaSeq       -- the Gauss-product bridge

    The two remaining obligations (ThetaGap.RateObligation, ThetaGap.BranchBridgeObligation) are
    `def`s of `Prop` (statements), not proved terms -- there is nothing to guard on them; they are
    the honestly-named gap between this finite pipeline and the φ(14) value box.

    conjecture1_proved = False.
-/
import ThetaValue

#print axioms ThetaValue.arg_eq_arctan_of_re_pos
#print axioms ThetaValue.imLn_formula
#print axioms ThetaValue.exp_Ln_eq_gammaSeq
