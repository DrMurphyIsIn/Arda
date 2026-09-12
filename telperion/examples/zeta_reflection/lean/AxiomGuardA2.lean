/-  AxiomGuardA2.lean -- A2 bridge-lemmas kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardA2.lean

    Prints the axiom sets of the A2 bridge anchors (theorems 3, 4, 7).  Expected on all:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      Theorem 3 (LogBranches -- FTC/branch bridge):
        * argChangeVert_eq_im_log_sub
        * argChangeHoriz_eq_im_log_sub
      Theorem 4 (LogZetaSeries -- prime-power log-zeta branch):
        * hasDerivAt_logZetaBranch
        * deriv_logZetaBranch
        * analyticOnNhd_logZetaBranch
        * logZetaBranch_tail_bound
      Theorem 7 (SignChain -- alternating-sign chain => T5 hLine):
        * exists_zero_of_sign_change
        * alternating_signs_chain

    conjecture1_proved = False (NOT a proof of RH).
-/
import LogBranches
import LogZetaSeries
import SignChain

#print axioms ZetaReflection.argChangeVert_eq_im_log_sub
#print axioms ZetaReflection.argChangeHoriz_eq_im_log_sub
#print axioms ZetaReflection.hasDerivAt_logZetaBranch
#print axioms ZetaReflection.deriv_logZetaBranch
#print axioms ZetaReflection.analyticOnNhd_logZetaBranch
#print axioms ZetaReflection.logZetaBranch_tail_bound
#print axioms ZetaReflection.exists_zero_of_sign_change
#print axioms ZetaReflection.alternating_signs_chain
