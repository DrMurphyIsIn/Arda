/-  AxiomGuardZeroSignDecomp.lean -- ANDÚRIL G2-FULL kernel-axiom guard.

    NOT a `lean_lib`; run via the toolchain lean with a hand-built LEAN_PATH (lake env is E2BIG-dead
    in this island), and with `/tmp/g2deps` (XiLineZeros.olean + LambdaLineReal.olean, built from the
    sibling `zeta_zero_localization` island source) on the path.  Expected on ALL:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    The G2-full sign-bridge results (Γℝ-VALUE / magnitude blocker removed):
      * gamma_r_polar_t              -- Γℝ(1/2+it) = M·exp(iφ), M > 0  (polar form, general t ≠ 0)
      * gLine_sign_decomp_t          -- gLine t = M·(cos φ·Re ζ − sin φ·Im ζ), M > 0  (the crown lemma)
      * exists_zero_of_sign_change   -- the IVT single-pair bridge (XiLineZeros-only)
      * first_zero_of_sign_quantities-- CONDITIONAL first-zero in (14,15) from the two sign quantities

    conjecture1_proved = False.
-/
import ZeroSignDecomp_t14

#print axioms ZeroSignDecomp.gamma_r_polar_t
#print axioms ZeroSignDecomp.gLine_sign_decomp_t
#print axioms ZeroSignDecomp.exists_zero_of_sign_change
#print axioms ZeroSignDecomp.first_zero_of_sign_quantities
