/-  AxiomGuardArctanTaylor.lean -- ANDÚRIL θ-value instrument kernel-axiom guard.

    NOT a `lean_lib`; run via the toolchain lean with a hand-built LEAN_PATH (lake env is
    E2BIG-dead in this island).  Expected on ALL: {propext, Classical.choice, Quot.sound} --
    no sorryAx, no ofReduceBool.

      * arctan_bracket           -- THE INSTRUMENT: |arctan u − atanPS u N| ≤ u^(2N+1)/(2N+1)
      * arctan_eq_ps_add_rem     -- the integral-representation split
      * rem_abs_le               -- the elementary remainder bound
      * arctan_le_self / self_sub_cube_le_arctan -- the far-tail corollaries

    conjecture1_proved = False.
-/
import ArctanTaylor

#print axioms ArctanTaylor.arctan_bracket
#print axioms ArctanTaylor.arctan_eq_ps_add_rem
#print axioms ArctanTaylor.rem_abs_le
#print axioms ArctanTaylor.arctan_le_self
#print axioms ArctanTaylor.self_sub_cube_le_arctan
