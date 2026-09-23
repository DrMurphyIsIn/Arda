/-  AxiomGuardA4.lean -- ANDÚRIL A4 / G2 kernel-axiom guard.

    A `lean_lib`; CI (telperion-zeta-reflection.yml) builds it, then runs

        lake env lean AxiomGuardA4.lean

    (with the sibling `zeta_zero_localization` build dir on `LEAN_PATH` so `XiLineZeros`
    resolves).

    Prints the axiom sets of the A4 `checkLine` soundness surface AND the G2 pilot instance.
    Expected on ALL: {propext, Classical.choice, Quot.sound} -- no `sorryAx`, no
    `ofReduceBool` (the `ok` sign chain is a KERNEL `decide`, not a `native_decide`; a
    `native_decide` would show `Lean.ofReduceBool` and would be flagged here).

    The G2 EVIDENCE is `ReflectedBand_t14.pilot`: a band conclusion (n on-line zeros of
    completedRiemannZeta) whose sign combinatorics carry NO numeric hypothesis -- only the
    named Arb-class `memR` enclosure facts -- and it is 3-axiom clean.

    conjecture1_proved = False (NOT a proof of RH).
-/
import CheckBand
import ReflectedBand_t14

/-! ### A4 checker soundness surface -/
#print axioms ZetaReflection.sign_of_box
#print axioms ZetaReflection.gLine_mul_neg_of_boxes
#print axioms ZetaReflection.zero_of_checked_pair
#print axioms ZetaReflection.checkLine_sign_isSome
#print axioms ZetaReflection.checkLine_adjacent_opposite
#print axioms ZetaReflection.checkLine_correct

/-! ### G2 pilot instance -- the reflected band with NO numeric sign hypotheses -/
#print axioms ReflectedBand_t14.ok
#print axioms ReflectedBand_t14.pilot
