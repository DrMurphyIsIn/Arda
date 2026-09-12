/-  AxiomGuardEMZeta.lean -- A2 Theorem 1 kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardEMZeta.lean

    Prints the axiom sets of the completed Euler-Maclaurin lemmas in `EMZeta.lean`.
    Expected on all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      Part A (periodized "saw" Bernoulli):
        * sawBernoulli_zero
        * sawBernoulli_eq_on_Ico
        * sawBernoulli_one_eq_on_Ico
      Part B (one-step Euler-Maclaurin over a unit cell):
        * em_unit_step

    conjecture1_proved = False (NOT a proof of RH; a classical analysis lemma).
-/
import EMZeta

#print axioms ZetaReflection.sawBernoulli_zero
#print axioms ZetaReflection.sawBernoulli_eq_on_Ico
#print axioms ZetaReflection.sawBernoulli_one_eq_on_Ico
#print axioms ZetaReflection.em_unit_step
