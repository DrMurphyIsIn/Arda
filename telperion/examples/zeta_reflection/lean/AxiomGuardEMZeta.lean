/-  AxiomGuardEMZeta.lean -- A2 Theorem 1 kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardEMZeta.lean

    Prints the axiom sets of the completed Euler-Maclaurin lemmas in `EMZeta.lean`.
    Expected on all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      Part A (periodized "saw" Bernoulli):
        * sawBernoulli_zero
        * sawBernoulli_measurable
        * abs_sawBernoulli_one_le
        * sawBernoulli_eq_on_Ico
        * sawBernoulli_one_eq_on_Ico
      Part B (one-step Euler-Maclaurin over a unit cell):
        * em_unit_step
      Part C (summed first-order Euler-Maclaurin over [0, N]):
        * euler_maclaurin_one
        * euler_maclaurin_one_window     -- general integer window [M, N]
      Part D (zeta base case, real exponent):
        * em_zeta_partial_real           -- EM representation of the partial zeta sum
        * em_zeta_remainder_integrableOn -- saw remainder integrable on (1,∞) for s>1 (D' input)
      Part D' (N → ∞ limit, real s > 1):
        * em_zeta_real                   -- EM representation of ∑' n, n^{-s}

    conjecture1_proved = False (NOT a proof of RH; a classical analysis lemma).
-/
import EMZeta

#print axioms ZetaReflection.sawBernoulli_zero
#print axioms ZetaReflection.sawBernoulli_measurable
#print axioms ZetaReflection.abs_sawBernoulli_one_le
#print axioms ZetaReflection.sawBernoulli_eq_on_Ico
#print axioms ZetaReflection.sawBernoulli_one_eq_on_Ico
#print axioms ZetaReflection.em_unit_step
#print axioms ZetaReflection.euler_maclaurin_one
#print axioms ZetaReflection.euler_maclaurin_one_window
#print axioms ZetaReflection.em_zeta_partial_real
#print axioms ZetaReflection.em_zeta_remainder_integrableOn
#print axioms ZetaReflection.em_zeta_real
