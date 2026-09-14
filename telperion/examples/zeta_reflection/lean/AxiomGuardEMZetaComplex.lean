/-  AxiomGuardEMZetaComplex.lean -- A2 Theorem 1 E-track kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardEMZetaComplex.lean

    Prints the axiom sets of the completed COMPLEX Euler-Maclaurin lemmas in `EMZetaComplex.lean`.
    Expected on all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      E1 (complex lift):
        * em_unit_step_cpow              -- one-step EM over [m,m+1], ℂ-valued f
        * euler_maclaurin_one_window_cpow -- summed EM over integer window [M,N], ℂ-valued
        * hasDerivAt_cpow_neg            -- σ-direction cpow derivative on ℝ>0
        * em_cpow_partial               -- finite-N EM for f x = (x:ℂ)^(-s)
      E2 (N→∞ complex representation, Re s > 1):
        * em_zeta_cpow                   -- EM representation of ∑' n, n^{-s} (complex)
        * em_zeta_cpow_riemannZeta       -- tied to riemannZeta via zeta_eq_tsum_one_div_nat_cpow
      E3 (K=1 analytic continuation into the critical strip, 0 < Re s):
        * em_zeta_strip                  -- riemannZeta s = EM closed form + remainder, 0<Re s, s≠1
        * em_zeta_strip_remainder_bound  -- explicit remainder tail bound
      E4 (evaluator-facing enclosure):
        * em_zeta_strip_enclosure        -- finite-sum + explicit-tail enclosure shape

    conjecture1_proved = False (NOT a proof of RH; a classical analysis lemma).
-/
import EMZetaComplex

#print axioms ZetaReflection.em_unit_step_cpow
#print axioms ZetaReflection.euler_maclaurin_one_window_cpow
#print axioms ZetaReflection.hasDerivAt_cpow_neg
#print axioms ZetaReflection.em_cpow_partial
#print axioms ZetaReflection.cpow_neg_integrableOn_Ioi
#print axioms ZetaReflection.em_cpow_remainder_integrableOn
#print axioms ZetaReflection.em_zeta_cpow
#print axioms ZetaReflection.em_zeta_cpow_riemannZeta
#print axioms ZetaReflection.em_cpow_remainder_integrableOn_strip
#print axioms ZetaReflection.emZetaRemainder_bound
#print axioms ZetaReflection.emZetaClosed_eq_riemannZeta_of_one_lt
#print axioms ZetaReflection.emZetaRemainder_hasDerivAt
#print axioms ZetaReflection.hasDerivAt_emIntegrand
#print axioms ZetaReflection.log_le_rpow_div
