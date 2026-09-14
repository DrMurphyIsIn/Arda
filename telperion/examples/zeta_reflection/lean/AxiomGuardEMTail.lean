/-  AxiomGuardEMTail.lean -- A2 Theorem 1 TAIL-track kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardEMTail.lean

    Prints the axiom sets of the completed order-K Euler-Maclaurin tail lemmas in `EMZetaTail.lean`.
    Expected on all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      Part F (order-2/3 periodized Bernoulli sup bounds):
        * abs_sawBernoulli_two_le          -- |sawBernoulli 2| ≤ 1/6
        * bernoulliFun_three               -- B₃ closed form (bernoulli 3 = 0)
        * abs_sawBernoulli_three_le        -- |sawBernoulli 3| ≤ 1/12
      Part G (saw-order-raising IBP step):
        * sawAntideriv_hasDerivAt_Ioo      -- shifted Bernoulli antiderivative on the open cell
        * em_saw_step                      -- the one-step IBP raising the saw order (proven WIP shape)
      Part H (N-decaying tail remainder engine):
        * em_tail_integral_bound           -- ‖∫_N^∞ saw_k·c·x^{-s-k}‖ ≤ B·‖c‖·N^{-(σ+k-1)}/(σ+k-1)
      Part I (K=3 instance and THE NUMBER):
        * em_tail3_bound                   -- order-3 tail bound with proven saw-3 sup 1/12
        * em_tail3_number                  -- ‖R₃(1/2+14i, N=200)‖ ≤ 1/1000  (go/no-go, kernel-decided)

    conjecture1_proved = False (NOT a proof of RH; a classical analysis lemma).
-/
import EMZetaTail

#print axioms ZetaReflection.abs_sawBernoulli_two_le
#print axioms ZetaReflection.bernoulliFun_three
#print axioms ZetaReflection.abs_sawBernoulli_three_le
#print axioms ZetaReflection.sawAntideriv_hasDerivAt_Ioo
#print axioms ZetaReflection.em_saw_step
#print axioms ZetaReflection.em_tail_integral_bound
#print axioms ZetaReflection.em_tail3_bound
#print axioms ZetaReflection.em_tail3_number
