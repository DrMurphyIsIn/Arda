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
      Part G' (summed order-raising over a window, telescoped boundary terms):
        * em_saw_step_window               -- ∫_M^N saw_k·fk in terms of ∫_M^N saw_{k+1}·fk1
      Part H (N-decaying tail remainder engine):
        * em_tail_integral_bound           -- ‖∫_N^∞ saw_k·c·x^{-s-k}‖ ≤ B·‖c‖·N^{-(σ+k-1)}/(σ+k-1)
      Part I (K=3 instance and THE NUMBER):
        * em_tail3_bound                   -- order-3 tail bound with proven saw-3 sup 1/12
        * em_tail3_number                  -- ‖R₃(1/2+14i, N=200)‖ ≤ 1/1000  (go/no-go, kernel-decided)
      Part J (ℂ order-raising + σ-derivatives for the ζ-identity assembly):
        * hasDerivAt_cpow_neg2             -- d/dx(-s·x^{-s-1}) = s(s+1)·x^{-s-2}
        * hasDerivAt_cpow_neg3             -- d/dx(s(s+1)·x^{-s-2}) = -s(s+1)(s+2)·x^{-s-3}
        * em_saw_step_cpow                 -- ℂ one-step saw-order-raising
        * em_saw_step_window_cpow          -- ℂ summed order-raising over [M,N]
      Part K (order-2/3 tail EM steps with the M→∞ limit, closed form):
        * em_tail2_step                    -- ∫_N^∞ saw₁·(-s x^{-s-1}) = B₂·s·N^{-s-1}/2 - (∫saw₂·…)/2
        * em_tail3_step                    -- ∫_N^∞ saw₂·s(s+1)x^{-s-2} = -(∫saw₃·…)/3  (B₃=0, no bdry)
      Part L (the ASSEMBLED ζ identity + checkBand-consumer enclosure):
        * em_tail_order3_identity          -- combined K=1-tail = B₂·s·N^{-s-1}/2 + (∫saw₃·…)/6
        * em_zeta_strip3                   -- riemannZeta s = 1/(s-1)+1/2 + ∫_1^N saw₁ + B₂ term + R₃
        * em_zeta_strip3_enclosure         -- ‖ζ s − emZetaFinite3 s N‖ ≤ em_tail3_bound/6
        * em_zeta_critical_line3_enclosure -- σ=1/2 band specialization (the A4 gLine box)

    conjecture1_proved = False (NOT a proof of RH; a classical analysis lemma).
-/
import EMZetaTail

#print axioms ZetaReflection.abs_sawBernoulli_two_le
#print axioms ZetaReflection.bernoulliFun_three
#print axioms ZetaReflection.abs_sawBernoulli_three_le
#print axioms ZetaReflection.sawAntideriv_hasDerivAt_Ioo
#print axioms ZetaReflection.em_saw_step
#print axioms ZetaReflection.em_saw_step_window
#print axioms ZetaReflection.em_tail_integral_bound
#print axioms ZetaReflection.em_tail3_bound
#print axioms ZetaReflection.em_tail3_number
#print axioms ZetaReflection.hasDerivAt_cpow_neg2
#print axioms ZetaReflection.hasDerivAt_cpow_neg3
#print axioms ZetaReflection.em_saw_step_cpow
#print axioms ZetaReflection.em_saw_step_window_cpow
#print axioms ZetaReflection.em_tail2_step
#print axioms ZetaReflection.em_tail3_step
#print axioms ZetaReflection.em_tail_order3_identity
#print axioms ZetaReflection.em_zeta_strip3
#print axioms ZetaReflection.em_zeta_strip3_enclosure
#print axioms ZetaReflection.em_zeta_critical_line3_enclosure
