/-  AxiomGuardBragg -- CI kernel-axiom guard for the certified Bragg amplitude.

    Like `AxiomGuardRHInBox.lean`, this is NOT a `lean_lib`; CI runs it explicitly with

        lake env lean AxiomGuardBragg.lean

    AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * CosEnclosure.cos_base / cos_base_interval -- order-4 Taylor two-sided cos
        bracket for |y| <= 1 (Mathlib `Real.cos_bound` backbone).
      * CosEnclosure.cos_step -- point-form double-angle error amplification.
      * CosEnclosure.cos_double_interval -- one bounded-rational interval doubling.
      * CosEnclosure.cos_encl / cos_encl_bracket -- terminal cos contract + Lipschitz
        bracket-width absorption (`Real.abs_cos_sub_cos_le`).
      * CosEnclosure.add_encl -- interval-sum fold glue.
      * BraggH100.bragg_amplitude_h100 -- THE HEADLINE: the first kernel-certified
        truncated Bragg amplitude F_100(u*) = sum cos(gamma_k * u*) over the 29 certified
        zeros up to height 100, enclosed in the certified interval.  The gLine sign
        changes are the documented Arb (`enclose_lambda`) non-kernel inputs, entering
        only through the `henc*` hypotheses -- the SAME trust class as the band `hLine`.

    Expected on all: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    conjecture1_proved = False.  This is a finite-T diffraction snapshot of the certified
    zeros, NOT a proof of the Riemann Hypothesis.
-/
import CosEnclosure
import BraggH100
import BraggSupport
import RHInBoxCore

/-! ### CosEnclosure -- certified cos machinery -/
#print axioms CosEnclosure.cos_base
#print axioms CosEnclosure.cos_base_interval
#print axioms CosEnclosure.cos_step
#print axioms CosEnclosure.cos_double_interval
#print axioms CosEnclosure.cos_encl
#print axioms CosEnclosure.cos_encl_bracket
#print axioms CosEnclosure.add_encl

/-! ### Exhaustion bridge (winding count -> Finset identity -> sum over the actual zero set) -/
#print axioms RHInBoxCore.support_eq_witnesses
#print axioms RHInBoxCore.sum_over_box_zeros_eq
#print axioms BraggSupport.sum_cos_over_zero_support_eq

/-! ### BraggH100 -- the headline certified Bragg amplitudes -/
#print axioms BraggH100.bragg_amplitude_h100
#print axioms BraggH100.bragg_amplitude_h100_complete
