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
      * ExpLaurentDeficit.expLaurent_recurrence_deficit{,_sq} -- the emitted exp-Laurent
        certificates (kind `exp_laurent_identity`): the clearance PRODUCT equals the
        amplification excess, and its Weil-energy square, both an exact reduction modulo
        the single relation e^d * e^(-d) = 1.
      * Quasicrystal.recurrence_deficit_eq_excess -- MIRRORMERE node
        MM_recurrence_deficit_eq_excess: the Face 4 (Bagchi recurrence) <-> Face 1 (Bragg
        defect) dictionary row at the certified displacement delta = 1/10, plus strict
        positivity of the deficit at every positive displacement.  A dictionary row between
        two finite instruments -- NOT an analytic theorem and NOT a step toward RH.
      * Quasicrystal.recurrence_deficit_sq_eq_abs_defect -- its second-order (Weil-energy)
        companion: the squared deficit is |defectFunctional excess|.
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
import ExpLaurentDeficit
import RecurrenceDeficit

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

/-! ### ExpLaurentDeficit / RecurrenceDeficit -- the Face 4 <-> Face 1 dictionary row -/
#print axioms ExpLaurentDeficit.expLaurent_recurrence_deficit
#print axioms ExpLaurentDeficit.expLaurent_recurrence_deficit_sq
#print axioms Quasicrystal.recurrence_deficit_eq_excess
#print axioms Quasicrystal.recurrence_deficit_sq_eq_abs_defect

/-! ### BraggH100 -- the headline certified Bragg amplitudes -/
#print axioms BraggH100.bragg_amplitude_h100
#print axioms BraggH100.bragg_amplitude_h100_complete
