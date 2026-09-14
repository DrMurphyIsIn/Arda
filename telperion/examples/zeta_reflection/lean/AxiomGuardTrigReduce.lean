/-  AxiomGuardTrigReduce.lean -- ANDÚRIL instrument (A) kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardTrigReduce.lean

    Prints the axiom sets of the trig-reduction instrument (`TrigReduce`, `TrigReduceD`) and the four
    operating-point certificates (`TrigReduceOperating`).  Expected on all:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    Core real-valued brackets + paired double-angle recurrence (TrigReduce):
      * cos_base_interval / sin_base_interval   -- order-4/5 Taylor two-sided brackets, |y| ≤ 1
      * cos_double_interval                     -- cos-from-cos doubling step
      * sin_double_interval                     -- PAIRED sin doubling (four-corner product envelope)
      * cos_encl / sin_encl                     -- terminal point contracts
      * cos_encl_bracket / sin_encl_bracket     -- Lipschitz absorption of the argument-box width
      * add_encl                                -- interval-sum glue

    Computable DIntv driver (TrigReduceD):
      * cosDblD_sound / sinDblD_sound           -- step-map soundness
      * stepD_sound                             -- paired step soundness
      * iterDouble_sound                        -- M-fold climb soundness (by induction)

    OPERATING-POINT CERTIFICATES (TrigReduceOperating) -- the instrument's fitness certificate:
      * cos_14log2   / sin_14log2               -- θ = 14·log 2   ≈ 9.7041  (n = 2),   width ≤ 1e-4
      * cos_14log200 / sin_14log200             -- θ = 14·log 200 ≈ 74.2277 (n = 200), width ≤ 1e-4

    conjecture1_proved = False (NOT a proof of RH; certified interval arithmetic for cos/sin).
-/
import TrigReduce
import TrigReduceD
import TrigReduceOperating

-- Core real-valued lemmas
#print axioms TrigReduce.cos_base_interval
#print axioms TrigReduce.sin_base_interval
#print axioms TrigReduce.cos_double_interval
#print axioms TrigReduce.sin_double_interval
#print axioms TrigReduce.cos_encl
#print axioms TrigReduce.sin_encl
#print axioms TrigReduce.cos_encl_bracket
#print axioms TrigReduce.sin_encl_bracket
#print axioms TrigReduce.add_encl

-- Computable DIntv driver
#print axioms TrigReduceD.cosDblD_sound
#print axioms TrigReduceD.sinDblD_sound
#print axioms TrigReduceD.stepD_sound
#print axioms TrigReduceD.iterDouble_sound

-- Operating-point certificates
#print axioms TrigReduceOperating.cos_14log2
#print axioms TrigReduceOperating.sin_14log2
#print axioms TrigReduceOperating.cos_14log200
#print axioms TrigReduceOperating.sin_14log200
