/-
Axiom guard for the quadratic-order-root-table island.

Run AFTER `lake build` (CI does): it prints the axiom dependencies of the QuadraticOrderRoot
consumer lemmas and of the emitted capstones, witnesses and Kummer-Dedekind corollaries.  A clean
run shows nothing beyond Mathlib's three axioms `[propext, Classical.choice, Quot.sound]`; CI
additionally fails the job if `sorryAx` (or `Lean.ofReduceBool`, the native_decide axiom) appears
anywhere in the output, and if fewer than 12 axiom lines are printed (a guard that elaborates to
nothing must not pass).

This file is HAND-WRITTEN (it is not emitted, so it is not part of the generate.py drift check)
and lists the anchors by name: adding an instance without adding its guard line is a visible
omission in the diff.

conjecture1_proved = False -- splitting facts about five explicit quadratic orders; nothing here
concerns zeta.
-/
import QuadraticOrderRootTable

-- The once-proved consumers (no instance data).
#print axioms QuadraticOrderRoot.not_form_eq_prime
#print axioms QuadraticOrderRoot.QuadInt.split_of_isRootMod
#print axioms QuadraticOrderRoot.QuadInt.inert_of_no_root
#print axioms QuadraticOrderRoot.QuadInt.ramified_of_dvd
#print axioms QuadraticOrderRoot.QuadInt.not_absNorm_eq_of_no_root
#print axioms QuadraticOrderRoot.classNumber_ne_one_of_witness
#print axioms QuadraticOrderRoot.classNumber_ne_one_of_isWitness
-- The structural control (REVIEW_E C2): p = c is the only conjunct refusing (d = 8, p = 2, y = 0).
#print axioms QuadraticOrderRoot.not_isWitness_two_two
#print axioms QuadraticOrderRoot.isWitness_two_two_other_conjuncts

-- The emitted face tables (one capstone per order).
#print axioms QuadraticOrderRootTable.d8
#print axioms QuadraticOrderRootTable.d20
#print axioms QuadraticOrderRootTable.d56
#print axioms QuadraticOrderRootTable.d31
#print axioms QuadraticOrderRootTable.d163

-- The Kummer-Dedekind corollaries, one of each face.
#print axioms QuadraticOrderRootTable.d8_ram_2_kd
#print axioms QuadraticOrderRootTable.d8_root_3_kd
#print axioms QuadraticOrderRootTable.d8_noroot_199_kd
#print axioms QuadraticOrderRootTable.d163_noroot_7_kd
#print axioms QuadraticOrderRootTable.d163_ram_163_kd

-- The class-number witnesses and their consequences (d = 8 and d = 163 have none: h = 1).
#print axioms QuadraticOrderRootTable.d20_w_3
#print axioms QuadraticOrderRootTable.d20_classNumber_ne_one
#print axioms QuadraticOrderRootTable.d56_classNumber_ne_one
#print axioms QuadraticOrderRootTable.d31_w_2
#print axioms QuadraticOrderRootTable.d31_classNumber_ne_one
