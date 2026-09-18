/-  AxiomGuardStirlingK4.lean -- A2 Theorem 2, honest higher-rate Binet ingredients guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardStirlingK4.lean

    Prints the axiom set of the kernel-clean higher-rate Binet lemma in `StirlingK4.lean`.
    Expected: {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      * binetTail_height_norm_le  -- height-aware per-term Binet bound
                                     ‖binetTail w k‖ ≤ (3/2)/((Re w+k)² + (Im w)²)

    conjecture1_proved = False (a per-term analytic bound, NOT a proof of RH).
-/
import StirlingK4

#print axioms ZetaReflection.binetTail_height_norm_le
