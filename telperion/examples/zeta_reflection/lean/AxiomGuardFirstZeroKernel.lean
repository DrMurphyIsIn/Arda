/-  AxiomGuardFirstZeroKernel.lean -- ANDÚRIL final kernel-axiom guard.

    A `lean_lib` (CI: telperion-zeta-reflection.yml builds it, then runs `lake env lean` on it).  Expected:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    `first_zero_kernel` is the argument-free, hypothesis-free theorem that a nontrivial zero of
    `completedRiemannZeta` exists in (14, 15).  conjecture1_proved = False.
-/
import ForgeFirstZeroKernel

#print axioms ForgeFirstZeroKernel.first_zero_kernel
