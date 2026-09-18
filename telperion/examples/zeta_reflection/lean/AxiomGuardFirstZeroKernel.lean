/-  AxiomGuardFirstZeroKernel.lean -- ANDÚRIL final kernel-axiom guard.

    NOT a `lean_lib`; run via the toolchain lean with a hand-built LEAN_PATH.  Expected:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

    `first_zero_kernel` is the argument-free, hypothesis-free theorem that a nontrivial zero of
    `completedRiemannZeta` exists in (14, 15).  conjecture1_proved = False.
-/
import ForgeFirstZeroKernel

#print axioms ForgeFirstZeroKernel.first_zero_kernel
