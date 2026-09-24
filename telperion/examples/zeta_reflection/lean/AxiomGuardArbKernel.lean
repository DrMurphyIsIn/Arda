/-  AxiomGuardArbKernel.lean -- kernel-axiom guard of the hypothesis-free G2 pilot.

    A `lean_lib` (not a default target).  Run as

        lake build AxiomGuardArbKernel && lake env lean AxiomGuardArbKernel.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`
    (nothing is assumed), no `Lean.ofReduceBool` (the sign chains are kernel `decide`, never
    `native_decide`), no new axiom.

    `ReflectedBand_t14_Kernel.pilot_kernel` has the verbatim conclusion of
    `ReflectedBand_t14.pilot` and NO hypotheses: the three Arb enclosure binders hmem0/hmem1/hmem2
    are replaced by proved memberships of `gLine` at t = 14, 15, 22 in wide, sign-definite dyadic
    boxes.  The anchors below are that theorem, its band datum's kernel-decided sign chain, the
    three memberships, and the new ingredients they rest on (Gamma_R magnitude envelope, zeta box
    at t = 22, theta phase box at t = 22).

    conjecture1_proved = False (two verified low zeros, not a proof of RH).
-/
import ReflectedBand_t14_Kernel

/-! ### The hypothesis-free pilot and its three proved memberships -/
#print axioms ReflectedBand_t14_Kernel.pilot_kernel
#print axioms ReflectedBand_t14_Kernel.okK
#print axioms KernelBandEnclosures.gLine14_encl
#print axioms KernelBandEnclosures.gLine15_encl
#print axioms KernelBandEnclosures.gLine22_encl

/-! ### Same conclusion as the Arb-conditional pilot (type-level check)

    For every value of the three original Arb binders, `ReflectedBand_t14.pilot h0 h1 h2` and the
    hypothesis-free `pilot_kernel` are equal proofs (proof irrelevance).  The equation only
    type-checks because the two propositions are the same. -/
example : ∀ h0 h1 h2, ReflectedBand_t14.pilot h0 h1 h2 = ReflectedBand_t14_Kernel.pilot_kernel :=
  fun _ _ _ => rfl

/-! ### New ingredients -/
#print axioms KernelGammaEnvelope.norm_Gamma_le_Gamma_re
#print axioms KernelGammaEnvelope.norm_Gamma_quarter_lower
#print axioms KernelGammaEnvelope.norm_Gamma_quarter_upper
#print axioms KernelGammaEnvelope.gLine_decomp_explicit
#print axioms KernelGammaEnvelope.gammaRMag_bounds
#print axioms ForgeZeta22.zeta_tail_t22
#print axioms ForgeZeta22.zt22_zeta_re
#print axioms ForgeZeta22.zt22_zeta_im
#print axioms ForgePhi22.sumbox
#print axioms ForgePhi22.phibox
#print axioms ForgePhi22.cossin22
