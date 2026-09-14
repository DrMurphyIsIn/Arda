/-  AxiomGuardZoo -- CI kernel-axiom guard for the certified DH diffraction (MIRRORMERE QC-B1).

    Like AxiomGuardBragg, this is NOT a lean_lib; CI runs it explicitly with

        lake env lean AxiomGuardZoo.lean

    AFTER `lake build ZooDH`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * ZooDH.cosh_bracket -- local order-6 cosh two-sided bracket (Real.exp_bound
        at +-x; odd terms cancel).  The tiny self-contained exp bracket for the ONE
        small rational the off-line cosh factor needs (no cross-island TaylorKernels).
      * ZooDH.dh_diffraction_online_box_u2 / _u5 -- THE HEADLINE on-line theorems:
        the DH analogue of BraggH100, sum cos(gamma_k * u) over the 52 on-line DH
        ordinates 0 < gamma_k <= 100 at u ~ log 2 and u ~ log 5, each cos enclosed by
        the CosEnclosure double-angle chain + Lipschitz absorption; certified interval.
      * ZooDH.dh_offline_term_box_u2 / _u5 -- the OFF-line pair contribution
        2*cosh(delta*u)*cos(gamma*u), delta = beta-1/2 != 0, with the DISTINCTIVE
        signature cosh(delta*u) > 1 exhibited (an on-line zero has delta=0, cosh=1).

    Expected on all: {propext, Classical.choice, Quot.sound} -- no sorryAx.

    The DH ordinate brackets / (beta,gamma) enclosures are the documented Arb
    inventory inputs (dh_zeros.json winding certificates + Re-D sign bisection),
    same trust class as BraggH100's hLine.  conjecture1_proved = False.  This is a
    finite-T diffraction snapshot of a KNOWN RH counterexample -- it proves nothing
    about RH; it is the falsification-zoo CONTROL with certified off-line zeros.
-/
import CosEnclosure
import ZooDH

/-! ### Local cosh bracket -/
#print axioms ZooDH.cosh_bracket

/-! ### On-line DH diffraction (headline) -/
#print axioms ZooDH.dh_diffraction_online_box_u2
#print axioms ZooDH.dh_diffraction_online_box_u5

/-! ### Off-line pair contribution + off-line signature -/
#print axioms ZooDH.dh_offline_term_box_u2
#print axioms ZooDH.dh_offline_term_box_u5
