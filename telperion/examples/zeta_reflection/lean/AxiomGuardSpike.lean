/-  AxiomGuardSpike.lean -- A0 spike kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardSpike.lean

    Prints the axiom sets of the spike anchors.  Expected on all:
    {propext, Classical.choice, Quot.sound} -- no sorryAx.

      * Spike.toy_ok           -- the DIntv `rfl` benchmark theorem (kernel reflection).
      * DIntvProd.DIntv.add_sound / mul_sound -- the mem-soundness proofs (A0 remit).

    conjecture1_proved = False (NOT a proof of RH).
-/
import Spike.Toy
import DIntvDef

#print axioms Spike.toy_ok
#print axioms DIntvProd.DIntv.add_sound
#print axioms DIntvProd.DIntv.mul_sound
