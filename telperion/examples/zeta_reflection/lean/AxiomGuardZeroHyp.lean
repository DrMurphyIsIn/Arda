/-  AxiomGuardZeroHyp.lean -- ANDÚRIL G2-full zero-hypothesis ζ-term sign box kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardZeroHyp.lean

    (or, when `lake env` is E2BIG-dead, via the toolchain lean with a hand-built LEAN_PATH).

    Prints the axiom sets of the zero-hypothesis ζ-term facts.  Expected on ALL:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      * term_re / term_im       -- the ζ-term atom (Re/Im of n^{-(1/2+it)}), general in (n,t)
      * inv_sqrt2_box           -- the n=2 amplitude box
      * re_term2_t14_box        -- THE HEADLINE: Re(2^{-(1/2+14i)}) ∈ [-0.6798, -0.6796], no hypotheses

    conjecture1_proved = False (a finite hypothesis-free enclosure of one ζ-series term on the
    critical line, NOT a proof of RH, NOT a hypothesis-free zero-existence theorem).
-/
import ZeroHypBand_t14

#print axioms ZeroHypBand_t14.term_re
#print axioms ZeroHypBand_t14.term_im
#print axioms ZeroHypBand_t14.inv_sqrt2_box
#print axioms ZeroHypBand_t14.re_term2_t14_box
