/-  AxiomGuardFullReflection.lean -- ANDÚRIL A4 STAGE 2 kernel-axiom guard.

    NOT a `lean_lib`; run explicitly with

        lake env lean AxiomGuardFullReflection.lean

    Prints the axiom sets of the Stage-2 finite-part + kernel-verified-envelope band in
    `FullyReflectedBand_t14.lean`.  Expected on all: {propext, Classical.choice, Quot.sound} --
    no sorryAx, no ofReduceBool, no native_decide.  The `ok` theorem is a KERNEL `decide` (the
    envelope widening `F ± W` is computed in the kernel, then sign + alternation decided).

      * checkBandFull_eq_checkLine -- Stage-2 checker = G2 checker on kernel-widened boxes
      * checkBandFull_correct      -- Stage-2 band soundness (residual: finite-part enclosure only)
      * ok                         -- KERNEL-DECIDED sign chain with in-kernel widening (t=14 band)
      * band                       -- the Stage-2 reflected band (2 on-line zeros in [14,22])

    The residual hypotheses of `band` (`hmem0/1/2`) are the finite-part-within-envelope facts — the
    mod-2π trig reduction + Γℝ VALUE enclosure that are NOT YET in the corpus (see file-header budget).

    conjecture1_proved = False.
-/
import FullyReflectedBand_t14

#print axioms FullyReflectedBand_t14.checkBandFull_eq_checkLine
#print axioms FullyReflectedBand_t14.checkBandFull_correct
#print axioms FullyReflectedBand_t14.ok
#print axioms FullyReflectedBand_t14.band
