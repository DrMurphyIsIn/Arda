/-  AxiomGuardRvMBridge -- CI kernel-axiom guard for the E6 RvM bridge island.

    Declared as a `lean_lib` in defaultTargets, so `lake build` compiles this file and thus
    transitively every module it imports. CI then runs

        lake env lean AxiomGuardRvMBridge.lean

    AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * RvMBridge.rvm_unbounded_mean_density -- the MIRRORMERE node statement, verbatim.
      * RvMBridge.eventually_Ncount_ge       -- the T log T lower bound from the RvM main clause.
      * Zeta23.thmA₀ / Zeta23.two_thirds_on_critical_line -- Theorem A (Alpoege--Furman), the
        UPSTREAM input (anthropics/formal-math zeta23/, pinned in lakefile.toml); guarding it here
        re-verifies the dependency's axiom hygiene at our pin.
      * Zeta23.riemannVonMangoldt_zeta / Zeta23.RvM.zeta_local_zero_count -- the upstream
        unconditional Riemann--von Mangoldt package (dyadic main clause + local count).
      * Zeta23.zetaSeam -- the seam facts (finite windows, reflection symmetry) the bridge uses.

    Expected: every line reads `[propext, Classical.choice, Quot.sound]`.
    conjecture1_proved = False. -/
import E6Bridge

#print axioms RvMBridge.rvm_unbounded_mean_density
#print axioms RvMBridge.eventually_Ncount_ge
#print axioms Zeta23.thmA₀
#print axioms Zeta23.two_thirds_on_critical_line
#print axioms Zeta23.riemannVonMangoldt_zeta
#print axioms Zeta23.RvM.zeta_local_zero_count
#print axioms Zeta23.zetaSeam
