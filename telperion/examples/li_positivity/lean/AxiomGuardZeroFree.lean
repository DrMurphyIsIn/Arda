/-  AxiomGuardZeroFree -- CI kernel-axiom guard for the two elementary zero-free-region artifacts.

    WHY THIS FILE EXISTS (audit 2026-09-18). `ZeroFreePolylog.lean` and `ZeroFreeElementary.lean`
    are the artifacts of the rh registry nodes `RH_zero_free_polylog` and `RH_zero_free_gamma5`.
    Both nodes were at `status = "proved"`, yet:

      * nothing imported either module,
      * neither was in `defaultTargets`,
      * neither was in `AxiomGuardLiPositivity`'s import closure,

    so `lake build` never compiled them and no CI step ever elaborated them. Three independently
    built worktrees confirmed it: `ZeroFreePolylog.olean` and `ZeroFreeElementary.olean` were
    absent from all of them while their neighbours were present. The nodes were granted against
    Lean that no build had checked.

    They cannot simply be added to `AxiomGuardLiPositivity`: `ZeroFreeElementary` re-declares
    `ZeroFreeBridge.zeta_sphere_bound`, which `DlvpZetaDisk` (already in that guard's closure)
    also declares, and Lean refuses the co-import with "environment already contains". The same
    name is declared in three modules on this island (`DlvpZetaDisk`, `DlvpZetaCountStrip`,
    `ZeroFreeElementary`), which is real duplication worth consolidating -- but consolidating it
    is a separate change, and it must not block getting these two artifacts under the kernel.

    So: a SECOND, minimal guard whose closure is exactly `ZeroFreePolylog` -> `ZeroFreeElementary`
    -> `StripBound` plus `ZetaLogBound`. Declared as a `lean_lib` in `defaultTargets`, so a bare
    `lake build` compiles it and therefore both artifacts; CI then runs
    `lake env lean AxiomGuardZeroFree.lean` and requires every printed line to be exactly Lean's
    three standard axioms.

    Guarded anchors:
      * ZeroFreeBridge.riemannZeta_zero_free_poly    -- RH_zero_free_gamma5 (beta <= 1 - c/gamma^5)
      * ZeroFreeBridge.riemannZeta_zero_free_polylog -- RH_zero_free_polylog
        (beta <= 1 - c/(gamma^4 (1 + log 2 gamma)))

    Both are elementary and BOTH ARE WEAKER THAN the 1899 de la Vallee Poussin region that this
    same registry already carries (`RH_dlvp_zero_free_region`). They are honest small results, not
    progress on anything. Expected: every line reads `[propext, Classical.choice, Quot.sound]`.
    conjecture1_proved = False. -/
import ZeroFreePolylog

#print axioms ZeroFreeBridge.riemannZeta_zero_free_poly
#print axioms ZeroFreeBridge.riemannZeta_zero_free_polylog
