/- AxiomGuardRH — CI kernel-axiom guard for the RH zero-free-region formalization.

   This is a TOP-LEVEL module: it is NOT a `lean_lib` in the lakefile and is not
   root-imported anywhere. CI runs it explicitly with

       lake env lean AxiomGuardRH.lean

   AFTER `lake build`, and FAILS the build if any `#print axioms` output below
   mentions `sorryAx` — i.e. if a guarded theorem secretly depends on a `sorry`.

   `#print axioms` is the authoritative, false-positive-free detector: a `grep` for
   the string `sorry` over `.lean` sources cannot tell a real proof gap from
   docstring prose like "no `sorry`" (which bit the R1 review), but the kernel's
   axiom trace can. A clean proof reports exactly
   `[propext, Classical.choice, Quot.sound]`.

   Guarded anchors — the UNCONDITIONAL results whose integrity actually matters:
     * riemannZeta_zero_free_poly     — the elementary unconditional |t|^{-5} region.
     * zeta_fract_repr                — the unconditional strip representation (R1+R2+R3).
     * zeta_strip_bound               — the crude strip growth bound (Phase 2).
     * zeta_repr_R1 / differentiableAt_fractIntegral / isPreconnected_stripDomain
                                      — the three discharged inputs of `zeta_fract_repr_of`.
     * zeta_log_bound / zeta_trunc / zeta_partial_sum_repr
                                      — the sharp near-line growth bound and its Euler–Maclaurin
                                        representation (previously guarded only transitively via the
                                        polylog region; now guarded directly).

   (The dVP core in ZeroFreeRegion is deliberately CONDITIONAL — takes the
   Borel–Carathéodory log-derivative bounds as hypotheses — so it is not guarded here.)
-/
import ZeroFreeElementary
import StripReprAssembled
import StripBound
import ZetaLogBound

#print axioms ZeroFreeBridge.riemannZeta_zero_free_poly
#print axioms ZeroFreeBridge.zeta_fract_repr
#print axioms ZeroFreeBridge.zeta_strip_bound
#print axioms ZeroFreeBridge.zeta_repr_R1
#print axioms ZeroFreeBridge.differentiableAt_fractIntegral
#print axioms ZeroFreeBridge.isPreconnected_stripDomain
#print axioms ZeroFreeBridge.zeta_log_bound
#print axioms ZeroFreeBridge.zeta_trunc
#print axioms ZeroFreeBridge.zeta_partial_sum_repr
