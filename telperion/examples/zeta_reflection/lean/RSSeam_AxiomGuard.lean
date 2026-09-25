/-  RSSeam_AxiomGuard.lean -- kernel-axiom guard of lane SEAM (RSSeam_B3Bound, RSSeam_Bridge): the
    C0-corrected Riemann-Siegel remainder bound lowered from t >= 10000 to t >= 509.

    A `lean_lib` (not a default target).  Run as

        lake build RSSeam_AxiomGuard && lake env lean RSSeam_AxiomGuard.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`
    (nothing is assumed), no `Lean.ofReduceBool` (nothing is compiled), no new axiom.

    Registry anchors (proposed):
      * AND_rs_remainder_c0_seam: `RSSeam.rs_remainder_C0_seam` -- for t >= 509, 0 < p,
        cos(2 pi p) ≠ 0, |phi - thetaMain t| <= 1/t:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (13/5) t^(-3/4).
      * AND_rs_Z_c0_seam: `RSSeam.rs_Z_C0_seam` -- the same for Re Lambda(1/2+it)/M with the
        island's branch-correct theta (phase discharged).

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears
    on the Riemann Hypothesis.
-/
import RSSeam_Bridge

/-! ### RSSeam_B3Bound (7 theorems) -/
#print axioms RSSeam.norm_E1_integrand_near
#print axioms RSSeam.norm_E1_integrand_far
#print axioms RSSeam.norm_rsE1_le
#print axioms RSSeam.E1_const_le
#print axioms RSSeam.rsAlpha_ge_9
#print axioms RSSeam.rs_remainder_C0_alpha_seam
#print axioms RSSeam.rs_remainder_C0_seam

/-! ### RSSeam_Bridge (1 theorem) -/
#print axioms RSSeam.rs_Z_C0_seam
