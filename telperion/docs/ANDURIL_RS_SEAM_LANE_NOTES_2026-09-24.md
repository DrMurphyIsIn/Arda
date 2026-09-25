# LANE_NOTES_SEAM -- lane SEAM (worktree arda-rs-seam, zeta_reflection island, Lean v4.32.0)

conjecture1_proved = False.  Finite-height zero-verification infrastructure only.

## Task (2026-09-24)
Lower the starting height of the C0 Riemann-Siegel remainder bound (lane RS: t >= 10000) so that the
RS range overlaps the Euler-Maclaurin kernel ladder (1000 on this branch, 8000 elsewhere).
New files only (prefix RSSeam_), lakefile append-only, RS_* files untouched, git read-only.

## Numerics first (untrusted, scratchpad/seam/remainder.py, mpmath dps 30)
Worst |Z - main - C0 term| * t^(3/4) over 400 random samples per window (|cos 2 pi p| >= 0.02):
  [200,300] 0.1203   [500,600] 0.1203   [900,1100] 0.1206   [1900,2100] 0.1198
  [5000,5100] 0.0421 [10000,10100] 0.1213     (worst always at p near 0 or 1; Gabcke 0.127)
So a constant of order 2-3 at t ~ 500 is realistic with a ~20x margin.

## Budget re-run (scratchpad/seam/budget.py, check_consts.py)
RS_B3Bound's a >= 39 was forced only by the near/far split at |v| = a/9 (far term e^{-pi a^2/162}).
Splitting at |v| = a/3 instead (still |w| = sqrt2 |v| <= a/2, so the log-Taylor amplitude bound holds):
  near: e <= |w|(13/25 + 17/4|w|^2)/a,  e <= 27/5 v^2 + 1/600  ->  integrand <= e^{1/600}/(pi a)(13/25 + 17/2 v^2) e^{-7v^2}
        integral <= 0.2408/a  (claimed 49/200)
  far:  integrand <= 5 e^{-pi a^2/18} e^{-pi v^2/2};  with x = pi a^2/18 >= 14, a <= x, e^{-x} <= 8!/x^8:
        <= 302400/x^7 /a <= (1/200)/a   (true value at a = 9: 5e-5/a)
  |rsE1 a p| <= (1/4)/a for a >= 9;  |rsJ| <= 4 unchanged;  8|delta| <= 4/(pi a^2) <= (3/20)/a
  total 2(1/4) + 3/20 = 13/20  ->  a-form (13/20) a^(-3/2);  (2pi)^(3/4) <= 4  ->  (13/5) t^(-3/4).
  a >= 9  <=>  t >= 2 pi 81 = 508.94, stated as t >= 509.
Why not lower: at a ~ 6 the far term e^{-pi a^2/18} a^2 is ~0.5 and the split cannot exceed |v| ~ a/(2 sqrt2);
going below ~500 needs a different far-field estimate (not needed for the seam).

## Delivered (all build green; peak RSS 5.9 GB for the full lake build of the guard, 8678 jobs)
- RSSeam_B3Bound.lean (365 lines; Bridge 84, guard 33): norm_E1_integrand_near / _far (a >= 9), norm_rsE1_le, E1_const_le
  ((1/4)/a), rsAlpha_ge_9, HEADLINES
    RSSeam.rs_remainder_C0_alpha_seam : t >= 509 -> |...| <= (13/20) a^(-3/2)
    RSSeam.rs_remainder_C0_seam       : t >= 509, 0 < rsFrac t, cos(2 pi rsFrac t) ≠ 0,
        |phi - rsThetaMain t| <= 1/t  ->
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) rsPsi p| <= (13/5) t^(-3/4)
- RSSeam_Bridge.lean: RSSeam.rs_Z_C0_seam -- RS_Bridge's rs_Z_C0 verbatim with t >= 509 and 13/5
  (phase discharged hypothesis-free via ThetaConverge + ZeroSignDecomp_t14 + RSTheta; theta_sub_thetaMain
  only needs t > 0).
- RSSeam_AxiomGuard.lean: 8 #print axioms, all [propext, Classical.choice, Quot.sound].
- lakefile.toml: 3 appended [[lean_lib]] blocks (RSSeam_B3Bound, RSSeam_Bridge, RSSeam_AxiomGuard).
- Forbidden-token scan clean (docstring mentions only); no emoji.

## Seam status
RS C0 bound now holds on [509, inf) with remainder (13/5) t^(-3/4): overlaps the EM ladder (1000 here,
8000 via AND.ladder_h8000_kernel).  Remaining for a joint ladder: B4 (in-kernel RS main-sum + Psi
evaluator) and B5 (band sign certificates) exactly as in the RS lane log; the seam itself is closed.
Not done: CI wiring of RSSeam_AxiomGuard into zeta-reflection-compiles (.github is out of scope).
