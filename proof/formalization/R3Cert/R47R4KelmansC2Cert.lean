/-
  R47 R4-kelmans corner nonnegativity brick (CORNER C2 -- the mixed/diagonal corner).

  SOURCE: proof/verification/psi_close.py, `certify_corners_nonneg` (corner C2).

  CONTEXT.  In the adjacent-Kelmans (Csikvari KC / k=2 GTS) backbone-monotonicity
  step, the change pi(beta') - pi(beta) factors as  P * FS * FQ * Phi, with
  P,FS,FQ > 0 and Phi a bilinear form in the marginals (sigma_Q, sigma_S).  Since
  Phi is affine in each marginal separately, Phi >= 0 on the box reduces to Phi >= 0
  at the four corners C0, C1, C3, C2.

  This brick certifies CORNER C2 = c1 + c2*Q + c3*S + c4*Q*S (the mixed corner
  where BOTH marginals sit at their upper box edge).  Writing C2 as a single
  rational function of (da, db, c) over a manifestly positive denominator, and
  applying the domain shift da = 1 + u, db = 2 + v, c = 3 + s (so u, v, s >= 0 over
  the physical domain da >= 1, db >= 2, c >= 3), the NUMERATOR is the polynomial

    N(u,v,s) = 48 u^2 v s^3 + 432 u^2 v s^2 + 1080 u^2 v s + 486 u^2 v
             + 48 u^2 s^3 + 432 u^2 s^2 + 1080 u^2 s + 486 u^2
             + 48 u v^2 s^3 + 432 u v^2 s^2 + 1080 u v^2 s + 486 u v^2
             + 112 u v s^4 + 1488 u v s^3 + 7020 u v s^2 + 13176 u v s + 6966 u v
             + 112 u s^4 + 1440 u s^3 + 6588 u s^2 + 12096 u s + 6480 u,

  which has ALL-NONNEGATIVE coefficients (its 22 coefficients
  [48,432,1080,486, 48,432,1080,486, 48,432,1080,486, 112,1488,7020,13176,6966,
  112,1440,6588,12096,6480] are all positive).  Hence N(u,v,s) >= 0 for all real
  u, v, s >= 0, which (over the positive denominator, whose coefficients are also
  all nonnegative) gives C2 >= 0 across the whole physical domain -- i.e. for every
  N, not merely the finite n <= 9 check.

  This is the exact polynomial produced by sympy (`sp.Poly(num_sh, u, v, s)`) in
  `certify_corners_nonneg`; re-verified in exact `Fraction` before writing.

  Self-contained: `import Mathlib` only, genuine proof (no sorry / no axiom / no
  vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert.Step3

/-- The Kelmans corner-C2 numerator (after the domain shift da=1+u, db=2+v, c=3+s).
    All 22 coefficients are nonnegative and all variables are nonnegative, so the
    polynomial is nonnegative.  This is the all-nonnegative-coefficient Polya
    certificate for the mixed corner C2 from `psi_close.certify_corners_nonneg`. -/
theorem kelmans_corner_C2_nonneg
    (u v s : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) :
    0 ≤ 48 * u ^ 2 * v * s ^ 3 + 432 * u ^ 2 * v * s ^ 2 + 1080 * u ^ 2 * v * s
        + 486 * u ^ 2 * v + 48 * u ^ 2 * s ^ 3 + 432 * u ^ 2 * s ^ 2
        + 1080 * u ^ 2 * s + 486 * u ^ 2 + 48 * u * v ^ 2 * s ^ 3
        + 432 * u * v ^ 2 * s ^ 2 + 1080 * u * v ^ 2 * s + 486 * u * v ^ 2
        + 112 * u * v * s ^ 4 + 1488 * u * v * s ^ 3 + 7020 * u * v * s ^ 2
        + 13176 * u * v * s + 6966 * u * v + 112 * u * s ^ 4 + 1440 * u * s ^ 3
        + 6588 * u * s ^ 2 + 12096 * u * s + 6480 * u := by
  positivity

end R3Cert.Step3
