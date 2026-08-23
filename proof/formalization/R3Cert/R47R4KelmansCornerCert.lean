/-
  R47 R4-kelmans corner nonnegativity brick.

  SOURCE: proof/verification/psi_close.py, `certify_corners_nonneg` (corner C0).

  CONTEXT.  In the adjacent-Kelmans (Csikvari KC / k=2 GTS) backbone-monotonicity
  step, the change pi(beta') - pi(beta) factors as  P * FS * FQ * Phi, with
  P,FS,FQ > 0 and Phi a bilinear form in the marginals (sigma_Q, sigma_S).  Since
  Phi is affine in each marginal separately, Phi >= 0 on the box reduces to Phi >= 0
  at the four corners C0,C1,C2,C3.

  This brick certifies CORNER C0 = c1.  Writing c1 as a single rational function of
  (da, db, c) over a manifestly positive denominator, and applying the domain shift
  da = 1 + u, db = 2 + v, c = 3 + s (so u, v, s >= 0 over the physical domain
  da >= 1, db >= 2, c >= 3), the NUMERATOR is the polynomial

    N(u,v,s) = 7 s^2 u v + 7 s^2 u + 3 s u^2 v + 3 s u^2 + 3 s u v^2 + 54 s u v
             + 51 s u + 9 u^2 v + 9 u^2 + 9 u v^2 + 108 u v + 99 u,

  which has ALL-NONNEGATIVE coefficients.  Hence N(u,v,s) >= 0 for all real
  u, v, s >= 0, which (over the positive denominator) gives C0 >= 0 across the whole
  physical domain -- i.e. for every N, not merely the finite n <= 9 check.

  This is the exact polynomial produced by sympy (`sp.Poly(num_sh, u, v, s)`) in
  `certify_corners_nonneg`; its 12 coefficients [3,9,3,9,3,9,7,54,108,7,51,99] are
  all positive.  Numerically re-verified in exact `Fraction` before writing.

  Self-contained: `import Mathlib` only, genuine proof (no sorry / no axiom / no
  vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert.Step3

/-- The Kelmans corner-C0 numerator (after the domain shift da=1+u, db=2+v, c=3+s).
    All coefficients are nonnegative and all variables are nonnegative, so the
    polynomial is nonnegative.  This is the all-nonnegative-coefficient Polya
    certificate for corner C0 from `psi_close.certify_corners_nonneg`. -/
theorem kelmans_corner_C0_nonneg
    (u v s : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) :
    0 ≤ 7 * s ^ 2 * u * v + 7 * s ^ 2 * u + 3 * s * u ^ 2 * v + 3 * s * u ^ 2
        + 3 * s * u * v ^ 2 + 54 * s * u * v + 51 * s * u + 9 * u ^ 2 * v
        + 9 * u ^ 2 + 9 * u * v ^ 2 + 108 * u * v + 99 * u := by
  positivity

end R3Cert.Step3