/-
  R47 R4-kelmans corner-C1 nonnegativity brick.

  SOURCE: proof/verification/psi_close.py, `certify_corners_nonneg` (corner C1,
  the corner AFTER C0).

  CONTEXT.  In the adjacent-Kelmans (Csikvari KC / k=2 GTS) backbone-monotonicity
  step, the change pi(beta') - pi(beta) factors as  P * FS * FQ * Phi, with
  P,FS,FQ > 0 and Phi a bilinear form in the marginals (sigma_Q, sigma_S).  Since
  Phi is affine in each marginal separately, Phi >= 0 on the box reduces to Phi >= 0
  at the four corners C0,C1,C2,C3.

  This brick certifies CORNER C1 = c1 + c2 * (da-1) * z1  (the corner that closes
  the c2 * MQ * FS term).  Writing C1 as a single rational function of (da, db, c)
  over a manifestly positive denominator, and applying the domain shift
  da = 1 + u, db = 2 + v, c = 3 + s (so u, v, s >= 0 over the physical domain
  da >= 1, db >= 2, c >= 3), the NUMERATOR is the polynomial

    N(u,v,s) = 28 s^3 u v + 28 s^3 u + 12 s^2 u^2 v + 12 s^2 u^2 + 12 s^2 u v^2
             + 294 s^2 u v + 282 s^2 u + 90 s u^2 v + 90 s u^2 + 54 s u v^2
             + 972 s u v + 918 s u + 162 u^2 v + 162 u^2 + 27 u v^2
             + 972 u v + 945 u,

  which has ALL-NONNEGATIVE coefficients.  Hence N(u,v,s) >= 0 for all real
  u, v, s >= 0, which (over the positive denominator -- also all-nonnegative
  coefficients) gives C1 >= 0 across the whole physical domain -- i.e. for every N,
  not merely the finite n <= 9 check.

  This is the exact polynomial produced by sympy (`sp.Poly(num_sh, u, v, s)`) in
  `certify_corners_nonneg`; its 17 coefficients
  [12,90,162,12,90,162,12,54,27,28,294,972,972,28,282,918,945] are all positive.
  Numerically re-verified against an independent rebuild of the C1 numerator in
  exact sympy before writing.

  Self-contained: `import Mathlib` only, genuine proof (no sorry / no axiom / no
  vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert.Step3

/-- The Kelmans corner-C1 numerator (after the domain shift da=1+u, db=2+v, c=3+s).
    All coefficients are nonnegative and all variables are nonnegative, so the
    polynomial is nonnegative.  This is the all-nonnegative-coefficient Polya
    certificate for corner C1 from `psi_close.certify_corners_nonneg`. -/
theorem kelmans_corner_C1_nonneg
    (u v s : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) :
    0 ≤ 28 * s ^ 3 * u * v + 28 * s ^ 3 * u + 12 * s ^ 2 * u ^ 2 * v
        + 12 * s ^ 2 * u ^ 2 + 12 * s ^ 2 * u * v ^ 2 + 294 * s ^ 2 * u * v
        + 282 * s ^ 2 * u + 90 * s * u ^ 2 * v + 90 * s * u ^ 2
        + 54 * s * u * v ^ 2 + 972 * s * u * v + 918 * s * u + 162 * u ^ 2 * v
        + 162 * u ^ 2 + 27 * u * v ^ 2 + 972 * u * v + 945 * u := by
  positivity

end R3Cert.Step3
