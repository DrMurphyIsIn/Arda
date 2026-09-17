/-
  R3Cert.R47HwhSymStar3Cert -- the NON-BALANCED extension of the symmetric-multi-star certificate to the
  full 3-hub family (arbitrary hub sizes m1,m2,m3 >= 2).  Extends `R47HwhSymStarCert` (balanced ST(k,m))
  to cover the non-balanced symmetric residual variants (`[4,3,3]`, `[5,4,4]`, `[5,3,2]`, ...).

  For a centre of degree 3 with hubs of sizes m1,m2,m3 (alpha_i=(2m_i+1)/(m_i+1)), the de-branching move
  (detach hub1 -> pendant path via leaf-leaf onto hub2, spectator hub3) has (closed form verified exactly
  vs the cavity engine) `Aobj(MS_move) - Aobj(MS) = N(m1,m2,m3) / (12 m1 (m1+1)(m2+1)(m3+1))`, with

      N(m1,m2,m3) = 24 m1^2 m2 m3 + 26 m1^2 m2 - 10 m1^2 m3 - 7 m1^2 + 20 m1 m2 m3 + 23 m1 m2 - m1 m3
                    - 36 m2 m3 - 27 m2 - 15 m3 - 9.

  The denominator is positive, so monotonicity <=> N >= 0.  Under the shift m_i = t_i + 2 (t_i >= 0, i.e.
  m_i >= 2), `N` has ALL NON-NEGATIVE coefficients (constant term 495), so `N >= 0` -- an explicit
  Positivstellensatz certificate.  Hence the de-branching move is `Aobj`-monotone on EVERY 3-hub
  multi-star with hubs of size >= 2 (balanced and non-balanced alike).

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- **The non-balanced 3-hub certificate**: `N(m1,m2,m3) >= 0` for hub sizes `m_i >= 2`, the
    cleared-denominator form of `Aobj(MS_move) - Aobj(MS) >= 0` for the general 3-hub multi-star.
    Proven from the all-non-negative-coefficient shifted form (`m_i = (m_i-2)+2`). -/
theorem symstar3_move_certificate (m1 m2 m3 : ℝ) (h1 : 2 ≤ m1) (h2 : 2 ≤ m2) (h3 : 2 ≤ m3) :
    0 ≤ 24*m1^2*m2*m3 + 26*m1^2*m2 - 10*m1^2*m3 - 7*m1^2 + 20*m1*m2*m3 + 23*m1*m2 - m1*m3
        - 36*m2*m3 - 27*m2 - 15*m3 - 9 := by
  have a : 0 ≤ m1 - 2 := by linarith
  have b : 0 ≤ m2 - 2 := by linarith
  have c : 0 ≤ m3 - 2 := by linarith
  nlinarith [a, b, c, mul_nonneg a b, mul_nonneg a c, mul_nonneg b c, mul_nonneg a a,
    mul_nonneg (mul_nonneg a a) b, mul_nonneg (mul_nonneg a a) c, mul_nonneg (mul_nonneg a b) c,
    mul_nonneg (mul_nonneg (mul_nonneg a a) b) c]

end Step3
end R3Cert
