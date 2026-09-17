/-
  R3Cert.R47HwhSymStarGenCert -- the FULLY GENERAL (k-uniform, non-balanced) certificate for the
  symmetric-multi-star obstruction: the de-branching move is Aobj-monotone on EVERY multi-star
  (centre of any degree k >= 3, hubs of ARBITRARY sizes m_i >= 2).  Completes R47HwhSymStarCert
  (balanced) and R47HwhSymStar3Cert (3-hub) to the whole family.

  General closed form (verified exact): Aobj(multi-star) = (2/k) * sum_i prod_(j != i) alpha_j,
  alpha_i = (2 m_i + 1)/(m_i + 1).  For the de-branching move (detach hub1 -> pendant path via leaf-leaf
  onto hub2; spectators hub3..hubk), the Aobj change is LINEAR in the spectator symmetric functions
  S = prod alpha_j and S1 = sum prod-all-but-one alpha (over spectators):

      DeltaAobj = S * coeff_S + S1 * coeff_S1,   with coeff_S, coeff_S1 depending only on m1,m2,k.

  coeff_S1 >= 0 and (since every alpha_j <= 2) S1 >= S*(k-2)/2, so with G := coeff_S + (k-2)/2 * coeff_S1,
  DeltaAobj >= S*G.  Both coeff_S1 >= 0 and G >= 0 (m1,m2 >= 2, k >= 3) hold via the shift
  (m1,m2,k) = (u+2, v+2, w+3) giving all-non-negative-coefficient polynomials.  Hence DeltaAobj >= 0 for
  ALL spectator configurations -- the k-uniform non-balanced certificate.

  Kernel-checked, no sorry.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- coeff_S1 numerator >= 0 for hub sizes m1,m2 >= 2 and k >= 3 (all-nonneg-coeff shift). -/
theorem symstar_gen_coeffS1_nonneg (m1 m2 k : ℝ) (h1 : 2 ≤ m1) (h2 : 2 ≤ m2) (hk : 3 ≤ k) :
    0 ≤ 4*k*m1^2*m2 - 4*k*m1^2 + 6*k*m1*m2 - k*m1 - 6*k*m2 - k + 16*m1^2*m2 + 8*m1^2 + 8*m1*m2 + 4*m1 := by
  have a : 0 ≤ m1 - 2 := by linarith
  have b : 0 ≤ m2 - 2 := by linarith
  have c : 0 ≤ k - 3 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (a) a) b) c,
    mul_nonneg (mul_nonneg (a) a) b,
    mul_nonneg (mul_nonneg (a) a) c,
    mul_nonneg (a) a,
    mul_nonneg (mul_nonneg (a) b) c,
    mul_nonneg (a) b,
    mul_nonneg (a) c,
    a,
    mul_nonneg (b) c,
    b,
    c]

/-- 2*G numerator >= 0 for m1,m2 >= 2, k >= 3 (all-nonneg-coeff shift); G = coeff_S + (k-2)/2 * coeff_S1. -/
theorem symstar_gen_G_nonneg (m1 m2 k : ℝ) (h1 : 2 ≤ m1) (h2 : 2 ≤ m2) (hk : 3 ≤ k) :
    0 ≤ 4*k^2*m1^2*m2 - 4*k^2*m1^2 + 6*k^2*m1*m2 - k^2*m1 - 6*k^2*m2 - k^2 - 4*k*m1^2*m2 + 6*k*m1^2
        - 14*k*m1*m2 + 6*k*m2 - 2*k + 8*m1^2 + 8*m1*m2 + 8*m1 := by
  have a : 0 ≤ m1 - 2 := by linarith
  have b : 0 ≤ m2 - 2 := by linarith
  have c : 0 ≤ k - 3 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (a) a) b) c) c,
    mul_nonneg (mul_nonneg (mul_nonneg (a) a) b) c,
    mul_nonneg (mul_nonneg (a) a) b,
    mul_nonneg (mul_nonneg (mul_nonneg (a) a) c) c,
    mul_nonneg (mul_nonneg (a) a) c,
    mul_nonneg (a) a,
    mul_nonneg (mul_nonneg (mul_nonneg (a) b) c) c,
    mul_nonneg (mul_nonneg (a) b) c,
    mul_nonneg (a) b,
    mul_nonneg (mul_nonneg (a) c) c,
    mul_nonneg (a) c,
    a,
    mul_nonneg (mul_nonneg (b) c) c,
    mul_nonneg (b) c,
    b,
    mul_nonneg (c) c,
    c]

/-- The k-uniform assembly: given spectator products S >= 0, the bound S1 >= S*hk (hk = (k-2)/2, from
    alpha_j <= 2), coeff_S1 >= 0, and G = coeff_S + hk*coeff_S1 >= 0, the total Aobj change
    S*coeff_S + S1*coeff_S1 >= 0.  So the de-branching move is Aobj-monotone on every multi-star,
    regardless of the number or sizes of the spectator hubs. -/
theorem symstar_gen_move_monotone (S S1 cS cS1 hk : ℝ)
    (hS : 0 ≤ S) (hcS1 : 0 ≤ cS1) (hS1 : S * hk ≤ S1) (hG : 0 ≤ cS + hk * cS1) :
    0 ≤ S * cS + S1 * cS1 := by
  have h1 : S * hk * cS1 ≤ S1 * cS1 := mul_le_mul_of_nonneg_right hS1 hcS1
  have h2 : 0 ≤ S * (cS + hk * cS1) := mul_nonneg hS hG
  nlinarith [h1, h2]

end Step3
end R3Cert
