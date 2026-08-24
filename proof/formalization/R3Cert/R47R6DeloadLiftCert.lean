/-
  R47 R6 hub de-loading affine-in-S lift -- the endpoint certificates cover all balanced
  other-arm arrangements.

  SOURCE: proof/verification/arm_bound.py, `certify_transfer_mixed` ("E is affine in S, so
  it suffices to certify the two activity endpoints").

  CONTEXT.  The hub de-loading transfer surplus `E(k, c0)` depends on the other-arm total
  activity `S = (k-1) s` and is AFFINE in `S`.  `R47R6DeloadTransferCert` (#106) certifies
  `E > 0` at the two endpoints `s = z(1,6) = 3/25` (arms at level 6) and `s = z(1,4) = 3/19`
  (arms at level 4).  Since any balanced arrangement of the other arms in `{4,5,6}` gives an
  `s` (hence `S`) strictly between those endpoints, this brick lifts the two endpoint
  certificates to the WHOLE interval by affineness: an affine function nonnegative at both
  endpoints of an interval is nonnegative throughout.

  HONEST SCOPE.  The affine-interpolation mechanism (reusable).  Combined with the two
  `R47R6DeloadTransferCert` endpoint certificates it gives `E >= 0` for every balanced
  other-arm arrangement -- the de-loading transfer never decreases the objective.  It does
  NOT include the transfer induction (hub -> 0) nor the conjecture.  Self-contained
  (`import Mathlib`); genuine proof (no `sorry`, no `axiom`, no vacuous hypothesis).
  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- **Affine-in-S lift.**  An affine function `A + B·S` nonnegative at both endpoints
    `Slo ≤ Shi` is nonnegative on the whole interval `[Slo, Shi]`.  This lifts the two
    de-loading endpoint certificates to every intermediate other-arm activity. -/
theorem deload_affine_lift (A B Slo Shi S : ℝ)
    (h0 : 0 ≤ A + B * Slo) (h1 : 0 ≤ A + B * Shi)
    (hlo : Slo ≤ S) (hhi : S ≤ Shi) :
    0 ≤ A + B * S := by
  rcases le_total 0 B with hB | hB
  · nlinarith [mul_nonneg hB (sub_nonneg.mpr hlo)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hB) (sub_nonneg.mpr hhi)]

end Step3
end R3Cert
