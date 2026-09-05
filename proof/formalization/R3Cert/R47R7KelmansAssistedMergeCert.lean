/-
  R47 / R7 -- KELMANS ASSISTED-MERGE monotonicity, machine-checked as an all-nonnegative
  Positivstellensatz certificate.  Companion to `R47R7KelmansTwoHubCert`: together they eliminate
  two-hub STUCKNESS on the merge family (the obstruction `Hdom` must clear).

  CONTEXT (proof/verification/kelmans_vertex_budget.py, `certify_assisted_merge_theorem`).  The
  ordered hub-merge gets STUCK on a two-hub configuration whose donor hub B is DE-LOADED (load 0):
  the plain hubward merge of a de-loaded donor strictly DECREASES `pi = per(L)/∏deg`, and the plain
  "borrow one cherry" move alone tends to `~0.9913 < 1` for giant hubs.  The ASSISTED MERGE is the
  single FUSED rule that dissolves this: borrow one cherry from a donor arm (arm `5 → 4`, donor load
  `0 → 1`), THEN hubward-merge the now-loaded donor.  This fused move STRICTLY INCREASES `pi` on the
  whole two-hub family, for all `pA ≥ pB ≥ 1` and receiver load `cA ∈ {0,…,5}`.

  THE CERTIFICATE.  With `pB = 1 + s`, `pA = pB + r` (`r, s ≥ 0` encodes `pA ≥ pB ≥ 1`), the gain
  `pi(after) − pi(before)`, cleared to a single fraction over a positive denominator, has an
  integer-cleared numerator that is a polynomial in `r, s` with ALL-NONNEGATIVE coefficients and a
  STRICTLY POSITIVE constant term -- hence strictly positive on the nonnegative orthant.  That is a
  Positivstellensatz witness for `pi(after) > pi(before)`: the assisted merge is uniformly
  `pi`-increasing.  With the loaded/de-loaded dichotomy (kelmans_mixed_load.py) this gives a COMPLETE
  local merge table -- hubward loaded donor → direct merge; hubward de-loaded donor → assisted merge;
  anti-hubward → reverse roles -- so K/H-STUCK CONFIGURATIONS CEASE TO EXIST on the two-hub family.

  Emitted verbatim from the sympy certificate (exact rationals, per-cell lcm-cleared); each
  `nlinarith` discharge needs only the monomial nonnegativities `r, s, rs, r², s², s³, rs², r²s ≥ 0`.

  HONEST SCOPE.  Two-hub family only (the base case).  The m-hub (m ≥ 3) elimination is the
  ENVIRONMENT version of these local rules and remains open.  Does NOT prove `Hdom` or Conjecture 1.
  Self-contained (`import Mathlib`), imported by nothing (self-building leaf via the lakefile glob),
  collision-safe with the `bg/lean-tree-to-hub` lane.  `conjecture1_proved = False`.
-/
import Mathlib

namespace R3Cert.Step3

/-- **Assisted-merge gain, receiver load `cA = 0`.**  The integer-cleared numerator of
    `pi(after) − pi(before)` (over a positive denominator) at `cA = 0`, in `r = pA−pB`, `s = pB−1`.
    All coefficients nonnegative, constant `> 0`: the assisted merge strictly increases `pi` for
    every `pA ≥ pB ≥ 1`. -/
theorem assisted_merge_gain_pos_c0 (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 4212*s*s*s + 6318*r*s*s + 2106*r*r*s + 92178*s*s + 92178*r*s + 14742*r*r
      + 151848*s + 75924*r + 41310 := by
  nlinarith [hr, hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs,
    mul_nonneg hs (mul_nonneg hs hs), mul_nonneg hr (mul_nonneg hs hs),
    mul_nonneg (mul_nonneg hr hr) hs]

/-- Assisted-merge gain, receiver load `cA = 1`. -/
theorem assisted_merge_gain_pos_c1 (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 12636*s*s*s + 18954*r*s*s + 6318*r*r*s + 247482*s*s + 290304*r*s + 44226*r*r
      + 607986*s + 324162*r + 327132 := by
  nlinarith [hr, hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs,
    mul_nonneg hs (mul_nonneg hs hs), mul_nonneg hr (mul_nonneg hs hs),
    mul_nonneg (mul_nonneg hr hr) hs]

/-- Assisted-merge gain, receiver load `cA = 2`. -/
theorem assisted_merge_gain_pos_c2 (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 37908*s*s*s + 56862*r*s*s + 18954*r*r*s + 655290*s*s + 912222*r*s + 132678*r*r
      + 2325996*s + 1261656*r + 1903986 := by
  nlinarith [hr, hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs,
    mul_nonneg hs (mul_nonneg hs hs), mul_nonneg hr (mul_nonneg hs hs),
    mul_nonneg (mul_nonneg hr hr) hs]

/-- Assisted-merge gain, receiver load `cA = 3`. -/
theorem assisted_merge_gain_pos_c3 (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 113724*s*s*s + 170586*r*s*s + 56862*r*r*s + 1704402*s*s + 2860596*r*s + 398034*r*r
      + 8618238*s + 4652478*r + 9418680 := by
  nlinarith [hr, hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs,
    mul_nonneg hs (mul_nonneg hs hs), mul_nonneg hr (mul_nonneg hs hs),
    mul_nonneg (mul_nonneg hr hr) hs]

/-- Assisted-merge gain, receiver load `cA = 4`. -/
theorem assisted_merge_gain_pos_c4 (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 341172*s*s*s + 511758*r*s*s + 170586*r*r*s + 4328802*s*s + 8953578*r*s + 1194102*r*r
      + 31177872*s + 16559964*r + 42193062 := by
  nlinarith [hr, hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs,
    mul_nonneg hs (mul_nonneg hs hs), mul_nonneg hr (mul_nonneg hs hs),
    mul_nonneg (mul_nonneg hr hr) hs]

/-- Assisted-merge gain, receiver load `cA = 5`. -/
theorem assisted_merge_gain_pos_c5 (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 1023516*s*s*s + 1535274*r*s*s + 511758*r*r*s + 10633194*s*s + 27976104*r*s + 3582306*r*r
      + 110710314*s + 57487482*r + 176840820 := by
  nlinarith [hr, hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs,
    mul_nonneg hs (mul_nonneg hs hs), mul_nonneg hr (mul_nonneg hs hs),
    mul_nonneg (mul_nonneg hr hr) hs]

end R3Cert.Step3
