/-
FLATNESS-FAMILY DOMINATION (R7 interpolation sliver), kernel-checked cores + induction.

Python side: proof/verification/flatness_domination_closed.py (exact, self-verifying).
Statement there: best_template(181+11q) > (23/20) * pi_star(cfg(q)) for ALL q >= 1, with
cfg(q) = (2,1,0,0,(q,5,9)), via the member family D (c0=0, nleaf=0, K=q+16,
loads [6,6] ++ [5]*(K-2)).

This file kernel-checks the three arithmetic obligations and the induction that combines
them, over the ratio sequence r(q) = D(q)/a(q):

  (V) validity_arith : the divmod/window integer facts putting family D inside the
      best_template enumeration space for every q >= 1 (pure omega);
  (B) base_ratio     : r(1) = 215670567600/147104535473 > 23/20 (norm_num);
  (S) step_poly      : the cross-multiplied step inequality, whose difference is EXACTLY
      379085447 q^2 + 1927564431 q + 7857434164 (all-positive coefficients; the quartic
      terms cancel identically -- checked by `nlinarith`/ring normalization here);
  (I) rSeq_gt        : the ratio sequence defined by r(1) and the exact one-step
      recurrence r(q+1) = r(q) * (stepD q / stepA q) satisfies r(q) > 23/20 forever.

Provenance discipline (same as _cell_lean_strings): the identification of stepA/stepD with
the true one-step ratios of pi_star(cfg(q)) and the family-D template value is verified
exactly against the code in pfinite_probe_w2.py (q = 1..119 for a; symbolic product forms
for both); the Lean side takes the recurrences as the definition of the sequences.
conjecture1_proved = False.
-/
import Mathlib

namespace FlatnessDomination

/-! ### (V) validity: family D is in the enumeration space, all q >= 1 -/

theorem validity_arith (q : ℤ) (hq : 1 ≤ q) :
    180 + 11 * q = 11 * (q + 16) + 4 ∧
    (180 + 11 * q) - (q + 16) = 10 * (q + 16) + 4 ∧
    (10 * (q + 16) + 4) % 2 = 0 ∧
    5 * (q + 16) + 2 ≤ 8 * (q + 16) ∧
    5 * (q + 16) + 2 = 5 * (q + 16) + 2 ∧
    2 < q + 16 ∧
    180 + 11 * q ≤ 13 * (q + 16) ∧
    9 * ((q + 16) - 1) ≤ 180 + 11 * q := by
  omega

/-! ### (B) base: r(1) > 23/20 -/

theorem base_ratio : (23 : ℚ) / 20 < 215670567600 / 147104535473 := by
  norm_num

/-! ### (S) the step inequality (cross-multiplied, denominator-free) -/

/-- The a-side one-step ratio numerator/denominator pieces (621/64 cancels in D/a). -/
theorem step_poly (q : ℚ) (hq : 0 ≤ q) :
    (q + 1) * (88185461 * q + 176596081) * ((q + 17) * (117 * q + 1868)) ≤
    (q + 16) * (117 * q + 1985) * ((q + 2) * (88185461 * q + 88410620)) := by
  nlinarith [sq_nonneg q, hq]

/-! ### (I) the induction over the ratio sequence -/

/-- One-step growth ratio of the family-D template value (the 621/64 factor omitted;
it cancels against `stepA` in the ratio recurrence). -/
noncomputable def stepD (q : ℚ) : ℚ := (q + 16) * (117 * q + 1985) / ((q + 17) * (117 * q + 1868))

/-- One-step growth ratio of a(q) = pi_star(cfg(q)) (621/64 likewise omitted). -/
noncomputable def stepA (q : ℚ) : ℚ :=
    (q + 1) * (88185461 * q + 176596081) / ((q + 2) * (88185461 * q + 88410620))

/-- The ratio sequence r; `rSeq n` is r at q = n + 1, so `rSeq 0 = r(1) = D(1)/a(1)`. -/
noncomputable def rSeq : ℕ → ℚ
  | 0 => 215670567600 / 147104535473
  | n + 1 => rSeq n * (stepD (n + 1) / stepA (n + 1))

lemma stepA_pos (q : ℚ) (hq : 0 ≤ q) : 0 < stepA q := by
  unfold stepA
  positivity

lemma stepD_pos (q : ℚ) (hq : 0 ≤ q) : 0 < stepD q := by
  unfold stepD
  positivity

/-- The step never shrinks the ratio: `1 ≤ stepD q / stepA q` for q ≥ 0. -/
lemma one_le_step (q : ℚ) (hq : 0 ≤ q) : 1 ≤ stepD q / stepA q := by
  rw [le_div_iff₀ (stepA_pos q hq), one_mul]
  unfold stepA stepD
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg q, hq]

/-- MAIN: the ratio sequence stays above 23/20 forever. -/
theorem rSeq_gt (n : ℕ) : (23 : ℚ) / 20 < rSeq n := by
  induction n with
  | zero => exact base_ratio
  | succ n ih =>
      have hq : (0 : ℚ) ≤ (n : ℚ) + 1 := by positivity
      have hstep := one_le_step ((n : ℚ) + 1) hq
      have hpos : (0 : ℚ) < rSeq n := lt_trans (by norm_num) ih
      calc (23 : ℚ) / 20 < rSeq n := ih
        _ = rSeq n * 1 := by ring
        _ ≤ rSeq n * (stepD ((n : ℚ) + 1) / stepA ((n : ℚ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hstep (le_of_lt hpos)
        _ = rSeq (n + 1) := by
              simp only [rSeq]

end FlatnessDomination

#print axioms FlatnessDomination.validity_arith
#print axioms FlatnessDomination.base_ratio
#print axioms FlatnessDomination.step_poly
#print axioms FlatnessDomination.rSeq_gt
