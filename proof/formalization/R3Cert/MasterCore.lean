import Mathlib

/-!
  # Master-step 1-variable core (capped-joint-induction candidate, 2026-08-19)

  The master step of the candidate reduces — via the cavity identity, the crude per-type
  bound `∏Bcap ≤ W^p`, and `q`-monotonicity — to the single-variable inequality
  `f p := ((4p+3)/(p+1))^11 · (64/621)^p ≤ 3^11` for all `p : ℕ`
  (see `docs/CANDIDATE_CAPPED_JOINT_master_step_proof.md`).

  Proof: `f` is antitone — `f (p+1) ≤ f p` — because the per-step ratio is
  `[(4p²+11p+7)/(4p²+11p+6)]^{-11}·(64/621) ≤ 1`, which clears to
  `64·(b+1)^11 ≤ 621·b^11` for `b = 4p²+11p+6 ≥ 6`, proved from `b+1 ≤ 7b/6` (⟺ `b ≥ 6`)
  and the integer fact `64·7^11 ≤ 621·6^11`.  Hence `f p ≤ f 0 = 3^11`.  Elementary,
  entirely in `ℚ`, no integrality subtlety (the master target's 0.56 margin is what makes
  the crude bound suffice).  conjecture1_proved = False.
-/

namespace R3Cert.MasterCore

/-- The reduced master-step sequence. -/
def f (p : ℕ) : ℚ := ((4 * (p : ℚ) + 3) / ((p : ℚ) + 1)) ^ 11 * (64 / 621) ^ p

/-- Cleared per-step inequality: `64·(4p²+11p+7)^11 ≤ 621·(4p²+11p+6)^11`. -/
lemma cleared (p : ℕ) :
    (64 : ℚ) * (4 * (p : ℚ) ^ 2 + 11 * p + 7) ^ 11
      ≤ 621 * (4 * (p : ℚ) ^ 2 + 11 * p + 6) ^ 11 := by
  have hp : (0 : ℚ) ≤ (p : ℚ) := by positivity
  set b : ℚ := 4 * (p : ℚ) ^ 2 + 11 * (p : ℚ) + 6 with hb
  have hb6 : (6 : ℚ) ≤ b := by rw [hb]; nlinarith [sq_nonneg (p : ℚ), hp]
  have h1 : 4 * (p : ℚ) ^ 2 + 11 * (p : ℚ) + 7 = b + 1 := by rw [hb]; ring
  rw [h1]
  have hb1 : (0 : ℚ) ≤ b + 1 := by linarith
  have hstep : b + 1 ≤ 7 * b / 6 := by linarith
  calc (64 : ℚ) * (b + 1) ^ 11
      ≤ 64 * (7 * b / 6) ^ 11 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb1 hstep 11) (by norm_num)
    _ = (64 * 7 ^ 11) / 6 ^ 11 * b ^ 11 := by ring
    _ ≤ 621 * b ^ 11 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- The per-step ratio inequality (denominators cleared via `cleared`). -/
lemma key (p : ℕ) :
    ((4 * (p : ℚ) + 7) / ((p : ℚ) + 2)) ^ 11 * (64 / 621)
      ≤ ((4 * (p : ℚ) + 3) / ((p : ℚ) + 1)) ^ 11 := by
  rw [div_pow, div_pow, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have lhs_eq : (4 * (p : ℚ) + 7) ^ 11 * 64 * ((p : ℚ) + 1) ^ 11
      = 64 * (4 * (p : ℚ) ^ 2 + 11 * (p : ℚ) + 7) ^ 11 := by
    rw [show 4 * (p : ℚ) ^ 2 + 11 * (p : ℚ) + 7 = (4 * (p : ℚ) + 7) * ((p : ℚ) + 1) from by ring,
      mul_pow]; ring
  have rhs_eq : (4 * (p : ℚ) + 3) ^ 11 * (((p : ℚ) + 2) ^ 11 * 621)
      = 621 * (4 * (p : ℚ) ^ 2 + 11 * (p : ℚ) + 6) ^ 11 := by
    rw [show 4 * (p : ℚ) ^ 2 + 11 * (p : ℚ) + 6 = (4 * (p : ℚ) + 3) * ((p : ℚ) + 2) from by ring,
      mul_pow]; ring
  rw [lhs_eq, rhs_eq]
  exact cleared p

/-- `f` is antitone. -/
lemma f_step (p : ℕ) : f (p + 1) ≤ f p := by
  have hc : (0 : ℚ) ≤ (64 / 621 : ℚ) ^ p := by positivity
  have hfp1 : f (p + 1)
      = ((4 * (p : ℚ) + 7) / ((p : ℚ) + 2)) ^ 11 * (64 / 621) * (64 / 621) ^ p := by
    unfold f; rw [pow_succ]; push_cast; ring
  rw [hfp1]; unfold f
  exact mul_le_mul_of_nonneg_right (key p) hc

/-- **Master-step core.** `((4p+3)/(p+1))^11 · (64/621)^p ≤ 3^11` for all `p`. -/
theorem master_core (p : ℕ) : f p ≤ 3 ^ 11 := by
  induction p with
  | zero => norm_num [f]
  | succ n ih => exact le_trans (f_step n) ih

end R3Cert.MasterCore
