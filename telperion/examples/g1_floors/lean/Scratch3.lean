import Mathlib

noncomputable def syn_max_f : ℕ → ℝ := fun n => (n + 1) * (3/5)^n

private lemma syn_max_f_pos (s : ℕ) : 0 < syn_max_f s := by
  simp only [syn_max_f]; positivity

private lemma syn_max_f_ratio (s : ℕ) :
    syn_max_f (s + 1) / syn_max_f s = (3 * ((s:ℝ) + 2)) / (5 * ((s:ℝ) + 1)) := by
  have hp := syn_max_f_pos s
  simp only [syn_max_f]
  rw [div_eq_div_iff (by simp only [syn_max_f] at hp; exact hp.ne') (by positivity)]
  push_cast [pow_succ]; ring

example (s : ℕ) (hs : (0:ℕ) ≤ s) (hlt : s < 1) : 1 ≤ syn_max_f (s + 1) / syn_max_f s := by
  have hr := syn_max_f_ratio s
  -- s < s* = 1 (Nat) => s <= s*-1 = 0, so (s:R) <= 0
  have hub : (s:ℝ) ≤ (0:ℝ) := by
    have : s ≤ 0 := by omega
    exact_mod_cast this
  rw [hr, le_div_iff₀ (by positivity)]
  nlinarith [hub]

example (s : ℕ) (hs : 1 ≤ s) : syn_max_f (s + 1) / syn_max_f s ≤ 1 := by
  have hr := syn_max_f_ratio s
  have hlb : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  rw [hr, div_le_one (by positivity)]
  nlinarith [hlb]
