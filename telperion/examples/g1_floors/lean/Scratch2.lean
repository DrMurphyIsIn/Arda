import Mathlib

noncomputable def syn_max_f : ℕ → ℝ := fun n => (n + 1) * (3/5)^n

private lemma syn_max_f_pos (s : ℕ) : 0 < syn_max_f s := by
  simp only [syn_max_f]; positivity

private lemma syn_max_f_ratio (s : ℕ) :
    syn_max_f (s + 1) / syn_max_f s = (3 * ((s:ℝ) + 2)) / (5 * ((s:ℝ) + 1)) := by
  have hp := syn_max_f_pos s
  simp only [syn_max_f]
  rw [div_eq_div_iff (by simp only [syn_max_f] at hp; exact hp.ne') (by positivity)]
  push_cast [pow_succ]
  ring
