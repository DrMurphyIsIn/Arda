import Mathlib

noncomputable def syn_max_f : ℕ → ℝ := fun n => (n + 1) * (3/5)^n

-- key: f s > 0
private lemma syn_max_f_pos (s : ℕ) : 0 < syn_max_f s := by
  simp only [syn_max_f]
  positivity

-- key ratio identity: f(s+1)/f(s) = (3/5)*(s+2)/(s+1)
private lemma syn_max_f_ratio (s : ℕ) :
    syn_max_f (s + 1) / syn_max_f s = (3 * (s + 2)) / (5 * (s + 1)) := by
  simp only [syn_max_f]
  have hb : (3/5 : ℝ)^(s+1) = (3/5)^s * (3/5) := by rw [pow_succ]
  have hp : (0:ℝ) < (3/5)^s := by positivity
  have hs1 : ((s:ℝ) + 1) > 0 := by positivity
  rw [hb]
  push_cast
  field_simp
  ring

private lemma syn_max_f_peak : syn_max_f 1 ≤ 6 / 5 := by
  simp only [syn_max_f]; norm_num

theorem unimodal_max_of_climb_descend
    (f : ℕ → ℝ) (s0 sstar : ℕ) (_hs : s0 ≤ sstar)
    (hclimb : ∀ s, s0 ≤ s → s < sstar → f s ≤ f (s + 1))
    (hdesc  : ∀ s, sstar ≤ s → f (s + 1) ≤ f s) :
    ∀ n, s0 ≤ n → f n ≤ f sstar := by
  have climb : ∀ a b, s0 ≤ a → a ≤ b → b ≤ sstar → f a ≤ f b := by
    intro a b ha hab hb
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih =>
      have hks : k < sstar := lt_of_lt_of_le (Nat.lt_succ_self k) hb
      have hbk : k ≤ sstar := le_of_lt hks
      exact le_trans (ih hbk) (hclimb k (le_trans ha hk) hks)
  have desc : ∀ a b, sstar ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih =>
      exact le_trans (hdesc k (le_trans ha hk)) ih
  intro n hn
  rcases (by omega : n ≤ sstar ∨ sstar < n) with h | h
  · exact climb n sstar hn h le_rfl
  · exact desc sstar n le_rfl (le_of_lt h)

theorem syn_max (n : ℕ) (hn : 0 ≤ n) : syn_max_f n ≤ 6 / 5 := by
  have hclimb : ∀ s, (0:ℕ) ≤ s → s < 1 → syn_max_f s ≤ syn_max_f (s + 1) := by
    intro s hs hlt
    have hp := syn_max_f_pos s
    have hr := syn_max_f_ratio s
    have heq : syn_max_f (s + 1) = (3 * ((s:ℝ) + 2)) / (5 * ((s:ℝ) + 1)) * syn_max_f s := by
      rw [eq_comm, ← hr, div_mul_cancel₀]; exact ne_of_gt hp
    have hsr : ((s:ℝ)) = 0 := by
      have : s = 0 := by omega
      exact_mod_cast this
    rw [heq]
    rw [le_mul_iff_one_le_left hp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsr]
  have hdesc : ∀ s, (1:ℕ) ≤ s → syn_max_f (s + 1) ≤ syn_max_f s := by
    intro s hs
    have hp := syn_max_f_pos s
    have hr := syn_max_f_ratio s
    have heq : syn_max_f (s + 1) = (3 * ((s:ℝ) + 2)) / (5 * ((s:ℝ) + 1)) * syn_max_f s := by
      rw [eq_comm, ← hr, div_mul_cancel₀]; exact ne_of_gt hp
    have hsr : ((s:ℝ)) ≥ 1 := by exact_mod_cast hs
    rw [heq]
    rw [mul_le_iff_le_one_left hp]
    rw [div_le_one (by positivity)]
    nlinarith [hsr]
  have hmax := unimodal_max_of_climb_descend syn_max_f 0 1 (by norm_num) hclimb hdesc n hn
  have hpeak := syn_max_f_peak
  linarith [hmax, hpeak]

#print axioms syn_max
