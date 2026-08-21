import Mathlib

namespace Telperion

/-- If `f : ℕ → ℝ` rises up to `sstar` and falls beyond it, then its maximum
over `n ≥ s0` is at `sstar`. -/
theorem unimodal_peak {f : ℕ → ℝ} {s0 sstar : ℕ}
    (hup : ∀ s, s0 ≤ s → s < sstar → f s ≤ f (s + 1))
    (hdn : ∀ s, sstar ≤ s → f (s + 1) ≤ f s) :
    ∀ n, s0 ≤ n → f n ≤ f sstar := by
  have climb : ∀ a b, s0 ≤ a → a ≤ b → b ≤ sstar → f a ≤ f b := by
    intro a b ha hab hb
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih =>
      have hks : k < sstar := lt_of_lt_of_le (Nat.lt_succ_self k) hb
      exact le_trans (ih (le_of_lt hks)) (hup k (le_trans ha hk) hks)
  have desc : ∀ a b, sstar ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih => exact le_trans (hdn k (le_trans ha hk)) ih
  intro n hn
  rcases (by omega : n ≤ sstar ∨ sstar < n) with h | h
  · exact climb n sstar hn h le_rfl
  · exact desc sstar n le_rfl (le_of_lt h)

/-- Bridge: from a positive sequence whose successor ratio is `≥ 1` below `sstar`
and `≤ 1` at/above it, derive the pointwise climb/descend hypotheses
`unimodal_peak` needs. Lets a caller assemble the full `f n ≤ B` theorem from a
Pólya-certified decreasing ratio plus the two crossing facts. -/
theorem climb_descend_of_ratio
    (f : ℕ → ℝ) (s0 sstar : ℕ) (hs0 : s0 ≤ sstar)
    (hpos : ∀ s, s0 ≤ s → 0 < f s)
    (hrup : ∀ s, s0 ≤ s → s < sstar → 1 ≤ f (s + 1) / f s)
    (hrdn : ∀ s, sstar ≤ s → f (s + 1) / f s ≤ 1) :
    (∀ s, s0 ≤ s → s < sstar → f s ≤ f (s + 1)) ∧
    (∀ s, sstar ≤ s → f (s + 1) ≤ f s) := by
  refine ⟨?_, ?_⟩
  · intro s hs hlt
    have hp : 0 < f s := hpos s hs
    have h := hrup s hs hlt
    rw [le_div_iff₀ hp] at h
    linarith
  · intro s hs
    have hp : 0 < f s := hpos s (le_trans hs0 hs)
    have h := hrdn s hs
    rw [div_le_one hp] at h
    linarith

end Telperion

-- near-star closed form f(n) = Phi^11(N(0,n))
noncomputable def nearstar_phi11_f : ℕ → ℝ := fun n => (64/621)^(2*n+1) * ((4*n+3)/(3*(n+1)))^11 * (3/2)^(11*n)

-- successor-ratio closed form (FACTORED, degree 11): r(x) = (486/529) * (1 + 1/(4x^2+11x+6))^11
noncomputable def nearstar_phi11_f_r : ℝ → ℝ := fun x => (486/529) * (1 + 1/(4*x^2+11*x+6))^11

-- ratio identity: f(s+1)/f(s) = nearstar_phi11_f_r (↑s)
private lemma nearstar_phi11_f_ratio_eq (s : ℕ) : nearstar_phi11_f (s + 1) / nearstar_phi11_f s = nearstar_phi11_f_r (s : ℝ) := by
  simp only [nearstar_phi11_f, nearstar_phi11_f_r]
  push_cast
  field_simp
  ring

-- nearstar_phi11_f_r is decreasing on x >= 0 (structural: 11th power of a decreasing nonneg base)
private lemma nearstar_phi11_f_r_dec (x : ℝ) (hx : 0 ≤ x) : nearstar_phi11_f_r (x + 1) ≤ nearstar_phi11_f_r x := by
  simp only [nearstar_phi11_f_r]
  have hdx : (0 : ℝ) < 4*x^2+11*x+6 := by positivity
  have hdx1 : (0 : ℝ) < 4*(x+1)^2+11*(x+1)+6 := by positivity
  have hden : 4*x^2+11*x+6 ≤ 4*(x+1)^2+11*(x+1)+6 := by nlinarith [hx]
  have hinv : 1/(4*(x+1)^2+11*(x+1)+6) ≤ 1/(4*x^2+11*x+6) := one_div_le_one_div_of_le hdx hden
  have hbase : (1 : ℝ) + 1/(4*(x+1)^2+11*(x+1)+6) ≤ 1 + 1/(4*x^2+11*x+6) := by linarith
  have hnn : (0 : ℝ) ≤ 1 + 1/(4*(x+1)^2+11*(x+1)+6) := by positivity
  have hpow : (1 + 1/(4*(x+1)^2+11*(x+1)+6))^11 ≤ (1 + 1/(4*x^2+11*x+6))^11 := pow_le_pow_left₀ hnn hbase 11
  have hc : (0 : ℝ) ≤ 486/529 := by norm_num
  exact mul_le_mul_of_nonneg_left hpow hc

-- nearstar_phi11_f_r anti-monotone in the ℕ index
private lemma nearstar_phi11_f_r_anti (a b : ℕ) (hab : a ≤ b) : nearstar_phi11_f_r (b : ℝ) ≤ nearstar_phi11_f_r (a : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih =>
    have hstep : nearstar_phi11_f_r ((k : ℝ) + 1) ≤ nearstar_phi11_f_r (k : ℝ) := nearstar_phi11_f_r_dec (k : ℝ) (by positivity)
    have hcast : nearstar_phi11_f_r (((k + 1 : ℕ)) : ℝ) ≤ nearstar_phi11_f_r (k : ℝ) := by
      push_cast; exact hstep
    exact le_trans hcast ih

-- crossing (hi): nearstar_phi11_f_r (↑5) = (980170052528609401200979968 / 996644577901404223353123569) < 1
private lemma nearstar_phi11_f_cross_hi_eval : nearstar_phi11_f_r ((5 : ℕ) : ℝ) = (980170052528609401200979968 / 996644577901404223353123569) := by
  simp only [nearstar_phi11_f_r]
  norm_num

theorem nearstar_phi11 (n : ℕ) (hn : 5 ≤ n) : nearstar_phi11_f n ≤ 1 := by
  have hpos : ∀ s, 5 ≤ s → 0 < nearstar_phi11_f s := by
    intro s hs; simp only [nearstar_phi11_f]; positivity
  -- no climb region (s0 = s* = 5): the hypothesis s < 5 is impossible
  have hrup : ∀ s, 5 ≤ s → s < 5 → 1 ≤ nearstar_phi11_f (s + 1) / nearstar_phi11_f s := by
    intro s hs hlt; omega
  have hrdn : ∀ s, 5 ≤ s → nearstar_phi11_f (s + 1) / nearstar_phi11_f s ≤ 1 := by
    intro s hs
    rw [nearstar_phi11_f_ratio_eq s]
    -- r anti-mono gives r(↑s) ≤ r(↑5) = (980170052528609401200979968 / 996644577901404223353123569) < 1
    have hmono := nearstar_phi11_f_r_anti 5 s hs
    rw [nearstar_phi11_f_cross_hi_eval] at hmono
    norm_num at hmono ⊢
    linarith
  obtain ⟨hclimb, hdesc⟩ := Telperion.climb_descend_of_ratio nearstar_phi11_f 5 5
      (by norm_num) hpos hrup hrdn
  have hmax := Telperion.unimodal_peak hclimb hdesc n hn
  -- peak value: f(5) = 1 (the tie 64*243*23 = 621*576)
  have hpeak : nearstar_phi11_f 5 ≤ 1 := by
    simp only [nearstar_phi11_f]; norm_num
  linarith [hmax, hpeak]
