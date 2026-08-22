import Mathlib

/-!
  # R7 collapse-tail monotonicity (G7, first brick) — 2026-08-22

  The G1 "m ≥ 4 collapse lemma" reduces each context-free ledger floor's minimisation over the
  child cavity `y ∈ (0, 1/2]` to a single point, using that the per-node slack is monotone
  INCREASING on the `y > T0` region for `m ≥ 4` (there the cav-hinge is off, so `slack` depends on
  `y` only through the log term and the `+(11/50)·m·(y−T0)` term). The `y`-dependent part of the
  slack is

      g(y) = (11/50)·m·y − log(1 + (c0 + m·y)/(k+1)),   k = a+nl+m ≥ m,  c0 = a/3+nl ≥ 0

  and the additive constants `p·L − a·log(3/2) − (11/50)·m·T0` do not affect monotonicity. This
  file proves `g` is non-decreasing on `y ≥ 0` for `m ≥ 4`, `k ≥ m` — the derivative-sign fact the
  collapse lemma rests on, WITHOUT derivatives: via `log(1+x) ≤ x` and `1/(k+1) ≤ 1/5 < 11/50`.

  This is one brick of G7 (the Lean-isation of the R7 assembly). `conjecture1_proved = False`.
-/

namespace R3Cert.R7CollapseMono

/-- The `y`-dependent part of the collapse-tail slack (`m` equal children at cavity `y`,
    `k = a+nl+m` total children, offset `c0 = a/3+nl`). -/
noncomputable def g (m k : ℕ) (c0 y : ℝ) : ℝ :=
  (11 / 50 : ℝ) * m * y - Real.log (1 + (c0 + m * y) / (k + 1))

set_option maxHeartbeats 1000000 in
/-- **Collapse-tail monotonicity.** For `m ≥ 4`, `k ≥ m`, `c0 ≥ 0`, the slack's `y`-part `g` is
    non-decreasing on `y ≥ 0`. Proof: `log(1+x) ≤ x` bounds the log increment by
    `m(y₂−y₁)/((k+1)+c0+m·y₁)`, and `1/(k+1) ≤ 1/5 < 11/50` (from `k ≥ 4`) dominates it. -/
theorem g_mono (m k : ℕ) (hm : 4 ≤ m) (hk : m ≤ k) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (y1 y2 : ℝ) (hy1 : 0 ≤ y1) (h12 : y1 ≤ y2) : g m k c0 y1 ≤ g m k c0 y2 := by
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hy2 : (0 : ℝ) ≤ y2 := le_trans hy1 h12
  unfold g
  set S1 : ℝ := c0 + (m : ℝ) * y1 with hS1
  set S2 : ℝ := c0 + (m : ℝ) * y2 with hS2
  have hS10 : (0 : ℝ) ≤ S1 := by rw [hS1]; have := mul_nonneg hm0 hy1; linarith
  have hS20 : (0 : ℝ) ≤ S2 := by rw [hS2]; have := mul_nonneg hm0 hy2; linarith
  have hd1 : (0 : ℝ) < 1 + S1 / ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ S1 / ((k : ℝ) + 1) := div_nonneg hS10 hkp.le; linarith
  have hd2 : (0 : ℝ) < 1 + S2 / ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ S2 / ((k : ℝ) + 1) := div_nonneg hS20 hkp.le; linarith
  -- log increment bounded via `log x ≤ x - 1`
  have hw : (0 : ℝ) < (1 + S2 / ((k : ℝ) + 1)) / (1 + S1 / ((k : ℝ) + 1)) := div_pos hd2 hd1
  have hlogdiv : Real.log ((1 + S2 / ((k : ℝ) + 1)) / (1 + S1 / ((k : ℝ) + 1)))
      = Real.log (1 + S2 / ((k : ℝ) + 1)) - Real.log (1 + S1 / ((k : ℝ) + 1)) :=
    Real.log_div hd2.ne' hd1.ne'
  have hratio : (1 + S2 / ((k : ℝ) + 1)) / (1 + S1 / ((k : ℝ) + 1)) - 1
      = (m : ℝ) * (y2 - y1) / (((k : ℝ) + 1) + S1) := by
    rw [hS1, hS2]; field_simp; ring
  have hlog : Real.log (1 + S2 / ((k : ℝ) + 1)) - Real.log (1 + S1 / ((k : ℝ) + 1))
      ≤ (m : ℝ) * (y2 - y1) / (((k : ℝ) + 1) + S1) := by
    have h2 := Real.log_le_sub_one_of_pos hw
    rw [hlogdiv, hratio] at h2
    exact h2
  -- dominating bound: m(y₂−y₁)/((k+1)+S1) ≤ (11/50)·m·(y₂−y₁)
  have hnn : (0 : ℝ) ≤ (m : ℝ) * (y2 - y1) := mul_nonneg hm0 (by linarith)
  have hden5 : (5 : ℝ) ≤ ((k : ℝ) + 1) + S1 := by
    have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hm hk
    linarith
  have hdenpos : (0 : ℝ) < ((k : ℝ) + 1) + S1 := by linarith
  have hbound : (m : ℝ) * (y2 - y1) / (((k : ℝ) + 1) + S1) ≤ (11 / 50 : ℝ) * (m : ℝ) * (y2 - y1) := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hnn, hden5, mul_nonneg hnn (by linarith : (0 : ℝ) ≤ ((k : ℝ) + 1) + S1 - 5)]
  -- assemble: log₂ − log₁ ≤ (11/50)·m·(y₂−y₁), then rearrange
  have hkey : Real.log (1 + S2 / ((k : ℝ) + 1)) - Real.log (1 + S1 / ((k : ℝ) + 1))
      ≤ (11 / 50 : ℝ) * (m : ℝ) * (y2 - y1) := le_trans hlog hbound
  have hexp : (11 / 50 : ℝ) * (m : ℝ) * (y2 - y1)
      = (11 / 50 : ℝ) * (m : ℝ) * y2 - (11 / 50 : ℝ) * (m : ℝ) * y1 := by ring
  linarith [hkey, hexp]

/-! ### G7 assembly brick: the collapse slack attains its minimum at the knee `t`.

  The `m ≥ 4` collapse reduces the floor's minimisation over `y ∈ (0, 1/2]` to the single point
  `y = T0`, because the slack is DECREASING on `(0, T0]` and INCREASING on `[T0, ∞)`. This wires
  `g_mono` (the increasing branch) together with the elementary `−log` decreasing branch into a
  single min-at-the-knee statement. The additive class-constant `p·L − a·log(3/2)` is dropped (it
  does not affect the argmin), and the cav-hinge `(cav − t)_+` is shown to vanish (`cav ≤ 1/5 ≤ t`
  for `m ≥ 4`). -/

/-- Cavity of the collapse node at child-cavity `y`: `1/((k+1) + c0 + m·y)`. `cav_le` shows it
    stays `≤ 1/5 ≤ t` for `m ≥ 4`, so the cav-hinge `(cav−t)_+` vanishes and the slack takes the
    `slk` form below. -/
noncomputable def cav (m k : ℕ) (c0 y : ℝ) : ℝ := 1 / (((k : ℝ) + 1) + (c0 + (m : ℝ) * y))

/-- For `m ≥ 4`, `k ≥ m`, the cavity stays `≤ 1/5 ≤ t` — the cav-hinge never activates, which is why
    `slk` below drops the `(cav−t)_+` term. -/
theorem cav_le (m k : ℕ) (hm : 4 ≤ m) (hk : m ≤ k) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (t : ℝ) (ht : (1 : ℝ) / 5 ≤ t) (y : ℝ) (hy : 0 ≤ y) : cav m k c0 y ≤ t := by
  unfold cav
  have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hm hk
  have hmy : (0 : ℝ) ≤ (m : ℝ) * y := by positivity
  have hden : (5 : ℝ) ≤ ((k : ℝ) + 1) + (c0 + (m : ℝ) * y) := by linarith
  have h5 : (1 : ℝ) / (((k : ℝ) + 1) + (c0 + (m : ℝ) * y)) ≤ 1 / 5 :=
    one_div_le_one_div_of_le (by norm_num) hden
  linarith

/-- The collapse slack, with the (vanishing, by `cav_le`) cav-hinge already dropped and the additive
    class-constant `p·L − a·log(3/2)` removed (neither affects the argmin over `y`):
    `slk y = −log(1+u) + (11/50)·m·(y−t)_+`, `u = (c0+m·y)/(k+1)`. -/
noncomputable def slk (m k : ℕ) (c0 t y : ℝ) : ℝ :=
  - Real.log (1 + (c0 + (m : ℝ) * y) / ((k : ℝ) + 1)) + (11 / 50 : ℝ) * (m : ℝ) * max 0 (y - t)

set_option maxHeartbeats 1000000 in
/-- **Collapse-tail min at the knee.** For `m ≥ 4`, `k ≥ m`, `c0 ≥ 0`, `1/5 ≤ t`, the collapse slack
    over `y ≥ 0` attains its minimum at `y = t`: `slk t ≤ slk y`. Decreasing on `(0,t]` (`u`
    increasing ⟹ `−log` decreasing) and increasing on `[t,∞)` (`g_mono`). -/
theorem slk_min_at_knee (m k : ℕ) (hm : 4 ≤ m) (hk : m ≤ k) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (t : ℝ) (ht : (1 : ℝ) / 5 ≤ t) (y : ℝ) (hy : 0 ≤ y) :
    slk m k c0 t t ≤ slk m k c0 t y := by
  have htnn : (0 : ℝ) ≤ t := le_trans (by norm_num) ht
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hslkt : slk m k c0 t t = - Real.log (1 + (c0 + (m : ℝ) * t) / ((k : ℝ) + 1)) := by
    unfold slk; rw [sub_self, max_self, mul_zero, add_zero]
  rw [hslkt]; unfold slk
  rcases le_total y t with hyt | hty
  · -- decreasing branch: `y ≤ t`, so `max 0 (y-t) = 0`
    rw [max_eq_left (by linarith : y - t ≤ 0), mul_zero, add_zero]
    have hnum : (m : ℝ) * y ≤ (m : ℝ) * t := mul_le_mul_of_nonneg_left hyt hm0
    have hmono : Real.log (1 + (c0 + (m : ℝ) * y) / ((k : ℝ) + 1))
        ≤ Real.log (1 + (c0 + (m : ℝ) * t) / ((k : ℝ) + 1)) := by gcongr
    linarith
  · -- increasing branch: `t ≤ y`, use `g_mono`
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ y - t)]
    have hg := g_mono m k hm hk c0 hc0 t y htnn hty
    unfold g at hg
    have hexp : (11 / 50 : ℝ) * (m : ℝ) * (y - t)
        = (11 / 50 : ℝ) * (m : ℝ) * y - (11 / 50 : ℝ) * (m : ℝ) * t := by ring
    linarith [hg, hexp]

end R3Cert.R7CollapseMono
