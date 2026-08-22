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

end R3Cert.R7CollapseMono
