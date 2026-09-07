/- telperion 0.1.6 | family LogProductBound | input-hash 4e38a407190e0063
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace LogProductBound

open Complex Metric

/-- Two-scale zero-factor bound on `closedBall c 2` (inner) / `sphere c 5` (outer):
    `log‖∏(c-ρ)^m‖ - log‖∏(z-ρ)^m‖ ≤ (Σ m)·(log 2 - log(5-2))` for zeros in
    the inner disk (nonneg multiplicities, c not a zero).  The dVP `AP` shape. -/
theorem log_product_bound_two_five {c z : ℂ}
    (hz : z ∈ sphere c (5 : ℝ)) (s : Finset ℂ) (m : ℂ → ℤ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hin : ∀ ρ ∈ s, ρ ∈ closedBall c (2 : ℝ))
    (hcne : ∀ ρ ∈ s, c ≠ ρ) :
    Real.log ‖∏ ρ ∈ s, (c - ρ) ^ (m ρ)‖ - Real.log ‖∏ ρ ∈ s, (z - ρ) ^ (m ρ)‖
      ≤ (∑ ρ ∈ s, (m ρ : ℝ)) * (Real.log (2 : ℝ) - Real.log ((5 : ℝ) - 2)) := by
  have hR0 : (1 : ℝ) ≤ 2 := by norm_num
  have hRR0 : (0 : ℝ) < (5 : ℝ) - 2 := by norm_num
  have hsep : ∀ ρ ∈ s, (5 : ℝ) - 2 ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hz' := hz; rw [mem_sphere_iff_norm] at hz'
    have hρ' := hin ρ hρ; rw [mem_closedBall_iff_norm] at hρ'
    calc (5 : ℝ) - 2 ≤ ‖z - c‖ - ‖ρ - c‖ := by rw [hz']; linarith
      _ ≤ ‖(z - c) - (ρ - c)‖ := norm_sub_norm_le _ _
      _ = ‖z - ρ‖ := by rw [sub_sub_sub_cancel_right]
  have hzne : ∀ ρ ∈ s, z ≠ ρ := by
    intro ρ hρ heq
    have := hsep ρ hρ; rw [heq, sub_self, norm_zero] at this; linarith
  have hlogprod : ∀ w : ℂ, (∀ ρ ∈ s, w ≠ ρ) →
      Real.log ‖∏ ρ ∈ s, (w - ρ) ^ (m ρ)‖ = ∑ ρ ∈ s, (m ρ : ℝ) * Real.log ‖w - ρ‖ := by
    intro w hw
    have hne : ∀ ρ ∈ s, ‖(w - ρ) ^ (m ρ)‖ ≠ 0 := by
      intro ρ hρ
      rw [norm_zpow]
      exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hw ρ hρ)))
    rw [norm_prod, Real.log_prod hne]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [norm_zpow, Real.log_zpow]
  rw [hlogprod c hcne, hlogprod z hzne, ← Finset.sum_sub_distrib]
  have hstep : ∑ ρ ∈ s, ((m ρ : ℝ) * Real.log ‖c - ρ‖ - (m ρ : ℝ) * Real.log ‖z - ρ‖)
      = ∑ ρ ∈ s, (m ρ : ℝ) * (Real.log ‖c - ρ‖ - Real.log ‖z - ρ‖) :=
    Finset.sum_congr rfl (fun ρ _ => by ring)
  rw [hstep, Finset.sum_mul]
  refine Finset.sum_le_sum (fun ρ hρ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hm ρ hρ)
  have hcρ : ‖c - ρ‖ ≤ 2 := by
    have hρ' := hin ρ hρ; rw [mem_closedBall_iff_norm] at hρ'
    rw [norm_sub_rev]; exact hρ'
  have hlog1 : Real.log ‖c - ρ‖ ≤ Real.log (2 : ℝ) := by
    rcases eq_or_lt_of_le (norm_nonneg (c - ρ)) with h0 | hpos
    · rw [← h0, Real.log_zero]; exact Real.log_nonneg hR0
    · exact Real.log_le_log hpos hcρ
  have hlog2 : Real.log ((5 : ℝ) - 2) ≤ Real.log ‖z - ρ‖ :=
    Real.log_le_log hRR0 (hsep ρ hρ)
  linarith
/-- Two-scale zero-factor bound on `closedBall c 1` (inner) / `sphere c 3` (outer):
    `log‖∏(c-ρ)^m‖ - log‖∏(z-ρ)^m‖ ≤ (Σ m)·(log 1 - log(3-1))` for zeros in
    the inner disk (nonneg multiplicities, c not a zero).  The dVP `AP` shape. -/
theorem log_product_bound_one_three {c z : ℂ}
    (hz : z ∈ sphere c (3 : ℝ)) (s : Finset ℂ) (m : ℂ → ℤ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hin : ∀ ρ ∈ s, ρ ∈ closedBall c (1 : ℝ))
    (hcne : ∀ ρ ∈ s, c ≠ ρ) :
    Real.log ‖∏ ρ ∈ s, (c - ρ) ^ (m ρ)‖ - Real.log ‖∏ ρ ∈ s, (z - ρ) ^ (m ρ)‖
      ≤ (∑ ρ ∈ s, (m ρ : ℝ)) * (Real.log (1 : ℝ) - Real.log ((3 : ℝ) - 1)) := by
  have hR0 : (1 : ℝ) ≤ 1 := by norm_num
  have hRR0 : (0 : ℝ) < (3 : ℝ) - 1 := by norm_num
  have hsep : ∀ ρ ∈ s, (3 : ℝ) - 1 ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hz' := hz; rw [mem_sphere_iff_norm] at hz'
    have hρ' := hin ρ hρ; rw [mem_closedBall_iff_norm] at hρ'
    calc (3 : ℝ) - 1 ≤ ‖z - c‖ - ‖ρ - c‖ := by rw [hz']; linarith
      _ ≤ ‖(z - c) - (ρ - c)‖ := norm_sub_norm_le _ _
      _ = ‖z - ρ‖ := by rw [sub_sub_sub_cancel_right]
  have hzne : ∀ ρ ∈ s, z ≠ ρ := by
    intro ρ hρ heq
    have := hsep ρ hρ; rw [heq, sub_self, norm_zero] at this; linarith
  have hlogprod : ∀ w : ℂ, (∀ ρ ∈ s, w ≠ ρ) →
      Real.log ‖∏ ρ ∈ s, (w - ρ) ^ (m ρ)‖ = ∑ ρ ∈ s, (m ρ : ℝ) * Real.log ‖w - ρ‖ := by
    intro w hw
    have hne : ∀ ρ ∈ s, ‖(w - ρ) ^ (m ρ)‖ ≠ 0 := by
      intro ρ hρ
      rw [norm_zpow]
      exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hw ρ hρ)))
    rw [norm_prod, Real.log_prod hne]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [norm_zpow, Real.log_zpow]
  rw [hlogprod c hcne, hlogprod z hzne, ← Finset.sum_sub_distrib]
  have hstep : ∑ ρ ∈ s, ((m ρ : ℝ) * Real.log ‖c - ρ‖ - (m ρ : ℝ) * Real.log ‖z - ρ‖)
      = ∑ ρ ∈ s, (m ρ : ℝ) * (Real.log ‖c - ρ‖ - Real.log ‖z - ρ‖) :=
    Finset.sum_congr rfl (fun ρ _ => by ring)
  rw [hstep, Finset.sum_mul]
  refine Finset.sum_le_sum (fun ρ hρ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hm ρ hρ)
  have hcρ : ‖c - ρ‖ ≤ 1 := by
    have hρ' := hin ρ hρ; rw [mem_closedBall_iff_norm] at hρ'
    rw [norm_sub_rev]; exact hρ'
  have hlog1 : Real.log ‖c - ρ‖ ≤ Real.log (1 : ℝ) := by
    rcases eq_or_lt_of_le (norm_nonneg (c - ρ)) with h0 | hpos
    · rw [← h0, Real.log_zero]; exact Real.log_nonneg hR0
    · exact Real.log_le_log hpos hcρ
  have hlog2 : Real.log ((3 : ℝ) - 1) ≤ Real.log ‖z - ρ‖ :=
    Real.log_le_log hRR0 (hsep ρ hρ)
  linarith

end LogProductBound
