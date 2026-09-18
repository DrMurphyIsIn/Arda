/- telperion 0.1.6 | family ShapeAudit | input-hash e60369f39226c4f8
   2 theorems, 5 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace Telperion
namespace ShapeAudit

-- headline_alone_is_trivial: STATEMENT-SHAPE COLLAPSE witness (kind bounded_hypothesis_collapse).
-- The shape `exists C >= 0, forall T >= 2, P T -> -(C * log T / T^1) <= W`
-- is closed, for EVERY W and EVERY hypothesis family P that fails above some
-- finite height B, by the explicit constant max 0 (-W) * B^1 / log 2.
-- Hence the shape carries none of its intended content: a classical case split
-- (RH true -> W >= 0 -> C := 0; RH false -> the ladder hypothesis is falsified
-- above a finite height -> this constant) closes it with no mathematics.
-- Exactly re-checked adversarial samples: W=-3, B=100, T=50; W=-1, B=10, T=2; W=-1/7, B=640000, T=100.
-- Refutes a SHAPE, not a theorem.  conjecture1_proved = False.
theorem headline_alone_is_trivial (W : ℝ) (Pr : ℝ → Prop) (B : ℝ) (hB : (2 : ℝ) ≤ B)
    (hfail : ∀ T : ℝ, B < T → ¬ Pr T) :
    (0 : ℝ) ≤ max 0 (-W) * B ^ 1 / Real.log 2 ∧
      ∀ T : ℝ, (2 : ℝ) ≤ T → Pr T →
        -(max 0 (-W) * B ^ 1 / Real.log 2 * Real.log T / T ^ 1) ≤ W := by
  have hT0pos : (0 : ℝ) < 2 := by norm_num
  have hlogT0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : (0 : ℝ) ≤ max 0 (-W) := le_max_left _ _
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le hT0pos hB
  refine ⟨by positivity, ?_⟩
  intro T hT hP
  have hTB : T ≤ B := by
    by_contra hcon
    exact hfail T (lt_of_not_ge hcon) hP
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hT0pos hT
  have hTk : (0 : ℝ) < T ^ 1 := pow_pos hTpos 1
  have hBk : T ^ 1 ≤ B ^ 1 := pow_le_pow_left₀ hTpos.le hTB 1
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log hT0pos hT
  have h1 : Real.log 2 * T ^ 1 ≤ B ^ 1 * Real.log T := by
    calc Real.log 2 * T ^ 1 ≤ Real.log 2 * B ^ 1 := by nlinarith
      _ ≤ Real.log T * B ^ 1 := by nlinarith [pow_pos hBpos 1]
      _ = B ^ 1 * Real.log T := by ring
  have h2 := mul_le_mul_of_nonneg_left h1 hM
  have hkey : max 0 (-W)
      ≤ max 0 (-W) * B ^ 1 / Real.log 2 * Real.log T / T ^ 1 := by
    rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
    calc max 0 (-W) * (Real.log 2 * T ^ 1)
        ≤ max 0 (-W) * (B ^ 1 * Real.log T) := h2
      _ = max 0 (-W) * B ^ 1 * Real.log T := by ring
  have hW : -W ≤ max 0 (-W) := le_max_right _ _
  linarith

-- headline_alone_is_trivial_cubed: STATEMENT-SHAPE COLLAPSE witness (kind bounded_hypothesis_collapse).
-- The shape `exists C >= 0, forall T >= 2, P T -> -(C * log T / T^3) <= W`
-- is closed, for EVERY W and EVERY hypothesis family P that fails above some
-- finite height B, by the explicit constant max 0 (-W) * B^3 / log 2.
-- Hence the shape carries none of its intended content: a classical case split
-- (RH true -> W >= 0 -> C := 0; RH false -> the ladder hypothesis is falsified
-- above a finite height -> this constant) closes it with no mathematics.
-- Exactly re-checked adversarial samples: W=-3, B=100, T=50; W=-1/7, B=640000, T=100.
-- Refutes a SHAPE, not a theorem.  conjecture1_proved = False.
theorem headline_alone_is_trivial_cubed (W : ℝ) (Pr : ℝ → Prop) (B : ℝ) (hB : (2 : ℝ) ≤ B)
    (hfail : ∀ T : ℝ, B < T → ¬ Pr T) :
    (0 : ℝ) ≤ max 0 (-W) * B ^ 3 / Real.log 2 ∧
      ∀ T : ℝ, (2 : ℝ) ≤ T → Pr T →
        -(max 0 (-W) * B ^ 3 / Real.log 2 * Real.log T / T ^ 3) ≤ W := by
  have hT0pos : (0 : ℝ) < 2 := by norm_num
  have hlogT0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : (0 : ℝ) ≤ max 0 (-W) := le_max_left _ _
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le hT0pos hB
  refine ⟨by positivity, ?_⟩
  intro T hT hP
  have hTB : T ≤ B := by
    by_contra hcon
    exact hfail T (lt_of_not_ge hcon) hP
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hT0pos hT
  have hTk : (0 : ℝ) < T ^ 3 := pow_pos hTpos 3
  have hBk : T ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hTpos.le hTB 3
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log hT0pos hT
  have h1 : Real.log 2 * T ^ 3 ≤ B ^ 3 * Real.log T := by
    calc Real.log 2 * T ^ 3 ≤ Real.log 2 * B ^ 3 := by nlinarith
      _ ≤ Real.log T * B ^ 3 := by nlinarith [pow_pos hBpos 3]
      _ = B ^ 3 * Real.log T := by ring
  have h2 := mul_le_mul_of_nonneg_left h1 hM
  have hkey : max 0 (-W)
      ≤ max 0 (-W) * B ^ 3 / Real.log 2 * Real.log T / T ^ 3 := by
    rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
    calc max 0 (-W) * (Real.log 2 * T ^ 3)
        ≤ max 0 (-W) * (B ^ 3 * Real.log T) := h2
      _ = max 0 (-W) * B ^ 3 * Real.log T := by ring
  have hW : -W ≤ max 0 (-W) := le_max_right _ _
  linarith

end ShapeAudit
end Telperion
