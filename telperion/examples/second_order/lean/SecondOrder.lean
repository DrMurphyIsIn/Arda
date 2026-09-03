/- telperion 0.1.6 | family SecondOrder | input-hash ad6d7e97660786ba
   6 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SecondOrder

-- so_geom_2_3: closed form for the second-order recurrence
--   (1)*f(q+2) + (0 - 5)*f(q+1) + (6)*f(q) = 0   (q >= 0),
-- certificate = the ring identity A*g(q+2)+B*g(q+1)+C*g(q)=0 (verified exactly
-- at certification) + the two base values, assembled by a two-step induction.

def so_geom_2_3_g (q : ℕ) : ℝ := (2 : ℝ) ^ q + (3 : ℝ) ^ q

theorem so_geom_2_3_base0 : so_geom_2_3_g 0 = 2 := by norm_num [so_geom_2_3_g]

theorem so_geom_2_3_base1 : so_geom_2_3_g (0 + 1) = 5 := by norm_num [so_geom_2_3_g]

theorem so_geom_2_3 (f : ℕ → ℝ)
    (hrec : ∀ q, 0 ≤ q →
      ((1 : ℝ)) * f (q + 2) + ((0 - 5 : ℝ)) * f (q + 1) + ((6 : ℝ)) * f q = 0)
    (hA : ∀ q, 0 ≤ q → ((1 : ℝ)) ≠ 0)
    (hb0 : f 0 = so_geom_2_3_g 0) (hb1 : f (0 + 1) = so_geom_2_3_g (0 + 1)) :
    ∀ q, 0 ≤ q → f q = so_geom_2_3_g q := by
  -- Strengthened predicate P q := (f q = g q) ∧ (f (q+1) = g (q+1)); a single
  -- Nat.le_induction carries the two-back dependence of the recurrence.
  have key : ∀ q, 0 ≤ q → f q = so_geom_2_3_g q ∧ f (q + 1) = so_geom_2_3_g (q + 1) := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => exact ⟨hb0, hb1⟩
    | succ m hm ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      -- recurrence-satisfaction of the closed form g (the (⋆) ring identity):
      have hgid : ((1 : ℝ)) * so_geom_2_3_g (m + 2) + ((0 - 5 : ℝ)) * so_geom_2_3_g (m + 1)
          + ((6 : ℝ)) * so_geom_2_3_g m = 0 := by
        simp only [so_geom_2_3_g]; push_cast; ring
      have hrecm := hrec m hm
      have hAm := hA m hm
      -- subtract the two relations, substitute the two inductive equalities,
      -- and cancel the (nonzero) leading coefficient A(m).
      have hcancel : ((1 : ℝ)) * f (m + 2) = ((1 : ℝ)) * so_geom_2_3_g (m + 2) := by
        rw [ih0, ih1] at hrecm
        linear_combination hrecm - hgid
      exact mul_left_cancel₀ hAm hcancel
  intro q hq
  exact (key q hq).1

-- so_linear: closed form for the second-order recurrence
--   (1)*f(q+2) + (0 - 2)*f(q+1) + (1)*f(q) = 0   (q >= 3),
-- certificate = the ring identity A*g(q+2)+B*g(q+1)+C*g(q)=0 (verified exactly
-- at certification) + the two base values, assembled by a two-step induction.

def so_linear_g (q : ℕ) : ℝ := (q : ℝ)

theorem so_linear_base0 : so_linear_g 3 = 3 := by norm_num [so_linear_g]

theorem so_linear_base1 : so_linear_g (3 + 1) = 4 := by norm_num [so_linear_g]

theorem so_linear (f : ℕ → ℝ)
    (hrec : ∀ q, 3 ≤ q →
      ((1 : ℝ)) * f (q + 2) + ((0 - 2 : ℝ)) * f (q + 1) + ((1 : ℝ)) * f q = 0)
    (hA : ∀ q, 3 ≤ q → ((1 : ℝ)) ≠ 0)
    (hb0 : f 3 = so_linear_g 3) (hb1 : f (3 + 1) = so_linear_g (3 + 1)) :
    ∀ q, 3 ≤ q → f q = so_linear_g q := by
  -- Strengthened predicate P q := (f q = g q) ∧ (f (q+1) = g (q+1)); a single
  -- Nat.le_induction carries the two-back dependence of the recurrence.
  have key : ∀ q, 3 ≤ q → f q = so_linear_g q ∧ f (q + 1) = so_linear_g (q + 1) := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => exact ⟨hb0, hb1⟩
    | succ m hm ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      -- recurrence-satisfaction of the closed form g (the (⋆) ring identity):
      have hgid : ((1 : ℝ)) * so_linear_g (m + 2) + ((0 - 2 : ℝ)) * so_linear_g (m + 1)
          + ((1 : ℝ)) * so_linear_g m = 0 := by
        simp only [so_linear_g]; push_cast; ring
      have hrecm := hrec m hm
      have hAm := hA m hm
      -- subtract the two relations, substitute the two inductive equalities,
      -- and cancel the (nonzero) leading coefficient A(m).
      have hcancel : ((1 : ℝ)) * f (m + 2) = ((1 : ℝ)) * so_linear_g (m + 2) := by
        rw [ih0, ih1] at hrecm
        linear_combination hrecm - hgid
      exact mul_left_cancel₀ hAm hcancel
  intro q hq
  exact (key q hq).1

end SecondOrder
