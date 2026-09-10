/-
RvMWeierstrass — Phase 2 of the polygamma project: the Weierstrass product foundation.

The digamma series (the missing foundation) comes from log-differentiating the Weierstrass product
`1/Γ(s) = s·e^{γs}·∏_{n≥1} (1 + s/n)·e^{-s/n}`.  Mathlib has no Weierstrass product for Γ, so we
build it, mirroring `Analysis/SpecialFunctions/Trigonometric/Cotangent.lean` (which proves the
cotangent partial-fraction series by the same route).  Unlike the sine product `∏(1 - x²/n²)`, the
Gamma factor needs the exponential regularizer `e^{-s/n}` for convergence.

THIS BRICK (Phase 2, sub-brick 1): the regularized factor `wFactor`, its non-vanishing, and the
`O(1/n²)` bound `‖wFactor n s - 1‖ ≤ 3‖s/(n+1)‖²` — the convergence engine of the product, resting on
the exp-Taylor estimate `norm_exp_sub_one_sub_id_le`.

conjecture1_proved = False.  Classical special-function analysis; does not prove or approach RH.
-/
import Mathlib

open Complex

namespace RvMWeierstrass

/-- The regularized Weierstrass factor `(1 + s/(n+1))·exp(-s/(n+1))` (indexed from `n=0`, so the
    `(n+1)`-th classical factor).  Its infinite product over `n` (times `s·e^{γs}`) is `1/Γ`. -/
noncomputable def wFactor (n : ℕ) (s : ℂ) : ℂ :=
  (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1)))

theorem natCast_add_one_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  exact_mod_cast (Nat.cast_add_one_ne_zero n : ((n : ℝ) + 1) ≠ 0)

/-- The factor is non-vanishing except at `s = -(n+1)` (the classical Γ pole it cancels). -/
theorem wFactor_ne_zero {n : ℕ} {s : ℂ} (hs : s ≠ -((n : ℂ) + 1)) : wFactor n s ≠ 0 := by
  have hn : ((n : ℂ) + 1) ≠ 0 := natCast_add_one_ne_zero n
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  intro h
  apply hs
  field_simp at h
  linear_combination h

/-- Algebraic identity: `wFactor n s - 1 = -w² + (1+w)·(e^{-w} - 1 + w)` with `w = s/(n+1)`. -/
theorem wFactor_sub_one_eq (n : ℕ) (s : ℂ) :
    wFactor n s - 1
      = -(s / ((n : ℂ) + 1)) ^ 2
        + (1 + s / ((n : ℂ) + 1))
          * (Complex.exp (-(s / ((n : ℂ) + 1))) - 1 + s / ((n : ℂ) + 1)) := by
  simp only [wFactor]; ring

/-- **The O(1/n²) convergence bound.**  For `‖s/(n+1)‖ ≤ 1`,
    `‖wFactor n s - 1‖ ≤ 3·‖s/(n+1)‖²`.  From the exp-Taylor estimate
    `‖e^{-w} - 1 - (-w)‖ ≤ ‖w‖²` and the triangle inequality. -/
theorem norm_wFactor_sub_one_le {n : ℕ} {s : ℂ} (hw : ‖s / ((n : ℂ) + 1)‖ ≤ 1) :
    ‖wFactor n s - 1‖ ≤ 3 * ‖s / ((n : ℂ) + 1)‖ ^ 2 := by
  set w : ℂ := s / ((n : ℂ) + 1) with hwdef
  -- R := exp(-w) - 1 + w has ‖R‖ ≤ ‖w‖²
  have hR : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -w) (by rwa [norm_neg])
    have he : Complex.exp (-w) - 1 - (-w) = Complex.exp (-w) - 1 + w := by ring
    rw [he, norm_neg] at h
    exact h
  have hid : wFactor n s - 1 = -(w ^ 2) + (1 + w) * (Complex.exp (-w) - 1 + w) := by
    rw [hwdef]; exact wFactor_sub_one_eq n s
  have h1w : ‖1 + w‖ ≤ 2 := by
    calc ‖1 + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
  rw [hid]
  calc ‖-(w ^ 2) + (1 + w) * (Complex.exp (-w) - 1 + w)‖
      ≤ ‖-(w ^ 2)‖ + ‖(1 + w) * (Complex.exp (-w) - 1 + w)‖ := norm_add_le _ _
    _ = ‖w‖ ^ 2 + ‖1 + w‖ * ‖Complex.exp (-w) - 1 + w‖ := by
        rw [norm_neg, norm_pow, norm_mul]
    _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ ^ 2 := by gcongr
    _ = 3 * ‖w‖ ^ 2 := by ring

end RvMWeierstrass
