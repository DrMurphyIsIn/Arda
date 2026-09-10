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

/-! ### b2: local-uniform convergence of the Weierstrass product. -/

set_option maxHeartbeats 1000000 in
open Filter Topology in
/-- A summable majorant for `‖wFactor n z - 1‖`, uniform over a compact `Z`, eventually in `n`. -/
theorem wFactor_bound_aux {Z : Set ℂ} (hZ : IsCompact Z) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ n in Filter.atTop, ∀ z ∈ Z, ‖wFactor n z - 1‖ ≤ u n := by
  have hf : ContinuousOn (fun z : ℂ => ‖z‖) Z := by fun_prop
  obtain ⟨C, hC⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hZ hf)
  have hCz : ∀ z ∈ Z, ‖z‖ ≤ C := fun z hz => hC _ ⟨z, hz, rfl⟩
  refine ⟨fun n => ‖(3 * C ^ 2 : ℝ) / ((n : ℝ) + 1) ^ 2‖, ?_, ?_⟩
  · have h := summable_pow_div_add (3 * C ^ 2 : ℝ) 2 1 Nat.one_lt_two
    simpa only [Nat.cast_one] using h
  · obtain ⟨N, hN⟩ := exists_nat_ge (max C 1)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => ?_⟩
    have hnN : (max C 1 : ℝ) ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnormn : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    have hCge : C ≤ (n : ℝ) := le_trans (le_max_left _ _) hnN
    have hwnorm : ‖z / ((n : ℂ) + 1)‖ = ‖z‖ / ((n : ℝ) + 1) := by rw [norm_div, hnormn]
    have hw1 : ‖z / ((n : ℂ) + 1)‖ ≤ 1 := by
      rw [hwnorm, div_le_one hnpos]; exact le_trans (hCz z hz) (by linarith)
    have hbound := norm_wFactor_sub_one_le (n := n) (s := z) hw1
    have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg z) (hCz z hz)
    have hun : ‖(3 * C ^ 2 : ℝ) / ((n : ℝ) + 1) ^ 2‖ = 3 * C ^ 2 / ((n : ℝ) + 1) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp only
    rw [hun]
    refine le_trans hbound ?_
    rw [hwnorm, div_pow, mul_div_assoc]
    have hsq : ‖z‖ ^ 2 ≤ C ^ 2 := by nlinarith [hCz z hz, norm_nonneg z, hCnn]
    gcongr

/-- **b2 — the Weierstrass product converges uniformly on every compact.** -/
theorem multipliableUniformlyOn_wFactor {Z : Set ℂ} (hZC : IsCompact Z) :
    MultipliableUniformlyOn (fun n : ℕ => fun s : ℂ => wFactor n s) Z := by
  obtain ⟨u, hu, hbd⟩ := wFactor_bound_aux hZC
  have hrw : (fun n : ℕ => fun s : ℂ => wFactor n s)
      = (fun n : ℕ => fun s : ℂ => 1 + (wFactor n s - 1)) := by funext n s; ring
  rw [hrw]
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards [hbd] with n hn z hz using hn z hz
  · intro n; unfold wFactor; fun_prop

/-- **b2 — the product converges locally uniformly on all of `ℂ`** (to its `tprod`). -/
theorem hasProdLocallyUniformlyOn_wFactor :
    HasProdLocallyUniformlyOn (fun n : ℕ => fun s : ℂ => wFactor n s)
      (fun s => ∏' n : ℕ, wFactor n s) (Set.univ : Set ℂ) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro Z _ hZC
  exact (multipliableUniformlyOn_wFactor hZC).hasProdUniformlyOn.congr_right
    (fun s _ => rfl)

end RvMWeierstrass
