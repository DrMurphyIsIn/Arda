import Mathlib

/-!
  # List-product bounds — the child-product plumbing (2026-08-20)

  `CappedJointConfig` needs `prodBcap = ∏Bcap ≤ 1` and `0 ≤ prodBcap` from per-child
  `0 ≤ Bcap(μ) ≤ 1`. This file kernel-checks those two list-product facts over `ℚ`, by
  induction with `by simp` membership proofs (pin-robust).  `conjecture1_proved = False`.
-/

namespace R3Cert.ProdBounds

/-- **Product ≤ 1.** If `0 ≤ f x ≤ 1` on every element, then `∏ (map f) ≤ 1`. -/
theorem map_prod_le_one {α : Type*} (l : List α) (f : α → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) (h1 : ∀ x ∈ l, f x ≤ 1) :
    (l.map f).prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha0 : 0 ≤ f a := h0 a (by simp)
    have ha1 : f a ≤ 1 := h1 a (by simp)
    have iht : (t.map f).prod ≤ 1 :=
      ih (fun x hx => h0 x (by simp [hx])) (fun x hx => h1 x (by simp [hx]))
    have hp0 : 0 ≤ (t.map f).prod :=
      List.prod_nonneg (fun y hy => by
        rw [List.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact h0 x (by simp [hx]))
    calc f a * (t.map f).prod ≤ 1 * 1 := mul_le_mul ha1 iht hp0 (by norm_num)
      _ = 1 := by norm_num

/-- **Product nonneg.** If `0 ≤ f x` on every element, then `0 ≤ ∏ (map f)`. -/
theorem map_prod_nonneg {α : Type*} (l : List α) (f : α → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).prod :=
  List.prod_nonneg (fun y hy => by
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h0 x hx)

end R3Cert.ProdBounds
