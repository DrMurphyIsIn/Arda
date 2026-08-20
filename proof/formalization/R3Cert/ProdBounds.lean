import Mathlib

/-!
  # List-product bounds — the child-product plumbing (2026-08-20)

  The assembly bridges (`GLemmaAssembly.glemma_step`, `master_step`) consume the child
  products `PF = ∏F_c`, `Pbc = ∏Bcap`, `Pgl = ∏glemma` and the relations
  `PF ≤ Pbc ≤ 1`, `Pbc ≤ Pgl`. Those come from the per-child induction hypotheses
  `F_c ≤ Bcap(μ_c) ≤ 1` and `Bcap(μ_c) ≤ glemma(μ_c)` via list-product monotonicity.
  This file kernel-checks that monotonicity, over `ℚ`.  `conjecture1_proved = False`.
-/

namespace R3Cert.ProdBounds

/-- **Product monotonicity.** For a list `l`, if `0 ≤ f x` and `f x ≤ g x` on every element,
    then `∏ (map f) ≤ ∏ (map g)`. -/
theorem map_prod_le {α : Type*} (l : List α) (f g : α → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) (hle : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha0 : 0 ≤ f a := h0 a (List.mem_cons_self a t)
    have hale : f a ≤ g a := hle a (List.mem_cons_self a t)
    have hag0 : 0 ≤ g a := le_trans ha0 hale
    have ht0 : ∀ x ∈ t, 0 ≤ f x := fun x hx => h0 x (List.mem_cons_of_mem a hx)
    have htle : ∀ x ∈ t, f x ≤ g x := fun x hx => hle x (List.mem_cons_of_mem a hx)
    have htih := ih ht0 htle
    have hprodf0 : 0 ≤ (t.map f).prod := by
      apply List.prod_nonneg
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ht0 x hx
    simp only [List.map_cons, List.prod_cons]
    calc f a * (t.map f).prod
        ≤ g a * (t.map f).prod := mul_le_mul_of_nonneg_right hale hprodf0
      _ ≤ g a * (t.map g).prod := mul_le_mul_of_nonneg_left htih hag0

/-- **Product ≤ 1.** If `0 ≤ f x ≤ 1` on every element, then `∏ (map f) ≤ 1`. -/
theorem map_prod_le_one {α : Type*} (l : List α) (f : α → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) (h1 : ∀ x ∈ l, f x ≤ 1) :
    (l.map f).prod ≤ 1 := by
  have h := map_prod_le l f (fun _ => 1) h0 h1
  simpa [List.map_const, List.prod_replicate] using h

/-- **Product nonneg.** If `0 ≤ f x` on every element, then `0 ≤ ∏ (map f)`. -/
theorem map_prod_nonneg {α : Type*} (l : List α) (f : α → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).prod := by
  apply List.prod_nonneg
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact h0 x hx

end R3Cert.ProdBounds
