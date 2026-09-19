theorem RH_barrier_orientation_only :
    (∀ {α : Type} (F : ℂ → α), (∀ ρ : ℂ, F (1 - (starRingEnd ℂ) ρ) = F ρ) →
        ∀ dec : α → Prop,
          ¬ (∀ ρ : ℂ, ρ.re ≠ 1 / 2 → (dec (F ρ) ↔ 1 / 2 < ρ.re)))
      ∧ (∃ F : ℂ → ℝ, (∀ ρ : ℂ, F (1 - (starRingEnd ℂ) ρ) = F ρ)
          ∧ (∀ ρ : ℂ, F ρ = 0 ↔ ρ.re = 1 / 2)) := by
  sorry
