import Mathlib

/-!
  # Hinge profile→equal-children floor (G7 assembly input) — 2026-08-22

  The `profile→equal` half of the G1 L2 class-floor lift: for the convex hinge
  `φ(y) = c·(y − t0)₊` (`c ≥ 0`), the sum of the per-child hinge slacks of an
  ARBITRARY multi-child profile is at least the collapsed (equal-children) value,

      Σ_{i∈s} (y i − t0)₊  ≥  ( Σ_{i∈s} y i − |s|·t0 )₊ .

  Pure `posPart` subadditivity over a `Finset` (`(Σ f)⁺ ≤ Σ f⁺`), abstract in
  `c`, `t0`, and the index type — the assembly instantiates `c = 11/50`,
  `t0 = T0 = ρB−1` and rewrites `c·(Σy − |s|·t0)₊ = |s|·φ(ȳ)` by positive
  homogeneity on its side.  For the BG hinge this IS the Jensen "min at equal
  children" reduction the slack-ledger dichotomy invokes; the additive
  y-independent class constant does not affect it (same as `slk_min_at_T0`).

  Mathlib has no `Finset.posPart_sum_le`, so `posPart_sum_le` is proved here by a
  clean `Finset` induction over the two-term subadditivity `(a+b)⁺ ≤ a⁺ + b⁺`.
  General arity (unbounded child count), per the assembly's quantification.
  `conjecture1_proved = False`.
-/

namespace R3Cert.HingeProfileFloor

open Finset

/-- Positive part is subadditive over a `Finset` sum: `(Σ_{i∈s} f i)⁺ ≤ Σ_{i∈s} (f i)⁺`. -/
theorem posPart_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i)⁺ ≤ ∑ i ∈ s, (f i)⁺ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hstep : (f a + ∑ i ∈ s, f i)⁺ ≤ (f a)⁺ + (∑ i ∈ s, f i)⁺ := by
        rw [posPart_def]
        exact sup_le (add_le_add (le_posPart _) (le_posPart _)) (by positivity)
      calc (f a + ∑ i ∈ s, f i)⁺
          ≤ (f a)⁺ + (∑ i ∈ s, f i)⁺ := hstep
        _ ≤ (f a)⁺ + ∑ i ∈ s, (f i)⁺ := by gcongr

/-- **profile→equal floor.** `(Σ y i − |s|·t0)⁺ ≤ Σ (y i − t0)⁺` — the sum of
    per-child hinge slacks dominates the collapsed equal-children value. -/
theorem hinge_profile_floor {ι : Type*} (s : Finset ι) (y : ι → ℝ) (t0 : ℝ) :
    (∑ i ∈ s, y i - s.card • t0)⁺ ≤ ∑ i ∈ s, (y i - t0)⁺ := by
  have hsum : (∑ i ∈ s, y i) - s.card • t0 = ∑ i ∈ s, (y i - t0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
  rw [hsum]
  exact posPart_sum_le s (fun i => y i - t0)

/-- The `c ≥ 0` scaled form the assembly consumes: `c·(Σ y i − |s|·t0)⁺ ≤ c·Σ (y i − t0)⁺`. -/
theorem hinge_profile_floor_mul {ι : Type*} (s : Finset ι) (y : ι → ℝ) (t0 c : ℝ)
    (hc : 0 ≤ c) :
    c * (∑ i ∈ s, y i - s.card • t0)⁺ ≤ c * ∑ i ∈ s, (y i - t0)⁺ :=
  mul_le_mul_of_nonneg_left (hinge_profile_floor s y t0) hc

end R3Cert.HingeProfileFloor
