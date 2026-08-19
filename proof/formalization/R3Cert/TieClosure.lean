import Mathlib

/-!
  # The tie-dominant half of the BG closure step, machine-checked

  A candidate closure for the Brualdi–Goldwasser inductive step (parallel
  crux-campaign session, 2026-08-19) reduces the conjecture to a per-hub F-factor
  bound against an explicit envelope.  Its **tie-dominant half** — the regime
  `S ≤ 3j/23` where the tie-recursive plateau lives (the family that broke every
  prior lead) — was proven by exact rational algebra.  This file kernel-checks
  that half, entirely in `ℚ` (no `rpow`):

  for a hub with `j` children of total cavity message `S` with `23 S ≤ 3 j`,
  `W · a_hub^11 ≤ F_tie(μ_hub)`, `W = 64/621`, `a_hub = 1 + S/(j+1)`,
  `μ_hub = 1/((j+1) a_hub)`, `F_tie(μ) = W (26/(23+3μ))^11`.

  The pivot is the closed-form identity `a_hub (23 + 3 μ_hub) = 23 a_hub +
  3/(j+1)`, which is `≤ 26 ⟺ 23 S ≤ 3 j`.

  HONEST SCOPE: this is ONE HALF of ONE step of a CANDIDATE closure.  The other
  half (`S > 3j/23`, near-star-dominant) and the validity claim are open;
  `conjecture1_proved = False`.  Self-contained (its own `aHub`/`muHub`/`Ftie`),
  so it neither depends on nor collides with the live cavity machinery.
-/

namespace R3Cert
namespace TieClosure

/-- Hub amplitude for `j` children of total cavity message `S`. -/
def aHub (j : ℕ) (S : ℚ) : ℚ := 1 + S / (j + 1)

/-- The hub cavity message (pinned by the identity `μ · a = 1/(j+1)`). -/
def muHub (j : ℕ) (S : ℚ) : ℚ := 1 / ((j + 1) * aHub j S)

/-- The tie-recursive F-factor, `W = 64/621`. -/
def Ftie (mu : ℚ) : ℚ := (64 / 621) * (26 / (23 + 3 * mu)) ^ 11

/-- **The tie-dominant half of the closure step.**  For a hub whose children's
    total message satisfies `23 S ≤ 3 j` (i.e. `S ≤ 3j/23`), the hub F-factor is
    bounded by `F_tie(μ_hub)`, exactly, for every `j` and `n`. -/
theorem tie_dominant_half (j : ℕ) (S : ℚ) (hS : 0 ≤ S) (h : 23 * S ≤ 3 * (j : ℚ)) :
    (64 / 621 : ℚ) * aHub j S ^ 11 ≤ Ftie (muHub j S) := by
  have hj1 : (0 : ℚ) < (j : ℚ) + 1 := by positivity
  have hj_ne : ((j : ℚ) + 1) ≠ 0 := ne_of_gt hj1
  have ha : (0 : ℚ) < aHub j S := by
    have : (0 : ℚ) ≤ S / ((j : ℚ) + 1) := div_nonneg hS (le_of_lt hj1)
    simp only [aHub]; linarith
  have ha_ne : aHub j S ≠ 0 := ne_of_gt ha
  have hmu : (0 : ℚ) < muHub j S := by
    simp only [muHub]; exact div_pos one_pos (mul_pos hj1 ha)
  have hden : (0 : ℚ) < 23 + 3 * muHub j S := by linarith
  -- the cavity identity μ_hub · a_hub = 1/(j+1)
  have hmua : muHub j S * aHub j S = 1 / ((j : ℚ) + 1) := by
    simp only [muHub]; field_simp
  -- the pivot: a_hub (23 + 3 μ_hub) ≤ 26  ⟺  23 S ≤ 3 j
  have hpivot : aHub j S * (23 + 3 * muHub j S) ≤ 26 := by
    have expand : aHub j S * (23 + 3 * muHub j S)
        = 23 * aHub j S + 3 * (muHub j S * aHub j S) := by ring
    rw [expand, hmua]
    simp only [aHub]
    rw [← sub_nonneg]
    have key : (26 : ℚ) - (23 * (1 + S / ((j : ℚ) + 1)) + 3 * (1 / ((j : ℚ) + 1)))
        = (3 * (j : ℚ) - 23 * S) / ((j : ℚ) + 1) := by field_simp; ring
    rw [key]
    exact div_nonneg (by linarith) (le_of_lt hj1)
  -- a_hub ≤ 26/(23+3μ_hub), then 11th power and scale by W
  have hcore : aHub j S ≤ 26 / (23 + 3 * muHub j S) := by
    rw [le_div_iff₀ hden]; exact hpivot
  calc (64 / 621 : ℚ) * aHub j S ^ 11
      ≤ (64 / 621) * (26 / (23 + 3 * muHub j S)) ^ 11 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_left₀ (le_of_lt ha) hcore 11
    _ = Ftie (muHub j S) := by simp only [Ftie]

/-- The corrected clean bound: in the tie-dominant regime, `a_hub < 26/23`
    (`⟺ 23 S < 3(j+1)`, which follows from `23 S ≤ 3 j`). -/
theorem aHub_lt (j : ℕ) (S : ℚ) (hS : 0 ≤ S) (h : 23 * S ≤ 3 * (j : ℚ)) :
    aHub j S < 26 / 23 := by
  have hj1 : (0 : ℚ) < (j : ℚ) + 1 := by positivity
  simp only [aHub]
  rw [← sub_pos]
  have key : (26 / 23 : ℚ) - (1 + S / ((j : ℚ) + 1))
      = (3 * ((j : ℚ) + 1) - 23 * S) / (23 * ((j : ℚ) + 1)) := by field_simp; ring
  rw [key]
  exact div_pos (by linarith) (by positivity)

/-- `W (26/23)^11 < 1` — `family_martingale`'s `64·26^11 < 621·23^11`. -/
theorem bound_lt_one : (64 / 621 : ℚ) * (26 / 23) ^ 11 < 1 := by norm_num

/-- **The corrected clean tie-dominant half** (env-free, strong-induction form):
    for `23 S ≤ 3 j`, the hub F-factor `W·a_hub^11 < 1` — so with the induction
    hypothesis `∏ F_child ≤ 1`, `F_hub = W·a_hub^11·∏ F_child < 1`.  No envelope,
    no continuity, no integrality gap: just `a_hub < 26/23` and `W(26/23)^11 < 1`.
    (The `∏ env ≤ 1` route is unsound — continuous `F_ns` exceeds 1 near k≈4.82;
    the strong hypothesis sidesteps it.)  conjecture1_proved = False. -/
theorem tie_dominant_half_lt_one (j : ℕ) (S : ℚ) (hS : 0 ≤ S)
    (h : 23 * S ≤ 3 * (j : ℚ)) :
    (64 / 621 : ℚ) * aHub j S ^ 11 < 1 := by
  have ha_lt : aHub j S < 26 / 23 := aHub_lt j S hS h
  have ha0 : (0 : ℚ) ≤ aHub j S := by
    have : (0 : ℚ) ≤ S / ((j : ℚ) + 1) := div_nonneg hS (by positivity)
    simp only [aHub]; linarith
  calc (64 / 621 : ℚ) * aHub j S ^ 11
      < (64 / 621) * (26 / 23) ^ 11 := by
        apply mul_lt_mul_of_pos_left _ (by norm_num)
        exact pow_lt_pow_left₀ ha_lt ha0 (by norm_num)
    _ < 1 := bound_lt_one

end TieClosure
end R3Cert
