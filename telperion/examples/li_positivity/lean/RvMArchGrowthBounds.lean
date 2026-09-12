/-
RvMArchGrowthBounds — Arc B (archimedean Li growth), PR B2: the real form + per-term bounds + tails.

B1b part 2 (`taylorCoeff_Gammaℝ_elem`) gave the archimedean Li coefficient as the COMPLEX elementary
series
  `taylorCoeff Γℝ n = −(γ+log π)/2·(n+1) − 1 + ∑'_j (((n+1)/(2(j+1)) − 1 + ((2j+2)/(2j+3))^(n+1)))`.
Every summand is real; this file extracts the honest REAL form and the elementary inequalities that
make the `(n/2)·log n` growth a harmonic-number statement:

  * `archRe` — the real summand `s n j = (n+1)/(2(j+1)) − 1 + ((2j+2)/(2j+3))^(n+1)`.
  * `summable_archRe` / `taylorCoeff_Gammaℝ_re_eq` — THE REAL FORM: the `.re` of the B1b series is
    `−((γ+log π)/2)·(n+1) − 1 + ∑'_j s n j`, a tsum of reals.
  * `archRe_lower` — Bernoulli: `s n j ≥ (n+1)/((2j+2)(2j+3)) > 0` (so the tail is a POSITIVE sum).
  * `archRe_upper_crude` — `r^(n+1) ≤ 1`: `s n j ≤ (n+1)/(2(j+1))`.
  * `archRe_upper_bonferroni` — second-order Bonferroni: `s n j ≤ (n+1)/((2j+2)(2j+3)) +
    (n(n+1)/2)·(1/(2j+3))²`.
  * `tail` helpers — explicit `O(1/n)` bounds on `∑_{j≥n}` of the two tail shapes.

conjecture1_proved = False: Γ-function calculus; nothing here approaches RH.
-/
import Mathlib
import RvMArchElemCoeff

open Complex

namespace RvMWeierstrass

/-- The real archimedean summand `s n j = (n+1)/(2(j+1)) − 1 + ((2j+2)/(2j+3))^(n+1)`. -/
noncomputable def archRe (n j : ℕ) : ℝ :=
  ((n : ℝ) + 1) / (2 * ((j : ℝ) + 1)) - 1 + (((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) ^ (n + 1))

/-- The `j`-th complex summand of the B1b series is the cast of the real summand `archRe n j`. -/
theorem archRe_ofReal (n j : ℕ) :
    (((n : ℂ) + 1) / (2 * ((j : ℂ) + 1)) - 1 + (((2 * (j : ℂ) + 2) / (2 * (j : ℂ) + 3)) ^ (n + 1)))
      = ((archRe n j : ℝ) : ℂ) := by
  unfold archRe
  push_cast
  ring

/-! ### Per-term elementary inequalities

Write `ε_j = 1/(2j+3)`, `r_j = (2j+2)/(2j+3) = 1 − ε_j`.  Three bounds hold for every `n, j`. -/

/-- The ratio lies in `(0, 1]`. -/
theorem archRe_r_pos (j : ℕ) : (0 : ℝ) < (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) := by
  apply div_pos <;> positivity

theorem archRe_r_le_one (j : ℕ) : (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith

/-- **Bernoulli lower bound** (Step 1a).  `r_j^(n+1) ≥ 1 − (n+1)·ε_j`, hence
    `s n j ≥ (n+1)/((2j+2)(2j+3)) > 0`. -/
theorem archRe_lower (n j : ℕ) :
    ((n : ℝ) + 1) / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3)) ≤ archRe n j := by
  unfold archRe
  have h3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  have h2 : (0 : ℝ) < 2 * (j : ℝ) + 2 := by positivity
  -- Bernoulli: `(1 + x)^(n+1) ≥ 1 + (n+1)x` with `x = -ε_j ∈ [-2, 0]`
  set ε : ℝ := 1 / (2 * (j : ℝ) + 3) with hε
  have hxge : (-2 : ℝ) ≤ -ε := by
    rw [hε]
    have : (1 : ℝ) / (2 * (j : ℝ) + 3) ≤ 1 := by
      rw [div_le_one h3]; linarith
    linarith
  have hbern : 1 + ((n : ℝ) + 1) * (-ε) ≤ (1 + (-ε)) ^ (n + 1) := by
    have := one_add_mul_le_pow hxge (n + 1)
    push_cast at this ⊢
    convert this using 2 <;> ring
  have hr : (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) = 1 + (-ε) := by
    rw [hε]; field_simp; ring
  rw [hr]
  -- now: (n+1)/((2j+2)(2j+3)) ≤ (n+1)/(2(j+1)) - 1 + (1-ε)^(n+1)
  -- suffices (n+1)/((2j+2)(2j+3)) ≤ (n+1)/(2(j+1)) - 1 + (1 + (n+1)(-ε))
  have hkey : ((n : ℝ) + 1) / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))
      = ((n : ℝ) + 1) / (2 * ((j : ℝ) + 1)) - 1 + (1 + ((n : ℝ) + 1) * (-ε)) := by
    rw [hε]
    field_simp
    ring
  rw [hkey]
  linarith [hbern]

/-- Positivity of the summand (immediate from the Bernoulli lower bound). -/
theorem archRe_pos (n j : ℕ) : 0 < archRe n j := by
  have h := archRe_lower n j
  have : (0 : ℝ) < ((n : ℝ) + 1) / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3)) := by positivity
  linarith

theorem archRe_nonneg (n j : ℕ) : 0 ≤ archRe n j := (archRe_pos n j).le

/-- **Crude upper bound** (Step 1c).  `r_j^(n+1) ≤ 1`, so `s n j ≤ (n+1)/(2(j+1))`. -/
theorem archRe_upper_crude (n j : ℕ) :
    archRe n j ≤ ((n : ℝ) + 1) / (2 * ((j : ℝ) + 1)) := by
  unfold archRe
  have hpow : ((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) ^ (n + 1) ≤ 1 := by
    apply pow_le_one₀ (archRe_r_pos j).le (archRe_r_le_one j)
  linarith

/-- **Second-order Bonferroni** (Step 1b), the elementary induction: for `0 ≤ ε ≤ 1`,
    `(1 − ε)^m ≤ 1 − m·ε + (m(m−1)/2)·ε²`. -/
theorem one_sub_pow_le_bonferroni {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (m : ℕ) :
    (1 - ε) ^ m ≤ 1 - (m : ℝ) * ε + ((m : ℝ) * ((m : ℝ) - 1) / 2) * ε ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hbase : (0 : ℝ) ≤ 1 - ε := by linarith
    -- (1-ε)^(m+1) = (1-ε)^m * (1-ε) ≤ RHS_m * (1-ε)
    have hstep : (1 - ε) ^ (m + 1) ≤
        (1 - (m : ℝ) * ε + ((m : ℝ) * ((m : ℝ) - 1) / 2) * ε ^ 2) * (1 - ε) := by
      rw [pow_succ]
      apply mul_le_mul_of_nonneg_right ih hbase
    refine hstep.trans ?_
    -- RHS_m·(1-ε) ≤ RHS_{m+1}: difference = (m/2)·ε³ ≥ 0 ... verify via nlinarith
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    -- `m(m-1) ≥ 0` since m is a Nat (product of consecutive integers)
    have hmm1 : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · simp [h0]
      · have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpos
        nlinarith
    have hε3 : (0 : ℝ) ≤ ε ^ 3 := by positivity
    -- the difference RHS_{m+1} − RHS_m·(1−ε) = (m(m−1)/2)·ε³ ≥ 0
    nlinarith [mul_nonneg hmm1 hε3]

/-- **Bonferroni upper bound** (Step 1b) for the summand.  With `ε_j = 1/(2j+3)`,
    `s n j ≤ (n+1)/((2j+2)(2j+3)) + (n(n+1)/2)·ε_j²`. -/
theorem archRe_upper_bonferroni (n j : ℕ) :
    archRe n j ≤ ((n : ℝ) + 1) / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))
      + ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / (2 * (j : ℝ) + 3)) ^ 2 := by
  unfold archRe
  have h3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  set ε : ℝ := 1 / (2 * (j : ℝ) + 3) with hε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 := by rw [hε]; rw [div_le_one h3]; linarith
  have hr : (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) = 1 - ε := by
    rw [hε]; field_simp; ring
  rw [hr]
  -- apply Bonferroni at m = n+1
  have hbon := one_sub_pow_le_bonferroni hε0 hε1 (n + 1)
  -- the linear part `(n+1)/(2(j+1)) - 1 + (1 - (n+1)ε)` equals `(n+1)/((2j+2)(2j+3))`
  have hlin : ((n : ℝ) + 1) / (2 * ((j : ℝ) + 1)) - 1 + (1 - ((n : ℝ) + 1) * ε)
      = ((n : ℝ) + 1) / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3)) := by
    rw [hε]; field_simp; ring
  -- Bonferroni's quadratic coefficient at m=n+1 is ((n+1)·n/2)
  have hquad : (((n : ℝ) + 1) * (((n : ℝ) + 1) - 1) / 2) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by ring
  push_cast at hbon
  nlinarith [hbon, hlin, hquad, sq_nonneg ε]

/-! ### Summability -/

/-- `1/(j+1)²` is summable. -/
theorem summable_one_div_sq_succ : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
  have h := Real.summable_one_div_nat_pow.mpr (le_refl 2)
  have h2 := (summable_nat_add_iff 1).mpr h
  simpa [div_eq_mul_inv] using h2

/-- The first tail shape `(n+1)/((2j+2)(2j+3))` is summable (`≤ (n+1)·/(j+1)²`). -/
theorem summable_tail_a (n : ℕ) :
    Summable (fun j : ℕ => ((n : ℝ) + 1) / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))) := by
  have hf : Summable (fun j : ℕ => ((n : ℝ) + 1) * (1 / ((j : ℝ) + 1) ^ 2)) :=
    (summable_one_div_sq_succ).mul_left _
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hf
  rw [div_le_iff₀ (by positivity)]
  rw [mul_comm ((n : ℝ) + 1) _, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith [Nat.cast_nonneg j (α := ℝ), hn]

/-- The second tail shape `(n(n+1)/2)·(1/(2j+3))²` is summable (`≤ (n(n+1)/2)·/(j+1)²`). -/
theorem summable_tail_b (n : ℕ) :
    Summable (fun j : ℕ => ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / (2 * (j : ℝ) + 3)) ^ 2) := by
  have hf : Summable (fun j : ℕ => ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / ((j : ℝ) + 1) ^ 2)) :=
    (summable_one_div_sq_succ).mul_left _
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hf
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_pow, one_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith [Nat.cast_nonneg j (α := ℝ)]

/-- `archRe n` is summable: dominated above by the Bonferroni bound (two `O(1/j²)` tails) and
    nonneg below. -/
theorem summable_archRe (n : ℕ) : Summable (fun j : ℕ => archRe n j) :=
  Summable.of_nonneg_of_le (fun j => (archRe_nonneg n j))
    (fun j => archRe_upper_bonferroni n j)
    ((summable_tail_a n).add (summable_tail_b n))

/-! ### The real form (Step 0) -/

/-- **THE REAL FORM.**  The real part of the archimedean Li coefficient is
    `−((γ+log π)/2)·(n+1) − 1 + ∑'_j archRe n j`, a tsum of REAL summands. -/
theorem taylorCoeff_Gammaℝ_re_eq (n : ℕ) :
    (LiCriterion.taylorCoeff Complex.Gammaℝ n).re
      = -((Real.eulerMascheroniConstant + Real.log Real.pi) / 2) * ((n : ℝ) + 1) - 1
        + ∑' j : ℕ, archRe n j := by
  -- the complex tsum is the cast of the real tsum
  have htsum : (∑' j : ℕ, (((n : ℂ) + 1) / (2 * ((j : ℂ) + 1)) - 1
      + (((2 * (j : ℂ) + 2) / (2 * (j : ℂ) + 3)) ^ (n + 1))))
      = ((∑' j : ℕ, archRe n j : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun j => archRe_ofReal n j)
  rw [taylorCoeff_Gammaℝ_elem, htsum]
  -- express the WHOLE complex RHS as the cast of the real RHS, then `.re` is transparent
  rw [show Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) from
    (Complex.ofReal_log Real.pi_pos.le).symm]
  rw [show (-((Real.eulerMascheroniConstant : ℂ) + ((Real.log Real.pi : ℝ) : ℂ)) / 2
        * ((n : ℂ) + 1) - 1 + ((∑' j : ℕ, archRe n j : ℝ) : ℂ))
      = (((-((Real.eulerMascheroniConstant + Real.log Real.pi) / 2) * ((n : ℝ) + 1) - 1
          + ∑' j : ℕ, archRe n j) : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.ofReal_re]

/-! ### Tail bounds (`O(1/n)`)

The reindexed `1/j²` tail, bounded by the telescoping `sum_Ioc_inv_sq_le_sub`. -/

/-- The reindexed `1/j²` tail is summable. -/
theorem tsum_tail_summable (n : ℕ) :
    Summable (fun k : ℕ => 1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2) := by
  have hf : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := summable_one_div_sq_succ
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hf
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [Nat.cast_nonneg k (α := ℝ), this]

/-- **The `1/j²` tail.**  For `n ≥ 1`, `∑'_k 1/(n+k+1)² ≤ 1/n`, by the telescoping comparison
    `1/(n+k+1)² ≤ 1/(n+k) − 1/(n+k+1)`. -/
theorem tsum_tail_inv_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑' k : ℕ, 1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro N
  -- telescoping upper bound: each term ≤ 1/(n+k) − 1/(n+k+1)
  have hterm : ∀ k : ℕ, 1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2
      ≤ 1 / ((n : ℝ) + (k : ℝ)) - 1 / ((n : ℝ) + (k : ℝ) + 1) := by
    intro k
    have hnk : (0 : ℝ) < (n : ℝ) + (k : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      positivity
    have hnk1 : (0 : ℝ) < (n : ℝ) + (k : ℝ) + 1 := by linarith
    rw [div_sub_div _ _ (ne_of_gt hnk) (ne_of_gt hnk1), div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    nlinarith [hnk, hnk1]
  calc ∑ k ∈ Finset.range N, 1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2
      ≤ ∑ k ∈ Finset.range N, (1 / ((n : ℝ) + (k : ℝ)) - 1 / ((n : ℝ) + (k : ℝ) + 1)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = ∑ k ∈ Finset.range N, ((fun m : ℕ => 1 / ((n : ℝ) + (m : ℝ))) k
          - (fun m : ℕ => 1 / ((n : ℝ) + (m : ℝ))) (k + 1)) := by
        apply Finset.sum_congr rfl; intro k _; push_cast; ring
    _ = 1 / (n : ℝ) - 1 / ((n : ℝ) + (N : ℝ)) := by
        rw [Finset.sum_range_sub' (fun m : ℕ => 1 / ((n : ℝ) + (m : ℝ)))]
        push_cast; ring_nf
    _ ≤ 1 / (n : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((n : ℝ) + (N : ℝ)) := by positivity
        linarith

end RvMWeierstrass
