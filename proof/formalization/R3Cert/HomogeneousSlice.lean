import Mathlib

/-!
  # Homogeneous-face slice: the trivial-zone proof (master-inequality arc, 2026-08-19)

  The near-star half of the Brualdi–Goldwasser step reduces to the homogeneous
  (C-broom) bound `H_C(j) = W (1 + j μ/(j+1))^11 F^j ≤ 1`, `W = 64/621`, for every
  real block `C` with cavity message `μ` and F-factor `F` (`0 ≤ F ≤ 1`, the latter
  being `phi_le_one`).  The C-broom (`j` copies of a real block `C`) is itself a
  real tree, so this bound is BG restricted to symmetric hubs.

  This file kernel-checks the FIRST PROVEN slice of that face: for `μ` in the
  trivial zone `W (1+μ)^11 ≤ 1` — i.e. `μ ≤ (621/64)^{1/11} − 1 ≈ 0.2295`, rational
  witness `229/1000` — the bound holds using ONLY `F ≤ 1`, because `j μ/(j+1) ≤ μ`
  and `F^j ≤ 1`.  This disposes of the entire small-μ tail (incl. the `m = 1/15`
  envelope-killer) with no envelope.  It is the EASY piece: the tight point (arm,
  `μ = 1/3`) sits above the zone, so the summit stays open in `(μ0, 1]`.  Entirely
  in `ℚ` (natural-power exponents; no `rpow`).  conjecture1_proved = False.
-/

namespace R3Cert.HomogeneousSlice

/-- Base constant `W = ρ_B^{-11}` numerology, `64/621`. -/
def W : ℚ := 64 / 621

/-- The homogeneous (C-broom) hub factor: `j` copies of a block `(μ, F)`. -/
def H (μ F : ℚ) (j : ℕ) : ℚ := W * (1 + (j : ℚ) * μ / ((j : ℚ) + 1)) ^ 11 * F ^ j

/-- `j μ/(j+1) ≤ μ` for `0 ≤ μ` — the amplitude never exceeds the message. -/
lemma frac_mul_le (μ : ℚ) (hμ : 0 ≤ μ) (j : ℕ) :
    (j : ℚ) * μ / ((j : ℚ) + 1) ≤ μ := by
  have hden : (0 : ℚ) < (j : ℚ) + 1 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [hμ, (by positivity : (0 : ℚ) ≤ (j : ℚ))]

/-- **Proven slice.** In the trivial zone `W (1+μ)^11 ≤ 1`, every homogeneous hub
    factor is `≤ 1`, using only `0 ≤ F ≤ 1` (= `phi_le_one`). -/
theorem H_le_one {μ F : ℚ} (hμ : 0 ≤ μ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hthr : W * (1 + μ) ^ 11 ≤ 1) (j : ℕ) : H μ F j ≤ 1 := by
  have hfrac : (j : ℚ) * μ / ((j : ℚ) + 1) ≤ μ := frac_mul_le μ hμ j
  have hfrac0 : (0 : ℚ) ≤ (j : ℚ) * μ / ((j : ℚ) + 1) := by positivity
  have hbase : 1 + (j : ℚ) * μ / ((j : ℚ) + 1) ≤ 1 + μ := by linarith
  have hbase0 : (0 : ℚ) ≤ 1 + (j : ℚ) * μ / ((j : ℚ) + 1) := by linarith
  have hpow : (1 + (j : ℚ) * μ / ((j : ℚ) + 1)) ^ 11 ≤ (1 + μ) ^ 11 :=
    pow_le_pow_left₀ hbase0 hbase 11
  have hFj : F ^ j ≤ 1 := pow_le_one₀ hF0 hF1
  have hFj0 : (0 : ℚ) ≤ F ^ j := by positivity
  have hW : (0 : ℚ) ≤ W := by norm_num [W]
  have hB0 : (0 : ℚ) ≤ (1 + μ) ^ 11 := by positivity
  have hWB0 : (0 : ℚ) ≤ W * (1 + μ) ^ 11 := mul_nonneg hW hB0
  calc H μ F j
      = W * (1 + (j : ℚ) * μ / ((j : ℚ) + 1)) ^ 11 * F ^ j := rfl
    _ ≤ W * (1 + μ) ^ 11 * F ^ j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hW) hFj0
    _ ≤ W * (1 + μ) ^ 11 * 1 := mul_le_mul_of_nonneg_left hFj hWB0
    _ = W * (1 + μ) ^ 11 := by ring
    _ ≤ 1 := hthr

/-- Rational witness that the trivial zone is nonempty up to `229/1000`
    (`W (1229/1000)^11 = 0.99577… ≤ 1`). -/
theorem thr_witness : W * (1 + 229 / 1000) ^ 11 ≤ 1 := by norm_num [W]

/-- Consequence: for `0 ≤ μ ≤ 229/1000` the homogeneous bound holds for every
    real block, unconditionally (only `0 ≤ F ≤ 1`). -/
theorem H_le_one_of_muLe {μ F : ℚ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 229 / 1000)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (j : ℕ) : H μ F j ≤ 1 := by
  refine H_le_one hμ0 hF0 hF1 ?_ j
  calc W * (1 + μ) ^ 11
      ≤ W * (1 + 229 / 1000) ^ 11 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith) (by linarith) 11) (by norm_num [W])
    _ ≤ 1 := thr_witness

end R3Cert.HomogeneousSlice
