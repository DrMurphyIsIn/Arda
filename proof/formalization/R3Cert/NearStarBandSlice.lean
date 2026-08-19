import R3Cert.HomogeneousSlice

/-!
  # Near-star band slice of the homogeneous face (master-inequality arc, 2026-08-19)

  `HomogeneousSlice` closes the homogeneous (C-broom) bound `H_C(j) ≤ 1` in the trivial
  zone `μ ≤ 229/1000` using only `F ≤ 1`.  The near-star children `N(0,k)` for `k ≥ 3`
  have `μ = 3/(4k+3) ≤ 3/15 = 0.2`, so they lie in that zone and are already covered.

  This file closes the two near-star children ABOVE the zone — `N(0,1)` (`μ = 3/7`) and
  `N(0,2)` (`μ = 3/11`) — where `F ≤ 1` alone is not enough but the block factor
  `F = B(k) < 1` gives fast tail decay: `H μ F j ≤ W(1+μ)^11 · F^j`, so a handful of
  explicit low-`j` cells plus `F^j ≤ F^{j0}` (`0 ≤ F ≤ 1`, `j ≥ j0`) closes all `j`.
  `N(0,1)`: explicit `j = 0,1,2`, tail `j ≥ 3`.  `N(0,2)`: explicit `j = 0,1`, tail `j ≥ 2`.

  Together with `HomogeneousSlice` (`k ≥ 3`) and the arm (`R(s)`, `NearStar.lean`), this
  closes the homogeneous face for the ENTIRE near-star/arm tight set.  The remaining open
  piece is the generic non-near-star band — the master-inequality crux.  All in `ℚ`, no
  `rpow`.  conjecture1_proved = False.
-/

namespace R3Cert.HomogeneousSlice

/-- Arm factor `W²(3/2)^11 = 486/529`. -/
def armF : ℚ := 486 / 529

/-- Near-star `N(0,k)` cavity message `3/(4k+3)`. -/
def nsMu (k : ℕ) : ℚ := 3 / (4 * (k : ℚ) + 3)

/-- Near-star `N(0,k)` block factor `B(k) = W · ((4k+3)/(3(k+1)))^11 · arm^k`. -/
def nsF (k : ℕ) : ℚ := W * ((4 * (k : ℚ) + 3) / (3 * ((k : ℚ) + 1))) ^ 11 * armF ^ k

/-- Tail bound: `H μ F j ≤ W(1+μ)^11 · F^j` — the amplitude never exceeds the message. -/
lemma H_le_tail (μ F : ℚ) (hμ : 0 ≤ μ) (j : ℕ) :
    H μ F j ≤ W * (1 + μ) ^ 11 * F ^ j := by
  have hfrac : (j : ℚ) * μ / ((j : ℚ) + 1) ≤ μ := frac_mul_le μ hμ j
  have hfrac0 : (0 : ℚ) ≤ (j : ℚ) * μ / ((j : ℚ) + 1) := by positivity
  have hbase0 : (0 : ℚ) ≤ 1 + (j : ℚ) * μ / ((j : ℚ) + 1) := by linarith
  have hbase : 1 + (j : ℚ) * μ / ((j : ℚ) + 1) ≤ 1 + μ := by linarith
  have hpow : (1 + (j : ℚ) * μ / ((j : ℚ) + 1)) ^ 11 ≤ (1 + μ) ^ 11 :=
    pow_le_pow_left₀ hbase0 hbase 11
  have hW : (0 : ℚ) ≤ W := by norm_num [W]
  have hFj : (0 : ℚ) ≤ F ^ j := by positivity
  calc H μ F j = W * (1 + (j : ℚ) * μ / ((j : ℚ) + 1)) ^ 11 * F ^ j := rfl
    _ ≤ W * (1 + μ) ^ 11 * F ^ j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hW) hFj

set_option maxHeartbeats 1000000 in
/-- Homogeneous face for the near-star child `N(0,1)` (`μ = 3/7`, above the trivial zone). -/
theorem H_nearStar_one (j : ℕ) : H (nsMu 1) (nsF 1) j ≤ 1 := by
  have hμ : (0 : ℚ) ≤ nsMu 1 := by norm_num [nsMu]
  have hF0 : (0 : ℚ) ≤ nsF 1 := by norm_num [nsF, armF, W]
  have hF1 : nsF 1 ≤ 1 := by norm_num [nsF, armF, W]
  rcases lt_or_ge j 3 with hj | hj
  · interval_cases j <;> norm_num [H, nsMu, nsF, armF, W]
  · calc H (nsMu 1) (nsF 1) j
        ≤ W * (1 + nsMu 1) ^ 11 * (nsF 1) ^ j := H_le_tail _ _ hμ j
      _ ≤ W * (1 + nsMu 1) ^ 11 * (nsF 1) ^ 3 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_right_of_le_one hF0 hF1 hj)
          norm_num [nsMu, nsF, armF, W]
      _ ≤ 1 := by norm_num [nsMu, nsF, armF, W]

set_option maxHeartbeats 1000000 in
/-- Homogeneous face for the near-star child `N(0,2)` (`μ = 3/11`, above the trivial zone). -/
theorem H_nearStar_two (j : ℕ) : H (nsMu 2) (nsF 2) j ≤ 1 := by
  have hμ : (0 : ℚ) ≤ nsMu 2 := by norm_num [nsMu]
  have hF0 : (0 : ℚ) ≤ nsF 2 := by norm_num [nsF, armF, W]
  have hF1 : nsF 2 ≤ 1 := by norm_num [nsF, armF, W]
  rcases lt_or_ge j 2 with hj | hj
  · interval_cases j <;> norm_num [H, nsMu, nsF, armF, W]
  · calc H (nsMu 2) (nsF 2) j
        ≤ W * (1 + nsMu 2) ^ 11 * (nsF 2) ^ j := H_le_tail _ _ hμ j
      _ ≤ W * (1 + nsMu 2) ^ 11 * (nsF 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_right_of_le_one hF0 hF1 hj)
          norm_num [nsMu, nsF, armF, W]
      _ ≤ 1 := by norm_num [nsMu, nsF, armF, W]

end R3Cert.HomogeneousSlice
