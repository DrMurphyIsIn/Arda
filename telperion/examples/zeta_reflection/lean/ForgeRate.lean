/-  ForgeRate.lean -- ANDÚRIL cert-forge: a TIGHT rate bound for imLnVal, unlocking small n₀.

    ThetaConverge.rate_obligation gives `|Λ − imLnVal x y n| ≤ C/n` with the CRUDE
    `C = 2(|y|(x+1) + |y|³/3)` (≈246 at y=7) — because it bounds the arctan cubic residual
    `|u − arctan u| ≤ |u|³/3` by `|y|³/(3m²)`, dropping a factor `1/m`.  The residual is really
    `O(1/m³)`, so for the RATE (a tail `Σ_{m≥n}`) the cubic term contributes `O(1/n²)`, negligible
    next to the `O(1/n)` `hfirst` term `|y|(x+1)/m²`.

    This file re-derives the increment bound keeping the extra `1/m` on the cube term, valid for
    `m ≥ n₀`:  `|Δ_m| ≤ (|y|(x+1) + |y|³/(3 n₀)) / m²`, then reuses the telescope + `sum_Ico_inv_sq_bound`
    machinery to get `|Λ − imLnVal x y n₀| ≤ 2(|y|(x+1) + |y|³/(3 n₀)) / n₀` — the SHARP rate (≈0.09 at
    n₀=200, y=7), the φ-box halfwidth the θ instrument needs.  Reuses ThetaConverge lemmas verbatim.

    conjecture1_proved = False.
-/
import ThetaConverge

open Real Filter Topology ThetaGap

namespace ForgeRate

/-- **Tight increment bound** (valid for `m ≥ n₀ ≥ 1`).  Keeps the extra `1/m` on the arctan cube
    residual, bounded by `1/n₀`:  `|Δ_m| ≤ (|y|(x+1) + |y|³/(3 n₀)) / m²`. -/
theorem incr_bound_tight (x y : ℝ) (hx : 0 < x) (n₀ m : ℕ) (hn₀ : 1 ≤ n₀) (hm : n₀ ≤ m) :
    |y * Real.log (1 + 1/(m:ℝ)) - Real.arctan (y/(x + (m:ℝ) + 1))|
      ≤ (|y| * (x+1) + |y| ^3/(3*(n₀:ℝ))) / (m:ℝ)^2 := by
  have hm1 : 1 ≤ m := le_trans hn₀ hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
  have hn₀pos : (0:ℝ) < n₀ := by exact_mod_cast hn₀
  have hn₀m : (n₀:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  set u : ℝ := y/(x + (m:ℝ) + 1) with hu_def
  have hden : (0:ℝ) < x + (m:ℝ) + 1 := by positivity
  -- hfirst (verbatim from ThetaConverge.incr_bound): |y log(1+1/m) − u| ≤ |y|(x+1)/m².
  have hlog_up : Real.log (1 + 1/(m:ℝ)) ≤ 1/(m:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := 1 + 1/(m:ℝ)) (by positivity); linarith
  have hlog_lo : 1/((m:ℝ)+1) ≤ Real.log (1 + 1/(m:ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (x := 1/(1 + 1/(m:ℝ))) (by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub] at h
    have he : 1/(1 + 1/(m:ℝ)) = (m:ℝ)/((m:ℝ)+1) := by field_simp
    rw [he] at h
    have h2 : (m:ℝ)/((m:ℝ)+1) - 1 = -(1/((m:ℝ)+1)) := by field_simp; ring
    rw [h2] at h; linarith
  set P : ℝ := Real.log (1 + 1/(m:ℝ)) - 1/(x + (m:ℝ) + 1) with hP_def
  have hP_lo : 0 ≤ P := by
    rw [hP_def]
    have : 1/(x + (m:ℝ) + 1) ≤ 1/((m:ℝ)+1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
    linarith
  have hP_hi : P ≤ (x+1)/(m:ℝ)^2 := by
    rw [hP_def]
    have hstep : Real.log (1 + 1/(m:ℝ)) - 1/(x+(m:ℝ)+1) ≤ 1/(m:ℝ) - 1/(x+(m:ℝ)+1) := by linarith
    have hdiff : 1/(m:ℝ) - 1/(x+(m:ℝ)+1) = (x+1)/((m:ℝ)*(x+(m:ℝ)+1)) := by field_simp; ring
    have hbound : (x+1)/((m:ℝ)*(x+(m:ℝ)+1)) ≤ (x+1)/(m:ℝ)^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
    linarith
  have hfirst_eq : y * Real.log (1 + 1/(m:ℝ)) - u = y * P := by rw [hP_def, hu_def]; ring
  have hfirst : |y * Real.log (1 + 1/(m:ℝ)) - u| ≤ |y| * (x+1)/(m:ℝ)^2 := by
    rw [hfirst_eq, abs_mul, abs_of_nonneg hP_lo]
    calc |y| * P ≤ |y| * ((x+1)/(m:ℝ)^2) := mul_le_mul_of_nonneg_left hP_hi (abs_nonneg y)
      _ = |y| * (x+1)/(m:ℝ)^2 := by ring
  have hu_abs : |u| ≤ |y|/(m:ℝ) := by
    rw [hu_def, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_left (abs_nonneg y) (by positivity); linarith
  -- TIGHT cube: |u−arctan u| ≤ |u|³/3 ≤ |y|³/(3m³) ≤ |y|³/(3 n₀ m²)  (using m ≥ n₀).
  have hsecond : |u - Real.arctan u| ≤ |y| ^3/(3*(n₀:ℝ)*(m:ℝ)^2) := by
    have hpow : |u| ^3 ≤ (|y|/(m:ℝ))^3 := pow_le_pow_left₀ (abs_nonneg u) hu_abs 3
    have h2 : (|y|/(m:ℝ))^3 = |y| ^3/(m:ℝ)^3 := by rw [div_pow]
    rw [h2] at hpow
    have hm3 : |y| ^3/(m:ℝ)^3/3 ≤ |y| ^3/(3*(n₀:ℝ)*(m:ℝ)^2) := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      -- 3 n₀ m² ≤ m³·3  ⇐  n₀ ≤ m
      nlinarith [hn₀m, sq_nonneg ((m:ℝ)), hmpos, hn₀pos]
    calc |u - Real.arctan u| = |Real.arctan u - u| := by rw [abs_sub_comm]
      _ ≤ |u| ^3/3 := ThetaConverge.arctan_sub_self_abs u
      _ ≤ |y| ^3/(m:ℝ)^3/3 := by linarith [hpow]
      _ ≤ |y| ^3/(3*(n₀:ℝ)*(m:ℝ)^2) := hm3
  have hsplit : y * Real.log (1 + 1/(m:ℝ)) - Real.arctan u
      = (y * Real.log (1 + 1/(m:ℝ)) - u) + (u - Real.arctan u) := by ring
  calc |y * Real.log (1 + 1/(m:ℝ)) - Real.arctan u|
      = |(y * Real.log (1 + 1/(m:ℝ)) - u) + (u - Real.arctan u)| := by rw [hsplit]
    _ ≤ |y * Real.log (1 + 1/(m:ℝ)) - u| + |u - Real.arctan u| := abs_add_le _ _
    _ ≤ |y| * (x+1)/(m:ℝ)^2 + |y| ^3/(3*(n₀:ℝ)*(m:ℝ)^2) := add_le_add hfirst hsecond
    _ = (|y| * (x+1) + |y| ^3/(3*(n₀:ℝ))) / (m:ℝ)^2 := by field_simp

/-- **Tight finite tail.**  `|imLnVal x y N − imLnVal x y n₀| ≤ 2 B' / n₀`, `B' = |y|(x+1)+|y|³/(3n₀)`,
    for `N ≥ n₀ ≥ 1`.  Telescope + `incr_bound_tight` (valid since every `m ∈ [n₀,N)` has `m ≥ n₀`). -/
theorem finite_tail_tight (x y : ℝ) (hx : 0 < x) (n₀ N : ℕ) (hn₀ : 1 ≤ n₀) (hn₀N : n₀ ≤ N) :
    |imLnVal x y N - imLnVal x y n₀|
      ≤ 2*(|y| * (x+1) + |y| ^3/(3*(n₀:ℝ)))/(n₀:ℝ) := by
  set B' : ℝ := |y| * (x+1) + |y| ^3/(3*(n₀:ℝ)) with hB'
  have hn₀pos : (0:ℝ) < n₀ := by exact_mod_cast hn₀
  have hB'nn : 0 ≤ B' := by rw [hB']; positivity
  have htel : imLnVal x y N - imLnVal x y n₀
      = ∑ m ∈ Finset.Ico n₀ N, (imLnVal x y (m+1) - imLnVal x y m) :=
    (Finset.sum_Ico_sub _ hn₀N).symm
  rw [htel]
  calc |∑ m ∈ Finset.Ico n₀ N, (imLnVal x y (m+1) - imLnVal x y m)|
      ≤ ∑ m ∈ Finset.Ico n₀ N, |imLnVal x y (m+1) - imLnVal x y m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ico n₀ N, B'/(m:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Ico] at hm
        have hm1 : 1 ≤ m := le_trans hn₀ hm.1
        rw [ThetaConverge.imLnVal_succ_sub x y m hm1]
        exact incr_bound_tight x y hx n₀ m hn₀ hm.1
    _ = B' * ∑ m ∈ Finset.Ico n₀ N, (1:ℝ)/(m:ℝ)^2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; rw [mul_one_div]
    _ ≤ B' * (2/(n₀:ℝ)) := mul_le_mul_of_nonneg_left (ThetaConverge.sum_Ico_inv_sq_bound n₀ N hn₀) hB'nn
    _ = 2*B'/(n₀:ℝ) := by ring

/-- **Tight rate at an operating order `n₀`.**  Given the limit `Λ` of `imLnVal x y`, the partial value
    at `n₀` is within `2 B'/n₀` (`B' = |y|(x+1)+|y|³/(3n₀)`) of `Λ`.  This is the SHARP φ-box halfwidth. -/
theorem rate_at (x y : ℝ) (hx : 0 < x) (Λ : ℝ)
    (hΛ : Filter.Tendsto (imLnVal x y) Filter.atTop (nhds Λ)) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) :
    |Λ - imLnVal x y n₀| ≤ 2*(|y| * (x+1) + |y| ^3/(3*(n₀:ℝ)))/(n₀:ℝ) := by
  have h1 : Filter.Tendsto (fun N => |imLnVal x y N - imLnVal x y n₀|) Filter.atTop
      (nhds |Λ - imLnVal x y n₀|) := by
    have := (hΛ.sub_const (imLnVal x y n₀)).abs; simpa using this
  apply le_of_tendsto h1
  filter_upwards [eventually_ge_atTop n₀] with N hN
  exact finite_tail_tight x y hx n₀ N hn₀ hN

end ForgeRate
