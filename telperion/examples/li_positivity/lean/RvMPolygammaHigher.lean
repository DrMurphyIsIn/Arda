/-
RvMPolygammaHigher — Phase 4a proper: higher polygamma values via the power-series derivative.

Builds the derivative engine for the Hurwitz-type power series and iterates it to the polygamma
formula:
  * `hasDerivAt_P` — for `p ≥ 2`, `d/ds ∑'_k 1/(s+k)^p = −p·∑'_k 1/(s+k)^(p+1)` (as `HasDerivAt`,
    so it also witnesses differentiability).
  * `iteratedDeriv_digamma` — `iteratedDeriv m digamma s = (−1)^(m+1)·m!·∑'_k 1/(s+k)^(m+1)` (m ≥ 1).

conjecture1_proved = False.
-/
import Mathlib
import RvMPolygamma

open Complex Filter Topology

namespace RvMWeierstrass

set_option maxHeartbeats 4000000 in
/-- **Power-series derivative engine.**  For `p ≥ 2` and `s` off the non-positive integers,
    `d/ds ∑'_k 1/(s+k)^p = −p·∑'_k 1/(s+k)^(p+1)` (stated as `HasDerivAt`). -/
theorem hasDerivAt_P {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    HasDerivAt (fun z : ℂ => ∑' k : ℕ, 1 / (z + (k : ℂ)) ^ p)
      (-(p : ℂ) * ∑' k : ℕ, 1 / (s + (k : ℂ)) ^ (p + 1)) s := by
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_norm_add hs
  set A : ℝ := ‖s‖ + ε / 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set D : ℝ := max 2 (2 * (2 * A + 3) / ε) with hD
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  set G : ℕ → ℂ → ℂ := fun k z => 1 / (z + (k : ℂ)) ^ p with hG
  set U : Set ℂ := Metric.ball s (ε / 2) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hsU : s ∈ U := by rw [hU, Metric.mem_ball, dist_self]; positivity
  -- term derivative:  d/dz 1/(z+k)^p = -p/(s+k)^(p+1)
  have hterm : ∀ k : ℕ, HasDerivAt (G k) (-(p : ℂ) / (s + (k : ℂ)) ^ (p + 1)) s := by
    intro k
    have hne : s + (k : ℂ) ≠ 0 := hs k
    have hbase : HasDerivAt (fun z : ℂ => z + (k : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).add_const (k : ℂ)
    have hfun : (fun z : ℂ => ((z + (k : ℂ)) ^ p)⁻¹) = G k := by funext z; simp only [hG, one_div]
    have hval : -((p : ℂ) * (s + (k : ℂ)) ^ (p - 1) * 1) / ((s + (k : ℂ)) ^ p) ^ 2
        = -(p : ℂ) / (s + (k : ℂ)) ^ (p + 1) := by
      rw [mul_one]
      have hpow2 : ((s + (k : ℂ)) ^ p) ^ 2 = (s + (k : ℂ)) ^ (p + 1) * (s + (k : ℂ)) ^ (p - 1) := by
        rw [← pow_add, ← pow_mul]; congr 1; omega
      rw [hpow2, show -((p : ℂ) * (s + (k : ℂ)) ^ (p - 1)) = -(p : ℂ) * (s + (k : ℂ)) ^ (p - 1)
          by ring, mul_div_mul_right _ _ (pow_ne_zero (p - 1) hne)]
    rw [← hval, ← hfun]
    exact (hbase.pow p).inv (by simpa using pow_ne_zero p hne)
  -- linear lower bound  (k+1) ≤ D·‖z+k‖  on U
  have hklow : ∀ k : ℕ, ∀ z ∈ U, (k : ℝ) + 1 ≤ D * ‖z + (k : ℂ)‖ := by
    intro k z hz
    rw [hU, Metric.mem_ball, dist_eq_norm] at hz
    have heps : ε / 2 ≤ ‖z + (k : ℂ)‖ := by
      have h3 := norm_sub_norm_le (s + (k : ℂ)) (s - z)
      have heq : (s + (k : ℂ)) - (s - z) = z + (k : ℂ) := by ring
      rw [heq, norm_sub_rev] at h3
      linarith [hbound k]
    have hzle : ‖z‖ ≤ A := by
      have := norm_sub_norm_le z s; rw [hA]; linarith
    have hgrow : (k : ℝ) - A ≤ ‖z + (k : ℂ)‖ := by
      have h3 := norm_sub_norm_le ((k : ℂ)) (-z)
      have heq : ((k : ℂ)) - (-z) = z + (k : ℂ) := by ring
      rw [norm_neg, heq, Complex.norm_natCast] at h3
      linarith
    rcases lt_or_ge (k : ℝ) (2 * A + 2) with hk | hk
    · have hDge : 2 * (2 * A + 3) / ε ≤ D := le_max_right _ _
      have hDe : 2 * (2 * A + 3) ≤ D * ε := by
        rw [show 2 * (2 * A + 3) = 2 * (2 * A + 3) / ε * ε by field_simp]
        exact mul_le_mul_of_nonneg_right hDge hε.le
      nlinarith [mul_le_mul_of_nonneg_left heps hDpos.le, hk, hApos, hDe, hε]
    · have hD2 : (2 : ℝ) ≤ D := le_max_left _ _
      nlinarith [mul_le_mul_of_nonneg_left hgrow hDpos.le, hk, hD2, hApos]
  have hUne : ∀ k : ℕ, ∀ z ∈ U, z + (k : ℂ) ≠ 0 := by
    intro k z hz
    have h := hklow k z hz
    have : (0 : ℝ) < ‖z + (k : ℂ)‖ := by nlinarith [Nat.cast_nonneg (α := ℝ) k, hDpos, norm_nonneg (z + (k : ℂ))]
    exact norm_pos_iff.mp this
  -- uniform bound  ‖G k z‖ ≤ Dᵖ/(k+1)ᵖ
  have hGle : ∀ k : ℕ, ∀ z ∈ U, ‖G k z‖ ≤ D ^ p / ((k : ℝ) + 1) ^ p := by
    intro k z hz
    have hkl := hklow k z hz
    have hzk : (0 : ℝ) < ‖z + (k : ℂ)‖ := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k, hDpos, norm_nonneg (z + (k : ℂ))]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hinv_le : 1 / ‖z + (k : ℂ)‖ ≤ D / ((k : ℝ) + 1) := by
      rw [div_le_div_iff₀ hzk hk1]; linarith
    have hGval : ‖G k z‖ = (1 / ‖z + (k : ℂ)‖) ^ p := by
      rw [hG, norm_div, norm_one, norm_pow, div_pow, one_pow]
    rw [hGval]
    calc (1 / ‖z + (k : ℂ)‖) ^ p ≤ (D / ((k : ℝ) + 1)) ^ p :=
          pow_le_pow_left₀ (by positivity) hinv_le p
      _ = D ^ p / ((k : ℝ) + 1) ^ p := by rw [div_pow]
  have hu : Summable (fun k : ℕ => D ^ p / ((k : ℝ) + 1) ^ p) := by
    have h := (summable_pow_div_add (D ^ p) p 1 (by omega)).of_norm
    simpa [Nat.cast_one] using h
  have hfdiff : ∀ k : ℕ, DifferentiableOn ℂ (G k) U := by
    intro k z hz
    have hne : z + (k : ℂ) ≠ 0 := hUne k z hz
    have : DifferentiableAt ℂ (G k) z := by
      simp only [hG, one_div]
      exact (((differentiableAt_id.add_const _).pow p).inv (pow_ne_zero p hne))
    exact this.differentiableWithinAt
  have hSderiv : HasSum (fun k : ℕ => deriv (G k) s) (deriv (fun z => ∑' k : ℕ, G k z) s) :=
    hasSum_deriv_of_summable_norm hu hfdiff hUopen hGle hsU
  have hSdiff : DifferentiableOn ℂ (fun z => ∑' k : ℕ, G k z) U :=
    differentiableOn_tsum_of_summable_norm hu hfdiff hUopen hGle
  have hPderiv : HasDerivAt (fun z => ∑' k : ℕ, G k z) (deriv (fun z => ∑' k : ℕ, G k z) s) s :=
    (hSdiff.differentiableAt (hUopen.mem_nhds hsU)).hasDerivAt
  have hval : deriv (fun z => ∑' k : ℕ, G k z) s = -(p : ℂ) * ∑' k : ℕ, 1 / (s + (k : ℂ)) ^ (p + 1) := by
    rw [← hSderiv.tsum_eq]
    simp only [fun k => (hterm k).deriv]
    rw [← tsum_mul_left]
    congr 1; funext k; rw [mul_one_div]
  rw [← hval]
  exact hPderiv

set_option maxHeartbeats 1000000 in
/-- **The polygamma values.**  For `m ≥ 1` and `s` off the non-positive integers,
    `iteratedDeriv m digamma s = (−1)^(m+1)·m!·∑'_k 1/(s+k)^(m+1)`. -/
theorem iteratedDeriv_digamma : ∀ (m : ℕ), 1 ≤ m → ∀ {s : ℂ}, (∀ j : ℕ, s + (j : ℂ) ≠ 0) →
    iteratedDeriv m Complex.digamma s
      = (-1) ^ (m + 1) * (m.factorial : ℂ) * ∑' k : ℕ, 1 / (s + (k : ℂ)) ^ (m + 1) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by norm_num)
  | succ n ih =>
    intro _ s hs
    rw [iteratedDeriv_succ]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- base case n = 0: deriv digamma = ∑ 1/(s+k)^2
      subst hn0
      rw [iteratedDeriv_zero, deriv_digamma_eq_tsum hs]
      norm_num
    · -- inductive step: differentiate iteratedDeriv n digamma = c · P (n+1)
      have hnbhd : iteratedDeriv n Complex.digamma
          =ᶠ[𝓝 s] fun z => (-1) ^ (n + 1) * (n.factorial : ℂ)
              * ∑' k : ℕ, 1 / (z + (k : ℂ)) ^ (n + 1) := by
        filter_upwards [poleCompl_mem_nhds hs] with z hz using ih hnpos hz
      have hP : HasDerivAt (fun z => ∑' k : ℕ, 1 / (z + (k : ℂ)) ^ (n + 1))
          (-((n : ℂ) + 1) * ∑' k : ℕ, 1 / (s + (k : ℂ)) ^ (n + 1 + 1)) s := by
        have := hasDerivAt_P (p := n + 1) (by omega) hs
        simpa using this
      have hcmul : HasDerivAt (fun z => (-1) ^ (n + 1) * (n.factorial : ℂ)
          * ∑' k : ℕ, 1 / (z + (k : ℂ)) ^ (n + 1))
          ((-1) ^ (n + 1) * (n.factorial : ℂ)
            * (-((n : ℂ) + 1) * ∑' k : ℕ, 1 / (s + (k : ℂ)) ^ (n + 1 + 1))) s := by
        simpa [mul_assoc] using hP.const_mul ((-1) ^ (n + 1) * (n.factorial : ℂ))
      rw [(hnbhd.hasDerivAt_iff.mpr hcmul).deriv]
      rw [Nat.factorial_succ]
      push_cast
      ring
