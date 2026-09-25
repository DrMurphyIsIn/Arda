/-  RSSeam_B3Bound.lean -- lane SEAM: the C0-corrected Riemann-Siegel remainder bound with a LOWER
    starting height, t >= 509 (saddle variable a = sqrt(t/2pi) >= 9) instead of t >= 10000 (a >= 39).
    Imports `RS_B3Bound` read-only and reuses its lemmas; nothing in lane RS is edited.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0_alpha_seam` : for t >= 509, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase
      phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (13/20) a^(-3/2).
      `rs_remainder_C0_seam` : the same in t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (13/5) t^(-3/4).

    ## What changed against `RS_B3Bound` (the error budget re-run at a >= 9)

      * near/far split of the error integral at |v| = a/3 (was a/9); near the saddle the amplitude
        bound |rsPhi - 1| <= e e^e still applies because |w| = sqrt 2 |v| <= a/2;
      * near: e <= |w| (13/25 + 17/4 |w|^2)/a and e <= 27/5 v^2 + 1/600, so the integrand is
        <= e^{1/600}/(pi a) (13/25 + 17/2 v^2) e^{-7 v^2};
      * far: |integrand| <= 5 e^{-pi a^2/18} e^{-pi v^2/2}, and e^{-x} <= 8!/x^8 at x >= 14;
      * |rsE1 a p| <= (49/200 + 1/200)/a = (1/4)/a for a >= 9 (was (9/50)/a for a >= 39);
      * |rsJ p| <= 4 (unchanged, `RSInt.norm_rsJ_le`); phase term 8|delta| <= 4/(pi a^2) <= (3/20)/a;
      * budget 2 (1/4) + 3/20 = 13/20 in the a-form; (2 pi)^(3/4) <= 4 gives 13/5 in t.

    Untrusted numerics (scratchpad/seam/remainder.py): the true C0-corrected remainder is
    <= 0.121 t^(-3/4) on samples in [200, 10100]; so 13/5 is honest with a ~20x margin.

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/
import RS_B3Bound

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSSeam

open RSInt

/-- Pointwise bound near the saddle point (`|v| <= a/3`), valid for `a >= 9`. -/
theorem norm_E1_integrand_near {a p v : ℝ} (ha : 9 ≤ a) (hv : |v| ≤ a / 3) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) * Real.exp (-7 * v ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hRHS : 0 ≤ Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) *
      Real.exp (-7 * v ^ 2) := by positivity
  rcases eq_or_ne v 0 with rfl | hv0
  · have h0 : rsPhi a ((0 : ℝ) * (1 + I) : ℂ) = 1 := by simp [rsPhi]
    rw [h0, sub_self, mul_zero, zero_mul, norm_zero]
    exact hRHS
  set w : ℂ := (v : ℂ) * (1 + I) with hwdef
  set n : ℝ := ‖w‖ with hn
  have hnv : n = Real.sqrt 2 * |v| := norm_w_eq v
  have hn2 : n ^ 2 = 2 * v ^ 2 := by
    rw [hnv, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
  have hn0 : 0 ≤ n := norm_nonneg _
  have hna : n ≤ a / 2 := by
    rw [hnv]
    calc Real.sqrt 2 * |v| ≤ 3 / 2 * (a / 3) :=
          mul_le_mul sqrt_two_le_three_halves hv (abs_nonneg _) (by norm_num)
      _ = a / 2 := by ring
  have hphi := norm_rsPhi_sub_one_le ha0 (show ‖w‖ ≤ a / 2 by rw [← hn]; exact hna)
  rw [← hn] at hphi
  set ε := n / (2 * a) + n ^ 2 / (2 * a ^ 2) + 4 * π / 3 * n ^ 3 / a with hε
  have hε1 : ε ≤ n * ((13 / 25 + 17 / 2 * v ^ 2) / a) := by
    have hv2 : 17 / 2 * v ^ 2 = 17 / 4 * n ^ 2 := by rw [hn2]; ring
    rw [hv2]
    have e : n * ((13 / 25 + 17 / 4 * n ^ 2) / a) - ε =
        n / a * (1 / 50 + (17 / 4 - 4 * π / 3) * n ^ 2 - n / (2 * a)) := by
      rw [hε]; field_simp; ring
    have h1 : n / (2 * a) ≤ n / 18 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) (by linarith)
    have h2 : (1 / 20 : ℝ) ≤ 17 / 4 - 4 * π / 3 := by linarith [Real.pi_lt_d2]
    have h3 : 0 ≤ 1 / 50 + 1 / 20 * n ^ 2 - n / 18 := by nlinarith [sq_nonneg (n - 5 / 9)]
    have h4 : 1 / 20 * n ^ 2 ≤ (17 / 4 - 4 * π / 3) * n ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg n)
    have h5 : 0 ≤ n / a * (1 / 50 + (17 / 4 - 4 * π / 3) * n ^ 2 - n / (2 * a)) :=
      mul_nonneg (div_nonneg hn0 ha0.le) (by linarith)
    linarith
  have hε2 : ε ≤ 27 / 5 * v ^ 2 + 1 / 600 := by
    have h1 : n / (2 * a) ≤ n / 18 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) (by linarith)
    have e1 : n / (2 * a) ≤ n ^ 2 / 2 + 1 / 648 := by nlinarith [sq_nonneg (n - 1 / 18)]
    have e2 : n ^ 2 / (2 * a ^ 2) ≤ n ^ 2 / 162 :=
      div_le_div_of_nonneg_left (sq_nonneg n) (by norm_num) (by nlinarith)
    have e3 : 4 * π / 3 * n ^ 3 / a ≤ 4 * π / 3 * n ^ 2 / 2 := by
      have h : n ^ 3 / a ≤ n ^ 2 / 2 := by
        rw [div_le_div_iff₀ ha0 (by norm_num)]
        have e : n ^ 3 * 2 = n ^ 2 * (2 * n) := by ring
        rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg n)
      calc 4 * π / 3 * n ^ 3 / a = 4 * π / 3 * (n ^ 3 / a) := by ring
        _ ≤ 4 * π / 3 * (n ^ 2 / 2) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 4 * π / 3 * n ^ 2 / 2 := by ring
    have e4 : 4 * π / 3 * n ^ 2 / 2 ≤ 21 / 10 * n ^ 2 := by
      nlinarith [sq_nonneg n, Real.pi_lt_d2]
    rw [hε]
    have e5 : n ^ 2 / 2 + n ^ 2 / 162 + 21 / 10 * n ^ 2 ≤ 27 / 10 * n ^ 2 := by
      nlinarith [sq_nonneg n]
    have e6 : 27 / 10 * n ^ 2 = 27 / 5 * v ^ 2 := by rw [hn2]; ring
    linarith
  have hexpw : ‖cexp (2 * ↑π * I * w ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) := norm_exp_gauss_diag v
  have him : ((p : ℂ) + w).im = v := by simp [hwdef]
  have hD : 2 * π * |v| ≤ ‖rsD (p + w)‖ := by
    have := norm_rsD_ge_two_pi_im (p + w); rwa [him] at this
  have hvpos : 0 < |v| := abs_pos.mpr hv0
  have hDpos : 0 < 2 * π * |v| := by positivity
  have hΦ : ‖rsPhi a w - 1‖ ≤
      n * ((13 / 25 + 17 / 2 * v ^ 2) / a) * Real.exp (27 / 5 * v ^ 2 + 1 / 600) :=
    hphi.trans (mul_le_mul hε1 (Real.exp_le_exp.mpr hε2) (Real.exp_pos _).le (by positivity))
  have hexp2 : Real.exp (-(4 * π) * v ^ 2) * Real.exp (27 / 5 * v ^ 2 + 1 / 600) =
      Real.exp (1 / 600) * Real.exp (-(4 * π - 27 / 5) * v ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc ‖cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * (rsPhi a w - 1) * (1 + I)‖
      = Real.exp (-(4 * π) * v ^ 2) * ‖rsPhi a w - 1‖ * Real.sqrt 2 / ‖rsD (p + w)‖ := by
        rw [norm_mul, norm_mul, norm_div, hexpw, norm_one_add_I]; ring
    _ ≤ Real.exp (-(4 * π) * v ^ 2) * (n * ((13 / 25 + 17 / 2 * v ^ 2) / a) *
          Real.exp (27 / 5 * v ^ 2 + 1 / 600)) * Real.sqrt 2 / (2 * π * |v|) := by
        gcongr
    _ = (Real.exp (-(4 * π) * v ^ 2) * Real.exp (27 / 5 * v ^ 2 + 1 / 600)) *
          (Real.sqrt 2 * Real.sqrt 2) * (13 / 25 + 17 / 2 * v ^ 2) / (2 * π * a) *
          (|v| / |v|) := by
        rw [hnv]; field_simp
    _ = Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) *
          Real.exp (-(4 * π - 27 / 5) * v ^ 2) := by
        rw [hexp2, hss, div_self hvpos.ne']; field_simp
    _ ≤ Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) * Real.exp (-7 * v ^ 2) := by
        gcongr
        nlinarith [Real.pi_gt_d2, sq_nonneg v]

/-- Pointwise bound away from the saddle point (`|v| >= a/3`), valid for `a >= 9`. -/
theorem norm_E1_integrand_far {a p v : ℝ} (ha : 9 ≤ a) (hv : a / 3 ≤ |v|) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2) := by
  have ha0 : 0 < a := by linarith
  set w : ℂ := (v : ℂ) * (1 + I) with hwdef
  have him : ((p : ℂ) + w).im = v := by simp [hwdef]
  have hv1 : 1 ≤ |v| := by linarith
  have hD : 1 ≤ ‖rsD (p + w)‖ := one_le_norm_rsD (by rw [him]; exact hv1)
  have hexpw : ‖cexp (2 * ↑π * I * w ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) := norm_exp_gauss_diag v
  have hG := norm_gauss_rsPhi_le ha0 v
  have hnum : ‖cexp (2 * ↑π * I * w ^ 2) * (rsPhi a w - 1)‖ ≤ 3 * Real.exp (-(π * v ^ 2)) := by
    rw [mul_sub, mul_one]
    have h4 : Real.exp (-(4 * π) * v ^ 2) ≤ Real.exp (-(π * v ^ 2)) := by
      apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, sq_nonneg v]
    calc _ ≤ ‖cexp (2 * ↑π * I * w ^ 2) * rsPhi a w‖ + ‖cexp (2 * ↑π * I * w ^ 2)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * Real.exp (-(π * v ^ 2)) + Real.exp (-(π * v ^ 2)) := by
          rw [hexpw]; exact add_le_add hG h4
      _ = 3 * Real.exp (-(π * v ^ 2)) := by ring
  have hsplit : Real.exp (-(π * v ^ 2)) ≤
      Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have : (a / 3) ^ 2 ≤ v ^ 2 := by
      rw [← sq_abs v]; exact pow_le_pow_left₀ (by positivity) hv 2
    nlinarith [Real.pi_pos]
  calc ‖cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * (rsPhi a w - 1) * (1 + I)‖
      = ‖cexp (2 * ↑π * I * w ^ 2) * (rsPhi a w - 1)‖ * Real.sqrt 2 / ‖rsD (p + w)‖ := by
        simp only [norm_mul, norm_div]; rw [norm_one_add_I]; ring
    _ ≤ 3 * Real.exp (-(π * v ^ 2)) * (3 / 2) / 1 := by
        gcongr
        exact sqrt_two_le_three_halves
    _ ≤ 5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2) := by
        have := Real.exp_pos (-(π * v ^ 2))
        rw [div_one]; nlinarith

/-- **The error integral at `a >= 9`.** -/
theorem norm_rsE1_le {a p : ℝ} (ha : 9 ≤ a) :
    ‖rsE1 a p‖ ≤ Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
      Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) := by
  have ha0 : 0 < a := by linarith
  set K₁ := Real.exp (1 / 600) / (π * a) with hK₁
  set K₂ := 5 * Real.exp (-(π * a ^ 2 / 18)) with hK₂
  have hi1 : Integrable (fun v : ℝ => Real.exp (-7 * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hi2 : Integrable (fun v : ℝ => v ^ 2 * Real.exp (-7 * v ^ 2)) :=
    integrable_sq_mul_exp_neg_mul_sq (by norm_num)
  have hi3 : Integrable (fun v : ℝ => Real.exp (-(π / 2) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hint : Integrable (fun v : ℝ => K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
      K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) + K₂ * Real.exp (-(π / 2) * v ^ 2)) :=
    ((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hpt : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) /
      rsD (p + (v : ℂ) * (1 + I)) * (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
        K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) + K₂ * Real.exp (-(π / 2) * v ^ 2) := by
    intro v
    have h1 : 0 ≤ K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
        K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) := by positivity
    have h2 : 0 ≤ K₂ * Real.exp (-(π / 2) * v ^ 2) := by positivity
    rcases le_total |v| (a / 3) with hv | hv
    · have := norm_E1_integrand_near (p := p) ha hv
      have e : K₁ * (13 / 25 + 17 / 2 * v ^ 2) * Real.exp (-7 * v ^ 2) =
          K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
            K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) := by ring
      rw [← hK₁, e] at this
      linarith
    · have := norm_E1_integrand_far (p := p) ha hv
      rw [← hK₂] at this
      linarith
  have hA : Integrable (fun v : ℝ => K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
      K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2))) := (hi1.const_mul _).add (hi2.const_mul _)
  have hB1 : Integrable (fun v : ℝ => K₁ * (13 / 25) * Real.exp (-7 * v ^ 2)) := hi1.const_mul _
  have hB2 : Integrable (fun v : ℝ => K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2))) :=
    hi2.const_mul _
  have hB3 : Integrable (fun v : ℝ => K₂ * Real.exp (-(π / 2) * v ^ 2)) := hi3.const_mul _
  unfold rsE1 lineUp
  simp only [ofReal_zero, zero_add]
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)) (le_of_eq ?_)
  rw [integral_add hA hB3, integral_add hB1 hB2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gaussian, integral_sq_mul_exp_neg_mul_sq (by norm_num),
    integral_gaussian]

/-- Numerics: for `a >= 9` the right side of `norm_rsE1_le` is at most `(1/4)/a`. -/
theorem E1_const_le {a : ℝ} (ha : 9 ≤ a) :
    Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
      Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 1 / 4 / a := by
  have ha0 : 0 < a := by linarith
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d4
  have he : Real.exp (1 / 600) ≤ 600 / 599 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 600) (by norm_num) (by norm_num)
    have e : (1 : ℝ) / (1 - 1 / 600) = 600 / 599 := by norm_num
    linarith
  have hs : Real.sqrt (π / 7) ≤ 67 / 100 := by
    calc Real.sqrt (π / 7) ≤ Real.sqrt ((67 / 100) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 67 / 100 := Real.sqrt_sq (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (π / 7) := Real.sqrt_nonneg _
  have hT12 : Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
      Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) ≤
      49 / 200 / a := by
    have e : Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
        Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) =
        (Real.exp (1 / 600) * Real.sqrt (π / 7) * (789 / 700) / π) / a := by
      field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ ha0.le
    rw [div_le_iff₀ Real.pi_pos]
    have := mul_le_mul he hs hs0 (by norm_num)
    nlinarith
  have hT3 : 5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 1 / 200 / a := by
    set x := π * a ^ 2 / 18 with hx
    have ha2 : 81 ≤ a ^ 2 := by nlinarith
    have hx14 : 14 ≤ x := by
      rw [hx, le_div_iff₀ (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_right hpi1.le (sq_nonneg a)]
    have hax : a ≤ x := by
      have h28 : 28 ≤ π * a := by nlinarith
      rw [hx]
      nlinarith
    have hexp : Real.exp (-x) ≤ 40320 / x ^ 8 := by
      rw [Real.exp_neg]
      have h8 := Real.pow_div_factorial_le_exp x (by linarith) 8
      have hpos : 0 < x ^ 8 / (Nat.factorial 8) := by positivity
      calc (Real.exp x)⁻¹ ≤ (x ^ 8 / (Nat.factorial 8))⁻¹ := inv_anti₀ hpos h8
        _ = 40320 / x ^ 8 := by norm_num [Nat.factorial]
    have hs2 : Real.sqrt (π / (π / 2)) = Real.sqrt 2 := by
      congr 1; field_simp
    rw [hs2, le_div_iff₀ ha0]
    have hx0 : 0 < x := by linarith
    calc 5 * Real.exp (-x) * Real.sqrt 2 * a ≤ 5 * (40320 / x ^ 8) * (3 / 2) * x := by
          gcongr
          exact sqrt_two_le_three_halves
      _ = 302400 / x ^ 7 := by field_simp; ring
      _ ≤ 1 / 200 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have : (14 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx14 7
          nlinarith
  calc _ ≤ 49 / 200 / a + 1 / 200 / a := add_le_add hT12 hT3
    _ = 1 / 4 / a := by ring

/-! ## The explicit C0 remainder bound from t >= 509 -/

theorem rsAlpha_ge_9 {t : ℝ} (ht : 509 ≤ t) : 9 ≤ rsAlpha t := by
  unfold rsAlpha
  rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d4]

/-- **The C0-corrected Riemann-Siegel remainder from t >= 509, `a`-form.**  For `t >= 509`,
    `0 < p = rsFrac t`, `cos(2 pi p) ≠ 0`, and any phase `phi` with `|phi - rsThetaMain t| <= 1/t`:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (13/20) a^(-3/2),  a = sqrt(t/2pi). -/
theorem rs_remainder_C0_alpha_seam {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      13 / 20 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  rw [rs_remainder_exact ht0 hp hcos φ]
  have ha9 : 9 ≤ rsAlpha t := rsAlpha_ge_9 ht
  have hta : t = 2 * π * rsAlpha t ^ 2 := t_eq_rsAlpha ht0.le
  set a := rsAlpha t with ha_def
  have ha0 : 0 < a := by linarith
  have hJ : ‖rsJ (rsFrac t)‖ ≤ 4 := norm_rsJ_le hp rsFrac_lt_one
  have hE : ‖rsE1 a (rsFrac t)‖ ≤ 1 / 4 / a := (norm_rsE1_le ha9).trans (E1_const_le ha9)
  have hA : |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
      rsJ (rsFrac t)).re| ≤ 2 * (|φ - rsThetaMain t| * 4) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (-(↑π / 8 * I))‖ = 1 := by rw [Complex.norm_exp]; simp
    have h2 : ‖cexp (I * (φ - rsThetaMain t)) - 1‖ ≤ |φ - rsThetaMain t| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ - rsThetaMain t)
      push_cast at this; rwa [Real.norm_eq_abs] at this
    rw [h1, one_mul]
    exact mul_le_mul h2 hJ (norm_nonneg _) (abs_nonneg _)
  have hB : |2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 a (rsFrac t)).re| ≤
      2 * (1 / 4 / a) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h1 : ‖cexp (I * (φ - rsThetaMain t - π / 8))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [h1, one_mul]; exact hE
  have hδ : |φ - rsThetaMain t| ≤ 1 / (2 * π * a ^ 2) := by rw [← hta]; exact hφ
  have h8 : 8 * |φ - rsThetaMain t| ≤ 3 / 20 / a := by
    have h1 : 8 * |φ - rsThetaMain t| ≤ 8 * (1 / (2 * π * a ^ 2)) := by linarith
    refine h1.trans ?_
    rw [show 8 * (1 / (2 * π * a ^ 2)) = 4 / (π * a ^ 2) by field_simp; ring,
      div_le_div_iff₀ (by positivity) ha0]
    have : 28 ≤ π * a := by nlinarith [Real.pi_gt_d2]
    nlinarith
  rw [abs_mul, abs_mul]
  have hsign : |(-1 : ℝ) ^ (rsNn t + 1)| = 1 := by simp
  rw [hsign, one_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  have hapos := Real.rpow_pos_of_pos ha0 (-(1 / 2 : ℝ))
  calc a ^ (-(1 / 2 : ℝ)) * |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
        rsJ (rsFrac t)).re + 2 * (cexp (I * (φ - rsThetaMain t - π / 8)) *
        rsE1 a (rsFrac t)).re|
      ≤ a ^ (-(1 / 2 : ℝ)) * (2 * (|φ - rsThetaMain t| * 4) + 2 * (1 / 4 / a)) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add hA hB)
    _ ≤ a ^ (-(1 / 2 : ℝ)) * (13 / 20 / a) := by
        gcongr
        have e : (13 : ℝ) / 20 / a = 3 / 20 / a + 2 * (1 / 4 / a) := by ring
        rw [e]; linarith
    _ = 13 / 20 * a ^ (-(3 / 2 : ℝ)) := by
        rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num, Real.rpow_add ha0, Real.rpow_neg_one]
        ring

/-- **SEAM HEADLINE: the explicit C0-corrected Riemann-Siegel remainder bound from t >= 509.**
    For `t >= 509`, `0 < p = rsFrac t`, `cos(2 pi p) ≠ 0`, and any phase `phi` with
    `|phi - rsThetaMain t| <= 1/t`:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (13/5) t^(-3/4). -/
theorem rs_remainder_C0_seam {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      13 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := rs_remainder_C0_alpha_seam ht hp hcos hφ
  rw [rsAlpha_rpow_neg_half ht0.le, rsAlpha_rpow_neg_three_halves ht0] at h
  have ht34 := Real.rpow_pos_of_pos ht0 (-(3 / 4 : ℝ))
  calc _ ≤ 13 / 20 * ((2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) := h
    _ ≤ 13 / 20 * (4 * t ^ (-(3 / 4 : ℝ))) := by gcongr; exact two_pi_rpow_three_quarters_le
    _ = 13 / 5 * t ^ (-(3 / 4 : ℝ)) := by ring

end RSSeam
