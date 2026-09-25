/-  RS_Fold.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 4:
    the chi-side line.  Mathlib-only (imports `RS_Mellin`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `norm_cpow_le_exp` : ‖x^w‖ <= e^{pi |Im w|} e^{Re w ‖x‖} for Re w >= 0 (growth of x^w).
      * `continuousAt_rsH_cpow_zero` : for Re s > 2 the chi-side integrand rsH(x) x^(s-1) is
        continuous at the pole x = 0 of rsH (removable via dslope, value 0).
      * `lineDn_zero_fold` : FOLDING.  For Re s > 2 the chi-side integral along the line through 0
        is (1 + e^{i pi s}) times the half-line integral:
            lineDn 0 (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s
        (rsH is odd, and (-x)^(s-1) = x^(s-1) e^{i pi (s-1)} on that line).
      * `lineDn_zero_eq` : the line through 0 may be moved to any c in (0, 1) (strip Cauchy; the
        pole at 0 sits on the boundary and is harmless for Re s > 2).
      * `lineDn_eq_fold` : lineDn c (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s, 0 < c < 1, Re s > 2.

    conjecture1_proved = False.
-/
import RS_Mellin

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. Growth of `x^w` -/

theorem norm_cpow_le_exp {w : ℂ} (hw : 0 ≤ w.re) (x : ℂ) :
    ‖x ^ w‖ ≤ Real.exp (π * |w.im|) * Real.exp (w.re * ‖x‖) := by
  have h1 : 1 ≤ Real.exp (π * |w.im|) * Real.exp (w.re * ‖x‖) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by positivity)
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne w 0 with rfl | hw0
    · simp only [Complex.cpow_zero, norm_one]; exact h1
    · rw [Complex.zero_cpow hw0, norm_zero]; positivity
  · rw [Complex.norm_cpow_of_ne_zero hx]
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hA : ‖x‖ ^ w.re ≤ Real.exp (w.re * ‖x‖) := by
      rw [Real.rpow_def_of_pos hpos]
      apply Real.exp_le_exp.mpr
      have := Real.log_le_sub_one_of_pos hpos
      nlinarith
    have hB : 1 / Real.exp (x.arg * w.im) ≤ Real.exp (π * |w.im|) := by
      rw [one_div, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have h2 := Complex.abs_arg_le_pi x
      have h3 : -(x.arg * w.im) ≤ |x.arg * w.im| := neg_le_abs _
      rw [abs_mul] at h3
      nlinarith [abs_nonneg w.im, abs_nonneg x.arg]
    calc ‖x‖ ^ w.re / Real.exp (x.arg * w.im)
        = ‖x‖ ^ w.re * (1 / Real.exp (x.arg * w.im)) := by ring
      _ ≤ Real.exp (w.re * ‖x‖) * Real.exp (π * |w.im|) :=
          mul_le_mul hA hB (by positivity) (Real.exp_pos _).le
      _ = Real.exp (π * |w.im|) * Real.exp (w.re * ‖x‖) := by ring

/-! ## 2. Continuity of the chi-side integrand at 0 -/

theorem rsH_neg (x : ℂ) : rsH (-x) = -rsH x := by
  unfold rsH rsD
  rw [neg_sq, show ↑π * I * -x = -(↑π * I * x) by ring, neg_neg, ← neg_sub, div_neg]

theorem continuousAt_rsH_cpow_zero {s : ℂ} (hs : 2 < s.re) :
    ContinuousAt (fun x => rsH x * x ^ (s - 1)) 0 := by
  set D₁ := dslope rsD 0 with hD₁
  have hD₁0 : D₁ 0 ≠ 0 := by
    rw [hD₁, dslope_same]
    have := deriv_rsD_int_ne_zero 0
    simpa using this
  have hD₁c : ContinuousAt D₁ 0 := continuousAt_dslope_same.mpr (differentiable_rsD 0)
  have hs2 : s - 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set G : ℂ → ℂ := fun x => cexp (-(↑π * I * x ^ 2)) * x ^ (s - 2) / D₁ x with hG
  have hGc : ContinuousAt G 0 := by
    have hc1 : ContinuousAt (fun x : ℂ => x ^ (s - 2)) 0 := by
      have h := continuousAt_cpow_zero_of_re_pos (z := s - 2) (by simp; linarith)
      exact h.comp (f := fun x : ℂ => (x, s - 2)) (by fun_prop)
    exact ((by fun_prop : ContinuousAt (fun x : ℂ => cexp (-(↑π * I * x ^ 2))) 0).mul hc1).div
      hD₁c hD₁0
  refine hGc.congr ?_
  have hball : ∀ᶠ x in 𝓝 (0 : ℂ), ‖x‖ < 1 / 2 := by
    have := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [this] with x hx
    simpa using hx
  filter_upwards [hball] with x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [hG, Complex.zero_cpow hs2, Complex.zero_cpow hs1, mul_zero, zero_div]
  · have hD : rsD x ≠ 0 := by
      intro h0
      obtain ⟨n, rfl⟩ := (rsD_eq_zero_iff x).mp h0
      have hn : |(n : ℝ)| < 1 / 2 := by simpa using hx
      have hn0 : n = 0 := by
        have h1 : (n : ℝ) < 1 / 2 := lt_of_le_of_lt (le_abs_self _) hn
        have h2 : -(1 / 2 : ℝ) < n := by linarith [neg_abs_le (n : ℝ)]
        have h3 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
        have h4 : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
        omega
      exact hx0 (by rw [hn0]; simp)
    have h00 : rsD 0 = 0 := by have := rsD_int 0; simpa using this
    have hdsl : D₁ x = rsD x / x := by
      rw [hD₁, dslope_of_ne _ hx0, slope_def_field, h00, sub_zero, sub_zero]
    simp only [hG]
    unfold rsH
    rw [hdsl, show s - 1 = (s - 2) + 1 by ring, Complex.cpow_add _ _ hx0, Complex.cpow_one]
    field_simp

/-! ## 3. Folding the line through 0 -/

theorem log_neg_one_sub_I : Complex.log (-(1 - I)) = Complex.log (1 - I) + ↑π * I := by
  have hne : (1 - I : ℂ) ≠ 0 := one_sub_I_ne_zero
  have him : (1 - I : ℂ).im < 0 := by simp
  apply Complex.ext
  · rw [Complex.add_re, Complex.log_re, Complex.log_re, norm_neg]; simp
  · rw [Complex.log_im, Complex.add_im, Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
    simp

theorem cpow_neg_line {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (((-r : ℝ) : ℂ) * (1 - I)) ^ w = (((r : ℝ) : ℂ) * (1 - I)) ^ w * cexp (↑π * I * w) := by
  have h1 : (((-r : ℝ) : ℂ) * (1 - I)) = (r : ℂ) * (-(1 - I)) := by push_cast; ring
  have hne : -(1 - I : ℂ) ≠ 0 := neg_ne_zero.mpr one_sub_I_ne_zero
  rw [h1, ofReal_mul_cpow hr hne, ofReal_mul_cpow hr one_sub_I_ne_zero,
    Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero one_sub_I_ne_zero,
    log_neg_one_sub_I, mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- The chi-side integrand along the line through 0. -/
def rsFdn (s : ℂ) (v : ℝ) : ℂ := rsH ((v : ℂ) * (1 - I)) * ((v : ℂ) * (1 - I)) ^ (s - 1) * (1 - I)

theorem rsFdn_neg {s : ℂ} {r : ℝ} (hr : 0 < r) : rsFdn s (-r) = cexp (↑π * I * s) * rsFdn s r := by
  unfold rsFdn
  rw [cpow_neg_line hr, show ((-r : ℝ) : ℂ) * (1 - I) = -((r : ℂ) * (1 - I)) by push_cast; ring,
    rsH_neg]
  have : cexp (↑π * I * (s - 1)) = -cexp (↑π * I * s) := by
    rw [show ↑π * I * (s - 1) = ↑π * I * s + -(↑π * I) by ring, Complex.exp_add, exp_neg_piI]
    ring
  rw [this]; ring

theorem continuous_rsFdn {s : ℂ} (hs : 2 < s.re) : Continuous (rsFdn s) := by
  rw [continuous_iff_continuousAt]
  intro v
  unfold rsFdn
  refine ContinuousAt.mul ?_ continuousAt_const
  rcases eq_or_ne v 0 with rfl | hv
  · have h := continuousAt_rsH_cpow_zero hs
    have h2 : ContinuousAt (fun v : ℝ => (v : ℂ) * (1 - I)) 0 := by fun_prop
    have h3 : ((0 : ℝ) : ℂ) * (1 - I) = 0 := by simp
    rw [← h3] at h
    exact ContinuousAt.comp (g := fun x => rsH x * x ^ (s - 1))
      (f := fun v : ℝ => (v : ℂ) * (1 - I)) h h2
  · have hx : ((v : ℂ) * (1 - I)).im ≠ 0 := by simp; exact hv
    have hD : rsD ((v : ℂ) * (1 - I)) ≠ 0 := by
      refine rsD_ne_zero_of_ne fun n hn => hx ?_
      rw [hn]; simp
    have hslit : (v : ℂ) * (1 - I) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr hx)
    have h1 : ContinuousAt (fun x => rsH x * x ^ (s - 1)) ((v : ℂ) * (1 - I)) :=
      (differentiableAt_rsH hD).continuousAt.mul (continuousAt_cpow_const hslit)
    have h2 : ContinuousAt (fun v : ℝ => (v : ℂ) * (1 - I)) v := by fun_prop
    exact ContinuousAt.comp (g := fun x => rsH x * x ^ (s - 1))
      (f := fun v : ℝ => (v : ℂ) * (1 - I)) h1 h2

theorem growth_cpow_sub_one {s : ℂ} (hs : 1 ≤ s.re) (x : ℂ) :
    ‖x ^ (s - 1)‖ ≤ Real.exp (π * |s.im|) * Real.exp ((s.re - 1) * ‖x‖) := by
  have := norm_cpow_le_exp (w := s - 1) (by simp; linarith) x
  simpa using this

theorem integrable_rsFdn {s : ℂ} (hs : 2 < s.re) : Integrable (rsFdn s) := by
  refine integrable_of_continuous_of_tail (continuous_rsFdn hs) (a := 2 * π) (R := 1)
    (C := (|Real.exp (π * |s.im|)| * Real.exp (|s.re - 1| * (|(0 : ℝ)| + |(0 : ℝ)|))) * Real.sqrt 2)
    (b := 2 * π * (|(0 : ℝ)| + |(0 : ℝ)|) + 2 * |s.re - 1|) (by positivity) (fun v hv => ?_)
  have hx : ((v : ℂ) * (1 - I)).re + ((v : ℂ) * (1 - I)).im ∈ Icc (0 : ℝ) 0 := by simp
  have him : ((v : ℂ) * (1 - I)).im = -v := by simp
  have h1 : 1 ≤ |((v : ℂ) * (1 - I)).im| := by rw [him, abs_neg]; exact hv
  have hb := norm_rsH_mul_le (ψ := fun x => x ^ (s - 1)) hx h1
    (growth_cpow_sub_one (by linarith) _)
  unfold rsFdn
  rw [norm_mul, norm_one_sub_I]
  rw [him, abs_neg, neg_sq] at hb
  calc ‖rsH ((v : ℂ) * (1 - I)) * ((v : ℂ) * (1 - I)) ^ (s - 1)‖ * Real.sqrt 2
      ≤ (|Real.exp (π * |s.im|)| * Real.exp (|s.re - 1| * (|(0 : ℝ)| + |(0 : ℝ)|))) *
          Real.exp (-(2 * π) * v ^ 2 + (2 * π * (|(0 : ℝ)| + |(0 : ℝ)|) + 2 * |s.re - 1|) * |v|) *
          Real.sqrt 2 := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg 2)
    _ = _ := by ring

/-- **Folding.**  For Re s > 2, `lineDn 0 (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s`. -/
theorem lineDn_zero_fold {s : ℂ} (hs : 2 < s.re) :
    lineDn 0 (fun x => rsH x * x ^ (s - 1)) = (1 + cexp (↑π * I * s)) * rsHR s := by
  have hL : lineDn 0 (fun x => rsH x * x ^ (s - 1)) = ∫ v : ℝ, rsFdn s v := by
    unfold lineDn rsFdn; congr 1; ext v; simp
  have hint := integrable_rsFdn hs
  rw [hL, ← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  have hIic : ∫ v in Iic (0 : ℝ), rsFdn s v = cexp (↑π * I * s) * rsHR s := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    unfold rsHR
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [rsFdn_neg hr]; unfold rsFdn; ring
  have hIoi : ∫ v in Ioi (0 : ℝ), rsFdn s v = rsHR s := by
    unfold rsHR rsFdn; rfl
  rw [hIic, hIoi]; ring

/-! ## 4. Moving the chi-side line off the pole -/

/-- For Re s > 2 and 0 < c < 1 the chi-side line through 0 may be moved to the line through `c`. -/
theorem lineDn_zero_eq {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    lineDn 0 (fun x => rsH x * x ^ (s - 1)) = lineDn c (fun x => rsH x * x ^ (s - 1)) := by
  -- the strip contains no integer other than 0, and meets the slit only at 0
  have hint0 : ∀ x : ℂ, x.re + x.im ∈ Icc (0 : ℝ) c → x ≠ 0 → rsD x ≠ 0 := by
    intro x hx hx0 h0
    obtain ⟨n, rfl⟩ := (rsD_eq_zero_iff x).mp h0
    have hn : (n : ℝ) ∈ Icc (0 : ℝ) c := by simpa using hx
    have h1 : 0 ≤ n := by exact_mod_cast hn.1
    have h2 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith [hn.2])
    have : n = 0 := by omega
    exact hx0 (by rw [this]; simp)
  have hslit : ∀ x : ℂ, x.re + x.im ∈ Icc (0 : ℝ) c → x ≠ 0 → x ∈ slitPlane := by
    intro x hx hx0
    rw [mem_slitPlane_iff]
    by_contra h
    rw [not_or, not_lt, not_not] at h
    have hre : x.re = 0 := by linarith [hx.1, h.1, h.2]
    exact hx0 (Complex.ext hre h.2)
  refine lineDn_eq_of_strip' hc.le ?_ ?_ (a := 2 * π) (by positivity)
    (C := |Real.exp (π * |s.im|)| * Real.exp (|s.re - 1| * (|(0 : ℝ)| + |c|)))
    (b := 2 * π * (|(0 : ℝ)| + |c|) + 2 * |s.re - 1|)
    (fun x hx h1 => norm_rsH_mul_le (ψ := fun x => x ^ (s - 1)) hx h1
      (growth_cpow_sub_one (by linarith) _))
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact (continuousAt_rsH_cpow_zero hs).continuousWithinAt
    · exact ((differentiableAt_rsH (hint0 x hx hx0)).continuousAt.mul
        (continuousAt_cpow_const (hslit x hx hx0))).continuousWithinAt
  · intro x hx
    have hx' : x.re + x.im ∈ Icc (0 : ℝ) c := ⟨hx.1.le, hx.2.le⟩
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx
    exact ((differentiableAt_rsH (hint0 x hx' hx0)).mul
      ((differentiableAt_id).cpow (differentiableAt_const _) (hslit x hx' hx0))).differentiableWithinAt

/-- The chi-side line through any `c ∈ (0,1)`, folded: for Re s > 2,
    `lineDn c (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s`. -/
theorem lineDn_eq_fold {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    lineDn c (fun x => rsH x * x ^ (s - 1)) = (1 + cexp (↑π * I * s)) * rsHR s := by
  rw [← lineDn_zero_eq hs hc hc1, lineDn_zero_fold hs]

end RSInt
