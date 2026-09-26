/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/
import RS_Fold

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/

theorem abs_log_le_of_ge {r m : ℝ} (hm : 0 < m) (hr : m ≤ r) : |Real.log r| ≤ r + |Real.log m| := by
  have hr0 : 0 < r := lt_of_lt_of_le hm hr
  rcases le_total 1 r with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hr0
    linarith [abs_nonneg (Real.log m)]
  · rw [abs_of_nonpos (Real.log_nonpos hr0.le h)]
    have h1 : Real.log m ≤ Real.log r := Real.log_le_log hm hr
    linarith [neg_abs_le (Real.log m)]

theorem norm_log_le {x : ℂ} {m : ℝ} (hm : 0 < m) (hx : m ≤ ‖x‖) :
    ‖Complex.log x‖ ≤ ‖x‖ + |Real.log m| + π := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log x)
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 := abs_log_le_of_ge hm hx
  have h3 := Complex.abs_arg_le_pi x
  linarith

/-- **Parametric holomorphy.**  If `W` is continuous with a Gaussian tail and `X` is a continuous
    path in the slit plane with `m <= |X v| <= alpha + beta |v|`, then `s |-> int W v * X v ^ s` is
    entire. -/
theorem differentiable_integral_cpow {W X : ℝ → ℂ} (hW : Continuous W) (hX : Continuous X)
    (hXs : ∀ v, X v ∈ slitPlane) {m : ℝ} (hm : 0 < m) (hXm : ∀ v, m ≤ ‖X v‖)
    {α β : ℝ} (hXb : ∀ v, ‖X v‖ ≤ α + β * |v|)
    {C a b : ℝ} (ha : 0 < a) (hWb : ∀ v, 1 ≤ |v| → ‖W v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|)) :
    Differentiable ℂ (fun s : ℂ => ∫ v : ℝ, W v * X v ^ s) := by
  intro s₀
  have hX0 : ∀ v, X v ≠ 0 := fun v => slitPlane_ne_zero (hXs v)
  set K : ℝ := ‖s₀‖ + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set L : ℝ → ℝ := fun v => α + β * |v| + |Real.log m| + π with hL
  have hlogL : ∀ v, ‖Complex.log (X v)‖ ≤ L v := by
    intro v
    have := norm_log_le hm (hXm v)
    have := hXb v
    simp only [hL]; linarith
  -- the dominating function
  set bound : ℝ → ℝ := fun v => ‖W v‖ * Real.exp (K * L v) with hbound
  have hcpow_le : ∀ v (s : ℂ), s ∈ Metric.ball s₀ 1 → ‖X v ^ s‖ ≤ Real.exp ((K - 1) * L v) := by
    intro v s hs
    rw [Complex.cpow_def_of_ne_zero (hX0 v)]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    have h1 : ‖s‖ ≤ ‖s₀‖ + 1 := by
      have := Metric.mem_ball.mp hs
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le s s₀
      linarith
    have h2 := hlogL v
    have hL0 : 0 ≤ L v := le_trans (norm_nonneg _) h2
    calc ‖Complex.log (X v)‖ * ‖s‖ ≤ L v * (‖s₀‖ + 1) :=
          mul_le_mul h2 h1 (norm_nonneg _) hL0
      _ = (K - 1) * L v := by simp only [hK]; ring
  have hbound_int : Integrable bound := by
    have hLc : Continuous L := by simp only [hL]; fun_prop
    refine integrable_of_continuous_of_tail (f := fun v => (bound v : ℂ))
      (by simp only [hbound]; fun_prop) (a := a) (R := 1)
      (C := C * Real.exp (K * (|α| + |Real.log m| + π)))
      (b := b + K * |β|) ha (fun v hv => ?_) |>.norm.congr (Eventually.of_forall fun v => ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [hbound]
      have h1 := hWb v hv
      have h2 : K * L v ≤ K * (|α| + |Real.log m| + π) + K * |β| * |v| := by
        simp only [hL]
        have : α + β * |v| + |Real.log m| + π ≤ |α| + |Real.log m| + π + |β| * |v| := by
          have := le_abs_self α
          have : β * |v| ≤ |β| * |v| := mul_le_mul_of_nonneg_right (le_abs_self β) (abs_nonneg v)
          linarith
        nlinarith
      calc ‖W v‖ * Real.exp (K * L v)
          ≤ C * Real.exp (-a * v ^ 2 + b * |v|) *
              Real.exp (K * (|α| + |Real.log m| + π) + K * |β| * |v|) :=
            mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le
              (le_trans (norm_nonneg _) h1)
        _ = C * Real.exp (K * (|α| + |Real.log m| + π)) *
              Real.exp (-a * v ^ 2 + (b + K * |β|) * |v|) := by
            have e1 : ∀ p q : ℝ, C * Real.exp p * Real.exp q = C * Real.exp (p + q) := by
              intro p q; rw [Real.exp_add]; ring
            rw [e1, e1]; congr 2; ring
    · simp only [Complex.norm_real, Real.norm_eq_abs, hbound]
      exact abs_of_nonneg (by positivity)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (s : ℂ) (v : ℝ) => W v * X v ^ s)
    (F' := fun (s : ℂ) (v : ℝ) => W v * (X v ^ s * Complex.log (X v)))
    (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => ?_) ?_ ?_ ?_ hbound_int ?_
  · exact key.2.differentiableAt
  · -- measurability
    have : Continuous (fun v => X v ^ s) := by
      rw [continuous_iff_continuousAt]; intro v
      exact (continuousAt_cpow_const (hXs v)).comp hX.continuousAt
    exact (hW.mul this).aestronglyMeasurable
  · -- integrability at s₀
    refine hbound_int.mono' ?_ (Eventually.of_forall fun v => ?_)
    · have : Continuous (fun v => X v ^ s₀) := by
        rw [continuous_iff_continuousAt]; intro v
        exact (continuousAt_cpow_const (hXs v)).comp hX.continuousAt
      exact (hW.mul this).aestronglyMeasurable
    · rw [norm_mul]
      have h1 := hcpow_le v s₀ (Metric.mem_ball_self one_pos)
      have hL0 : 0 ≤ L v := le_trans (norm_nonneg _) (hlogL v)
      have h2 : Real.exp ((K - 1) * L v) ≤ Real.exp (K * L v) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
  · -- measurability of the derivative
    have h1 : Continuous (fun v => X v ^ s₀) := by
      rw [continuous_iff_continuousAt]; intro v
      exact (continuousAt_cpow_const (hXs v)).comp hX.continuousAt
    have h2 : Continuous (fun v => Complex.log (X v)) := by
      rw [continuous_iff_continuousAt]; intro v
      exact (continuousAt_clog (hXs v)).comp hX.continuousAt
    exact (hW.mul (h1.mul h2)).aestronglyMeasurable
  · -- the bound on the derivative
    refine Eventually.of_forall fun v s hs => ?_
    rw [norm_mul, norm_mul]
    have h1 := hcpow_le v s hs
    have h2 := hlogL v
    have hL0 : 0 ≤ L v := le_trans (norm_nonneg _) h2
    have h3 : Real.exp ((K - 1) * L v) * L v ≤ Real.exp (K * L v) := by
      have h4 : L v ≤ Real.exp (L v) := by
        have := Real.add_one_le_exp (L v); linarith
      calc Real.exp ((K - 1) * L v) * L v ≤ Real.exp ((K - 1) * L v) * Real.exp (L v) :=
            mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
        _ = Real.exp (K * L v) := by rw [← Real.exp_add]; congr 1; ring
    calc ‖W v‖ * (‖X v ^ s‖ * ‖Complex.log (X v)‖)
        ≤ ‖W v‖ * (Real.exp ((K - 1) * L v) * L v) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ ‖W v‖ * Real.exp (K * L v) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  · -- the derivative
    refine Eventually.of_forall fun v s _ => ?_
    exact ((Complex.hasStrictDerivAt_const_cpow (Or.inl (hX0 v))).hasDerivAt).const_mul (W v)

/-! ## 2. The two Riemann-Siegel line integrals are entire in `s` -/

theorem norm_ge_half_of_upLine {c v : ℝ} : |c| / 2 ≤ ‖(c : ℂ) + v * (1 + I)‖ := by
  have h1 := Complex.abs_re_le_norm ((c : ℂ) + v * (1 + I))
  have h2 := Complex.abs_im_le_norm ((c : ℂ) + v * (1 + I))
  simp at h1 h2
  have : |c| ≤ |c + v| + |v| := by
    calc |c| = |(c + v) + (-v)| := by ring_nf
      _ ≤ |c + v| + |-v| := abs_add_le _ _
      _ = |c + v| + |v| := by rw [abs_neg]
  linarith

theorem norm_ge_half_of_dnLine {c v : ℝ} : |c| / 2 ≤ ‖(c : ℂ) + v * (1 - I)‖ := by
  have h1 := Complex.abs_re_le_norm ((c : ℂ) + v * (1 - I))
  have h2 := Complex.abs_im_le_norm ((c : ℂ) + v * (1 - I))
  simp at h1 h2
  have : |c| ≤ |c + v| + |v| := by
    calc |c| = |(c + v) + (-v)| := by ring_nf
      _ ≤ |c + v| + |-v| := abs_add_le _ _
      _ = |c + v| + |v| := by rw [abs_neg]
  linarith

theorem norm_le_of_upLine (c v : ℝ) : ‖(c : ℂ) + v * (1 + I)‖ ≤ |c| + 2 * |v| := by
  have h := norm_add_le (c : ℂ) (v * (1 + I))
  rw [norm_mul, Complex.norm_real, norm_one_add_I, Real.norm_eq_abs] at h
  have : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : |v| * Real.sqrt 2 ≤ 2 * |v| := by nlinarith [abs_nonneg v]
  simp at h
  linarith

theorem norm_le_of_dnLine (c v : ℝ) : ‖(c : ℂ) + v * (1 - I)‖ ≤ |c| + 2 * |v| := by
  have h := norm_add_le (c : ℂ) (v * (1 - I))
  rw [norm_mul, Complex.norm_real, norm_one_sub_I, Real.norm_eq_abs] at h
  have : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : |v| * Real.sqrt 2 ≤ 2 * |v| := by nlinarith [abs_nonneg v]
  simp at h
  linarith

theorem upLine_mem_slitPlane {c : ℝ} (hc : 0 < c) (v : ℝ) : (c : ℂ) + v * (1 + I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne v 0 with rfl | hv
  · left; simpa using hc
  · right; simpa using hv

theorem dnLine_mem_slitPlane {c : ℝ} (hc : 0 < c) (v : ℝ) : (c : ℂ) + v * (1 - I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne v 0 with rfl | hv
  · left; simpa using hc
  · right; simpa using hv

theorem continuous_rsH_line {c : ℝ} (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Continuous (fun v : ℝ => rsH ((c : ℂ) + v * (1 - I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  have h1 : ContinuousAt rsH ((c : ℂ) + v * (1 - I)) :=
    (differentiableAt_rsH (rsD_ne_zero_of_ne (lineDn_pt_ne_int hcl v))).continuousAt
  have h2 : ContinuousAt (fun v : ℝ => (c : ℂ) + v * (1 - I)) v := by fun_prop
  exact ContinuousAt.comp (g := rsH) (f := fun v : ℝ => (c : ℂ) + v * (1 - I)) h1 h2

/-- `s |-> lineUp c (rsG x^(-s))` is entire (c > 0 not an integer). -/
theorem differentiable_rsA {c : ℝ} (hc : 0 < c) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Differentiable ℂ (fun s : ℂ => lineUp c (fun x => rsG x * x ^ (-s))) := by
  have hmain := differentiable_integral_cpow (W := fun v => rsG ((c : ℂ) + v * (1 + I)) * (1 + I))
    (X := fun v => (c : ℂ) + v * (1 + I)) ((continuous_rsG_line hcl).mul continuous_const)
    (by fun_prop) (upLine_mem_slitPlane hc) (m := |c| / 2) (by positivity)
    (fun v => norm_ge_half_of_upLine) (α := |c|) (β := 2) (fun v => norm_le_of_upLine c v)
    (C := Real.sqrt 2) (a := 2 * π) (b := 2 * π * (|c| + |c|)) (by positivity) (fun v hv => ?_)
  · have hfun : (fun s : ℂ => lineUp c (fun x => rsG x * x ^ (-s))) =
        (fun s : ℂ => ∫ v : ℝ, rsG ((c : ℂ) + v * (1 + I)) * (1 + I) * ((c : ℂ) + v * (1 + I)) ^ s)
          ∘ (fun s : ℂ => -s) := by
      ext s; simp only [Function.comp, lineUp]; congr 1; ext v; ring
    rw [hfun]
    exact hmain.comp differentiable_id.neg
  · have hx : ((c : ℂ) + v * (1 + I)).re - ((c : ℂ) + v * (1 + I)).im ∈ Icc c c := by simp
    have h1 : 1 ≤ |((c : ℂ) + v * (1 + I)).im| := by simpa using hv
    have hb := norm_rsG_le hx h1
    rw [norm_mul, norm_one_add_I]
    simp only [lineUp_pt_im] at hb
    calc ‖rsG ((c : ℂ) + v * (1 + I))‖ * Real.sqrt 2
        ≤ Real.exp (-(2 * π) * v ^ 2 + 2 * π * (|c| + |c|) * |v|) * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * Real.exp (-(2 * π) * v ^ 2 + 2 * π * (|c| + |c|) * |v|) := by ring

/-- `s |-> lineDn c (rsH x^(s-1))` is entire (c > 0 not an integer). -/
theorem differentiable_rsB {c : ℝ} (hc : 0 < c) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Differentiable ℂ (fun s : ℂ => lineDn c (fun x => rsH x * x ^ (s - 1))) := by
  have hmain := differentiable_integral_cpow (W := fun v => rsH ((c : ℂ) + v * (1 - I)) * (1 - I))
    (X := fun v => (c : ℂ) + v * (1 - I)) ((continuous_rsH_line hcl).mul continuous_const)
    (by fun_prop) (dnLine_mem_slitPlane hc) (m := |c| / 2) (by positivity)
    (fun v => norm_ge_half_of_dnLine) (α := |c|) (β := 2) (fun v => norm_le_of_dnLine c v)
    (C := Real.sqrt 2) (a := 2 * π) (b := 2 * π * (|c| + |c|)) (by positivity) (fun v hv => ?_)
  · have hfun : (fun s : ℂ => lineDn c (fun x => rsH x * x ^ (s - 1))) =
        (fun s : ℂ => ∫ v : ℝ, rsH ((c : ℂ) + v * (1 - I)) * (1 - I) * ((c : ℂ) + v * (1 - I)) ^ s)
          ∘ (fun s : ℂ => s - 1) := by
      ext s; simp only [Function.comp, lineDn]; congr 1; ext v; ring
    rw [hfun]
    exact hmain.comp (differentiable_id.sub_const 1)
  · have hx : ((c : ℂ) + v * (1 - I)).re + ((c : ℂ) + v * (1 - I)).im ∈ Icc c c := by simp
    have h1 : 1 ≤ |((c : ℂ) + v * (1 - I)).im| := by simpa using hv
    have hb := norm_rsH_le hx h1
    rw [norm_mul, norm_one_sub_I]
    rw [show ((c : ℂ) + v * (1 - I)).im = -v by simp, abs_neg, neg_sq] at hb
    calc ‖rsH ((c : ℂ) + v * (1 - I))‖ * Real.sqrt 2
        ≤ Real.exp (-(2 * π) * v ^ 2 + 2 * π * (|c| + |c|) * |v|) * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * Real.exp (-(2 * π) * v ^ 2 + 2 * π * (|c| + |c|) * |v|) := by ring

/-! ## 3. The chi factor -/

/-- The functional-equation factor `chi(s) = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`
    (`zeta(s) = chi(s) zeta(1-s)`); written with `(Gamma (s/2))⁻¹` so that it is visibly holomorphic
    away from the poles `s = 1, 3, 5, ...` of `Gamma((1-s)/2)`. -/
def rsChi (s : ℂ) : ℂ := (↑π : ℂ) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) * (Gamma (s / 2))⁻¹

theorem differentiableAt_rsChi {s : ℂ} (hs : ∀ k : ℕ, s ≠ 2 * k + 1) :
    DifferentiableAt ℂ rsChi s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (↑π : ℂ) ^ (s - 1 / 2)) s :=
    (differentiableAt_id.sub_const _).const_cpow (Or.inl pi_ne_zero')
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Gamma ((1 - s) / 2)) s := by
    refine (Complex.differentiableAt_Gamma _ ?_).comp s (by fun_prop)
    intro m hm
    apply hs m
    linear_combination -2 * hm
  have h3 : DifferentiableAt ℂ (fun s : ℂ => (Gamma (s / 2))⁻¹) s :=
    DifferentiableAt.comp (g := fun s : ℂ => (Gamma s)⁻¹) (f := fun s : ℂ => s / 2) s
      (Complex.differentiable_one_div_Gamma (s / 2)) (by fun_prop)
  exact (h1.mul h2).mul h3

/-- **The Gamma identity behind chi.**  For Re s > 0 and cos(pi s / 2) ≠ 0:
    `rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s`  (reflection + duplication). -/
theorem rsChi_mul_Gamma_cos {s : ℂ} (hs : 0 < s.re) (hcos : Complex.cos (↑π * s / 2) ≠ 0) :
    rsChi s * Gamma s * (2 * Complex.cos (↑π * s / 2)) = (2 * ↑π) ^ s := by
  have hGb : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGh : Gamma (s / 2 + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hdup := Complex.Gamma_mul_Gamma_add_half (s / 2)
  rw [show 2 * (s / 2) = s by ring] at hdup
  have href := Complex.Gamma_mul_Gamma_one_sub ((1 - s) / 2)
  rw [show 1 - (1 - s) / 2 = s / 2 + 1 / 2 by ring,
    show (↑π : ℂ) * ((1 - s) / 2) = ↑π / 2 - ↑π * s / 2 by ring, Complex.sin_pi_div_two_sub] at href
  have hpi0 := pi_ne_zero'
  set Q : ℂ := (↑π : ℂ) ^ (1 / 2 : ℂ) with hQ
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) = Q := by
    rw [hQ, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  rw [hsqrt] at hdup
  set P : ℂ := (↑π : ℂ) ^ (s - 1 / 2) with hP
  set T : ℂ := (2 : ℂ) ^ (1 - s) with hT
  have hQ0 : Q ≠ 0 := by rw [hQ, Ne, Complex.cpow_eq_zero_iff]; exact fun h => hpi0 h.1
  have hT0 : T ≠ 0 := by rw [hT, Ne, Complex.cpow_eq_zero_iff]; exact fun h => two_ne_zero h.1
  have hPQ : P * Q = (↑π : ℂ) ^ s := by
    rw [hP, hQ, ← Complex.cpow_add _ _ hpi0]; congr 1; ring
  have hQQ : Q * Q = ↑π := by
    rw [hQ, ← Complex.cpow_add _ _ hpi0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.cpow_one]
  have hT2 : T * (2 : ℂ) ^ s = 2 := by
    rw [hT, ← Complex.cpow_add _ _ two_ne_zero, show 1 - s + s = 1 by ring, Complex.cpow_one]
  have h2pi : (2 * ↑π : ℂ) ^ s = (2 : ℂ) ^ s * (↑π : ℂ) ^ s := by
    have := Complex.mul_cpow_ofReal_nonneg (a := 2) (b := π) (by norm_num) Real.pi_pos.le s
    push_cast at this; exact this
  -- Gamma s from the duplication formula
  have hGs : Gamma s = Gamma (s / 2) * Gamma (s / 2 + 1 / 2) / (T * Q) := by
    rw [eq_div_iff (mul_ne_zero hT0 hQ0), hdup]; ring
  -- Gamma((1-s)/2) Gamma(s/2 + 1/2) = pi / cos
  unfold rsChi
  rw [← hP, hGs, h2pi, ← hPQ]
  have key : Gamma ((1 - s) / 2) * Gamma (s / 2 + 1 / 2) * Complex.cos (↑π * s / 2) = ↑π := by
    rw [href]; field_simp
  calc P * Gamma ((1 - s) / 2) * (Gamma (s / 2))⁻¹ *
        (Gamma (s / 2) * Gamma (s / 2 + 1 / 2) / (T * Q)) * (2 * Complex.cos (↑π * s / 2))
      = 2 * P * (Gamma ((1 - s) / 2) * Gamma (s / 2 + 1 / 2) * Complex.cos (↑π * s / 2)) /
          (T * Q) := by field_simp
    _ = 2 * P * (Q * Q) / (T * Q) := by rw [key, hQQ]
    _ = 2 * P * Q / T := by field_simp
    _ = T * (2 : ℂ) ^ s * P * Q / T := by rw [hT2]
    _ = (2 : ℂ) ^ s * (P * Q) := by field_simp

theorem one_add_I_cpow_mul (s : ℂ) : (1 + I) ^ s * (1 - I) ^ (-s) = cexp (↑π * I * s / 2) := by
  have hne : (1 - I : ℂ) ≠ 0 := one_sub_I_ne_zero
  have hre : 0 < (1 - I : ℂ).re := by simp
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hlog : Complex.log (1 + I) = Complex.log I + Complex.log (1 - I) := by
    have h : (1 + I : ℂ) = I * (1 - I) := by ring_nf; rw [I_sq]; ring
    rw [h]
    refine (Complex.log_mul_eq_add_log_iff I_ne_zero hne).mpr ⟨?_, ?_⟩
    · rw [Complex.arg_I]; linarith [(abs_lt.mp harg).1, Real.pi_pos]
    · rw [Complex.arg_I]; linarith [(abs_lt.mp harg).2, Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero one_add_I_ne_zero, Complex.cpow_def_of_ne_zero hne, hlog,
    Complex.log_I, ← Complex.exp_add]
  congr 1; ring

theorem one_add_exp_eq (s : ℂ) :
    1 + cexp (↑π * I * s) = 2 * Complex.cos (↑π * s / 2) * cexp (↑π * I * s / 2) := by
  rw [Complex.two_cos, add_mul, ← Complex.exp_add, ← Complex.exp_add]
  rw [show ↑π * s / 2 * I + ↑π * I * s / 2 = ↑π * I * s by ring,
    show -(↑π * s / 2) * I + ↑π * I * s / 2 = 0 by ring, Complex.exp_zero]
  ring

theorem cos_ne_zero_of_one_add_exp {s : ℂ} (h : 1 + cexp (↑π * I * s) ≠ 0) :
    Complex.cos (↑π * s / 2) ≠ 0 := by
  intro hc; apply h; rw [one_add_exp_eq, hc]; ring

/-- The chi factor in the form produced by the Mellin/folding computation. -/
theorem rsChi_eq {s : ℂ} (hs : 0 < s.re) (h : 1 + cexp (↑π * I * s) ≠ 0) :
    rsChi s = (2 * ↑π) ^ s * (1 + I) ^ s * (1 - I) ^ (-s) / (Gamma s * (1 + cexp (↑π * I * s))) := by
  have hcos := cos_ne_zero_of_one_add_exp h
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hE : cexp (↑π * I * s / 2) ≠ 0 := Complex.exp_ne_zero _
  rw [eq_div_iff (mul_ne_zero hG h), mul_assoc ((2 * (π : ℂ)) ^ s), one_add_I_cpow_mul,
    one_add_exp_eq, ← rsChi_mul_Gamma_cos hs hcos]
  ring

end RSInt
