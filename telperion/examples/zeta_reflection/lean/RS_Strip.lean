/-  RS_Strip.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 1:
    contour tools.

    Mathlib-only (no corpus import), so the file can serve the dbn island's M5 layer L6 as well.

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integrable_exp_quad`, `integrable_of_continuous_of_tail` : integrability of a continuous
        function from a Gaussian-type tail bound `C exp(-a v^2 + b |v|)`.
      * `strip_integral_eq` : Cauchy's theorem on a HORIZONTAL STRIP y1 <= Im z <= y2 with decay at
        both ends: the integrals along the two edges agree.  (Mathlib's rectangle theorem
        `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` plus two limits.)
      * `lineUp c F`, `lineDn c F` : the oriented integrals along the slanted lines through the real
        point `c` with directions `1 + I` (slope +1) and `1 - I` (slope -1).
      * `lineUp_eq_of_strip`, `lineDn_eq_of_strip` : line independence -- the integral along the line
        through `c1` equals the one through `c2` when `F` is continuous on the closed slanted strip,
        holomorphic inside, and tends to 0 at infinity in the strip.

    conjecture1_proved = False.  Contour-integration infrastructure; nothing here bears on RH.
-/
import Mathlib

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RSInt

/-! ## 1. Integrability from a Gaussian tail -/

theorem exp_quad_le (a b v : ℝ) (ha : 0 < a) :
    Real.exp (-a * v ^ 2 + b * |v|) ≤ Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * v ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2a : 0 < 2 * a := by positivity
  have key : 2 * a * (-a * v ^ 2 + b * |v|) ≤ 2 * a * (b ^ 2 / (2 * a) + -(a / 2) * v ^ 2) := by
    rw [mul_add (2 * a) (b ^ 2 / (2 * a)), mul_div_cancel₀ _ h2a.ne']
    nlinarith [sq_nonneg (a * |v| - b), show a ^ 2 * |v| ^ 2 = a ^ 2 * v ^ 2 by rw [sq_abs]]
  exact le_of_mul_le_mul_left key h2a

theorem integrable_exp_quad {a b : ℝ} (ha : 0 < a) :
    Integrable (fun v : ℝ => Real.exp (-a * v ^ 2 + b * |v|)) := by
  have h1 : Integrable (fun v : ℝ => Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine h1.mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_quad_le a b v ha

/-- A continuous function with a Gaussian-type tail bound is integrable. -/
theorem integrable_of_continuous_of_tail {f : ℝ → ℂ} (hf : Continuous f) {a b C R : ℝ}
    (ha : 0 < a) (htail : ∀ v : ℝ, R ≤ |v| → ‖f v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|)) :
    Integrable f := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hf.continuousOn
  have hind : Integrable (Set.indicator (Icc (-R) R) (fun _ : ℝ => M)) :=
    (integrableOn_const (C := M) (by simp)).integrable_indicator measurableSet_Icc
  have hint : Integrable (fun v : ℝ =>
      Set.indicator (Icc (-R) R) (fun _ : ℝ => M) v + |C| * Real.exp (-a * v ^ 2 + b * |v|)) :=
    hind.add ((integrable_exp_quad ha).const_mul _)
  refine hint.mono' hf.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  have hE : 0 ≤ |C| * Real.exp (-a * v ^ 2 + b * |v|) := by positivity
  by_cases hv : v ∈ Icc (-R) R
  · rw [Set.indicator_of_mem hv]
    have := hM v hv
    linarith
  · rw [Set.indicator_of_notMem hv, zero_add]
    have hRv : R ≤ |v| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
      rcases hv with hv | hv
      · linarith [neg_le_abs v]
      · linarith [le_abs_self v]
    calc ‖f v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|) := htail v hRv
      _ ≤ |C| * Real.exp (-a * v ^ 2 + b * |v|) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le

/-! ## 2. Cauchy's theorem on a horizontal strip -/

/-- **Strip Cauchy.**  If `f` is continuous on the closed horizontal strip `y1 <= Im z <= y2`,
    holomorphic on the open strip, integrable along both edges, and tends to `0` at both ends of the
    strip uniformly in the height, then the two edge integrals agree. -/
theorem strip_integral_eq {f : ℂ → ℂ} {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂)
    (hcont : ContinuousOn f {z : ℂ | z.im ∈ Icc y₁ y₂})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | z.im ∈ Ioo y₁ y₂})
    (hint₁ : Integrable (fun x : ℝ => f (x + y₁ * I)))
    (hint₂ : Integrable (fun x : ℝ => f (x + y₂ * I)))
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x y : ℝ, R ≤ |x| → y ∈ Icc y₁ y₂ → ‖f (x + y * I)‖ ≤ ε) :
    ∫ x : ℝ, f (x + y₁ * I) = ∫ x : ℝ, f (x + y₂ * I) := by
  -- the rectangle identity on [-T, T] x [y1, y2]
  have key : ∀ T : ℝ, 0 ≤ T →
      (∫ x in (-T)..T, f (x + y₁ * I)) - (∫ x in (-T)..T, f (x + y₂ * I)) +
        I • (∫ y in y₁..y₂, f (T + y * I)) - I • (∫ y in y₁..y₂, f (-T + y * I)) = 0 := by
    intro T hT
    have hre1 : ((-T : ℝ) + y₁ * I : ℂ).re = -T := by simp
    have him1 : ((-T : ℝ) + y₁ * I : ℂ).im = y₁ := by simp
    have hre2 : ((T : ℝ) + y₂ * I : ℂ).re = T := by simp
    have him2 : ((T : ℝ) + y₂ * I : ℂ).im = y₂ := by simp
    have H := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
      ((-T : ℝ) + y₁ * I) ((T : ℝ) + y₂ * I) ?_ ?_
    · rw [hre1, him1, hre2, him2] at H
      simpa using H
    · rw [hre1, him1, hre2, him2]
      refine hcont.mono fun z hz => ?_
      rw [mem_reProdIm] at hz
      simp only [mem_setOf_eq]
      rw [Set.uIcc_of_le hy] at hz
      exact hz.2
    · rw [hre1, him1, hre2, him2]
      refine hdiff.mono fun z hz => ?_
      rw [mem_reProdIm] at hz
      simp only [mem_setOf_eq]
      rw [min_eq_left hy, max_eq_right hy] at hz
      exact hz.2
  -- the vertical sides tend to zero
  have hvert : ∀ s : ℝ, s = 1 ∨ s = -1 →
      Tendsto (fun T : ℝ => ∫ y in y₁..y₂, f (s * T + y * I)) atTop (𝓝 0) := by
    intro s hs
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := hdecay (ε / (2 * (y₂ - y₁ + 1))) (by
      have : 0 < y₂ - y₁ + 1 := by linarith
      positivity)
    rw [eventually_atTop]
    refine ⟨max R 0, fun T hT => ?_⟩
    rw [dist_zero_right]
    have hsT : R ≤ |s * T| := by
      rcases hs with rfl | rfl
      · rw [one_mul, abs_of_nonneg (le_trans (le_max_right _ _) hT)]
        exact le_trans (le_max_left _ _) hT
      · rw [neg_one_mul, abs_neg, abs_of_nonneg (le_trans (le_max_right _ _) hT)]
        exact le_trans (le_max_left _ _) hT
    have hb : ∀ y ∈ Set.uIoc y₁ y₂, ‖f (↑s * ↑T + ↑y * I)‖ ≤ ε / (2 * (y₂ - y₁ + 1)) := by
      intro y hy'
      rw [Set.uIoc_of_le hy] at hy'
      have := hR (s * T) y hsT ⟨le_of_lt hy'.1, hy'.2⟩
      rwa [ofReal_mul] at this
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hpos : 0 < y₂ - y₁ + 1 := by linarith
    calc ‖∫ y in y₁..y₂, f (↑s * ↑T + ↑y * I)‖
        ≤ ε / (2 * (y₂ - y₁ + 1)) * |y₂ - y₁| := this
      _ < ε := by
        rw [abs_of_nonneg (by linarith)]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  have h1 := intervalIntegral_tendsto_integral hint₁ tendsto_neg_atTop_atBot tendsto_id
  have h2 := intervalIntegral_tendsto_integral hint₂ tendsto_neg_atTop_atBot tendsto_id
  have hv1 := hvert 1 (Or.inl rfl)
  have hvm := hvert (-1) (Or.inr rfl)
  simp only [ofReal_one, one_mul, ofReal_neg, neg_mul] at hv1 hvm
  have hlim := ((h1.sub h2).add (hv1.const_smul I)).sub (hvm.const_smul I)
  simp only [smul_zero, add_zero, sub_zero] at hlim
  have hzero : Tendsto (fun T : ℝ =>
      (∫ x in (-T)..(id T), f (x + y₁ * I)) - (∫ x in (-T)..(id T), f (x + y₂ * I)) +
        I • (∫ y in y₁..y₂, f (T + y * I)) - I • (∫ y in y₁..y₂, f (-T + y * I))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    exact ⟨0, fun T hT => (key T hT).symm⟩
  have := tendsto_nhds_unique hlim hzero
  exact sub_eq_zero.mp this

/-! ## 3. Slanted lines -/

/-- The integral along the line through the real point `c` with direction `1 + I` (slope +1),
    oriented from lower left to upper right: `∫ F (c + v (1 + I)) (1 + I) dv`. -/
def lineUp (c : ℝ) (F : ℂ → ℂ) : ℂ := ∫ v : ℝ, F (c + v * (1 + I)) * (1 + I)

/-- The integral along the line through the real point `c` with direction `1 - I` (slope -1),
    oriented from upper left to lower right: `∫ F (c + v (1 - I)) (1 - I) dv`. -/
def lineDn (c : ℝ) (F : ℂ → ℂ) : ℂ := ∫ v : ℝ, F (c + v * (1 - I)) * (1 - I)

theorem lineUp_point (c u : ℝ) :
    (c : ℂ) + ((u - c / 2 : ℝ) : ℂ) * (1 + I) = (1 + I) * ((u : ℂ) + ((-c / 2 : ℝ) : ℂ) * I) := by
  push_cast; ring_nf; rw [I_sq]; ring

theorem lineDn_point (c u : ℝ) :
    (c : ℂ) + ((u - c / 2 : ℝ) : ℂ) * (1 - I) = (1 - I) * ((u : ℂ) + ((c / 2 : ℝ) : ℂ) * I) := by
  push_cast; ring_nf; rw [I_sq]; ring

/-- `lineUp` as a horizontal-line integral in the rotated coordinate `z`, `x = (1 + I) z`. -/
theorem lineUp_eq_rot (c : ℝ) (F : ℂ → ℂ) :
    lineUp c F = ∫ u : ℝ, F ((1 + I) * ((u : ℂ) + ((-c / 2 : ℝ) : ℂ) * I)) * (1 + I) := by
  unfold lineUp
  rw [← integral_sub_right_eq_self (fun v : ℝ => F (c + v * (1 + I)) * (1 + I)) (c / 2)]
  congr 1
  ext u
  rw [lineUp_point]

/-- `lineDn` as a horizontal-line integral in the rotated coordinate `z`, `x = (1 - I) z`. -/
theorem lineDn_eq_rot (c : ℝ) (F : ℂ → ℂ) :
    lineDn c F = ∫ u : ℝ, F ((1 - I) * ((u : ℂ) + ((c / 2 : ℝ) : ℂ) * I)) * (1 - I) := by
  unfold lineDn
  rw [← integral_sub_right_eq_self (fun v : ℝ => F (c + v * (1 - I)) * (1 - I)) (c / 2)]
  congr 1
  ext u
  rw [lineDn_point]

theorem re_sub_im_rotUp (z : ℂ) : ((1 + I) * z).re - ((1 + I) * z).im = -2 * z.im := by
  simp [mul_re, mul_im]; ring

theorem re_add_im_rotDn (z : ℂ) : ((1 - I) * z).re + ((1 - I) * z).im = 2 * z.im := by
  simp [mul_re, mul_im]; ring

theorem norm_rot_ge (w z : ℂ) (hw : ‖w‖ = Real.sqrt 2) : |z.re| ≤ ‖w * z‖ := by
  rw [norm_mul, hw]
  have h1 : |z.re| ≤ ‖z‖ := abs_re_le_norm z
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [norm_nonneg z]

theorem norm_one_add_I : ‖(1 + I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num

theorem norm_one_sub_I : ‖(1 - I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num

/-- **Line independence (slope +1).**  If `F` is continuous on the closed slanted strip
    `c1 <= Re x - Im x <= c2`, holomorphic inside, integrable along both lines and tends to `0` at
    infinity inside the strip, then `lineUp c1 F = lineUp c2 F`. -/
theorem lineUp_eq_of_strip {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂})
    (hint₁ : Integrable (fun v : ℝ => F (c₁ + v * (1 + I))))
    (hint₂ : Integrable (fun v : ℝ => F (c₂ + v * (1 + I))))
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → R ≤ ‖x‖ → ‖F x‖ ≤ ε) :
    lineUp c₁ F = lineUp c₂ F := by
  rw [lineUp_eq_rot, lineUp_eq_rot]
  set f : ℂ → ℂ := fun z => F ((1 + I) * z) * (1 + I) with hf
  have hy : -c₂ / 2 ≤ -c₁ / 2 := by linarith
  have hmaps : ∀ z : ℂ, z.im ∈ Icc (-c₂ / 2) (-c₁ / 2) →
      ((1 + I) * z).re - ((1 + I) * z).im ∈ Icc c₁ c₂ := by
    intro z hz
    rw [re_sub_im_rotUp]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hmapso : ∀ z : ℂ, z.im ∈ Ioo (-c₂ / 2) (-c₁ / 2) →
      ((1 + I) * z).re - ((1 + I) * z).im ∈ Ioo c₁ c₂ := by
    intro z hz
    rw [re_sub_im_rotUp]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have key := strip_integral_eq (f := f) hy
    (by
      intro z hz
      exact ((hcont _ (hmaps z hz)).comp (continuousWithinAt_id.const_mul (1 + I))
        (fun w hw => hmaps w hw)).mul continuousWithinAt_const)
    (by
      intro z hz
      exact ((hdiff _ (hmapso z hz)).comp z ((differentiableWithinAt_id).const_mul (1 + I))
        (fun w hw => hmapso w hw)).mul (differentiableWithinAt_const _))
    (by
      have := (hint₂.comp_sub_right (c₂ / 2)).mul_const (1 + I)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [hf]
      rw [lineUp_point])
    (by
      have := (hint₁.comp_sub_right (c₁ / 2)).mul_const (1 + I)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [hf]
      rw [lineUp_point])
    (by
      intro ε hε
      obtain ⟨R, hR⟩ := hdecay (ε / Real.sqrt 2) (by positivity)
      refine ⟨R, fun x y hx hy' => ?_⟩
      have hm := hmaps (x + y * I) (by simpa using hy')
      have hnorm : R ≤ ‖(1 + I) * ((x : ℂ) + y * I)‖ := by
        have h := norm_rot_ge (1 + I) ((x : ℂ) + y * I) norm_one_add_I
        have hre : ((x : ℂ) + y * I).re = x := by simp
        rw [hre] at h
        linarith
      simp only [hf]
      rw [norm_mul, norm_one_add_I]
      have := hR _ hm hnorm
      calc ‖F ((1 + I) * (↑x + ↑y * I))‖ * Real.sqrt 2 ≤ ε / Real.sqrt 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg 2)
        _ = ε := by field_simp)
  simp only [hf] at key
  exact key.symm

/-- **Line independence (slope -1).**  The `lineDn` analogue of `lineUp_eq_of_strip`, on the strip
    `c1 <= Re x + Im x <= c2`. -/
theorem lineDn_eq_of_strip {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re + x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re + x.im ∈ Ioo c₁ c₂})
    (hint₁ : Integrable (fun v : ℝ => F (c₁ + v * (1 - I))))
    (hint₂ : Integrable (fun v : ℝ => F (c₂ + v * (1 - I))))
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → R ≤ ‖x‖ → ‖F x‖ ≤ ε) :
    lineDn c₁ F = lineDn c₂ F := by
  rw [lineDn_eq_rot, lineDn_eq_rot]
  set f : ℂ → ℂ := fun z => F ((1 - I) * z) * (1 - I) with hf
  have hy : c₁ / 2 ≤ c₂ / 2 := by linarith
  have hmaps : ∀ z : ℂ, z.im ∈ Icc (c₁ / 2) (c₂ / 2) →
      ((1 - I) * z).re + ((1 - I) * z).im ∈ Icc c₁ c₂ := by
    intro z hz
    rw [re_add_im_rotDn]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hmapso : ∀ z : ℂ, z.im ∈ Ioo (c₁ / 2) (c₂ / 2) →
      ((1 - I) * z).re + ((1 - I) * z).im ∈ Ioo c₁ c₂ := by
    intro z hz
    rw [re_add_im_rotDn]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have key := strip_integral_eq (f := f) hy
    (by
      intro z hz
      exact ((hcont _ (hmaps z hz)).comp (continuousWithinAt_id.const_mul (1 - I))
        (fun w hw => hmaps w hw)).mul continuousWithinAt_const)
    (by
      intro z hz
      exact ((hdiff _ (hmapso z hz)).comp z ((differentiableWithinAt_id).const_mul (1 - I))
        (fun w hw => hmapso w hw)).mul (differentiableWithinAt_const _))
    (by
      have := (hint₁.comp_sub_right (c₁ / 2)).mul_const (1 - I)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [hf]
      rw [lineDn_point])
    (by
      have := (hint₂.comp_sub_right (c₂ / 2)).mul_const (1 - I)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [hf]
      rw [lineDn_point])
    (by
      intro ε hε
      obtain ⟨R, hR⟩ := hdecay (ε / Real.sqrt 2) (by positivity)
      refine ⟨R, fun x y hx hy' => ?_⟩
      have hm := hmaps (x + y * I) (by simpa using hy')
      have hnorm : R ≤ ‖(1 - I) * ((x : ℂ) + y * I)‖ := by
        have h := norm_rot_ge (1 - I) ((x : ℂ) + y * I) norm_one_sub_I
        have hre : ((x : ℂ) + y * I).re = x := by simp
        rw [hre] at h
        linarith
      simp only [hf]
      rw [norm_mul, norm_one_sub_I]
      have := hR _ hm hnorm
      calc ‖F ((1 - I) * (↑x + ↑y * I))‖ * Real.sqrt 2 ≤ ε / Real.sqrt 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg 2)
        _ = ε := by field_simp)
  simp only [hf] at key
  exact key

end RSInt
