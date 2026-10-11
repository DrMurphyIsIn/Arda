import ArchS3_Limits
import ArchS7_Lemma41

/-!
# ArchS7c_Decay: the log-variable kernel `H_w` and its decay

For a test function `g` (smooth, compact support) and `w > 0`:

* `cw w t = 1{t>0} e^{t/2} cos(2π w e^t)` and `Hw g w s = ∫ g(x) c_w(x+s) dx`.
* `exists_radius`: `g x = 0` for `|x| ≥ L`.
* `Hw_eq_zero`: `H_w(s) = 0` for `s ≤ -L`.
* `norm_Hw_le_large`: `|H_w(s)| ≤ e^{-s/2}/(2πw) · C_g` for `s > L` (one integration by parts in `x`).
* `norm_Hw_le`: `|H_w(s)| ≤ K e^{-|s|/2}` for all `s`, hence `H_w ∈ L¹ ∩ L²`.

`H_w(log|u|) |u|^{-1/2}` is the row `M(w,u)` of the operator `P F P ϑ(g)` (S7c notes §2).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace ArchS7c

set_option linter.unusedSectionVars false

/-- `c_w(t) = 1{t>0} e^{t/2} cos(2π w e^t)`. -/
def cw (w t : ℝ) : ℂ :=
  if 0 < t then ((Real.exp (t / 2) * Real.cos (2 * Real.pi * w * Real.exp t) : ℝ) : ℂ) else 0

/-- `H_w(s) = ∫ g(x) c_w(x + s) dx`. -/
def Hw (g : ℝ → ℂ) (w s : ℝ) : ℂ := ∫ x, g x * cw w (x + s)

theorem measurable_cw (w : ℝ) : Measurable (cw w) := by
  unfold cw
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact Complex.measurable_ofReal.comp (by fun_prop)

theorem norm_cw_le (w t : ℝ) : ‖cw w t‖ ≤ Real.exp (t / 2) := by
  unfold cw
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  · rw [norm_zero]; positivity

theorem cw_of_pos (w : ℝ) {t : ℝ} (ht : 0 < t) :
    cw w t = ((Real.exp (t / 2) * Real.cos (2 * Real.pi * w * Real.exp t) : ℝ) : ℂ) := by
  rw [cw, if_pos ht]

theorem cw_of_nonpos (w : ℝ) {t : ℝ} (ht : t ≤ 0) : cw w t = 0 := by
  rw [cw, if_neg (not_lt.mpr ht)]

section

variable {g : ℝ → ℂ}

/-- A support radius: `g x = 0` for `|x| ≥ L`. -/
theorem exists_radius (hc : HasCompactSupport g) : ∃ L : ℝ, 0 < L ∧ ∀ x, L ≤ |x| → g x = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hc.isCompact.isBounded
  refine ⟨max R 0 + 1, by positivity, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hx'
  have h := hR hx'
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
  have := le_max_left R 0
  linarith

theorem lt_of_ne_zero {L : ℝ} (hL : ∀ x, L ≤ |x| → g x = 0) {x : ℝ} (hx : g x ≠ 0) : |x| < L :=
  not_le.mp fun h => hx (hL x h)

theorem Hw_eq_zero {L : ℝ} (hL : ∀ x, L ≤ |x| → g x = 0) (w : ℝ) {s : ℝ} (hs : s ≤ -L) :
    Hw g w s = 0 := by
  unfold Hw
  have : (fun x => g x * cw w (x + s)) = fun _ => (0 : ℂ) := by
    funext x
    by_cases hx : g x = 0
    · rw [hx, zero_mul]
    · have := (abs_lt.mp (lt_of_ne_zero hL hx)).2
      rw [cw_of_nonpos w (by linarith), mul_zero]
  rw [this, integral_zero]

theorem norm_Hw_le_small (hg : Integrable g) {L : ℝ} (hL : ∀ x, L ≤ |x| → g x = 0) (w s : ℝ) :
    ‖Hw g w s‖ ≤ Real.exp ((L + s) / 2) * ∫ x, ‖g x‖ := by
  unfold Hw
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.norm.const_mul _) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  by_cases hx : g x = 0
  · rw [hx, norm_zero, zero_mul]; positivity
  · have hxL := (abs_lt.mp (lt_of_ne_zero hL hx)).2
    calc ‖g x‖ * ‖cw w (x + s)‖ ≤ ‖g x‖ * Real.exp ((L + s) / 2) := by
          gcongr
          exact (norm_cw_le w _).trans (Real.exp_le_exp.mpr (by linarith))
      _ = _ := by ring

/-- The integration-by-parts constant `C_g = ∫_{-L}^{L} |g' - g/2| e^{-x/2}`. -/
def ibpC (g : ℝ → ℂ) (L : ℝ) : ℝ := ∫ x in (-L)..L, ‖deriv g x - g x / 2‖ * Real.exp (-x / 2)

theorem ibpC_nonneg (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) : 0 ≤ ibpC g L :=
  intervalIntegral.integral_nonneg (by linarith) fun x _ => by positivity

theorem Hw_eq_interval {L : ℝ} (hL : ∀ x, L ≤ |x| → g x = 0) (hL0 : 0 < L) (w : ℝ) {s : ℝ}
    (hs : L < s) :
    Hw g w s = ∫ x in (-L)..L,
      g x * ((Real.exp ((x + s) / 2) * Real.cos (2 * Real.pi * w * Real.exp (x + s)) : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∫ x in Ioc (-L) L, g x * cw w (x + s) = Hw g w s := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have : L ≤ |x| := by
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hL x this, zero_mul]
  rw [← h1]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  show g x * cw w (x + s) = _
  rw [cw_of_pos w (by linarith [hx.1])]

/-- **One integration by parts**: `|H_w(s)| ≤ e^{-s/2}/(2πw) · C_g` for `s > L`. -/
theorem norm_Hw_le_large (hW : WeilExplicit.IsWeilTest g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, L ≤ |x| → g x = 0) {w : ℝ} (hw : 0 < w) {s : ℝ} (hs : L < s) :
    ‖Hw g w s‖ ≤ Real.exp (-s / 2) / (2 * Real.pi * w) * ibpC g L := by
  rw [Hw_eq_interval hL hL0 w hs]
  have hpw : 0 < 2 * Real.pi * w := by positivity
  set c : ℝ → ℝ := fun x => Real.exp (-(x + s) / 2) / (2 * Real.pi * w) with hcdef
  set u : ℝ → ℂ := fun x => g x * (c x : ℂ) with hudef
  set u' : ℝ → ℂ := fun x => deriv g x * (c x : ℂ) + g x * ((-(c x) / 2 : ℝ) : ℂ) with hu'def
  set φ : ℝ → ℝ := fun x => 2 * Real.pi * w * Real.exp (x + s) with hφdef
  set v : ℝ → ℂ := fun x => ((Real.sin (φ x) : ℝ) : ℂ) with hvdef
  set v' : ℝ → ℂ := fun x => ((Real.cos (φ x) * φ x : ℝ) : ℂ) with hv'def
  have hgd : Differentiable ℝ g := hW.1.differentiable (by simp)
  have hgc : Continuous g := hW.1.continuous
  have hdgc : Continuous (deriv g) := hW.1.continuous_deriv (by simp)
  have hc : ∀ x, HasDerivAt c (-(c x) / 2) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(x + s) / 2) (-1 / 2) x := by
      have := ((hasDerivAt_id x).add_const s).neg.div_const 2
      simpa using this
    have h2 := ((Real.hasDerivAt_exp _).comp x h1).div_const (2 * Real.pi * w)
    have e : -(c x) / 2 = Real.exp (-(x + s) / 2) * (-1 / 2) / (2 * Real.pi * w) := by
      show -(Real.exp (-(x + s) / 2) / (2 * Real.pi * w)) / 2 = _
      ring
    rw [e]; exact h2
  have hφ : ∀ x, HasDerivAt φ (φ x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x + s) 1 x := (hasDerivAt_id x).add_const s
    have h2 := ((Real.hasDerivAt_exp _).comp x h1).const_mul (2 * Real.pi * w)
    have e : φ x = 2 * Real.pi * w * (Real.exp (x + s) * 1) := by
      show 2 * Real.pi * w * Real.exp (x + s) = _
      ring
    rw [e]; exact h2
  have hu : ∀ x, HasDerivAt u (u' x) x := fun x =>
    (hgd x).hasDerivAt.mul (hc x).ofReal_comp
  have hv : ∀ x, HasDerivAt v (v' x) x := by
    intro x
    have := ((Real.hasDerivAt_sin (φ x)).comp x (hφ x)).ofReal_comp
    simpa [hvdef, hv'def] using this
  have hcc : Continuous c := by simp only [hcdef]; fun_prop
  have hφc : Continuous φ := by simp only [hφdef]; fun_prop
  have hu'c : Continuous u' := by
    simp only [hu'def]
    exact (hdgc.mul (Complex.continuous_ofReal.comp hcc)).add
      (hgc.mul (Complex.continuous_ofReal.comp (hcc.neg.div_const 2)))
  have hv'c : Continuous v' := by
    simp only [hv'def]
    exact Complex.continuous_ofReal.comp ((Real.continuous_cos.comp hφc).mul hφc)
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -L) (b := L)
    (fun x _ => hu x) (fun x _ => hv x) (hu'c.intervalIntegrable _ _) (hv'c.intervalIntegrable _ _)
  have hint : ∀ x, g x * ((Real.exp ((x + s) / 2) * Real.cos (2 * Real.pi * w * Real.exp (x + s)) : ℝ) : ℂ)
      = u x * v' x := by
    intro x
    show g x * ((Real.exp ((x + s) / 2) * Real.cos (2 * Real.pi * w * Real.exp (x + s)) : ℝ) : ℂ)
      = g x * ((Real.exp (-(x + s) / 2) / (2 * Real.pi * w) : ℝ) : ℂ)
        * ((Real.cos (2 * Real.pi * w * Real.exp (x + s)) * (2 * Real.pi * w * Real.exp (x + s)) : ℝ) : ℂ)
    have e1 : Real.exp (-(x + s) / 2) * Real.exp (x + s) = Real.exp ((x + s) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(x + s) / 2) / (2 * Real.pi * w)
        * (Real.cos (2 * Real.pi * w * Real.exp (x + s)) * (2 * Real.pi * w * Real.exp (x + s)))
        = Real.exp ((x + s) / 2) * Real.cos (2 * Real.pi * w * Real.exp (x + s)) := by
      rw [← e1]; field_simp
    rw [mul_assoc (g x), ← Complex.ofReal_mul, e2]
  have hgL : g L = 0 := hL L (by rw [abs_of_pos hL0])
  have hgL' : g (-L) = 0 := hL (-L) (by rw [abs_neg, abs_of_pos hL0])
  simp_rw [hint]
  rw [key]
  simp only [hudef, hgL, hgL', zero_mul, sub_zero, zero_sub, norm_neg]
  have hbound : ∀ x, ‖u' x * v x‖
      ≤ Real.exp (-s / 2) / (2 * Real.pi * w) * (‖deriv g x - g x / 2‖ * Real.exp (-x / 2)) := by
    intro x
    have hu'eq : u' x = (deriv g x - g x / 2) * (c x : ℂ) := by
      simp only [hu'def]; push_cast; ring
    have hvx : ‖v x‖ ≤ 1 := by
      simp only [hvdef, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _
    have hcx : c x = Real.exp (-s / 2) / (2 * Real.pi * w) * Real.exp (-x / 2) := by
      simp only [hcdef]
      rw [div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring
    rw [norm_mul, hu'eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by simp only [hcdef]; positivity), hcx]
    calc ‖deriv g x - g x / 2‖ * (Real.exp (-s / 2) / (2 * Real.pi * w) * Real.exp (-x / 2)) * ‖v x‖
        ≤ ‖deriv g x - g x / 2‖ * (Real.exp (-s / 2) / (2 * Real.pi * w) * Real.exp (-x / 2)) * 1 := by
          gcongr
      _ = _ := by ring
  calc ‖∫ x in (-L)..L, u' x * v x‖
      ≤ ∫ x in (-L)..L, Real.exp (-s / 2) / (2 * Real.pi * w) * (‖deriv g x - g x / 2‖ * Real.exp (-x / 2)) :=
        intervalIntegral.norm_integral_le_of_norm_le (by linarith)
          (Eventually.of_forall fun x _ => hbound x)
          ((by fun_prop : Continuous fun x =>
            Real.exp (-s / 2) / (2 * Real.pi * w) * (‖deriv g x - g x / 2‖ * Real.exp (-x / 2))).intervalIntegrable _ _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, ibpC]

/-- The decay constant. -/
def Kc (g : ℝ → ℂ) (L w : ℝ) : ℝ :=
  Real.exp (3 * L / 2) * (∫ x, ‖g x‖) + ibpC g L / (2 * Real.pi * w)

theorem Kc_nonneg (g : ℝ → ℂ) {L w : ℝ} (hL : 0 < L) (hw : 0 < w) : 0 ≤ Kc g L w := by
  unfold Kc
  have := ibpC_nonneg g hL
  have : 0 ≤ ∫ x, ‖g x‖ := integral_nonneg fun _ => norm_nonneg _
  positivity

/-- **Decay of `H_w`**: `|H_w(s)| ≤ K e^{-|s|/2}` for every `s`. -/
theorem norm_Hw_le (hW : WeilExplicit.IsWeilTest g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, L ≤ |x| → g x = 0) {w : ℝ} (hw : 0 < w) (s : ℝ) :
    ‖Hw g w s‖ ≤ Kc g L w * Real.exp (-|s| / 2) := by
  have hg : Integrable g := hW.1.continuous.integrable_of_hasCompactSupport hW.2
  have hI : 0 ≤ ∫ x, ‖g x‖ := integral_nonneg fun _ => norm_nonneg _
  have hC := ibpC_nonneg g hL0
  have hpw : 0 < 2 * Real.pi * w := by positivity
  rcases le_or_gt s (-L) with h1 | h1
  · rw [Hw_eq_zero hL w h1, norm_zero]
    exact mul_nonneg (Kc_nonneg g hL0 hw) (Real.exp_pos _).le
  rcases le_or_gt s L with h2 | h2
  · have habs : |s| ≤ L := abs_le.mpr ⟨by linarith, h2⟩
    calc ‖Hw g w s‖ ≤ Real.exp ((L + s) / 2) * ∫ x, ‖g x‖ := norm_Hw_le_small hg hL w s
      _ ≤ Real.exp (3 * L / 2) * Real.exp (-|s| / 2) * ∫ x, ‖g x‖ := by
          gcongr
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith)
      _ ≤ Kc g L w * Real.exp (-|s| / 2) := by
          unfold Kc
          have : 0 ≤ ibpC g L / (2 * Real.pi * w) * Real.exp (-|s| / 2) := by positivity
          nlinarith [Real.exp_pos (-|s| / 2)]
  · rw [abs_of_pos (by linarith)]
    calc ‖Hw g w s‖ ≤ Real.exp (-s / 2) / (2 * Real.pi * w) * ibpC g L :=
          norm_Hw_le_large hW hL0 hL hw h2
      _ = ibpC g L / (2 * Real.pi * w) * Real.exp (-s / 2) := by ring
      _ ≤ Kc g L w * Real.exp (-s / 2) := by
          unfold Kc
          have : 0 ≤ Real.exp (3 * L / 2) * (∫ x, ‖g x‖) * Real.exp (-s / 2) := by positivity
          nlinarith [Real.exp_pos (-s / 2)]

/-- `e^{-|s|/2} ≤ 8/(1+s²)`. -/
theorem exp_neg_abs_half_le (s : ℝ) : Real.exp (-|s| / 2) ≤ 8 * (1 + s ^ 2)⁻¹ := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := |s| / 2) (by positivity)
  have h : (1 + s ^ 2) / 8 ≤ Real.exp (|s| / 2) := by
    nlinarith [sq_abs s, abs_nonneg s]
  calc Real.exp (-|s| / 2) = (Real.exp (|s| / 2))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
    _ ≤ ((1 + s ^ 2) / 8)⁻¹ := inv_anti₀ (by positivity) h
    _ = 8 * (1 + s ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

theorem aestronglyMeasurable_Hw (hgc : Continuous g) (w : ℝ) :
    AEStronglyMeasurable (Hw g w) volume := by
  have hm : Measurable fun p : ℝ × ℝ => g p.2 * cw w (p.2 + p.1) :=
    (hgc.measurable.comp measurable_snd).mul ((measurable_cw w).comp (measurable_snd.add measurable_fst))
  exact hm.aestronglyMeasurable.integral_prod_right' (μ := volume) (ν := volume)

theorem norm_Hw_le' (hW : WeilExplicit.IsWeilTest g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, L ≤ |x| → g x = 0) {w : ℝ} (hw : 0 < w) (s : ℝ) :
    ‖Hw g w s‖ ≤ 8 * Kc g L w * (1 + s ^ 2)⁻¹ := by
  calc ‖Hw g w s‖ ≤ Kc g L w * Real.exp (-|s| / 2) := norm_Hw_le hW hL0 hL hw s
    _ ≤ Kc g L w * (8 * (1 + s ^ 2)⁻¹) := by
        gcongr
        · exact Kc_nonneg g hL0 hw
        · exact exp_neg_abs_half_le s
    _ = _ := by ring

theorem integrable_Hw (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) :
    Integrable (Hw g w) := by
  obtain ⟨L, hL0, hL⟩ := exists_radius hW.2
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (8 * Kc g L w))
    (aestronglyMeasurable_Hw hW.1.continuous w) (Eventually.of_forall fun s => ?_)
  exact norm_Hw_le' hW hL0 hL hw s

theorem memLp_Hw (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) :
    MemLp (Hw g w) 2 volume := by
  obtain ⟨L, hL0, hL⟩ := exists_radius hW.2
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_Hw hW.1.continuous w)]
  have hK := Kc_nonneg g hL0 hw
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul ((8 * Kc g L w) ^ 2))
    ((aestronglyMeasurable_Hw hW.1.continuous w).norm.pow 2) (Eventually.of_forall fun s => ?_)
  have h1 := norm_Hw_le' hW hL0 hL hw s
  have h2 : (1 + s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have h3 : 0 ≤ (1 + s ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖Hw g w s‖ ^ 2 ≤ (8 * Kc g L w * (1 + s ^ 2)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (8 * Kc g L w) ^ 2 * ((1 + s ^ 2)⁻¹ * (1 + s ^ 2)⁻¹) := by ring
    _ ≤ (8 * Kc g L w) ^ 2 * (1 + s ^ 2)⁻¹ := by
        gcongr
        nlinarith

end

end ArchS7c
