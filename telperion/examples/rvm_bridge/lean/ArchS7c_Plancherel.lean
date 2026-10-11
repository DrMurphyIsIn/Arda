import ArchS7c_FourierH

/-!
# ArchS7c_Plancherel: the row kernel `M(w,·)` and its squared norm

* `plancherel`: for `F ∈ L¹ ∩ L²(ℝ)`, `∫ |F|² = (1/2π) ∫ |∫ F(s) e^{irs} ds|² dr`
  (Mathlib's L² isometry + S6 `fourier_ae_eq`).
* `integral_normSq_Hw`: `∫ |H_w|² = (1/2π) ∫ hsq g (-r) |Φ_r(w)|²/(4w) dr`.
* `Mk g w u = ∫ g(x) e^{x/2} 1{e^x|u| > 1} cos(2π e^x u w) dx`, the row of `P F P ϑ(g)`.
* `Mk_eq`: `Mk g w u = |u|^{-1/2} H_w(log|u|)`; `Mk_neg`, `Mk_neg_w` (evenness).
* `normSq_Mk_le`, `memLp_Mk`: `|M(w,u)|² ≤ 2K²/(1+u²)`, so `M(w,·) ∈ L²`.
* **`integral_normSq_Mk`**: `∫ |M(w,u)|² du = (1/4π) ∫ hsq g (-r) |Φ_r(w)|²/w dr` for `w > 0`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology Complex FourierTransform
open scoped ComplexConjugate

noncomputable section

namespace ArchS7c

open ArchS3

set_option linter.unusedSectionVars false

/-! ### Plancherel on `L¹ ∩ L²` with the kernel `e^{irs}` -/

theorem fourier_eq_transform (F : ℝ → ℂ) (r : ℝ) :
    ∫ s, F s * cexp (I * r * s) = 𝓕 F (-r / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext s
  rw [smul_eq_mul, mul_comm]
  congr 2
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem plancherel {F : ℝ → ℂ} (hF : Integrable F) (hF2 : MemLp F 2 volume) :
    Integrable (fun r : ℝ => ‖∫ s, F s * cexp (I * r * s)‖ ^ 2)
      ∧ ∫ s, ‖F s‖ ^ 2 = (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖∫ s, F s * cexp (I * r * s)‖ ^ 2 := by
  set f : ArchS6.L2R := hF2.toLp F
  have hfF : (f : ℝ → ℂ) =ᵐ[volume] F := hF2.coeFn_toLp
  have hf : Integrable (f : ℝ → ℂ) := hF.congr hfF.symm
  have h1 := ArchS6.fourier_ae_eq f hf
  have h2 : 𝓕 (f : ℝ → ℂ) = 𝓕 F := funext (ArchS7.fourier_congr_ae hfF)
  rw [h2] at h1
  have hphi : (fun ξ => ‖(𝓕 f : ArchS6.L2R) ξ‖ ^ 2) =ᵐ[volume] fun ξ => ‖𝓕 F ξ‖ ^ 2 := by
    filter_upwards [h1] with ξ hξ; rw [hξ]
  have hint : Integrable fun ξ => ‖𝓕 F ξ‖ ^ 2 :=
    ((Lp.memLp (𝓕 f : ArchS6.L2R)).integrable_norm_pow two_ne_zero).congr hphi
  have hval : ∫ ξ, ‖𝓕 F ξ‖ ^ 2 = ∫ s, ‖F s‖ ^ 2 := by
    rw [← integral_congr_ae hphi, ← ArchS7.norm_sq_eq_integral, Lp.norm_fourier_eq,
      ArchS7.norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hfF] with s hs; rw [hs]
  have hc : (-1 / (2 * Real.pi)) ≠ 0 := by
    have := Real.pi_pos; field_simp; norm_num
  have e : (fun r : ℝ => ‖∫ s, F s * cexp (I * r * s)‖ ^ 2)
      = fun r => (fun ξ => ‖𝓕 F ξ‖ ^ 2) (-1 / (2 * Real.pi) * r) := by
    funext r; rw [fourier_eq_transform]; congr 3; ring
  refine ⟨by rw [e]; exact hint.comp_mul_left' hc, ?_⟩
  rw [e, Measure.integral_comp_mul_left (fun ξ => ‖𝓕 F ξ‖ ^ 2), hval, smul_eq_mul, inv_div, abs_div, abs_neg, abs_one,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have := Real.pi_pos
  field_simp

/-! ### `∫ |H_w|²` -/

section

variable {g : ℝ → ℂ}

theorem normSq_cpow_neg_zt {w : ℝ} (hw : 0 < w) (r : ℝ) : ‖(w : ℂ) ^ (-zt r)‖ ^ 2 = 1 / w := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hw]
  have : (-zt r).re = -1 / 2 := by simp [zt]; norm_num
  rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hw.le]
  norm_num
  rw [Real.rpow_neg_one]

theorem normSq_fourier_Hw (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) (r : ℝ) :
    ‖∫ s, Hw g w s * cexp (I * r * s)‖ ^ 2
      = RvMBridge31.hsq g (-r) * ‖Phi r w‖ ^ 2 / (4 * w) := by
  rw [fourier_Hw hW hw r, norm_mul, norm_mul, norm_div, Complex.norm_ofNat, mul_pow, mul_pow,
    div_pow, normSq_cpow_neg_zt hw r, RvMBridge31.hsq]
  field_simp
  ring

theorem integrable_hsq_Phi (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) :
    Integrable fun r : ℝ => RvMBridge31.hsq g (-r) * ‖Phi r w‖ ^ 2 / (4 * w) := by
  have := (plancherel (integrable_Hw hW hw) (memLp_Hw hW hw)).1
  refine this.congr (Eventually.of_forall fun r => ?_)
  exact normSq_fourier_Hw hW hw r

theorem integral_normSq_Hw (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) :
    ∫ s, ‖Hw g w s‖ ^ 2
      = (1 / (2 * Real.pi)) * ∫ r : ℝ, RvMBridge31.hsq g (-r) * ‖Phi r w‖ ^ 2 / (4 * w) := by
  rw [(plancherel (integrable_Hw hW hw) (memLp_Hw hW hw)).2]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun r => normSq_fourier_Hw hW hw r)

end

/-! ### The row kernel `M(w,u)` -/

/-- `e^{x/2} 1{e^x|u| > 1} cos(2π e^x u w)`. -/
def mk (w u x : ℝ) : ℝ :=
  if 1 < Real.exp x * |u| then Real.exp (x / 2) * Real.cos (2 * Real.pi * (Real.exp x * u) * w) else 0

/-- **The row of `P F P ϑ(g)`**: `M(w,u) = ∫ g(x) e^{x/2} 1{e^x|u|>1} cos(2π e^x u w) dx`. -/
def Mk (g : ℝ → ℂ) (w u : ℝ) : ℂ := ∫ x, g x * (mk w u x : ℂ)

theorem one_lt_exp_iff' {y : ℝ} : 1 < Real.exp y ↔ 0 < y := by
  rw [← Real.exp_zero, Real.exp_lt_exp]

theorem mk_neg (w u x : ℝ) : mk w (-u) x = mk w u x := by
  unfold mk
  rw [abs_neg, show 2 * Real.pi * (Real.exp x * -u) * w = -(2 * Real.pi * (Real.exp x * u) * w) by ring,
    Real.cos_neg]

theorem mk_neg_w (w u x : ℝ) : mk (-w) u x = mk w u x := by
  unfold mk
  rw [show 2 * Real.pi * (Real.exp x * u) * -w = -(2 * Real.pi * (Real.exp x * u) * w) by ring,
    Real.cos_neg]

theorem Mk_neg (g : ℝ → ℂ) (w u : ℝ) : Mk g w (-u) = Mk g w u := by
  unfold Mk; simp_rw [mk_neg]

theorem Mk_neg_w (g : ℝ → ℂ) (w u : ℝ) : Mk g (-w) u = Mk g w u := by
  unfold Mk; simp_rw [mk_neg_w]

theorem mk_zero (w x : ℝ) : mk w 0 x = 0 := by
  unfold mk; rw [abs_zero, mul_zero, if_neg (by norm_num)]

theorem Mk_zero (g : ℝ → ℂ) (w : ℝ) : Mk g w 0 = 0 := by
  unfold Mk; simp [mk_zero]

theorem mk_eq {w : ℝ} (hw : 0 < w) {u : ℝ} (hu : u ≠ 0) (x : ℝ) :
    (mk w u x : ℂ) = (Real.exp (-(Real.log |u|) / 2) : ℂ) * cw w (x + Real.log |u|) := by
  have hu' : 0 < |u| := abs_pos.mpr hu
  have he : Real.exp x * |u| = Real.exp (x + Real.log |u|) := by
    rw [Real.exp_add, Real.exp_log hu']
  unfold mk cw
  rw [he]
  by_cases h : 0 < x + Real.log |u|
  · rw [if_pos (one_lt_exp_iff'.mpr h), if_pos h]
    have e1 : Real.exp (x / 2) = Real.exp (-(Real.log |u|) / 2) * Real.exp ((x + Real.log |u|) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.cos (2 * Real.pi * (Real.exp x * u) * w)
        = Real.cos (2 * Real.pi * w * Real.exp (x + Real.log |u|)) := by
      rw [← Real.cos_abs, ← he]
      congr 1
      simp only [abs_mul, abs_two, abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos x), abs_of_pos hw]
      ring
    rw [e1, e2]; push_cast; ring
  · rw [if_neg (fun h' => h (one_lt_exp_iff'.mp h')), if_neg h]; simp

theorem Mk_eq (g : ℝ → ℂ) {w : ℝ} (hw : 0 < w) {u : ℝ} (hu : u ≠ 0) :
    Mk g w u = (Real.exp (-(Real.log |u|) / 2) : ℂ) * Hw g w (Real.log |u|) := by
  unfold Mk Hw
  rw [← integral_const_mul]
  congr 1; funext x
  rw [mk_eq hw hu x]; ring

theorem measurable_mk (w : ℝ) : Measurable fun p : ℝ × ℝ => mk w p.1 p.2 := by
  unfold mk
  refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop) measurable_const

section

variable {g : ℝ → ℂ}

theorem aestronglyMeasurable_Mk (hgc : Continuous g) (w : ℝ) :
    AEStronglyMeasurable (Mk g w) volume := by
  have hm : Measurable fun p : ℝ × ℝ => g p.2 * (mk w p.1 p.2 : ℂ) :=
    (hgc.measurable.comp measurable_snd).mul (Complex.measurable_ofReal.comp (measurable_mk w))
  exact hm.aestronglyMeasurable.integral_prod_right' (μ := volume) (ν := volume)

/-- `|M(w,u)|² ≤ 2K²/(1+u²)`. -/
theorem normSq_Mk_le (hW : WeilExplicit.IsWeilTest g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, L ≤ |x| → g x = 0) {w : ℝ} (hw : 0 < w) (u : ℝ) :
    ‖Mk g w u‖ ^ 2 ≤ 2 * Kc g L w ^ 2 * (1 + u ^ 2)⁻¹ := by
  have hK := Kc_nonneg g hL0 hw
  rcases eq_or_ne u 0 with rfl | hu
  · rw [Mk_zero, norm_zero, zero_pow two_ne_zero]; positivity
  have hu' : 0 < |u| := abs_pos.mpr hu
  set s := Real.log |u| with hs
  have hb := norm_Hw_le hW hL0 hL hw s
  rw [Mk_eq g hw hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rcases le_or_gt 1 |u| with h1 | h1
  · have hs0 : 0 ≤ s := Real.log_nonneg h1
    have : Real.exp (-s / 2) * ‖Hw g w s‖ ≤ Kc g L w * |u|⁻¹ := by
      calc Real.exp (-s / 2) * ‖Hw g w s‖ ≤ Real.exp (-s / 2) * (Kc g L w * Real.exp (-|s| / 2)) := by
            gcongr
        _ = Kc g L w * Real.exp (-s) := by
            rw [abs_of_nonneg hs0, mul_left_comm, ← Real.exp_add]; congr 2; ring
        _ = Kc g L w * |u|⁻¹ := by rw [Real.exp_neg, hs, Real.exp_log hu']
    calc (Real.exp (-s / 2) * ‖Hw g w s‖) ^ 2 ≤ (Kc g L w * |u|⁻¹) ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
      _ = Kc g L w ^ 2 * (|u| ^ 2)⁻¹ := by rw [mul_pow, inv_pow]
      _ ≤ 2 * Kc g L w ^ 2 * (1 + u ^ 2)⁻¹ := by
          have ha : 1 ≤ |u| ^ 2 := by nlinarith
          have hx : (|u| ^ 2)⁻¹ ≤ 2 * (1 + u ^ 2)⁻¹ := by
            rw [hu2, show 2 * (1 + |u| ^ 2)⁻¹ = 2 / (1 + |u| ^ 2) by ring, inv_eq_one_div,
              div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          have := mul_le_mul_of_nonneg_left hx (sq_nonneg (Kc g L w))
          linarith
  · have hs0 : s < 0 := Real.log_neg hu' h1
    have : Real.exp (-s / 2) * ‖Hw g w s‖ ≤ Kc g L w := by
      calc Real.exp (-s / 2) * ‖Hw g w s‖ ≤ Real.exp (-s / 2) * (Kc g L w * Real.exp (-|s| / 2)) := by
            gcongr
        _ = Kc g L w := by
            rw [abs_of_neg hs0, mul_left_comm, ← Real.exp_add]
            rw [show -s / 2 + - -s / 2 = 0 by ring, Real.exp_zero, mul_one]
    calc (Real.exp (-s / 2) * ‖Hw g w s‖) ^ 2 ≤ Kc g L w ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
      _ ≤ 2 * Kc g L w ^ 2 * (1 + u ^ 2)⁻¹ := by
          rw [mul_assoc]
          have hx : 1 ≤ 2 * (1 + u ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
            nlinarith [abs_nonneg u]
          nlinarith [sq_nonneg (Kc g L w)]

theorem memLp_Mk (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) : MemLp (Mk g w) 2 volume := by
  obtain ⟨L, hL0, hL⟩ := exists_radius hW.2
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_Mk hW.1.continuous w)]
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * Kc g L w ^ 2))
    ((aestronglyMeasurable_Mk hW.1.continuous w).norm.pow 2) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact normSq_Mk_le hW hL0 hL hw u

theorem memLp_Mk' (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : w ≠ 0) :
    MemLp (Mk g w) 2 volume := by
  rcases lt_or_gt_of_ne hw with h | h
  · have e : Mk g w = Mk g (-w) := funext fun u => (Mk_neg_w g w u).symm
    rw [e]; exact memLp_Mk hW (neg_pos.mpr h)
  · exact memLp_Mk hW h

/-- `∫_ℝ |M(w,u)|² du = 2 ∫ |H_w(s)|² ds` (`u = ±e^s`). -/
theorem integral_normSq_Mk_eq_Hw (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) :
    ∫ u, ‖Mk g w u‖ ^ 2 = 2 * ∫ s, ‖Hw g w s‖ ^ 2 := by
  have h1 : ∫ u, ‖Mk g w u‖ ^ 2 = ∫ u, ‖Mk g w |u|‖ ^ 2 := by
    congr 1; funext u
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Mk_neg]
  rw [h1, integral_comp_abs (f := fun u => ‖Mk g w u‖ ^ 2)]
  congr 1
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun u => ‖Mk g w u‖ ^ 2)
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at hsub
  rw [hsub]
  congr 1; funext s
  rw [abs_of_pos (Real.exp_pos s), smul_eq_mul, Mk_eq g hw (Real.exp_pos s).ne',
    abs_of_pos (Real.exp_pos s), Real.log_exp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← mul_assoc]
  have : Real.exp s * Real.exp (-s / 2) ^ 2 = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, show s + (-s / 2 + -s / 2) = 0 by ring, Real.exp_zero]
  rw [this, one_mul]

/-- **Per-`w` Plancherel**: `∫ |M(w,u)|² du = (1/4π) ∫ hsq g (-r) |Φ_r(w)|²/w dr` for `w > 0`. -/
theorem integral_normSq_Mk (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) :
    ∫ u, ‖Mk g w u‖ ^ 2
      = (1 / (4 * Real.pi)) * ∫ r : ℝ, RvMBridge31.hsq g (-r) * ‖Phi r w‖ ^ 2 / w := by
  rw [integral_normSq_Mk_eq_Hw hW hw, integral_normSq_Hw hW hw]
  have e : (fun r : ℝ => RvMBridge31.hsq g (-r) * ‖Phi r w‖ ^ 2 / (4 * w))
      = fun r => (1 / 4) * (RvMBridge31.hsq g (-r) * ‖Phi r w‖ ^ 2 / w) := by
    funext r; field_simp
  rw [e, integral_const_mul]
  have := Real.pi_pos
  field_simp

end

end ArchS7c
