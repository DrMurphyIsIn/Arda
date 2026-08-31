import StripRepr

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal NNReal

namespace ZeroFreeBridge

/-- Parameter-derivative of the strip integrand at base point `z`:
`-fract(x) * Complex.log x * x^{-(z+1)}`. -/
noncomputable def fractIntegrand' (z : ℂ) (x : ℝ) : ℂ :=
    -(((Int.fract x : ℝ) : ℂ) * Complex.log (x : ℂ) * (x : ℂ) ^ (-(z + 1)))

/-- The uniform dominating function on `Ioi 1` for parameter `re > σ₀`. -/
noncomputable def fractBound (σ₀ : ℝ) (x : ℝ) : ℝ :=
    Real.log x * x ^ (-(σ₀ + 1))

/-- Rewrite `fractIntegrand` as a product with a negative complex power (for `x > 0`). -/
theorem fractIntegrand_eq_mul {s : ℂ} {x : ℝ} :
    fractIntegrand s x = ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  unfold fractIntegrand
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-- Integrability of the dominating function `log x * x^(-(σ₀+1))` on `Ioi 1`, for `σ₀ > 0`. -/
theorem integrableOn_fractBound {σ₀ : ℝ} (hσ : 0 < σ₀) :
    IntegrableOn (fractBound σ₀) (Ioi (1 : ℝ)) := by
  -- dominate by g x = (2/σ₀) * x^(-(σ₀/2 + 1)), integrable since exponent < -1
  have hε : (0 : ℝ) < σ₀ / 2 := by positivity
  set g : ℝ → ℝ := fun x => (σ₀ / 2)⁻¹ * x ^ (-(σ₀ / 2 + 1)) with hg
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-(σ₀ / 2 + 1))) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    exact (hbase.const_mul _)
  refine Integrable.mono' hgint ?_ ?_
  · -- measurability of fractBound
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact Real.measurable_log
    · exact (Real.measurable_rpow_const)
  · -- pointwise bound a.e. on Ioi 1
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hrpow0 : 0 ≤ x ^ (-(σ₀ + 1)) := Real.rpow_nonneg (le_of_lt hx0) _
    -- fractBound x ≥ 0, so ‖·‖ = fractBound x
    have hb0 : 0 ≤ fractBound σ₀ x := by
      unfold fractBound; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hb0]
    -- log x ≤ x^(σ₀/2)/(σ₀/2)
    have hlogle : Real.log x ≤ x ^ (σ₀ / 2) / (σ₀ / 2) :=
      Real.log_le_rpow_div (le_of_lt hx0) hε
    -- fractBound x = log x * x^(-(σ₀+1)) ≤ (x^(σ₀/2)/(σ₀/2)) * x^(-(σ₀+1)) = g x
    have hstep : fractBound σ₀ x ≤ (x ^ (σ₀ / 2) / (σ₀ / 2)) * x ^ (-(σ₀ + 1)) := by
      unfold fractBound
      exact mul_le_mul_of_nonneg_right hlogle hrpow0
    refine hstep.trans ?_
    rw [hg]
    -- (x^(σ₀/2)/(σ₀/2)) * x^(-(σ₀+1)) = (σ₀/2)⁻¹ * x^(-(σ₀/2+1))
    rw [div_mul_eq_mul_div, ← Real.rpow_add hx0]
    rw [mul_comm ((σ₀ / 2)⁻¹) _, mul_div_assoc]
    apply le_of_eq
    rw [mul_comm]
    congr 1
    · ring_nf
    · rw [div_eq_inv_mul]

/-- Main result on the open right half-plane. -/
theorem differentiableAt_fractIntegral' {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ fractIntegral z := by
  set σ₀ : ℝ := z.re / 2 with hσ0
  have hσpos : 0 < σ₀ := by rw [hσ0]; linarith
  -- the strip S = {w | σ₀ < w.re}
  set S : Set ℂ := {w : ℂ | σ₀ < w.re} with hSdef
  have hzS : z ∈ S := by rw [hSdef]; simp only [mem_setOf_eq]; rw [hσ0]; linarith
  have hSopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hSnhds : S ∈ 𝓝 z := hSopen.mem_nhds hzS
  have hSconvex : Convex ℝ S := convex_halfSpace_re_gt σ₀
  -- F w x = fractIntegrand w x
  set F : ℂ → ℝ → ℂ := fun w x => fractIntegrand w x with hFdef
  -- derivative function F' x (at base point z)
  set F' : ℝ → ℂ := fun x => fractIntegrand' z x with hF'def
  -- the dominating function
  set bound : ℝ → ℝ := fractBound σ₀ with hbdef
  -- MEASURABILITY of F w for w in a neighbourhood of z
  have hmeasFw : ∀ w : ℂ, AEStronglyMeasurable (F w) (volume.restrict (Ioi (1 : ℝ))) := by
    intro w
    apply Measurable.aestronglyMeasurable
    unfold_let F
    unfold fractIntegrand
    apply Measurable.div
    · exact (Complex.measurable_ofReal.comp measurable_fract)
    · apply Measurable.pow measurable_const
      exact measurable_const.comp (Complex.measurable_ofReal.comp measurable_id)
  -- hF_meas
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict (Ioi (1 : ℝ))) :=
    Filter.Eventually.of_forall hmeasFw
  -- hF'_meas
  have hF'_meas : AEStronglyMeasurable F' (volume.restrict (Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    unfold_let F'
    unfold fractIntegrand'
    apply Measurable.neg
    apply Measurable.mul
    · apply Measurable.mul
      · exact (Complex.measurable_ofReal.comp measurable_fract)
      · exact Complex.measurable_log.comp
          (Complex.measurable_ofReal.comp measurable_id)
    · apply Measurable.pow measurable_const
      exact measurable_const.comp (Complex.measurable_ofReal.comp measurable_id)
  -- BASE integrability hF_int : Integrable (F z) on Ioi 1
  have hF_int : Integrable (F z) (volume.restrict (Ioi (1 : ℝ))) := by
    -- dominate ‖fract x * x^{-(z+1)}‖ ≤ x^{-(z.re+1)} which is ≤ x^{-(σ₀+1)} (integrable)
    have hbase : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ (-(z + 1))‖) (Ioi (1 : ℝ)) := by
      apply integrableOn_Ioi_norm_cpow_of_lt (c := 1)
      · -- (-(z+1)).re < -1
        simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
        linarith
      · norm_num
    refine Integrable.mono' hbase (hmeasFw z) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := by linarith
    -- ‖F z x‖ = ‖fract x‖ * ‖x^{-(z+1)}‖ ≤ 1 * ‖x^{-(z+1)}‖
    rw [hFdef]
    simp only
    rw [fractIntegrand_eq_mul, norm_mul]
    have hfr : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
      exact le_of_lt (Int.fract_lt_one x)
    calc ‖((Int.fract x : ℝ) : ℂ)‖ * ‖(x : ℂ) ^ (-(z + 1))‖
        ≤ 1 * ‖(x : ℂ) ^ (-(z + 1))‖ :=
          mul_le_mul_of_nonneg_right hfr (norm_nonneg _)
      _ = ‖(x : ℂ) ^ (-(z + 1))‖ := one_mul _
  -- bound_integrable
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    rw [hbdef]; exact integrableOn_fractBound hσpos
  -- h_diff : a.e. HasDerivAt (F · x) (F' x) z
  have h_diff : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      HasDerivAt (fun w => F w x) (F' x) z := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hxne : (x : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
    -- inner derivative: HasDerivAt (fun w => -(w+1)) (-1) z
    have hinner : HasDerivAt (fun w : ℂ => -(w + 1)) (-1) z := by
      have h1 : HasDerivAt (fun w : ℂ => w + 1) 1 z :=
        (hasDerivAt_id z).add_const 1
      simpa using h1.neg
    -- HasDerivAt (fun w => (x:ℂ)^(-(w+1))) ((x:ℂ)^(-(z+1)) * Complex.log x * (-1)) z
    have hpow : HasDerivAt (fun w : ℂ => (x : ℂ) ^ (-(w + 1)))
        ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) z :=
      hinner.const_cpow (Or.inl hxne)
    -- multiply by the constant fract x
    have hmul : HasDerivAt (fun w : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1)))
        (((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1))) z :=
      hpow.const_mul _
    -- rewrite F and F' into this form
    have hFrw : (fun w => F w x) = fun w : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1)) := by
      funext w; rw [hFdef]; simp only; rw [fractIntegrand_eq_mul]
    rw [hFrw]
    have hF'rw : F' x = ((Int.fract x : ℝ) : ℂ)
        * ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) := by
      rw [hF'def]; unfold fractIntegrand'; ring
    rw [hF'rw]
    exact hmul
  -- h_lipsch : a.e. LipschitzOnWith (Real.nnabs (bound x)) (F · x) S
  have h_lipsch : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      LipschitzOnWith (Real.nnabs (bound x)) (fun w => F w x) S := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hxne : (x : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    -- bound x ≥ 0, so nnabs (bound x) coerces to bound x
    have hb0 : 0 ≤ bound x := by
      rw [hbdef]; unfold fractBound
      have : 0 ≤ x ^ (-(σ₀ + 1)) := Real.rpow_nonneg (le_of_lt hx0) _
      positivity
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le hSconvex
      (f := fun w => F w x)
      (f' := fun w => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1))
    · -- derivative on S
      intro w hw
      have hinner : HasDerivAt (fun v : ℂ => -(v + 1)) (-1) w := by
        have h1 : HasDerivAt (fun v : ℂ => v + 1) 1 w := (hasDerivAt_id w).add_const 1
        simpa using h1.neg
      have hpow : HasDerivAt (fun v : ℂ => (x : ℂ) ^ (-(v + 1)))
          ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1)) w :=
        hinner.const_cpow (Or.inl hxne)
      have hmul : HasDerivAt (fun v : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(v + 1)))
          (((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1))) w :=
        hpow.const_mul _
      have hFrw : (fun v => F v x) = fun v : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(v + 1)) := by
        funext v; rw [hFdef]; simp only; rw [fractIntegrand_eq_mul]
      rw [hFrw]
      have : (((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1)))
          = ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1) := by
        ring
      rw [this] at hmul
      exact hmul.hasDerivWithinAt
    · -- norm bound on derivative over S, ≤ nnabs (bound x)
      intro w hw
      rw [hSdef] at hw
      simp only [mem_setOf_eq] at hw
      -- ‖f' w‖ = fract x * |log x| * x^{-(w.re+1)} ≤ 1 * log x * x^{-(σ₀+1)} = bound x
      rw [← NNReal.coe_le_coe]
      rw [Real.coe_nnabs, abs_of_nonneg hb0]
      rw [coe_nnnorm]
      -- compute ‖ f' w ‖
      have hnormeq : ‖((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))
          * Complex.log (x : ℂ) * (-1)‖
          = (Int.fract x) * Real.log x * x ^ (-(w.re + 1)) := by
        rw [norm_mul, norm_mul, norm_mul]
        rw [norm_neg, norm_one, mul_one]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        rw [← Complex.ofReal_log (le_of_lt hx0), Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlog0]
        congr 2
        · ring
        · simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      rw [hnormeq]
      rw [hbdef]; unfold fractBound
      -- (fract x) * log x * x^{-(w.re+1)} ≤ log x * x^{-(σ₀+1)}
      have hfrle : Int.fract x ≤ 1 := le_of_lt (Int.fract_lt_one x)
      have hrpow_mono : x ^ (-(w.re + 1)) ≤ x ^ (-(σ₀ + 1)) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hrpow0 : 0 ≤ x ^ (-(w.re + 1)) := Real.rpow_nonneg (le_of_lt hx0) _
      calc (Int.fract x) * Real.log x * x ^ (-(w.re + 1))
          ≤ 1 * Real.log x * x ^ (-(w.re + 1)) := by
            apply mul_le_mul_of_nonneg_right _ hrpow0
            exact mul_le_mul_of_nonneg_right hfrle hlog0
        _ = Real.log x * x ^ (-(w.re + 1)) := by rw [one_mul]
        _ ≤ Real.log x * x ^ (-(σ₀ + 1)) :=
            mul_le_mul_of_nonneg_left hrpow_mono hlog0
  -- APPLY the parametric integral theorem
  have main := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (x₀ := z) (bound := bound)
    hSnhds hF_meas hF_int hF'_meas h_lipsch hbound_int h_diff
  -- main.2 : HasDerivAt (fun w => ∫ a, F w a ∂μ) (∫ a, F' a ∂μ) z
  have hderiv : HasDerivAt (fun w => ∫ a in Ioi (1 : ℝ), F w a) (∫ a in Ioi (1 : ℝ), F' a) z :=
    main.2
  -- (fun w => ∫ a in Ioi 1, F w a) = fractIntegral
  have hcongr : (fun w => ∫ a in Ioi (1 : ℝ), F w a) = fractIntegral := by
    funext w; rw [hFdef]; rfl
  rw [hcongr] at hderiv
  exact hderiv.differentiableAt

/-- `stripDomain` version (hypothesis R2 of `zeta_fract_repr_of`). -/
theorem differentiableAt_fractIntegral {z : ℂ} (hz : z ∈ stripDomain) :
    DifferentiableAt ℂ fractIntegral z :=
  differentiableAt_fractIntegral' hz.1.1

end ZeroFreeBridge
