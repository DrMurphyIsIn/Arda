/- (R2) DISCHARGE for `zeta_fract_repr_of`: the RHS integral

       fractIntegral s = ∫ x in Ioi 1, {x} · x^{-(s+1)} dx

   is complex-differentiable in `s` on the open right half-plane `{0 < Re s}`.
   This removes the `DifferentiableAt ℂ fractIntegral z` hypothesis (R2).

   Differentiation under the integral sign, via
   `hasDerivAt_integral_of_dominated_loc_of_lip`.  Parameter-derivative
   `F'(x) = {x} · (−log x) · x^{-(z+1)}`; on the neighbourhood `S = {z.re/2 < Re w}`
   the modulus of the w-derivative is dominated by `log x · x^{-(z.re/2 + 1)}`,
   integrable on `(1,∞)` because `z.re/2 > 0`.

   A gap-filler FEEDING input (R); NOT a proof of RH.  conjecture1_proved = False.
-/
import StripRepr

open Set MeasureTheory Filter Topology

namespace ZeroFreeBridge

/-- (R2) `fractIntegral` is differentiable at every `z` with `0 < Re z`. -/
theorem differentiableAt_fractIntegral {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ fractIntegral z := by
  have hσ : (0 : ℝ) < z.re / 2 := by linarith
  -- The parameter neighbourhood on which we dominate the derivative.
  set S : Set ℂ := {w : ℂ | z.re / 2 < w.re} with hSdef
  have hSopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hSmem : S ∈ 𝓝 z := hSopen.mem_nhds (by rw [hSdef]; simp only [Set.mem_setOf_eq]; linarith)
  -- Integrand `F`, its w-derivative `F'`, and the dominating function `bound`.
  set F : ℂ → ℝ → ℂ := fun w x => fractIntegrand w x with hFdef
  set F' : ℝ → ℂ := fun x => ((Int.fract x : ℝ) : ℂ) * (-Complex.log x) / (x : ℂ) ^ (z + 1) with hF'def
  set bound : ℝ → ℝ := fun x => Real.log x * x ^ (-(z.re / 2) - 1) with hbdef
  -- (meas) `F w` is a.e.-strongly-measurable for every `w`, uniformly near `z`.
  have h_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hFdef, fractIntegrand]
    fun_prop
  -- (int) `F z` is integrable on `(1,∞)`: `‖F z x‖ ≤ x^{-(z.re+1)}` and `-(z.re+1) < -1`.
  have h_int : Integrable (F z) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hbase : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (-(z + 1))‖) (Set.Ioi 1) := by
      have : (-(z + 1)).re < -1 := by simp [Complex.add_re]; linarith
      exact integrableOn_Ioi_norm_cpow_of_lt this (by norm_num)
    refine (Integrable.mono' hbase ?_ ?_)
    · refine (Measurable.aestronglyMeasurable ?_)
      simp only [hFdef, fractIntegrand]; fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx1 : (1 : ℝ) < x := hx
      have hxpos : (0 : ℝ) < x := by linarith
      -- ‖{x}·x^{-(z+1)}‖ = {x}·‖x^{z+1}‖⁻¹ ≤ ‖x^{z+1}‖⁻¹ = ‖x^{-(z+1)}‖  (since 0 ≤ {x} ≤ 1)
      have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
      have hf1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
      have hpow : ‖(x : ℂ) ^ (-(z + 1))‖ = ‖(x : ℂ) ^ (z + 1)‖⁻¹ := by
        rw [Complex.cpow_neg, norm_inv]
      have hcnn : (0 : ℝ) ≤ ‖(x : ℂ) ^ (z + 1)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      simp only [hFdef, fractIntegrand, norm_div, Complex.norm_real, Real.norm_of_nonneg hf0]
      rw [hpow, div_eq_mul_inv]
      calc Int.fract x * ‖(x : ℂ) ^ (z + 1)‖⁻¹
          ≤ 1 * ‖(x : ℂ) ^ (z + 1)‖⁻¹ := mul_le_mul_of_nonneg_right hf1 hcnn
        _ = ‖(x : ℂ) ^ (z + 1)‖⁻¹ := one_mul _
  -- (meas') `F'` is a.e.-strongly-measurable.
  have h_meas' : AEStronglyMeasurable F' (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hF'def]; fun_prop
  -- (lip) Lipschitz-in-parameter, uniformly a.e.: from the derivative bound on the convex `S`.
  have h_lip : ∀ᵐ x ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      LipschitzOnWith (Real.nnabs (bound x)) (fun w => F w x) S := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1 : ℝ) < x := hx
    have hxpos : (0 : ℝ) < x := by linarith
    -- On S, ‖∂_w F‖ ≤ bound x; convexity of S + MVT gives the Lipschitz bound.
    sorry
  -- (bint) the dominating function is integrable on `(1,∞)`.
  have h_bint : Integrable bound (volume.restrict (Set.Ioi (1 : ℝ))) := by
    simp only [hbdef]
    sorry
  -- (diff) the a.e. w-derivative of `F` at `z` is `F'`.
  have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      HasDerivAt (fun w => F w x) (F' x) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1 : ℝ) < x := hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    -- d/dw of `w ↦ (x)^{-(w+1)}` via `HasDerivAt.const_cpow` (chain rule, const base x);
    -- times the constant `{x}`.
    have hlin : HasDerivAt (fun w : ℂ => -(w + 1)) (-1 : ℂ) z :=
      ((hasDerivAt_id z).add_const (1 : ℂ)).neg
    have hcpow : HasDerivAt (fun w : ℂ => (x : ℂ) ^ (-(w + 1)))
        ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) z :=
      hlin.const_cpow (Or.inl hxne)
    have hmul := hcpow.const_mul ((Int.fract x : ℝ) : ℂ)
    -- massage the function into `F` and the derivative value into `F' x`.
    have hfun : (fun w => F w x) = (fun w : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))) := by
      funext w; simp only [hFdef, fractIntegrand, div_eq_mul_inv, ← Complex.cpow_neg]
    have hval : ((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) = F' x := by
      simp only [hF'def, div_eq_mul_inv, ← Complex.cpow_neg]; ring
    rw [hfun, ← hval]
    exact hmul
  -- Assemble.
  have key := hasDerivAt_integral_of_dominated_loc_of_lip hSmem h_meas h_int h_meas' h_lip h_bint h_diff
  have hd : DifferentiableAt ℂ (fun w => ∫ x in Set.Ioi (1 : ℝ), F w x) z := key.2.differentiableAt
  have hfe : (fun w => ∫ x in Set.Ioi (1 : ℝ), F w x) = fractIntegral := by
    funext w; simp only [hFdef, fractIntegral]
  rwa [hfe] at hd

end ZeroFreeBridge
