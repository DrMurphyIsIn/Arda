import ArchS7c_Decay

/-!
# ArchS7c_FourierH: the Fourier transform of `H_w` is `paperFT g (-r) · w^{-1/2-ir} Φ_r(w)/2`

* `Cpart w r T = ∫₀^T c_w(t) e^{irt} dt`.
* `Cpart_eq`: `Cpart w r T = w^{-z_r}/2 · ∫_w^{w e^T} s^{z_r - 1} 2cos(2πs) ds` (substitution `s = w e^t`),
  with `z_r = 1/2 + ir` (S3's `zt`).
* `tendsto_Cpart`: `Cpart w r T → w^{-z_r} Φ_r(w)/2` as `T → ∞` (S3's `tendsto_integral_Phi`).
* `norm_Cpart_le`: a bound uniform in `T`.
* `trunc_eq`: Fubini for the truncated transform `∫_{s ≤ T} H_w(s) e^{irs} ds`.
* **`fourier_Hw`**: `∫ H_w(s) e^{irs} ds = paperFT g (-r) · (w^{-z_r} Φ_r(w)/2)`.

No damping is used: the improper oscillatory integral enters only through S3's `Φ`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

noncomputable section

namespace ArchS7c

open ArchS3

set_option linter.unusedSectionVars false

/-- `∫₀^T c_w(t) e^{irt} dt`. -/
def Cpart (w r T : ℝ) : ℂ := ∫ t in (0 : ℝ)..T, cw w t * cexp (I * r * t)

theorem ofReal_exp_cpow (t : ℝ) (z : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ z = cexp (t * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

theorem cpow_zt_ne_zero {w : ℝ} (hw : 0 < w) (r : ℝ) : (w : ℂ) ^ zt r ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hw.ne'))

/-- The substitution integrand: `(w e^t) · pD r 0 (w e^t) = 2 w^{z_r} c_w(t) e^{irt}` for `t > 0`. -/
theorem smul_pD_comp {w : ℝ} (hw : 0 < w) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    (w * Real.exp t) • pD r 0 (w * Real.exp t) = 2 * (w : ℂ) ^ zt r * (cw w t * cexp (I * r * t)) := by
  have hs : (0 : ℝ) < w * Real.exp t := mul_pos hw (Real.exp_pos t)
  have hs' : ((w * Real.exp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Complex.real_smul, pD, cosD, cw_of_pos w ht]
  have e1 : ((w * Real.exp t : ℝ) : ℂ) * ((w * Real.exp t : ℝ) : ℂ) ^ (zt r - 1)
      = ((w * Real.exp t : ℝ) : ℂ) ^ zt r := by
    rw [Complex.cpow_sub _ _ hs', Complex.cpow_one]; field_simp
  have e2 : ((w * Real.exp t : ℝ) : ℂ) ^ zt r = (w : ℂ) ^ zt r * cexp (t * zt r) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hw.le (Real.exp_pos t).le,
      ofReal_exp_cpow]
  have e3 : cexp (t * zt r) = ((Real.exp (t / 2) : ℝ) : ℂ) * cexp (I * r * t) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, zt]; congr 1; push_cast; ring
  rw [← mul_assoc, e1, e2, e3]
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  push_cast
  ring_nf

theorem Cpart_eq {w : ℝ} (hw : 0 < w) (r : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Cpart w r T = (w : ℂ) ^ (-zt r) / 2 * ∫ s in w..w * Real.exp T, pD r 0 s := by
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := T)
    (f := fun t => w * Real.exp t) (f' := fun t => w * Real.exp t) (g := pD r 0)
    (fun x _ => by simpa using (Real.hasDerivAt_exp x).const_mul w)
    (by fun_prop)
    ((continuousOn_pD r 0).mono (by
      rintro _ ⟨x, _, rfl⟩
      exact mul_pos hw (Real.exp_pos x)))
  simp only [Real.exp_zero, mul_one, Function.comp_def] at hsub
  have hcongr : ∫ x in (0 : ℝ)..T, (w * Real.exp x) • pD r 0 (w * Real.exp x)
      = ∫ x in (0 : ℝ)..T, 2 * (w : ℂ) ^ zt r * (cw w x * cexp (I * r * x)) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hT] at hx
    exact smul_pD_comp hw r hx.1
  rw [hcongr, intervalIntegral.integral_const_mul] at hsub
  rw [← hsub, Cpart, Complex.cpow_neg]
  have := cpow_zt_ne_zero hw r
  field_simp

theorem Cpart_of_nonpos (w r : ℝ) {T : ℝ} (hT : T ≤ 0) : Cpart w r T = 0 := by
  unfold Cpart
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℂ)) (Eventually.of_forall fun x hx => ?_)]
  · simp
  rw [Set.uIoc_of_ge hT] at hx
  rw [cw_of_nonpos w hx.2, zero_mul]

theorem integral_pD_eq_sub {r a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) :
    ∫ s in a..R, pD r 0 s = Phi r a - Phi r R := by
  rw [← Gpart_sub ha hR, Phi, Phi]; ring

/-- The uniform bound on the partial transforms. -/
def CB (w r : ℝ) : ℝ := ‖(w : ℂ) ^ (-zt r)‖ / 2 * (2 * Kt r * w ^ (-1 / 2 : ℝ))

theorem CB_nonneg {w : ℝ} (hw : 0 < w) (r : ℝ) : 0 ≤ CB w r := by
  unfold CB; have := Kt_nonneg r; positivity

theorem norm_Cpart_le {w : ℝ} (hw : 0 < w) (r T : ℝ) : ‖Cpart w r T‖ ≤ CB w r := by
  rcases le_or_gt T 0 with hT | hT
  · rw [Cpart_of_nonpos w r hT, norm_zero]; exact CB_nonneg hw r
  have hR : w ≤ w * Real.exp T := le_mul_of_one_le_right hw.le (Real.one_le_exp hT.le)
  have hR0 : 0 < w * Real.exp T := mul_pos hw (Real.exp_pos T)
  rw [Cpart_eq hw r hT.le, integral_pD_eq_sub hw.le hR0.le, norm_mul, CB, norm_div,
    Complex.norm_ofNat]
  gcongr
  calc ‖Phi r w - Phi r (w * Real.exp T)‖ ≤ ‖Phi r w‖ + ‖Phi r (w * Real.exp T)‖ := norm_sub_le _ _
    _ ≤ Kt r * w ^ (-1 / 2 : ℝ) + Kt r * (w * Real.exp T) ^ (-1 / 2 : ℝ) :=
        add_le_add (norm_Phi_le hw) (norm_Phi_le hR0)
    _ ≤ Kt r * w ^ (-1 / 2 : ℝ) + Kt r * w ^ (-1 / 2 : ℝ) := by
        have := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (z := (-1 / 2 : ℝ)) hw hR (by norm_num)) (Kt_nonneg r)
        linarith
    _ = 2 * Kt r * w ^ (-1 / 2 : ℝ) := by ring

theorem tendsto_Cpart {w : ℝ} (hw : 0 < w) (r : ℝ) :
    Tendsto (fun T => Cpart w r T) atTop (𝓝 ((w : ℂ) ^ (-zt r) / 2 * Phi r w)) := by
  have h1 := tendsto_integral_Phi (t := r) hw
  have h2 : Tendsto (fun T => w * Real.exp T) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hw
  have h3 := (h1.comp h2).const_mul ((w : ℂ) ^ (-zt r) / 2)
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [Cpart_eq hw r hT]; rfl

theorem measurable_cw_exp (w r : ℝ) : Measurable fun t : ℝ => cw w t * cexp (I * r * t) :=
  (measurable_cw w).mul (by fun_prop)

theorem integral_indicator_Iic (w r R : ℝ) :
    ∫ t, (Iic R).indicator (fun t => cw w t * cexp (I * r * t)) t = Cpart w r R := by
  rw [integral_indicator measurableSet_Iic,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Ioc_subset_Iic_self
      (fun t ht => ?_)]
  · rcases le_or_gt R 0 with hR | hR
    · rw [Ioc_eq_empty (not_lt.mpr hR), Measure.restrict_empty, integral_zero_measure,
        Cpart_of_nonpos w r hR]
    · rw [Cpart, intervalIntegral.integral_of_le hR.le]
  · have ht0 : t ≤ 0 := by
      by_contra h
      exact ht.2 ⟨not_le.mp h, ht.1⟩
    rw [cw_of_nonpos w ht0, zero_mul]

section

variable {g : ℝ → ℂ}

/-- The Fubini integrand of the truncated transform. -/
def truncF (g : ℝ → ℂ) (w r T : ℝ) (p : ℝ × ℝ) : ℂ :=
  g p.2 * (Iic T).indicator (fun s => cw w (p.2 + s) * cexp (I * r * s)) p.1

theorem measurable_truncF (hgc : Continuous g) (w r T : ℝ) : Measurable (truncF g w r T) := by
  have e : truncF g w r T = fun p : ℝ × ℝ =>
      if p.1 ∈ Iic T then g p.2 * (cw w (p.2 + p.1) * cexp (I * r * p.1)) else 0 := by
    funext p
    unfold truncF
    by_cases h : p.1 ∈ Iic T
    · rw [indicator_of_mem h, if_pos h]
    · rw [indicator_of_notMem h, if_neg h, mul_zero]
  rw [e]
  refine Measurable.ite (measurableSet_Iic.preimage measurable_fst) ?_ measurable_const
  exact (hgc.measurable.comp measurable_snd).mul
    (((measurable_cw w).comp (measurable_snd.add measurable_fst)).mul (by fun_prop))

theorem norm_cexp_I_mul (r s : ℝ) : ‖cexp (I * r * s)‖ = 1 := by
  rw [show I * (r : ℂ) * s = ((r * s : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem integrable_truncF (hW : WeilExplicit.IsWeilTest g) (w r T : ℝ) :
    Integrable (truncF g w r T) (volume.prod volume) := by
  obtain ⟨L, hL0, hL⟩ := exists_radius hW.2
  have hg : Integrable g := hW.1.continuous.integrable_of_hasCompactSupport hW.2
  have hk : Integrable ((Icc (-L) T).indicator fun _ => Real.exp ((L + T) / 2)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  have hk0 : ∀ s, 0 ≤ (Icc (-L) T).indicator (fun _ => Real.exp ((L + T) / 2)) s :=
    fun s => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) s
  refine Integrable.mono' (hk.mul_prod hg.norm)
    (measurable_truncF hW.1.continuous w r T).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  unfold truncF
  rw [norm_mul, mul_comm]
  rcases eq_or_ne (g p.2) 0 with hgx | hgx
  · rw [hgx, norm_zero, mul_zero, mul_zero]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hx := abs_lt.mp (lt_of_ne_zero hL hgx)
  by_cases hs : p.1 ∈ Iic T
  · rw [indicator_of_mem hs]
    by_cases hxs : 0 < p.2 + p.1
    · have hmem : p.1 ∈ Icc (-L) T := ⟨by linarith [hx.2], hs⟩
      rw [indicator_of_mem hmem, norm_mul, norm_cexp_I_mul, mul_one]
      exact (norm_cw_le w _).trans (Real.exp_le_exp.mpr (by linarith [hx.2, show p.1 ≤ T from hs]))
    · rw [cw_of_nonpos w (not_lt.mp hxs), zero_mul, norm_zero]; exact hk0 _
  · rw [indicator_of_notMem hs, norm_zero]; exact hk0 _

/-- Fubini for the truncated transform. -/
theorem trunc_eq (hW : WeilExplicit.IsWeilTest g) (w r T : ℝ) :
    ∫ s, (Iic T).indicator (fun s => Hw g w s * cexp (I * r * s)) s
      = ∫ x, g x * (cexp (I * ((-r : ℝ) : ℂ) * x) * Cpart w r (T + x)) := by
  have h1 : (fun s => (Iic T).indicator (fun s => Hw g w s * cexp (I * r * s)) s)
      = fun s => ∫ x, truncF g w r T (s, x) := by
    funext s
    by_cases hs : s ∈ Iic T
    · rw [indicator_of_mem hs, Hw, ← integral_mul_const]
      congr 1; funext x
      simp only [truncF, indicator_of_mem hs]
      ring
    · rw [indicator_of_notMem hs]
      simp only [truncF, indicator_of_notMem hs, mul_zero, integral_zero]
  rw [h1, integral_integral_swap (f := fun s x => truncF g w r T (s, x)) (integrable_truncF hW w r T)]
  congr 1; funext x
  simp only [truncF]
  rw [integral_const_mul]
  congr 1
  have h2 : (fun s => (Iic T).indicator (fun s => cw w (x + s) * cexp (I * r * s)) s)
      = fun s => cexp (I * ((-r : ℝ) : ℂ) * x)
          * (Iic (T + x)).indicator (fun t => cw w t * cexp (I * r * t)) (s + x) := by
    funext s
    by_cases hs : s ≤ T
    · rw [indicator_of_mem (show s ∈ Iic T from hs),
        indicator_of_mem (show s + x ∈ Iic (T + x) by rw [mem_Iic]; linarith)]
      rw [add_comm x s, show cexp (I * r * s) = cexp (I * ((-r : ℝ) : ℂ) * x)
          * cexp (I * r * ((s + x : ℝ) : ℂ)) by rw [← Complex.exp_add]; congr 1; push_cast; ring]
      ring
    · rw [indicator_of_notMem (show s ∉ Iic T by rw [mem_Iic]; exact hs),
        indicator_of_notMem (show s + x ∉ Iic (T + x) by rw [mem_Iic]; linarith), mul_zero]
  rw [h2, integral_const_mul,
    integral_add_right_eq_self (μ := volume)
      (fun t => (Iic (T + x)).indicator (fun t => cw w t * cexp (I * r * t)) t) x,
    integral_indicator_Iic]

theorem intervalIntegrable_cw_exp (w r a b : ℝ) :
    IntervalIntegrable (fun t => cw w t * cexp (I * r * t)) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun t => Real.exp (t / 2))
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (t / 2)).intervalIntegrable a b)
    (measurable_cw_exp w r).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  show ‖cw w t * cexp (I * r * t)‖ ≤ Real.exp (t / 2)
  rw [norm_mul, norm_cexp_I_mul, mul_one]
  exact norm_cw_le w t

/-- **The Fourier transform of `H_w`**: `∫ H_w(s) e^{irs} ds = paperFT g (-r) · w^{-z_r} Φ_r(w)/2`. -/
theorem fourier_Hw (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : 0 < w) (r : ℝ) :
    ∫ s, Hw g w s * cexp (I * r * s)
      = Zeta23.paperFT g ((-r : ℝ) : ℂ) * ((w : ℂ) ^ (-zt r) / 2 * Phi r w) := by
  have hg : Integrable g := hW.1.continuous.integrable_of_hasCompactSupport hW.2
  have hHm : AEStronglyMeasurable (fun s => Hw g w s * cexp (I * r * s)) volume :=
    (aestronglyMeasurable_Hw hW.1.continuous w).mul (by fun_prop : Continuous fun s : ℝ =>
      cexp (I * r * s)).aestronglyMeasurable
  have hnorm : ∀ s, ‖Hw g w s * cexp (I * r * s)‖ = ‖Hw g w s‖ := fun s => by
    rw [norm_mul, norm_cexp_I_mul, mul_one]
  have hlim1 : Tendsto (fun T => ∫ s, (Iic T).indicator (fun s => Hw g w s * cexp (I * r * s)) s)
      atTop (𝓝 (∫ s, Hw g w s * cexp (I * r * s))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖Hw g w s‖)
      (Eventually.of_forall fun T => hHm.indicator measurableSet_Iic)
      (Eventually.of_forall fun T => Eventually.of_forall fun s => ?_) (integrable_Hw hW hw).norm
      (Eventually.of_forall fun s => ?_)
    · rw [← hnorm]; exact norm_indicator_le_norm_self _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop s] with T hT
      rw [indicator_of_mem (show s ∈ Iic T from hT)]
  have hCc : Continuous fun T => Cpart w r T := by
    unfold Cpart
    exact intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_cw_exp w r a b) 0
  have hlim2 : Tendsto (fun T => ∫ x, g x * (cexp (I * ((-r : ℝ) : ℂ) * x) * Cpart w r (T + x)))
      atTop (𝓝 (∫ x, g x * (cexp (I * ((-r : ℝ) : ℂ) * x) * ((w : ℂ) ^ (-zt r) / 2 * Phi r w)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖g x‖ * CB w r)
      (Eventually.of_forall fun T => ?_) (Eventually.of_forall fun T => Eventually.of_forall fun x => ?_)
      (hg.norm.mul_const _) (Eventually.of_forall fun x => ?_)
    · exact (hW.1.continuous.mul ((by fun_prop : Continuous fun x : ℝ => cexp (I * ((-r : ℝ) : ℂ) * x)).mul
        (hCc.comp (continuous_const.add continuous_id)))).aestronglyMeasurable
    · rw [norm_mul, norm_mul, show ((-r : ℝ) : ℂ) = ((-r : ℝ) : ℂ) from rfl, norm_cexp_I_mul, one_mul]
      exact mul_le_mul_of_nonneg_left (norm_Cpart_le hw r _) (norm_nonneg _)
    · exact (((tendsto_Cpart hw r).comp (tendsto_atTop_add_const_right _ x tendsto_id)).const_mul
        (cexp (I * ((-r : ℝ) : ℂ) * x))).const_mul (g x)
  have hT : ∀ T, ∫ s, (Iic T).indicator (fun s => Hw g w s * cexp (I * r * s)) s
      = ∫ x, g x * (cexp (I * ((-r : ℝ) : ℂ) * x) * Cpart w r (T + x)) := trunc_eq hW w r
  simp_rw [hT] at hlim1
  rw [tendsto_nhds_unique hlim1 hlim2, Zeta23.paperFT, ← integral_mul_const]
  congr 1; funext x; ring

end

end ArchS7c
