import ArchS7c_Plancherel

/-!
# ArchS7c_Row: `P F P ϑ(g)` is the integral operator with rows `M(w,·)` (integrable inputs)

For `y ∈ L²(ℝ)_ev` with `y ∈ L¹`:

* `coeFn_theta`: `(ϑ(g) y)(v) = ∫ g(x) e^{-x/2} y(e^{-x} v) dx` a.e. (weak form against smooth
  compactly supported tests), and this function is integrable (`integrable_Vp`).
* `fourier_PVy`: `𝓕(1{|v|>1} ϑ(g)y)(w) = ∫ y(u) M^E(w,u) du` (two Fubinis, `v = e^x u`), with
  `M^E` the complex-exponential kernel; evenness of `y` turns it into `M` (`integral_MkE_eq`).
* **`coeFn_Q_integrable`**: `(P F P ϑ(g) y)(w) = 1{|w|>1} ∫ M(w,u) y(u) du` a.e.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology Complex FourierTransform
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace ArchS7c

open ArchS6 ArchS7

set_option linter.unusedSectionVars false

/-! ### Product integrability for dilations -/

theorem integral_norm_thF (F : ℝ → ℂ) (x : ℝ) :
    ∫ v, ‖thF x F v‖ = Real.exp (x / 2) * ∫ v, ‖F v‖ := by
  unfold thF
  simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun v => ‖F v‖), smul_eq_mul,
    ← Real.exp_neg, neg_neg, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
  congr 2; ring

theorem measurable_thF_prod {F : ℝ → ℂ} (hF : Measurable F) :
    Measurable fun p : ℝ × ℝ => thF p.1 F p.2 := by
  unfold thF
  exact (by fun_prop : Measurable fun p : ℝ × ℝ => ((Real.exp (-p.1 / 2) : ℝ) : ℂ)).mul
    (hF.comp (by fun_prop))

/-- `(x, v) ↦ k(x) b(v) e^{-x/2} F(e^{-x} v)` is integrable for `F ∈ L¹`, `b` bounded and
`k(x) e^{x/2} ∈ L¹`. -/
theorem integrable_thF_prod {F : ℝ → ℂ} (hF : Integrable F) (hFm : Measurable F) {k : ℝ → ℂ}
    (hkm : Measurable k) (hk : Integrable fun x => ‖k x‖ * Real.exp (x / 2)) {b : ℝ → ℂ}
    (hb : Measurable b) {C : ℝ} (hbC : ∀ v, ‖b v‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => k p.1 * (b p.2 * thF p.1 F p.2)) (volume.prod volume) := by
  have hm : Measurable fun p : ℝ × ℝ => k p.1 * (b p.2 * thF p.1 F p.2) :=
    (hkm.comp measurable_fst).mul ((hb.comp measurable_snd).mul (measurable_thF_prod hFm))
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbC 0)
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · refine Eventually.of_forall fun x => ?_
    refine Integrable.mono' (((integrable_thF hF x).norm.const_mul C).const_mul ‖k x‖)
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    simp only [norm_mul]
    gcongr
    · exact hbC v
  · refine Integrable.mono' ((hk.mul_const (C * ∫ v, ‖F v‖)))
      (hm.norm.aestronglyMeasurable.integral_prod_right' (μ := volume) (ν := volume))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ v, ‖k x * (b v * thF x F v)‖
        ≤ ∫ v, ‖k x‖ * (C * ‖thF x F v‖) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (((integrable_thF hF x).norm.const_mul C).const_mul _) (Eventually.of_forall fun v => ?_)
          simp only [norm_mul]
          gcongr
          exact hbC v
      _ = ‖k x‖ * Real.exp (x / 2) * (C * ∫ v, ‖F v‖) := by
          rw [integral_const_mul, integral_const_mul, integral_norm_thF]; ring

/-! ### `ϑ(g) y` pointwise for integrable `y` -/

section

variable {g : ℝ → ℂ}

/-- The pointwise formula `(ϑ(g) y)(v) = ∫ g(x) e^{-x/2} y(e^{-x} v) dx`. -/
def Vp (g F : ℝ → ℂ) (v : ℝ) : ℂ := ∫ x, g x * thF x F v

theorem integrable_g_exp (hW : WeilExplicit.IsWeilTest g) :
    Integrable fun x => ‖g x‖ * Real.exp (x / 2) :=
  (hW.1.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hW.2.norm.mul_right

theorem integrable_Vp (hW : WeilExplicit.IsWeilTest g) {F : ℝ → ℂ} (hF : Integrable F)
    (hFm : Measurable F) : Integrable (Vp g F) := by
  have h := integrable_thF_prod hF hFm hW.1.continuous.measurable (integrable_g_exp hW)
    (b := fun _ => 1) measurable_const (C := 1) (fun _ => by simp)
  have := h.integral_prod_right
  simp only [one_mul] at this
  exact this

theorem coeFn_theta (hW : WeilExplicit.IsWeilTest g) (hg : Integrable g) (y : evenL2)
    (hy : Integrable ((y : L2R) : ℝ → ℂ)) :
    (((theta g hg y : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume] Vp g ((y : L2R) : ℝ → ℂ) := by
  set F : ℝ → ℂ := ((y : L2R) : ℝ → ℂ) with hFdef
  have hFm : Measurable F := (Lp.stronglyMeasurable _).measurable
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    (integrable_Vp hW hy hFm).locallyIntegrable fun φ hφ hφc => ?_
  have hφm : MemLp (fun v => (φ v : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hφc.comp_left Complex.ofReal_zero)
  set Φ : L2R := hφm.toLp _
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hinner : ∀ f : L2R, ⟪Φ, f⟫_ℂ = ∫ v, φ v • (f : ℝ → ℂ) v := by
    intro f
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hφm.coeFn_toLp] with v hv
    rw [hv, RCLike.inner_apply, Complex.real_smul]
    simp [mul_comm]
  -- the Bochner integral in `L²(ℝ)`
  have hint : Integrable (fun x => g x • thL x (y : L2R)) := by
    refine (evenL2.subtypeL.integrable_comp (integrable_smul_thE g hg y)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Submodule.subtypeL_apply, Submodule.coe_smul, coe_thE]
  have hVy : ((theta g hg y : evenL2) : L2R) = ∫ x, g x • thL x (y : L2R) := by
    rw [theta_apply, ← Submodule.subtypeL_apply,
      ← evenL2.subtypeL.integral_comp_comm (integrable_smul_thE g hg y)]
    congr 1
  have hprod := integrable_thF_prod hy hFm hW.1.continuous.measurable (integrable_g_exp hW)
    (b := fun v => (φ v : ℂ)) (Complex.measurable_ofReal.comp hφ.continuous.measurable) (C := C)
    (fun v => by simpa [Complex.norm_real] using hC v)
  have hswap := integral_integral_swap (f := fun x v => g x * ((φ v : ℂ) * thF x F v)) hprod
  calc ∫ v, φ v • (((theta g hg y : evenL2) : L2R) : ℝ → ℂ) v
      = ⟪Φ, ((theta g hg y : evenL2) : L2R)⟫_ℂ := (hinner _).symm
    _ = ∫ x, ∫ v, g x * ((φ v : ℂ) * thF x F v) := by
        rw [hVy, ← integral_inner hint]
        congr 1; funext x
        rw [inner_smul_right, hinner, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_thL x (y : L2R)] with v hv
        rw [hv, Complex.real_smul]
    _ = ∫ v, ∫ x, g x * ((φ v : ℂ) * thF x F v) := hswap
    _ = ∫ v, φ v • Vp g F v := by
        congr 1; funext v
        rw [Vp, Complex.real_smul, ← integral_const_mul]
        congr 1; funext x; ring

/-! ### The Fourier step -/

/-- `1{|v|>1} e^{-2πivw}`. -/
def bW (w v : ℝ) : ℂ := if 1 < |v| then cexp (↑(-2 * Real.pi * v * w) * I) else 0

theorem measurable_bW (w : ℝ) : Measurable (bW w) := by
  unfold bW
  exact Measurable.ite (measurableSet_lt measurable_const measurable_abs) (by fun_prop) measurable_const

theorem norm_bW_le (w v : ℝ) : ‖bW w v‖ ≤ 1 := by
  unfold bW
  split_ifs
  · rw [Complex.norm_exp_ofReal_mul_I]
  · simp

/-- `e^{x/2} 1{|e^x u|>1} e^{-2πi e^x u w}`. -/
def mkE (w u x : ℝ) : ℂ := (Real.exp (x / 2) : ℂ) * bW w (Real.exp x * u)

/-- The complex-exponential row. -/
def MkE (g : ℝ → ℂ) (w u : ℝ) : ℂ := ∫ x, g x * mkE w u x

theorem measurable_mkE (w : ℝ) : Measurable fun p : ℝ × ℝ => mkE w p.1 p.2 := by
  unfold mkE
  exact (by fun_prop : Measurable fun p : ℝ × ℝ => ((Real.exp (p.2 / 2) : ℝ) : ℂ)).mul
    ((measurable_bW w).comp (by fun_prop))

theorem norm_mkE_le (w u x : ℝ) : ‖mkE w u x‖ ≤ Real.exp (x / 2) := by
  unfold mkE
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_bW_le _ _)

theorem mkE_add_neg (w u x : ℝ) : mkE w u x + mkE w (-u) x = 2 * (mk w u x : ℂ) := by
  unfold mkE mk bW
  have ha : |Real.exp x * -u| = |Real.exp x * u| := by rw [mul_neg, abs_neg]
  have hb : |Real.exp x * u| = Real.exp x * |u| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos x)]
  rw [ha, hb]
  split_ifs
  · have e1 : cexp (↑(-2 * Real.pi * (Real.exp x * u) * w) * I)
        = cexp (-((2 * Real.pi * (Real.exp x * u) * w : ℝ) : ℂ) * I) := by congr 1; push_cast; ring
    have e2 : cexp (↑(-2 * Real.pi * (Real.exp x * -u) * w) * I)
        = cexp (((2 * Real.pi * (Real.exp x * u) * w : ℝ) : ℂ) * I) := by congr 1; push_cast; ring
    rw [e1, e2, ← mul_add, add_comm, ← Complex.two_cos]
    push_cast; ring
  · simp

theorem integrable_g_mkE (hW : WeilExplicit.IsWeilTest g) (w u : ℝ) :
    Integrable fun x => g x * mkE w u x := by
  refine Integrable.mono' (integrable_g_exp hW)
    (hW.1.continuous.measurable.mul ((measurable_mkE w).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_mkE_le w u x) (norm_nonneg _)

theorem MkE_add_neg (hW : WeilExplicit.IsWeilTest g) (w u : ℝ) :
    MkE g w u + MkE g w (-u) = 2 * Mk g w u := by
  unfold MkE Mk
  rw [← integral_add (integrable_g_mkE hW w u) (integrable_g_mkE hW w (-u)), ← integral_const_mul]
  congr 1; funext x
  rw [← mul_add, mkE_add_neg]; ring

theorem norm_MkE_le (hW : WeilExplicit.IsWeilTest g) (w u : ℝ) :
    ‖MkE g w u‖ ≤ ∫ x, ‖g x‖ * Real.exp (x / 2) := by
  unfold MkE
  refine norm_integral_le_of_norm_le (integrable_g_exp hW) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_mkE_le w u x) (norm_nonneg _)

theorem aestronglyMeasurable_MkE (hgc : Continuous g) (w : ℝ) :
    AEStronglyMeasurable (MkE g w) volume := by
  have hm : Measurable fun p : ℝ × ℝ => g p.2 * mkE w p.1 p.2 :=
    (hgc.measurable.comp measurable_snd).mul (measurable_mkE w)
  exact hm.aestronglyMeasurable.integral_prod_right' (μ := volume) (ν := volume)

/-- Substitution `v = e^x u` in the inner integral. -/
theorem integral_bW_thF (F : ℝ → ℂ) (w x : ℝ) :
    ∫ v, bW w v * thF x F v = (Real.exp (x / 2) : ℂ) * ∫ u, bW w (Real.exp x * u) * F u := by
  have key := Measure.integral_comp_mul_left (fun v => bW w v * thF x F v) (Real.exp x)
  have e : ∀ u, bW w (Real.exp x * u) * thF x F (Real.exp x * u)
      = (Real.exp (-x / 2) : ℂ) * (bW w (Real.exp x * u) * F u) := by
    intro u
    unfold thF
    rw [show Real.exp (-x) * (Real.exp x * u) = u by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]]
    ring
  simp_rw [e] at key
  rw [integral_const_mul, ← Real.exp_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul] at key
  have hx : (Real.exp (-x) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have h2 : (Real.exp (x / 2) : ℂ) = Real.exp x * Real.exp (-x / 2) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  have h3 : (Real.exp x : ℂ) * Real.exp (-x) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  rw [h2, mul_assoc, key, ← mul_assoc, h3, one_mul]

/-- **The Fourier step**: `∫ 1{|v|>1} e^{-2πivw} (ϑ(g)y)(v) dv = ∫ y(u) M^E(w,u) du`. -/
theorem integral_bW_Vp (hW : WeilExplicit.IsWeilTest g) {F : ℝ → ℂ} (hF : Integrable F)
    (hFm : Measurable F) (w : ℝ) :
    ∫ v, bW w v * Vp g F v = ∫ u, F u * MkE g w u := by
  have h1 := integrable_thF_prod hF hFm hW.1.continuous.measurable (integrable_g_exp hW)
    (measurable_bW w) (C := 1) (norm_bW_le w)
  have hs1 := integral_integral_swap (f := fun x v => g x * (bW w v * thF x F v)) h1
  have h2 : Integrable (fun p : ℝ × ℝ => g p.1 * (mkE w p.2 p.1 * F p.2)) (volume.prod volume) := by
    refine Integrable.mono' ((integrable_g_exp hW).mul_prod hF.norm)
      ((hW.1.continuous.measurable.comp measurable_fst).mul
        (((measurable_mkE w).comp measurable_swap).mul (hFm.comp measurable_snd))).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, ← mul_assoc]
    gcongr
    exact norm_mkE_le _ _ _
  have hs2 := integral_integral_swap (f := fun x u => g x * (mkE w u x * F u)) h2
  calc ∫ v, bW w v * Vp g F v = ∫ v, ∫ x, g x * (bW w v * thF x F v) := by
        congr 1; funext v
        rw [Vp, ← integral_const_mul]; congr 1; funext x; ring
    _ = ∫ x, ∫ v, g x * (bW w v * thF x F v) := hs1.symm
    _ = ∫ x, ∫ u, g x * (mkE w u x * F u) := by
        congr 1; funext x
        rw [integral_const_mul, integral_const_mul, integral_bW_thF]
        congr 1
        rw [← integral_const_mul]
        congr 1; funext u
        unfold mkE; ring
    _ = ∫ u, ∫ x, g x * (mkE w u x * F u) := hs2
    _ = ∫ u, F u * MkE g w u := by
        congr 1; funext u
        rw [MkE, ← integral_const_mul]; congr 1; funext x; ring

/-- Evenness turns `M^E` into `M`. -/
theorem integral_MkE_eq (hW : WeilExplicit.IsWeilTest g) {F : ℝ → ℂ} (hF : Integrable F)
    (hev : (fun u => F (-u)) =ᵐ[volume] F) (w : ℝ) :
    ∫ u, F u * MkE g w u = ∫ u, Mk g w u * F u := by
  have hB := norm_MkE_le hW w
  have hm : StronglyMeasurable (MkE g w) := by
    have hm : Measurable fun p : ℝ × ℝ => g p.2 * mkE w p.1 p.2 :=
      (hW.1.continuous.measurable.comp measurable_snd).mul (measurable_mkE w)
    exact hm.stronglyMeasurable.integral_prod_right (ν := volume)
  have hi : ∀ G : ℝ → ℂ, Measurable G → (∀ u, ‖G u‖ ≤ ∫ x, ‖g x‖ * Real.exp (x / 2)) →
      Integrable fun u => F u * G u := by
    intro G hGm hG
    refine Integrable.mono' (hF.norm.mul_const (∫ x, ‖g x‖ * Real.exp (x / 2)))
      (hF.1.mul hGm.aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hG u) (norm_nonneg _)
  have hi1 := hi _ hm.measurable hB
  have hi2 := hi (fun u => MkE g w (-u)) (hm.measurable.comp measurable_neg) (fun u => hB _)
  have hflip : ∫ u, F u * MkE g w u = ∫ u, F u * MkE g w (-u) := by
    rw [← integral_neg_eq_self (fun u => F u * MkE g w u)]
    refine integral_congr_ae ?_
    filter_upwards [hev] with u hu
    rw [hu]
  have h2 : 2 * ∫ u, F u * MkE g w u = 2 * ∫ u, Mk g w u * F u := by
    rw [two_mul, ← integral_const_mul]
    nth_rewrite 2 [hflip]
    rw [← integral_add hi1 hi2]
    congr 1; funext u
    rw [← mul_add, MkE_add_neg hW]; ring
  exact mul_left_cancel₀ two_ne_zero h2

end

end ArchS7c
