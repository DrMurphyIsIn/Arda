/-  RS_Mellin.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 3:
    the Mellin step.  Mathlib-only (imports `RS_Kernel`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integral_cpow_mul_exp_neg_mul_Ioi_complex` : the complex-scaled Gamma integral
            int_0^oo rho^(s-1) e^(-z rho) d rho = (1/z)^s Gamma(s),     Re s > 0, Re z > 0,
        extending Mathlib's real-`z` lemma by the identity theorem.
      * `one_div_mul_cpow` : the branch bookkeeping (1/(x(1+i)))^s = x^(-s) (1+i)^(-s) whenever
        Re(x(1+i)) > 0.
      * `mellin_step` : Fubini on (line) x (0, oo):
            Gamma(s) lineUp c (rsG x^(-s)) = (1+i)^s int_0^oo rho^(s-1) rsK c ((1+i) rho) d rho,
        with rsK c y = lineUp c (rsG e^(-x y)) the Mordell integral.
      * `rsK_split` : the Mordell closed form at y = (1+i) rho, split into the Bose kernel and the
        Gaussian (chi-side) kernel.
      * `integral_bose` : int_0^oo rho^(s-1) / (e^((1+i) rho) - 1) = (1+i)^(-s) Gamma(s) zeta(s),
        Re s > 1 (geometric series, termwise integration, Mathlib's Dirichlet series for zeta).
      * `integral_Epart` : the chi-side kernel integral equals (2 pi)^s (1-i)^(-s) rsHR s, where
        rsHR s = int_0^oo rsH(r(1-i)) (r(1-i))^(s-1) (1-i) dr is half of the chi-side line.
      * `mellin_identity` : for Re s > 1 and 0 < c < 1,
            Gamma(s) lineUp c (rsG x^(-s)) = -Gamma(s) zeta(s) + (2 pi)^s (1+i)^s (1-i)^(-s) rsHR s.

    conjecture1_proved = False.  Classical integral identities for zeta; nothing here bears on RH.
-/
import RS_Kernel

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. Integrability of `rho^a e^(-b rho)` and norms -/

theorem integrableOn_rpow_exp {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    IntegrableOn (fun ρ : ℝ => ρ ^ a * Real.exp (-(b * ρ))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow ha le_rfl hb
  refine this.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem norm_ofReal_cpow {ρ : ℝ} (hρ : 0 < ρ) (s : ℂ) : ‖(ρ : ℂ) ^ s‖ = ρ ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hρ s

theorem one_add_I_ne_zero : (1 + I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem one_sub_I_ne_zero : (1 - I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

/-! ## 2. Branch bookkeeping -/

theorem arg_ne_pi_of_re_pos {z : ℂ} (hz : 0 < z.re) : z.arg ≠ π := by
  have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  intro h; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]

theorem one_div_cpow_eq {z : ℂ} (hz : 0 < z.re) (s : ℂ) : (1 / z) ^ s = z ^ (-s) := by
  rw [one_div, Complex.inv_cpow _ _ (arg_ne_pi_of_re_pos hz), Complex.cpow_neg]

/-- `(1/(x (1+i)))^s = x^(-s) (1+i)^(-s)` whenever `Re (x (1+i)) > 0`. -/
theorem one_div_mul_cpow {x : ℂ} (hx : 0 < (x * (1 + I)).re) (s : ℂ) :
    (1 / (x * (1 + I))) ^ s = x ^ (-s) * (1 + I) ^ (-s) := by
  set z := x * (1 + I) with hz
  have hz0 : z ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hx0 : x ≠ 0 := by intro h; rw [h, zero_mul] at hz; exact hz0 hz
  set w : ℂ := (1 + I)⁻¹ with hw
  have hw0 : w ≠ 0 := inv_ne_zero one_add_I_ne_zero
  have hwre : 0 < w.re := by rw [hw, Complex.inv_re]; simp [Complex.normSq_apply]
  have hxzw : x = z * w := by rw [hz, hw, mul_assoc, mul_inv_cancel₀ one_add_I_ne_zero, mul_one]
  have hargz := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hargw := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  have hlog : Complex.log x = Complex.log z + Complex.log w := by
    rw [hxzw]
    refine (Complex.log_mul_eq_add_log_iff hz0 hw0).mpr ⟨?_, ?_⟩
    · linarith [(abs_lt.mp hargz).1, (abs_lt.mp hargw).1, Real.pi_pos]
    · linarith [(abs_lt.mp hargz).2, (abs_lt.mp hargw).2, Real.pi_pos]
  have hlogw : Complex.log w = -Complex.log (1 + I) := by
    rw [hw, Complex.log_inv _ (arg_ne_pi_of_re_pos (by simp))]
  rw [one_div_cpow_eq hx, Complex.cpow_def_of_ne_zero hz0, Complex.cpow_def_of_ne_zero hx0,
    Complex.cpow_def_of_ne_zero one_add_I_ne_zero, hlog, hlogw, ← Complex.exp_add]
  congr 1; ring

/-! ## 3. The complex-scaled Gamma integral -/

theorem integral_cpow_mul_exp_neg_mul_Ioi_complex {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * cexp (-(z * ρ)) = (1 / z) ^ s * Gamma s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set f : ℂ → ℂ := fun z => ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * cexp (-(z * ρ)) with hf
  set g : ℂ → ℂ := fun z => (1 / z) ^ s * Gamma s with hg
  -- continuity of the integrand in rho on (0, oo)
  have hcpow : ContinuousOn (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1)) (Ioi 0) := by
    intro ρ hρ
    exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hf_diff : DifferentiableOn ℂ f U := by
    intro z₀ hz₀
    have hz₀' : 0 < z₀.re := hz₀
    set r := z₀.re / 2 with hr
    have hr0 : 0 < r := by positivity
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun z (ρ : ℝ) => (ρ : ℂ) ^ (s - 1) * cexp (-(z * ρ)))
      (F' := fun z (ρ : ℝ) => (ρ : ℂ) ^ (s - 1) * (cexp (-(z * ρ)) * (-(ρ : ℂ))))
      (x₀ := z₀) (bound := fun ρ : ℝ => ρ ^ s.re * Real.exp (-(r * ρ)))
      (Metric.ball_mem_nhds z₀ hr0)
      (Eventually.of_forall fun z =>
        (hcpow.mul (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable measurableSet_Ioi)
      ?_ ((hcpow.mul (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable
        measurableSet_Ioi) ?_ (integrableOn_rpow_exp (by linarith) hr0) ?_
    · exact key.2.differentiableAt.differentiableWithinAt
    · -- integrability at z₀
      refine (integrableOn_rpow_exp (a := s.re - 1) (b := z₀.re) (by linarith) hz₀').mono'
        ((hcpow.mul (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable measurableSet_Ioi) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
      rw [norm_mul, norm_ofReal_cpow hρ, Complex.norm_exp]
      simp
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ z hz => ?_)
      have hρ' : (0 : ℝ) < ρ := hρ
      have hzre : r < z.re := by
        have h1 := Metric.mem_ball.mp hz
        rw [Complex.dist_eq] at h1
        have h2 := Complex.abs_re_le_norm (z - z₀)
        rw [Complex.sub_re] at h2
        have h3 := neg_abs_le (z.re - z₀.re)
        linarith
      rw [norm_mul, norm_mul, norm_ofReal_cpow hρ', Complex.norm_exp, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ']
      have hre : (-(z * (ρ : ℂ))).re = -(z.re * ρ) := by simp
      rw [hre]
      have hexp : Real.exp (-(z.re * ρ)) ≤ Real.exp (-(r * ρ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hpow : ρ ^ (s - 1).re * ρ = ρ ^ s.re := by
        rw [Complex.sub_re, Complex.one_re, Real.rpow_sub hρ', Real.rpow_one]
        field_simp
      calc ρ ^ (s - 1).re * (Real.exp (-(z.re * ρ)) * ρ)
          = ρ ^ (s - 1).re * ρ * Real.exp (-(z.re * ρ)) := by ring
        _ ≤ ρ ^ s.re * Real.exp (-(r * ρ)) := by
            rw [hpow]
            exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hρ'.le _)
    · refine Eventually.of_forall fun ρ z _ => ?_
      have h0 : HasDerivAt (fun z : ℂ => z * (ρ : ℂ)) (ρ : ℂ) z := by
        simpa using (hasDerivAt_id z).mul_const (ρ : ℂ)
      have h1 : HasDerivAt (fun z : ℂ => -(z * (ρ : ℂ))) (-(ρ : ℂ)) z := h0.neg
      exact h1.cexp.const_mul _
  have hg_diff : DifferentiableOn ℂ g U := by
    intro z hz
    have hz' : 0 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'
    have hmem : 1 / z ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left
      rw [one_div, Complex.inv_re]
      exact div_pos hz' (Complex.normSq_pos.mpr hz0)
    exact (((differentiableAt_const 1).div differentiableAt_id hz0).cpow
      (differentiableAt_const s) hmem).mul_const _ |>.differentiableWithinAt
  have hagree : ∀ r : ℝ, 0 < r → f r = g r := by
    intro r hr
    simp only [hf, hg]
    exact integral_cpow_mul_exp_neg_mul_Ioi hs hr
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = g w := by
    have ht : Tendsto (fun k : ℕ => (((1 : ℝ) + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 1) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (1 : ℝ)
        rw [add_zero] at h0
        have := (Complex.continuous_ofReal.tendsto 1).comp h0
        rw [Complex.ofReal_one] at this
        exact this
      · refine Eventually.of_forall fun k => ?_
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h2 : ((1 : ℝ) + 1 / ((k : ℝ) + 1)) = 1 := by exact_mod_cast h
        have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    exact ht.frequently (Frequently.of_forall fun k => hagree _ (by positivity))
  exact (hf_diff.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    (hg_diff.analyticOnNhd hUo) hpre h1U hfreq hz

/-! ## 4. The Mellin step (Fubini) -/

/-- The Mordell integral as a function of `y`: `rsK c y = lineUp c (x |-> rsG x e^{-x y})`. -/
def rsK (c : ℝ) (y : ℂ) : ℂ := lineUp c (fun x => rsG x * cexp (-(x * y)))

theorem re_lineUp_mul (c v : ℝ) : (((c : ℂ) + v * (1 + I)) * (1 + I)).re = c := by
  simp

theorem cpow_mul_cpow_neg_one_add_I (s : ℂ) : (1 + I) ^ s * (1 + I) ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => one_add_I_ne_zero h.1

theorem gamma_cpow_line {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    Gamma s * ((c : ℂ) + v * (1 + I)) ^ (-s) =
      (1 + I) ^ s * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) *
        cexp (-(((c : ℂ) + v * (1 + I)) * (1 + I) * ρ)) := by
  have hre : 0 < (((c : ℂ) + v * (1 + I)) * (1 + I)).re := by rw [re_lineUp_mul]; exact hc
  rw [integral_cpow_mul_exp_neg_mul_Ioi_complex hs hre, one_div_mul_cpow hre]
  have h1 := cpow_mul_cpow_neg_one_add_I s
  linear_combination (-(((c : ℂ) + v * (1 + I)) ^ (-s) * Gamma s)) * h1

theorem continuous_rsG_line {c : ℝ} (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Continuous (fun v : ℝ => rsG ((c : ℂ) + v * (1 + I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  have h1 : ContinuousAt rsG ((c : ℂ) + v * (1 + I)) :=
    (differentiableAt_rsG (rsD_ne_zero_of_ne (lineUp_pt_ne_int hcl v))).continuousAt
  have h2 : ContinuousAt (fun v : ℝ => (c : ℂ) + v * (1 + I)) v := by fun_prop
  exact ContinuousAt.comp (g := rsG) (f := fun v : ℝ => (c : ℂ) + v * (1 + I)) h1 h2

/-- **The Mellin step.**  Fubini on `ℝ × (0, ∞)` with the complex-scaled Gamma integral. -/
theorem mellin_step {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {s : ℂ} (hs : 0 < s.re) :
    Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) =
      (1 + I) ^ s * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsK c ((1 + I) * ρ) := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ c :=
    notInt_of_Ioo (n := 0) (by simpa using hc) (by simpa using hc1)
  set F : ℝ → ℝ → ℂ := fun v ρ => rsG ((c : ℂ) + v * (1 + I)) * (1 + I) *
    ((ρ : ℂ) ^ (s - 1) * cexp (-(((c : ℂ) + v * (1 + I)) * (1 + I) * ρ))) with hF
  have hL : Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) =
      (1 + I) ^ s * ∫ v : ℝ, ∫ ρ in Ioi (0 : ℝ), F v ρ := by
    unfold lineUp
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; ext v
    simp only [hF]
    rw [integral_const_mul]
    have := gamma_cpow_line hc hs v
    calc Gamma s * (rsG ((c : ℂ) + v * (1 + I)) * ((c : ℂ) + v * (1 + I)) ^ (-s) * (1 + I))
        = rsG ((c : ℂ) + v * (1 + I)) * (1 + I) * (Gamma s * ((c : ℂ) + v * (1 + I)) ^ (-s)) := by
          ring
      _ = _ := by rw [this]; ring
  -- integrability on the product
  have hf₁ : Integrable (fun v : ℝ => ‖rsG ((c : ℂ) + v * (1 + I)) * (1 + I)‖) :=
    ((integrable_lineUp_rsG hcl).mul_const (1 + I)).norm
  have hf₂ : Integrable (fun ρ : ℝ => ‖(ρ : ℂ) ^ (s - 1)‖ * Real.exp (-(c * ρ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine (integrableOn_rpow_exp (a := s.re - 1) (b := c) (by linarith) hc).congr_fun
      (fun ρ hρ => ?_) measurableSet_Ioi
    simp only
    rw [norm_ofReal_cpow hρ, Complex.sub_re, Complex.one_re]
  have hprod := hf₁.mul_prod hf₂
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 : Measurable (fun p : ℝ × ℝ => rsG ((c : ℂ) + p.1 * (1 + I)) * (1 + I)) :=
      ((continuous_rsG_line hcl).measurable.comp measurable_fst).mul_const _
    have h2 : Measurable (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ (s - 1)) :=
      (Complex.measurable_ofReal.comp measurable_snd).pow_const _
    have h3 : Measurable (fun p : ℝ × ℝ =>
        cexp (-(((c : ℂ) + p.1 * (1 + I)) * (1 + I) * p.2))) :=
      (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        cexp (-(((c : ℂ) + p.1 * (1 + I)) * (1 + I) * p.2)))).measurable
    exact (h1.mul (h2.mul h3)).aestronglyMeasurable
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hre : ∀ v ρ : ℝ, (-(((c : ℂ) + v * (1 + I)) * (1 + I) * (ρ : ℂ))).re = -(c * ρ) := by
      intro v ρ; simp
    refine hprod.mono' hmeas (Eventually.of_forall fun p => le_of_eq ?_)
    simp only [Function.uncurry, hF]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, hre]
  rw [hL, integral_integral_swap hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => ?_)
  simp only [hF, rsK, lineUp]
  rw [← integral_const_mul]
  congr 1; ext v
  rw [show ((c : ℂ) + v * (1 + I)) * (1 + I) * (ρ : ℂ) = ((c : ℂ) + v * (1 + I)) * ((1 + I) * ρ) by
    ring]
  ring

/-! ## 5. Splitting the Mordell kernel -/

theorem norm_exp_one_add_I_mul (ρ : ℝ) : ‖cexp ((1 + I) * ρ)‖ = Real.exp ρ := by
  rw [Complex.norm_exp]; simp

theorem exp_one_add_I_ne_one {ρ : ℝ} (hρ : 0 < ρ) : cexp ((1 + I) * ρ) ≠ 1 := by
  intro h
  have := norm_exp_one_add_I_mul ρ
  rw [h, norm_one] at this
  have h2 : (1 : ℝ) < Real.exp ρ := Real.one_lt_exp_iff.mpr hρ
  linarith

/-- The Mordell closed form at `y = (1+i) rho`, split into the Bose kernel and the Gaussian
    kernel. -/
theorem rsK_split {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    rsK c ((1 + I) * ρ) = -(1 / (cexp ((1 + I) * ρ) - 1)) +
      cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π)) /
        (cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))) := by
  set y : ℂ := (1 + I) * ρ with hy
  have hM := lineUp_mordell hc hc1 y
  set u := cexp (y / 2) with hu
  set G := cexp (I * y ^ 2 / (4 * ↑π)) with hG
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hneg : cexp (-y / 2) = u⁻¹ := by rw [neg_div, Complex.exp_neg]
  have hneg' : cexp (-(y / 2)) = u⁻¹ := Complex.exp_neg _
  have hyy : cexp y = u * u := by rw [hu, ← Complex.exp_add]; ring_nf
  have hne1 : u * u ≠ 1 := by rw [← hyy]; exact exp_one_add_I_ne_one hρ
  have hd1 : u⁻¹ - u ≠ 0 := by
    intro h
    apply hne1
    have : u⁻¹ = u := sub_eq_zero.mp h
    calc u * u = u * u⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel₀ hu0
  have hd2 : u - u⁻¹ ≠ 0 := by
    intro h; apply hd1; rw [← neg_sub, h, neg_zero]
  have hd3 : u * u - 1 ≠ 0 := sub_ne_zero.mpr hne1
  unfold rsK
  rw [hneg] at hM
  rw [hyy, hneg']
  have hK : lineUp c (fun x => rsG x * cexp (-(x * y))) = (u⁻¹ - G) / (u⁻¹ - u) := by
    rw [eq_div_iff hd1]; exact hM
  rw [hK, div_eq_iff hd1]
  have e0 : u⁻¹ - u = -u⁻¹ * (u * u - 1) := by field_simp; ring
  have e1 : 1 / (u * u - 1) * (u⁻¹ - u) = -u⁻¹ := by
    rw [e0, one_div, mul_comm, mul_assoc, mul_inv_cancel₀ hd3, mul_one]
  have e2 : G / (u - u⁻¹) * (u⁻¹ - u) = -G := by
    rw [show u⁻¹ - u = -(u - u⁻¹) by ring, mul_neg, div_mul_cancel₀ _ hd2]
  linear_combination e1 - e2

/-! ## 6. The Bose integral -/

theorem cpow_nat_succ_mul {k : ℕ} (s : ℂ) :
    (1 / (((k : ℂ) + 1) * (1 + I))) ^ s = 1 / ((k : ℂ) + 1) ^ s * (1 + I) ^ (-s) := by
  have hre : 0 < (((k : ℂ) + 1) * (1 + I)).re := by simp; positivity
  rw [one_div_mul_cpow hre, Complex.cpow_neg, one_div]

theorem integral_bose {s : ℂ} (hs : 1 < s.re) :
    ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1)) =
      (1 + I) ^ (-s) * Gamma s * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  set f : ℕ → ℝ → ℂ := fun k ρ => (ρ : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * (1 + I) * ρ)) with hf
  have hser : ∀ ρ : ℝ, 0 < ρ →
      HasSum (fun k => f k ρ) ((ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1))) := by
    intro ρ hρ
    set q := cexp (-((1 + I) * ρ)) with hq
    have hqn : ‖q‖ < 1 := by
      rw [hq, Complex.norm_exp]
      simp only [neg_re, mul_re, add_re, one_re, I_re, ofReal_re, add_im, one_im, I_im, ofReal_im]
      simp only [add_zero, one_mul, mul_zero, sub_zero, zero_add]
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    have h1 := (hasSum_geometric_of_norm_lt_one hqn).mul_left ((ρ : ℂ) ^ (s - 1) * q)
    have hE0 : cexp ((1 + I) * ρ) ≠ 0 := Complex.exp_ne_zero _
    have hE1 : cexp ((1 + I) * ρ) - 1 ≠ 0 := sub_ne_zero.mpr (exp_one_add_I_ne_one hρ)
    have hqinv : q = (cexp ((1 + I) * ρ))⁻¹ := by rw [hq, Complex.exp_neg]
    have h1q : 1 - q ≠ 0 := by
      rw [hqinv]; intro h
      apply exp_one_add_I_ne_one hρ
      have := sub_eq_zero.mp h
      field_simp at this
      exact this
    have hfun : (fun k => f k ρ) = fun i => (ρ : ℂ) ^ (s - 1) * q * q ^ i := by
      ext k
      simp only [hf]
      rw [show (ρ : ℂ) ^ (s - 1) * q * q ^ k = (ρ : ℂ) ^ (s - 1) * q ^ (k + 1) by ring, hq,
        ← Complex.exp_nat_mul]
      congr 2; push_cast; ring
    have hval : (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1)) =
        (ρ : ℂ) ^ (s - 1) * q * (1 - q)⁻¹ := by
      rw [hqinv]; field_simp
    rw [hfun, hval]; exact h1
  have hint : ∀ k : ℕ, Integrable (f k) (volume.restrict (Ioi (0 : ℝ))) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    refine (integrableOn_rpow_exp (a := s.re - 1) (b := (k : ℝ) + 1) (by linarith) hk).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro ρ hρ
      exact (((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
        Complex.continuous_ofReal.continuousAt).mul (by fun_prop)).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
      simp only [hf]
      rw [norm_mul, norm_ofReal_cpow hρ, Complex.norm_exp]
      apply le_of_eq
      congr 2
      simp
  have hnorm : ∀ k : ℕ, ∫ ρ in Ioi (0 : ℝ), ‖f k ρ‖ =
      (1 / ((k : ℝ) + 1)) ^ s.re * Real.Gamma s.re := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 hk]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    simp only [hf]
    rw [norm_mul, norm_ofReal_cpow hρ, Complex.norm_exp]
    congr 2
    simp
  have hsum : Summable (fun k : ℕ => ∫ ρ in Ioi (0 : ℝ), ‖f k ρ‖) := by
    simp_rw [hnorm]
    refine Summable.mul_right _ ?_
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) :=
      Real.summable_one_div_nat_rpow.mpr hs
    have h2 := (summable_nat_add_iff 1).mpr h1
    refine h2.congr (fun k => ?_)
    push_cast
    rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]
  have hval : ∀ k : ℕ, ∫ ρ in Ioi (0 : ℝ), f k ρ =
      1 / ((k : ℂ) + 1) ^ s * (1 + I) ^ (-s) * Gamma s := by
    intro k
    have hre : 0 < (((k : ℂ) + 1) * (1 + I)).re := by simp; positivity
    simp only [hf]
    rw [integral_cpow_mul_exp_neg_mul_Ioi_complex hs0 hre, cpow_nat_succ_mul]
  calc ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1))
      = ∫ ρ in Ioi (0 : ℝ), ∑' k, f k ρ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
        exact (hser ρ hρ).tsum_eq.symm
    _ = ∑' k, ∫ ρ in Ioi (0 : ℝ), f k ρ := (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' k : ℕ, 1 / ((k : ℂ) + 1) ^ s * ((1 + I) ^ (-s) * Gamma s) := by
        congr 1; ext k; rw [hval]; ring
    _ = (1 + I) ^ (-s) * Gamma s * riemannZeta s := by
        rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hs]; ring

/-! ## 7. The chi-side kernel -/

/-- The chi-side (Gaussian) kernel on the ray `y = (1+i) rho`:
    `rsE rho = e^{i y^2/(4 pi)} / (e^{y/2} - e^{-y/2})`. -/
def rsE (ρ : ℝ) : ℂ :=
  cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π)) / (cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2)))

/-- Half of the chi-side line: `rsHR s = int_0^oo rsH(r(1-i)) (r(1-i))^(s-1) (1-i) dr`. -/
def rsHR (s : ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), rsH (r * (1 - I)) * ((r : ℂ) * (1 - I)) ^ (s - 1) * (1 - I)

theorem rsH_ray (r : ℝ) : rsH ((r : ℂ) * (1 - I)) = rsE (2 * π * r) := by
  unfold rsH rsD rsE
  have hpi := pi_ne_zero'
  push_cast
  congr 1
  · congr 1
    field_simp
    linear_combination (-8 * (r : ℂ) ^ 2) * I_sq
  · congr 1
    · congr 1; linear_combination (-(↑π * (r : ℂ))) * I_sq
    · congr 1; linear_combination (↑π * (r : ℂ)) * I_sq

theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz), Complex.cpow_def_of_ne_zero hr0,
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  congr 1; ring

theorem cpow_mul_cpow_neg {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z ^ s * z ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hz h.1

theorem integral_Epart (s : ℂ) :
    ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ = (2 * ↑π) ^ s * (1 - I) ^ (-s) * rsHR s := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hpi0 : (2 * ↑π : ℂ) ≠ 0 := by
    have := pi_ne_zero'; exact mul_ne_zero two_ne_zero this
  have h1 : rsHR s = (1 - I) ^ s * ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * rsE (2 * π * r) := by
    unfold rsHR
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [rsH_ray, ofReal_mul_cpow hr one_sub_I_ne_zero]
    have h : (1 - I) ^ (s - 1) * (1 - I) = (1 - I) ^ s := by
      rw [Complex.cpow_sub _ _ one_sub_I_ne_zero, Complex.cpow_one,
        div_mul_cancel₀ _ one_sub_I_ne_zero]
    linear_combination (rsE (2 * π * r) * (r : ℂ) ^ (s - 1)) * h
  have h2 : ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * rsE (2 * π * r) =
      (2 * ↑π) ^ (-s) * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ := by
    have hsub := integral_comp_mul_left_Ioi (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1) * rsE ρ) 0 hpi
    rw [mul_zero] at hsub
    have hpt : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * rsE (2 * π * r) =
        (2 * ↑π) ^ (1 - s) * ((((2 * π * r : ℝ)) : ℂ) ^ (s - 1) * rsE (2 * π * r)) := by
      intro r hr
      rw [show (((2 * π * r : ℝ)) : ℂ) = (((2 * π : ℝ)) : ℂ) * (r : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg hpi.le (le_of_lt hr)]
      have hc : (2 * ↑π : ℂ) ^ (1 - s) * (((2 * π : ℝ)) : ℂ) ^ (s - 1) = 1 := by
        push_cast
        rw [← Complex.cpow_add _ _ hpi0, show 1 - s + (s - 1) = 0 by ring, Complex.cpow_zero]
      linear_combination (-((r : ℂ) ^ (s - 1) * rsE (2 * π * r))) * hc
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hsub, Complex.real_smul]
    push_cast
    rw [← mul_assoc]
    congr 1
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hpi0]
    congr 1; ring
  rw [h1, h2]
  have e1 := cpow_mul_cpow_neg one_sub_I_ne_zero s
  have e2 := cpow_mul_cpow_neg hpi0 s
  linear_combination (-(∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ)) *
    ((2 * ↑π) ^ s * (2 * ↑π) ^ (-s) * e1 + e2)

/-! ## 8. Integrability of the two pieces on (0, oo) -/

theorem le_exp_sub_exp {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ ≤ Real.exp (ρ / 2) - Real.exp (-(ρ / 2)) := by
  have h := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ ρ / 2)
  rw [Real.sinh_eq] at h
  linarith

theorem norm_exp_half_sub_ge {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ ≤ ‖cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))‖ := by
  have h1 : ‖cexp ((1 + I) * ρ / 2)‖ = Real.exp (ρ / 2) := by rw [Complex.norm_exp]; simp
  have h2 : ‖cexp (-((1 + I) * ρ / 2))‖ = Real.exp (-(ρ / 2)) := by rw [Complex.norm_exp]; simp
  have := norm_sub_norm_le (cexp ((1 + I) * ρ / 2)) (cexp (-((1 + I) * ρ / 2)))
  rw [h1, h2] at this
  linarith [le_exp_sub_exp hρ]

theorem norm_exp_sub_one_ge {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ * Real.exp (ρ / 2) ≤ ‖cexp ((1 + I) * ρ) - 1‖ := by
  have h1 := norm_sub_norm_le (cexp ((1 + I) * ρ)) 1
  rw [norm_exp_one_add_I_mul, norm_one] at h1
  have h2 := le_exp_sub_exp hρ
  have h3 : Real.exp ρ - 1 = Real.exp (ρ / 2) * (Real.exp (ρ / 2) - Real.exp (-(ρ / 2))) := by
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add, show ρ / 2 + ρ / 2 = ρ by ring,
      show ρ / 2 + -(ρ / 2) = 0 by ring, Real.exp_zero]
  have h4 : ρ * Real.exp (ρ / 2) ≤ Real.exp ρ - 1 := by
    rw [h3, mul_comm]; exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  linarith

theorem integrableOn_bose {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1))) (Ioi 0) := by
  refine (integrableOn_rpow_exp (a := s.re - 2) (b := 1 / 2) (by linarith) (by norm_num)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro ρ hρ
    have hne : cexp ((1 + I) * ρ) - 1 ≠ 0 := sub_ne_zero.mpr (exp_one_add_I_ne_one hρ)
    exact (((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
      Complex.continuous_ofReal.continuousAt).mul
      (continuousAt_const.div (by fun_prop) hne)).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ' : (0 : ℝ) < ρ := hρ
    have hden := norm_exp_sub_one_ge hρ'.le
    have hpos : 0 < ρ * Real.exp (ρ / 2) := by positivity
    rw [norm_mul, norm_ofReal_cpow hρ', norm_div, norm_one]
    have hq : 1 / ‖cexp ((1 + I) * ρ) - 1‖ ≤ 1 / (ρ * Real.exp (ρ / 2)) :=
      one_div_le_one_div_of_le hpos hden
    have hpow : ρ ^ (s - 1).re * (1 / (ρ * Real.exp (ρ / 2))) =
        ρ ^ (s.re - 2) * Real.exp (-(1 / 2 * ρ)) := by
      rw [Complex.sub_re, Complex.one_re, show s.re - 2 = (s.re - 1) - 1 by ring,
        Real.rpow_sub_one hρ'.ne' (s.re - 1), show -(1 / 2 * ρ) = -(ρ / 2) by ring, Real.exp_neg]
      ring
    calc ρ ^ (s - 1).re * (1 / ‖cexp ((1 + I) * ρ) - 1‖)
        ≤ ρ ^ (s - 1).re * (1 / (ρ * Real.exp (ρ / 2))) :=
          mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hρ'.le _)
      _ = _ := hpow

theorem integrableOn_Epart {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1) * rsE ρ) (Ioi 0) := by
  have hb : (0 : ℝ) < 1 / (2 * π) := by positivity
  refine (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := s.re - 2) (by linarith)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro ρ hρ
    have hne : cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2)) ≠ 0 := by
      intro h
      have := norm_exp_half_sub_ge (le_of_lt hρ)
      rw [h, norm_zero] at this
      exact absurd this (not_le.mpr hρ)
    unfold rsE
    exact (((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
      Complex.continuous_ofReal.continuousAt).mul
      ((by fun_prop : ContinuousAt (fun ρ : ℝ => cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π))) ρ).div
        (by fun_prop) hne)).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ' : (0 : ℝ) < ρ := hρ
    have hden := norm_exp_half_sub_ge hρ'.le
    have hnum : ‖cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π))‖ = Real.exp (-(1 / (2 * π)) * ρ ^ 2) := by
      rw [Complex.norm_exp]
      congr 1
      have hpi := Real.pi_pos
      simp [pow_two, mul_re, mul_im, div_re]
      field_simp
      ring
    unfold rsE
    rw [norm_mul, norm_ofReal_cpow hρ', norm_div, hnum]
    have hq : Real.exp (-(1 / (2 * π)) * ρ ^ 2) /
        ‖cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))‖ ≤
        Real.exp (-(1 / (2 * π)) * ρ ^ 2) / ρ :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hρ' hden
    calc ρ ^ (s - 1).re * (Real.exp (-(1 / (2 * π)) * ρ ^ 2) /
          ‖cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))‖)
        ≤ ρ ^ (s - 1).re * (Real.exp (-(1 / (2 * π)) * ρ ^ 2) / ρ) :=
          mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hρ'.le _)
      _ = ρ ^ (s.re - 2) * Real.exp (-(1 / (2 * π)) * ρ ^ 2) := by
          rw [Complex.sub_re, Complex.one_re, show s.re - 2 = (s.re - 1) - 1 by ring,
            Real.rpow_sub_one hρ'.ne' (s.re - 1)]
          ring

/-! ## 9. The Mellin identity -/

/-- **The Mellin identity** (Re s > 1, 0 < c < 1):
    Gamma(s) lineUp c (rsG x^(-s)) = -Gamma(s) zeta(s) + (2 pi)^s (1+i)^s (1-i)^(-s) rsHR s. -/
theorem mellin_identity {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {s : ℂ} (hs : 1 < s.re) :
    Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) =
      -(Gamma s * riemannZeta s) + (2 * ↑π) ^ s * (1 + I) ^ s * (1 - I) ^ (-s) * rsHR s := by
  rw [mellin_step hc hc1 (by linarith)]
  have hsplit : ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsK c ((1 + I) * ρ) =
      (∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ) -
        ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1)) := by
    rw [← integral_sub (integrableOn_Epart hs) (integrableOn_bose hs)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    rw [rsK_split hc hc1 hρ]; unfold rsE; ring
  rw [hsplit, integral_bose hs, integral_Epart s]
  have h1 := cpow_mul_cpow_neg_one_add_I s
  linear_combination (-(Gamma s * riemannZeta s)) * h1

end RSInt
