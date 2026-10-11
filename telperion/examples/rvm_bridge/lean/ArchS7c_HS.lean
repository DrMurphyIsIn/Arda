import ArchS7c_RowAll

/-!
# ArchS7c_HS: `‖P F P ϑ(g)‖²_HS = archW g + Dfun g`

* `countable_of_hilbertBasis`: a Hilbert basis of `L²(ℝ)_ev` is countable.
* `rowE`: `conj M(w,·)` as a vector of `L²(ℝ)_ev` (`|w| > 1`), `⟨rowE, y⟩ = ∫ M(w,u) y(u) du`.
* `hs_eq_lintegral`: `Σ_k ‖Q e_k‖² = ∫ 1{|w|>1} ‖M(w,·)‖² dw` (Tonelli + Parseval).
* `measurable_PhiM`, `measurable_hsq`: joint measurability for Tonelli in `(w, r)`.
* `Nnorm_neg`: `Nnorm` is even (via `ell_eq_Nnorm`).
* **`hs_Q_eq`**: `Σ_k ‖Q e_k‖² = archW g + Dfun g` in `ℝ≥0∞`.

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

namespace ArchS7c

open ArchS6 ArchS7 ArchS3

set_option linter.unusedSectionVars false

/-- Every Hilbert basis of `L²(ℝ)_ev` is countable (separability). -/
theorem countable_of_hilbertBasis {κ : Type*} (e : HilbertBasis κ ℂ evenL2) : Countable κ := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : TopologicalSpace.SeparableSpace evenL2 := inferInstance
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (e i) (1 / 2)) ?_
    (fun _ ↦ Metric.isOpen_ball) (fun i ↦ ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro z hzi hzj
  have hd : ‖e i - e j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq ℂ, e.orthonormal.1 i, e.orthonormal.1 j, e.orthonormal.2 hij]; norm_num
  have h1 : ‖e i - e j‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hzi hzj
    calc ‖e i - e j‖ = ‖(z - e j) - (z - e i)‖ := by congr 1; abel
      _ ≤ ‖z - e j‖ + ‖z - e i‖ := norm_sub_le _ _
      _ < 1 := by linarith
  nlinarith [norm_nonneg (e i - e j)]

section

variable {g : ℝ → ℂ}

theorem memLp_conj_Mk (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : w ≠ 0) :
    MemLp (fun u => conj (Mk g w u)) 2 volume := by
  have hM := memLp_Mk' hW hw
  have hm : AEStronglyMeasurable (fun u => conj (Mk g w u)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hM.1
  rw [memLp_two_iff_integrable_sq_norm hm]
  have := (memLp_two_iff_integrable_sq_norm hM.1).mp hM
  simpa [Complex.norm_conj] using this

/-- The row vector `conj M(w,·) ∈ L²(ℝ)`. -/
def rowVec (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : w ≠ 0) : L2R := (memLp_conj_Mk hW hw).toLp _

theorem rowVec_mem (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : w ≠ 0) : rowVec hW hw ∈ evenL2 := by
  rw [mem_evenL2]
  apply Lp.ext
  filter_upwards [coeFn_reflect (rowVec hW hw), ae_eq_comp_neg (memLp_conj_Mk hW hw).coeFn_toLp,
    (memLp_conj_Mk hW hw).coeFn_toLp] with v h1 h2 h3
  rw [h1, rowVec, h2, h3, Mk_neg]

/-- The row vector in `L²(ℝ)_ev`. -/
def rowE (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : w ≠ 0) : evenL2 := ⟨rowVec hW hw, rowVec_mem hW hw⟩

theorem inner_rowE (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : w ≠ 0) (y : evenL2) :
    ⟪rowE hW hw, y⟫_ℂ = ∫ u, Mk g w u * ((y : L2R) : ℝ → ℂ) u := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_conj_Mk hW hw).coeFn_toLp] with u hu
  show ⟪((rowVec hW hw : L2R) : ℝ → ℂ) u, _⟫_ℂ = _
  rw [rowVec, hu, RCLike.inner_apply, Complex.conj_conj, mul_comm]

theorem norm_rowE_sq (hW : WeilExplicit.IsWeilTest g) {w : ℝ} (hw : w ≠ 0) :
    ‖rowE hW hw‖ ^ 2 = ∫ u, ‖Mk g w u‖ ^ 2 := by
  rw [Submodule.coe_norm, norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_conj_Mk hW hw).coeFn_toLp] with u hu
  show ‖((rowVec hW hw : L2R) : ℝ → ℂ) u‖ ^ 2 = _
  rw [rowVec, hu, Complex.norm_conj]

/-- **Tonelli + Parseval**: `Σ_k ‖Q e_k‖² = ∫ 1{|w|>1} ‖M(w,·)‖² dw`. -/
theorem hs_eq_lintegral (hW : WeilExplicit.IsWeilTest g) (hg : Integrable g) {κ : Type*}
    (e : HilbertBasis κ ℂ evenL2) :
    ∑' k, ENNReal.ofReal (‖Qop g hg (e k)‖ ^ 2)
      = ∫⁻ w, ENNReal.ofReal (if 1 < |w| then ∫ u, ‖Mk g w u‖ ^ 2 else 0) := by
  have := countable_of_hilbertBasis e
  have h1 : ∀ k, ENNReal.ofReal (‖Qop g hg (e k)‖ ^ 2)
      = ∫⁻ w, ENNReal.ofReal (‖(((Qop g hg (e k) : evenL2) : L2R) : ℝ → ℂ) w‖ ^ 2) := by
    intro k
    rw [Submodule.coe_norm, norm_sq_eq_integral,
      ofReal_integral_eq_lintegral_ofReal ((Lp.memLp _).integrable_norm_pow two_ne_zero)
        (Eventually.of_forall fun _ => by positivity)]
  simp_rw [h1]
  rw [← lintegral_tsum fun k => ((Lp.stronglyMeasurable _).measurable.norm.pow_const 2
    |>.ennreal_ofReal).aemeasurable]
  apply lintegral_congr_ae
  have hall : ∀ᵐ w ∂volume, ∀ k, (((Qop g hg (e k) : evenL2) : L2R) : ℝ → ℂ) w
      = rowF g (((e k : evenL2) : L2R) : ℝ → ℂ) w :=
    ae_all_iff.mpr fun k => coeFn_Q hW hg (e k)
  filter_upwards [hall] with w hw
  simp_rw [hw]
  by_cases h : 1 < |w|
  · have hw0 : w ≠ 0 := fun h0 => by rw [h0, abs_zero] at h; linarith
    have hr : ∀ k, rowF g (((e k : evenL2) : L2R) : ℝ → ℂ) w = ⟪rowE hW hw0, e k⟫_ℂ := by
      intro k; rw [rowF, if_pos h, inner_rowE]
    simp_rw [hr, norm_inner_symm (rowE hW hw0)]
    rw [tsum_ofReal_norm_inner_sq e, norm_rowE_sq, if_pos h]
  · simp [rowF, h]

/-! ### Measurability in `(w, r)` -/

/-- `Φ_t(a)` for `a > 0`, extended by `0`. -/
def PhiM (t a : ℝ) : ℂ := if 0 < a then Phi t a else 0

theorem measurable_intervalIntegral_pD (n : ℝ) :
    Measurable fun p : ℝ × ℝ => ∫ s in p.2..n, pD p.1 0 s := by
  have hpD : Measurable fun q : (ℝ × ℝ) × ℝ => pD q.1.1 0 q.2 := by
    unfold pD cosD zt; fun_prop
  have hA : ∀ (lo hi : ℝ × ℝ → ℝ), Measurable lo → Measurable hi →
      Measurable fun p : ℝ × ℝ => ∫ s, (Ioc (lo p) (hi p)).indicator (pD p.1 0) s := by
    intro lo hi hlo hhi
    have hm : Measurable (Function.uncurry fun (p : ℝ × ℝ) (s : ℝ) =>
        (Ioc (lo p) (hi p)).indicator (pD p.1 0) s) := by
      have e : (Function.uncurry fun (p : ℝ × ℝ) (s : ℝ) => (Ioc (lo p) (hi p)).indicator (pD p.1 0) s)
          = fun q : (ℝ × ℝ) × ℝ => if lo q.1 < q.2 ∧ q.2 ≤ hi q.1 then pD q.1.1 0 q.2 else 0 := by
        funext q
        simp only [Function.uncurry, indicator, mem_Ioc]
      rw [e]
      refine Measurable.ite ?_ hpD measurable_const
      exact (measurableSet_lt (hlo.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hhi.comp measurable_fst))
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  have e : (fun p : ℝ × ℝ => ∫ s in p.2..n, pD p.1 0 s)
      = fun p => (∫ s, (Ioc p.2 n).indicator (pD p.1 0) s) - ∫ s, (Ioc n p.2).indicator (pD p.1 0) s := by
    funext p
    rw [intervalIntegral, integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rw [e]
  exact (hA (fun p => p.2) (fun _ => n) measurable_snd measurable_const).sub
    (hA (fun _ => n) (fun p => p.2) measurable_const measurable_snd)

theorem measurable_PhiM : Measurable fun p : ℝ × ℝ => PhiM p.1 p.2 := by
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (p : ℝ × ℝ) =>
    if 0 < p.2 then ∫ s in p.2..(n : ℝ), pD p.1 0 s else 0)
    (fun n => Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      (measurable_intervalIntegral_pD n) measurable_const) ?_
  rw [tendsto_pi_nhds]
  intro p
  unfold PhiM
  by_cases hp : 0 < p.2
  · simp only [if_pos hp]
    exact (tendsto_integral_Phi hp).comp tendsto_natCast_atTop_atTop
  · simp only [if_neg hp]; exact tendsto_const_nhds

theorem measurable_hsq (hgc : Continuous g) : Measurable (RvMBridge31.hsq g) := by
  have hm : StronglyMeasurable (Function.uncurry fun (r : ℝ) (u : ℝ) => g u * cexp (I * (r : ℂ) * u)) := by
    apply Measurable.stronglyMeasurable
    exact (hgc.measurable.comp measurable_snd).mul (by fun_prop)
  have h := (hm.integral_prod_right (ν := volume)).measurable
  unfold RvMBridge31.hsq Zeta23.paperFT
  exact (h.norm.pow_const 2)

theorem Nnorm_neg (r : ℝ) : Nnorm (-r) = Nnorm r := by
  rw [← ell_eq_Nnorm, ← ell_eq_Nnorm, ell, ell, RvMBridge30.psiR_neg]
  congr 1
  unfold deltaHat
  congr 1; funext u
  rw [neg_mul, Real.cos_neg]

/-- The `w`-integral for fixed `r`. -/
theorem lintegral_w (hW : WeilExplicit.IsWeilTest g) (r : ℝ) :
    ∫⁻ w, ENNReal.ofReal (if 1 < |w| then RvMBridge31.hsq g (-r) * ‖PhiM r |w|‖ ^ 2 / |w| / (4 * Real.pi)
      else 0)
      = ENNReal.ofReal (RvMBridge31.hsq g (-r) * Nnorm r / (2 * Real.pi)) := by
  set c := RvMBridge31.hsq g (-r) / (4 * Real.pi) with hc
  have hc0 : 0 ≤ c := by rw [hc]; unfold RvMBridge31.hsq; positivity
  set f : ℝ → ℝ := (Ioi (1 : ℝ)).indicator fun a => c * (‖Phi r a‖ ^ 2 / a) with hf
  have hfi : Integrable f :=
    (integrable_indicator_iff measurableSet_Ioi).mpr ((integrableOn_normSq_Phi r).const_mul c)
  have hpt : ∀ w, (if 1 < |w| then RvMBridge31.hsq g (-r) * ‖PhiM r |w|‖ ^ 2 / |w| / (4 * Real.pi) else 0)
      = f w + f (-w) := by
    intro w
    simp only [hf, indicator, mem_Ioi]
    by_cases h : 1 < |w|
    · rw [if_pos h]
      have h0 : 0 < |w| := by linarith
      rw [PhiM, if_pos h0]
      rcases le_or_gt 0 w with hw | hw
      · have h1 : 1 < w := by rwa [abs_of_nonneg hw] at h
        rw [abs_of_nonneg hw, if_pos h1, if_neg (by linarith), add_zero, hc]; ring
      · have h1 : 1 < -w := by rwa [abs_of_neg hw] at h
        rw [abs_of_neg hw, if_neg (by linarith), if_pos h1, zero_add, hc]; ring
    · rw [if_neg h, if_neg (fun h1 => h (lt_of_lt_of_le h1 (le_abs_self w))),
        if_neg (fun h1 => h (lt_of_lt_of_le h1 (neg_le_abs w))), add_zero]
  simp_rw [hpt]
  have hfi' : Integrable fun w => f (-w) := hfi.comp_neg
  have hnn : ∀ w, 0 ≤ f w := fun w => indicator_nonneg (fun a ha => by
    have : (0 : ℝ) < a := lt_trans one_pos ha
    positivity) w
  have hsum : Integrable (fun w => f w + f (-w)) := hfi.add hfi'
  rw [← ofReal_integral_eq_lintegral_ofReal hsum
    (Eventually.of_forall fun w => add_nonneg (hnn w) (hnn (-w))), integral_add hfi hfi',
    integral_neg_eq_self f volume, hf, integral_indicator measurableSet_Ioi, integral_const_mul,
    ← Nnorm, hc]
  congr 1
  have := Real.pi_pos
  field_simp
  ring

/-- **The HS norm** in `ℝ≥0∞`: `Σ_k ‖P F P ϑ(g) e_k‖² = archW g + Dfun g`. -/
theorem hs_Q_eq (hW : WeilExplicit.IsWeilTest g) (hg : Integrable g) {κ : Type*}
    (e : HilbertBasis κ ℂ evenL2) :
    ∑' k, ENNReal.ofReal (‖Qop g hg (e k)‖ ^ 2) = ENNReal.ofReal (archW g + Dfun g) := by
  rw [hs_eq_lintegral hW hg e]
  set G : ℝ → ℝ → ℝ≥0∞ := fun w r => ENNReal.ofReal
    (if 1 < |w| then RvMBridge31.hsq g (-r) * ‖PhiM r |w|‖ ^ 2 / |w| / (4 * Real.pi) else 0) with hG
  have hpt : ∀ w, ENNReal.ofReal (if 1 < |w| then ∫ u, ‖Mk g w u‖ ^ 2 else 0) = ∫⁻ r, G w r := by
    intro w
    by_cases h : 1 < |w|
    · have h0 : 0 < |w| := by linarith
      have hMw : Mk g w = Mk g |w| := by
        rcases le_or_gt 0 w with hw | hw
        · rw [abs_of_nonneg hw]
        · rw [abs_of_neg hw]; funext u; rw [Mk_neg_w]
      rw [if_pos h, hMw, integral_normSq_Mk hW h0]
      have hi : Integrable fun r =>
          1 / (4 * Real.pi) * (RvMBridge31.hsq g (-r) * ‖Phi r |w|‖ ^ 2 / |w|) := by
        refine ((integrable_hsq_Phi hW h0).const_mul (1 / Real.pi)).congr
          (Eventually.of_forall fun r => ?_)
        have := Real.pi_pos
        simp only
        field_simp
      rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun r => by unfold RvMBridge31.hsq; positivity)]
      refine lintegral_congr fun r => ?_
      simp only [hG, if_pos h, PhiM, if_pos h0]
      congr 1; ring
    · simp only [hG, if_neg h, ENNReal.ofReal_zero, lintegral_zero]
  simp_rw [hpt]
  have hGm : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
    refine Measurable.aemeasurable ?_
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.ite (measurableSet_lt measurable_const (measurable_abs.comp measurable_fst)) ?_
      measurable_const
    exact ((((measurable_hsq hW.1.continuous).comp measurable_snd.neg).mul
      ((measurable_PhiM.comp (measurable_snd.prodMk (measurable_abs.comp measurable_fst))).norm.pow_const 2)).div
      (measurable_abs.comp measurable_fst)).div_const _
  rw [lintegral_lintegral_swap hGm]
  have hw : ∀ r, ∫⁻ w, G w r = ENNReal.ofReal (RvMBridge31.hsq g (-r) * Nnorm r / (2 * Real.pi)) :=
    fun r => lintegral_w hW r
  simp_rw [hw]
  set H : ℝ → ℝ := fun r => RvMBridge31.hsq g r * Nnorm r with hH
  have hHi : Integrable H := by
    have h1 := RvMBridge31.integrable_hsq_mul_psiR hW
    have h2 := (RvMBridge31.integrable_hsq hW).mul_const (Real.log Real.pi)
    have h3 := integrable_hsq_mul_deltaHat hW
    refine ((h1.sub h2).add h3).congr (Eventually.of_forall fun r => ?_)
    simp only [hH, Pi.add_apply, Pi.sub_apply, ← ell_eq_Nnorm, ell]
    ring
  have hint : Integrable fun r => RvMBridge31.hsq g (-r) * Nnorm r / (2 * Real.pi) := by
    refine (hHi.comp_neg.div_const (2 * Real.pi)).congr (Eventually.of_forall fun r => ?_)
    simp only [hH, Nnorm_neg]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun r => by have := Nnorm_nonneg r; unfold RvMBridge31.hsq; positivity)]
  congr 1
  show _ = Lfun g
  rw [Lfun_eq_integral_Nnorm hW]
  have e : (fun r => RvMBridge31.hsq g (-r) * Nnorm r / (2 * Real.pi))
      = fun r => 1 / (2 * Real.pi) * H (-r) := by
    funext r; simp only [hH, Nnorm_neg]; ring
  rw [e, integral_const_mul, integral_neg_eq_self H volume]

end

end ArchS7c
