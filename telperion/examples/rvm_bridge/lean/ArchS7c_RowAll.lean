import ArchS7c_Row

/-!
# ArchS7c_RowAll: the row identity for every `y ∈ L²(ℝ)_ev`

`Q y = P F P ϑ(g) y` (on `L²(ℝ)_ev`, `P = 1 - P₁`, `F` the Fourier transform).

* `coeFn_evenP`: `(P z)(w) = 1{|w|>1} z(w)` a.e.
* `coeFn_Q_integrable`: `(Q y)(w) = 1{|w|>1} ∫ M(w,u) y(u) du` a.e., for integrable `y`.
* **`coeFn_Q`**: the same for every `y ∈ L²(ℝ)_ev` (truncations `1_{[-n,n]} y`, an a.e.-convergent
  subsequence, and dominated convergence in `u` using `M(w,·) ∈ L²`).

conjecture1_proved = False.
-/

open MeasureTheory Set Filter Topology Complex FourierTransform
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace ArchS7c

open ArchS6 ArchS7

set_option linter.unusedSectionVars false

/-- The operator `Q = P F P ϑ(g)` on `L²(ℝ)_ev`. -/
def Qop (g : ℝ → ℂ) (hg : Integrable g) : evenL2 →L[ℂ] evenL2 :=
  evenPair.P ∘L evenPair.F ∘L evenPair.P ∘L theta g hg

theorem Qop_apply (g : ℝ → ℂ) (hg : Integrable g) (y : evenL2) :
    Qop g hg y = evenPair.P (evenPair.F (evenPair.P (theta g hg y))) := rfl

/-- The row form `1{|w|>1} ∫ M(w,u) y(u) du`. -/
def rowF (g F : ℝ → ℂ) (w : ℝ) : ℂ := if 1 < |w| then ∫ u, Mk g w u * F u else 0

theorem coeFn_evenP (z : evenL2) :
    (((evenPair.P z : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun w => if 1 < |w| then ((z : L2R) : ℝ → ℂ) w else 0 := by
  rw [ProjPair.P_apply, Submodule.coe_sub, evenPair_P₁]
  filter_upwards [Lp.coeFn_sub (z : L2R) (P1 (z : L2R)), coeFn_P1 (z : L2R)] with w h1 h2
  rw [h1, Pi.sub_apply, h2]
  by_cases hw : 1 < |w|
  · rw [if_pos hw, indicator_of_notMem (fun h => by
      have := abs_le.mpr ⟨h.1, h.2⟩; linarith), sub_zero]
  · rw [if_neg hw, indicator_of_mem (show w ∈ Icc (-1 : ℝ) 1 from abs_le.mp (not_lt.mp hw)), sub_self]

theorem even_ae (y : evenL2) :
    (fun u => ((y : L2R) : ℝ → ℂ) (-u)) =ᵐ[volume] ((y : L2R) : ℝ → ℂ) := by
  have h := coeFn_reflect (y : L2R)
  rw [mem_evenL2.mp y.2] at h
  exact h.symm

section

variable {g : ℝ → ℂ}

theorem coeFn_Q_integrable (hW : WeilExplicit.IsWeilTest g) (hg : Integrable g) (y : evenL2)
    (hy : Integrable ((y : L2R) : ℝ → ℂ)) :
    (((Qop g hg y : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume] rowF g ((y : L2R) : ℝ → ℂ) := by
  set F : ℝ → ℂ := ((y : L2R) : ℝ → ℂ) with hFdef
  have hFm : Measurable F := (Lp.stronglyMeasurable _).measurable
  set z1 := evenPair.P (theta g hg y) with hz1def
  have hz1 : (((z1 : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume] fun v => if 1 < |v| then Vp g F v else 0 := by
    filter_upwards [coeFn_evenP (theta g hg y), coeFn_theta hW hg y hy] with v h1 h2
    rw [hz1def, h1, h2]
  have hz1i : Integrable (((z1 : evenL2) : L2R) : ℝ → ℂ) := by
    refine Integrable.mono' (integrable_Vp hW hy hFm).norm (Lp.aestronglyMeasurable _) ?_
    filter_upwards [hz1] with v hv
    rw [hv]; split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have h2 : ((((evenPair.F z1 : evenL2) : L2R)) : ℝ → ℂ) =ᵐ[volume] fun w => ∫ u, Mk g w u * F u := by
    filter_upwards [fourier_ae_eq ((z1 : evenL2) : L2R) hz1i] with w hw
    rw [show ((evenPair.F z1 : evenL2) : L2R) = 𝓕 ((z1 : evenL2) : L2R) from rfl, hw,
      fourier_congr_ae hz1 w, Real.fourier_real_eq_integral_exp_smul]
    rw [← integral_MkE_eq hW hy (even_ae y) w, ← integral_bW_Vp hW hy hFm w]
    congr 1; funext v
    unfold bW
    split_ifs <;> simp [smul_eq_mul]
  rw [Qop_apply, ← hz1def]
  filter_upwards [coeFn_evenP (evenPair.F z1), h2] with w e1 e2
  rw [e1, rowF]
  split_ifs
  · exact e2
  · rfl

/-! ### Truncation -/

/-- `1_{[-n,n]} y`. -/
def truncFun (y : evenL2) (n : ℕ) : ℝ → ℂ := (Icc (-(n : ℝ)) n).indicator ((y : L2R) : ℝ → ℂ)

theorem memLp_truncFun (y : evenL2) (n : ℕ) : MemLp (truncFun y n) 2 volume :=
  (Lp.memLp _).indicator measurableSet_Icc

theorem integrable_truncFun (y : evenL2) (n : ℕ) : Integrable (truncFun y n) :=
  (integrable_indicator_iff measurableSet_Icc).mpr
    (((Lp.memLp (y : L2R)).locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc)

theorem truncL_mem (y : evenL2) (n : ℕ) : (memLp_truncFun y n).toLp _ ∈ evenL2 := by
  rw [mem_evenL2]
  apply Lp.ext
  filter_upwards [coeFn_reflect ((memLp_truncFun y n).toLp _),
    ae_eq_comp_neg (memLp_truncFun y n).coeFn_toLp, (memLp_truncFun y n).coeFn_toLp, even_ae y]
    with v h1 h2 h3 h4
  rw [h1, h2, h3]
  unfold truncFun
  by_cases hv : v ∈ Icc (-(n : ℝ)) n
  · have hv' : -v ∈ Icc (-(n : ℝ)) n := ⟨by linarith [hv.2], by linarith [hv.1]⟩
    rw [indicator_of_mem hv, indicator_of_mem hv', h4]
  · have hv' : -v ∉ Icc (-(n : ℝ)) n := fun h => hv ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_notMem hv, indicator_of_notMem hv']

/-- The truncation as an element of `L²(ℝ)_ev`. -/
def truncE (y : evenL2) (n : ℕ) : evenL2 := ⟨(memLp_truncFun y n).toLp _, truncL_mem y n⟩

theorem coeFn_truncE (y : evenL2) (n : ℕ) :
    (((truncE y n : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume] truncFun y n :=
  (memLp_truncFun y n).coeFn_toLp

theorem tendsto_truncE (y : evenL2) : Tendsto (truncE y) atTop (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set F : ℝ → ℂ := ((y : L2R) : ℝ → ℂ)
  have hsq : ∀ n, ‖truncE y n - y‖ ^ 2 = ∫ v, ‖truncFun y n v - F v‖ ^ 2 := by
    intro n
    rw [Submodule.coe_norm, Submodule.coe_sub, norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((truncE y n : evenL2) : L2R) (y : L2R), coeFn_truncE y n] with v h1 h2
    rw [h1, Pi.sub_apply, h2]
  have hlim : Tendsto (fun n : ℕ => ∫ v, ‖truncFun y n v - F v‖ ^ 2) atTop (𝓝 0) := by
    have hFi : Integrable fun v => ‖F v‖ ^ 2 := (Lp.memLp (y : L2R)).integrable_norm_pow two_ne_zero
    rw [show (0 : ℝ) = ∫ _v : ℝ, (0 : ℝ) by simp]
    refine tendsto_integral_of_dominated_convergence (fun v => ‖F v‖ ^ 2)
      (fun n => ((((memLp_truncFun y n).1.sub (Lp.aestronglyMeasurable _)).norm).pow 2)) hFi
      (fun n => Eventually.of_forall fun v => ?_) (Eventually.of_forall fun v => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      unfold truncFun
      by_cases hv : v ∈ Icc (-(n : ℝ)) n
      · rw [indicator_of_mem hv, sub_self, norm_zero, zero_pow two_ne_zero]; positivity
      · rw [indicator_of_notMem hv, zero_sub, norm_neg]
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge |v|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hv : v ∈ Icc (-(n : ℝ)) n := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        exact abs_le.mp (hN.trans this)
      unfold truncFun
      rw [indicator_of_mem hv, sub_self, norm_zero]; norm_num
  have h0 : Tendsto (fun n : ℕ => ‖truncE y n - y‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hsq]; exact hlim
  have := h0.sqrt
  simp only [Real.sqrt_zero] at this
  refine this.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- `∫ M(w,u) (1_{[-n,n]} y)(u) du → ∫ M(w,u) y(u) du`. -/
theorem tendsto_rowF (hW : WeilExplicit.IsWeilTest g) (y : evenL2) (w : ℝ) :
    Tendsto (fun n => rowF g (truncFun y n) w) atTop (𝓝 (rowF g ((y : L2R) : ℝ → ℂ) w)) := by
  unfold rowF
  by_cases hw : 1 < |w|
  · simp only [if_pos hw]
    have hw0 : w ≠ 0 := fun h => by rw [h, abs_zero] at hw; linarith
    set F : ℝ → ℂ := ((y : L2R) : ℝ → ℂ)
    have hM := memLp_Mk' hW hw0
    have hMi : Integrable fun u => ‖Mk g w u‖ ^ 2 :=
      (memLp_two_iff_integrable_sq_norm hM.1).mp hM
    have hFi : Integrable fun v => ‖F v‖ ^ 2 := (Lp.memLp (y : L2R)).integrable_norm_pow two_ne_zero
    refine tendsto_integral_of_dominated_convergence (fun u => ‖Mk g w u‖ ^ 2 + ‖F u‖ ^ 2)
      (fun n => hM.1.mul (memLp_truncFun y n).1) (hMi.add hFi)
      (fun n => Eventually.of_forall fun u => ?_) (Eventually.of_forall fun u => ?_)
    · rw [norm_mul]
      have h1 : ‖truncFun y n u‖ ≤ ‖F u‖ := by
        unfold truncFun
        by_cases hu : u ∈ Icc (-(n : ℝ)) n
        · rw [indicator_of_mem hu]
        · rw [indicator_of_notMem hu, norm_zero]; exact norm_nonneg _
      nlinarith [norm_nonneg (Mk g w u), norm_nonneg (truncFun y n u), norm_nonneg (F u),
        sq_nonneg (‖Mk g w u‖ - ‖F u‖)]
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge |u|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hu : u ∈ Icc (-(n : ℝ)) n := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        exact abs_le.mp (hN.trans this)
      unfold truncFun
      rw [indicator_of_mem hu]
  · simp only [if_neg hw]; exact tendsto_const_nhds

theorem rowF_congr {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) (w : ℝ) : rowF g F w = rowF g G w := by
  unfold rowF
  split_ifs
  · exact integral_congr_ae (by filter_upwards [h] with u hu; rw [hu])
  · rfl

/-- **The row identity on all of `L²(ℝ)_ev`**: `(P F P ϑ(g) y)(w) = 1{|w|>1} ∫ M(w,u) y(u) du` a.e. -/
theorem coeFn_Q (hW : WeilExplicit.IsWeilTest g) (hg : Integrable g) (y : evenL2) :
    (((Qop g hg y : evenL2) : L2R) : ℝ → ℂ) =ᵐ[volume] rowF g ((y : L2R) : ℝ → ℂ) := by
  have hQ : Tendsto (fun n => ((Qop g hg (truncE y n) : evenL2) : L2R)) atTop
      (𝓝 ((Qop g hg y : evenL2) : L2R)) :=
    (continuous_subtype_val.tendsto _).comp ((Qop g hg).continuous.tendsto y |>.comp (tendsto_truncE y))
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hQ
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun n => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hQ
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hall : ∀ᵐ w ∂volume, ∀ n,
      (((Qop g hg (truncE y n) : evenL2) : L2R) : ℝ → ℂ) w = rowF g (truncFun y n) w := by
    rw [ae_all_iff]
    intro n
    have hi : Integrable (((truncE y n : evenL2) : L2R) : ℝ → ℂ) :=
      (integrable_truncFun y n).congr (coeFn_truncE y n).symm
    filter_upwards [coeFn_Q_integrable hW hg (truncE y n) hi] with w hw
    rw [hw, rowF_congr (coeFn_truncE y n) w]
  filter_upwards [hae, hall] with w h1 h2
  have h3 := (tendsto_rowF hW y w).comp hns.tendsto_atTop
  refine tendsto_nhds_unique h1 (h3.congr fun k => ?_)
  simp only [Function.comp_apply]
  exact (h2 (ns k)).symm

end

end ArchS7c
