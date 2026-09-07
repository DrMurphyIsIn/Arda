/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/
import Mathlib

open Complex Filter MeasureTheory Real
open scoped Topology

namespace RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/

/-- Log-derivatives agree wherever the functions agree on a NEIGHBORHOOD. -/
theorem logDeriv_congr_nhds {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[nhds z] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- Log-derivatives agree at any point of an OPEN set on which the functions agree. -/
theorem logDeriv_congr_eqOn_open {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (h : Set.EqOn f₁ f₂ U) :
    logDeriv f₁ z = logDeriv f₂ z :=
  logDeriv_congr_nhds (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h)

/-- **Codiscrete transfer.** -/
theorem logDeriv_congr_of_codiscrete {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z₀ z : ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ U) (hf₂ : AnalyticOnNhd ℂ f₂ U)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U) (hz : z ∈ U)
    (h : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  have hmem : {x | f₁ x = f₂ x} ∪ Uᶜ ∈ 𝓝[≠] z₀ :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h) z₀ hz₀
  have hU_nhds : U ∈ 𝓝[≠] z₀ := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz₀)
  have hev : ∀ᶠ x in 𝓝[≠] z₀, f₁ x = f₂ x := by
    filter_upwards [hmem, hU_nhds] with x hx hxU
    rcases hx with h1 | h2
    · exact h1
    · exact absurd hxU h2
  exact logDeriv_congr_eqOn_open hU hz
    (hf₁.eqOn_of_preconnected_of_frequently_eq hf₂ hUc hz₀ hev.frequently)

/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/

theorem logDeriv_factor {u z : ℂ} (d : ℤ) (_hzu : z - u ≠ 0) :
    logDeriv (fun w : ℂ => (w - u) ^ d) z = (d : ℂ) / (z - u) := by
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
  rw [logDeriv_fun_zpow hdiff d]
  have : logDeriv (fun w : ℂ => w - u) z = 1 / (z - u) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => w - u) z = 1 := by
      simp [deriv_sub_const (f := fun w : ℂ => w) u (x := z)]
    rw [hderiv]
  rw [this]; ring

theorem logDeriv_finset_prod {T : Finset ℂ} (D : ℂ → ℤ) (z : ℂ)
    (hz : ∀ u ∈ T, z - u ≠ 0) :
    logDeriv (fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u)) z
      = ∑ u ∈ T, (D u : ℂ) / (z - u) := by
  have hne : ∀ u ∈ T, ((fun w : ℂ => (w - u) ^ (D u)) z) ≠ 0 :=
    fun u hu => zpow_ne_zero _ (hz u hu)
  have hdiff : ∀ u ∈ T, DifferentiableAt ℂ (fun w : ℂ => (w - u) ^ (D u)) z := by
    intro u hu
    have hbase : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
    exact (differentiableAt_zpow.2 (Or.inl (hz u hu))).comp z hbase
  set F : ℂ → ℂ → ℂ := fun u w => (w - u) ^ (D u) with hF
  have hfun : (fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u)) = fun w : ℂ => ∏ u ∈ T, F u w := rfl
  rw [hfun, logDeriv_prod (s := T) (f := F) (x := z) hne hdiff]
  exact Finset.sum_congr rfl (fun u hu => logDeriv_factor (D u) (hz u hu))

/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/

theorem meromorphicOrderAt_zeta_ne_top :
    ∀ u ∈ ({1}ᶜ : Set ℂ), meromorphicOrderAt riemannZeta u ≠ ⊤ := by
  have hconn : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hMero : MeromorphicOn riemannZeta ({1}ᶜ : Set ℂ) := analyticOn_riemannZeta.meromorphicOn
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hz2 : AnalyticAt ℂ riemannZeta 2 := analyticOn_riemannZeta 2 h2mem
  have hne2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hord2 : meromorphicOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [hz2.meromorphicOrderAt_eq, hz2.analyticOrderAt_eq_zero.mpr hne2]; simp
  intro u hu
  exact hMero.meromorphicOrderAt_ne_top_of_isPreconnected hconn.isPreconnected h2mem hu hord2

/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/

/-- Monodromy jump `log(-x) - log x = pi*i` when `Im x < 0` (principal branch). -/
theorem log_neg_sub_im_neg (x : ℂ) (hx : x.im < 0) :
    Complex.log (-x) - Complex.log x = ↑π * I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]

/-- Monodromy jump `log(-x) - log x = -(pi*i)` when `Im x > 0` (principal branch). -/
theorem log_neg_sub_im_pos (x : ℂ) (hx : 0 < x.im) :
    Complex.log (-x) - Complex.log x = -(↑π * I) := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]

/-- **Generic per-pole winding.**  Winding number ONE about a pole `ρ` strictly interior to the box
    `[sigma0, sigma1] x [T0, T1]`: `Bd((z-ρ)^{-1}) = 2*pi*i`.  Segment/`Complex.log` branch-split
    proof, verbatim structure of `winding_lambda_five_rect_winding` with variable corners. -/
theorem rect_winding_generic
    (sigma0 sigma1 T0 T1 : ℝ) (ρ : ℂ)
    (hre0 : sigma0 < ρ.re) (hre1 : ρ.re < sigma1)
    (him0 : T0 < ρ.im) (him1 : ρ.im < T1) :
    (∫ x in sigma0..sigma1, ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
        - (∫ x in sigma0..sigma1, ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in T0..T1, (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in T0..T1, (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I := by
  have hσ : sigma0 ≤ sigma1 := le_of_lt (lt_trans hre0 hre1)
  have hTle : T0 ≤ T1 := le_of_lt (lt_trans him0 him1)
  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - ρ).im ≠ 0) →
      (∫ x in sigma0..sigma1, ((↑x + c) - ρ)⁻¹)
        = Complex.log ((↑sigma1 + c) - ρ) - Complex.log ((↑sigma0 + c) - ρ) := by
    intro c hc
    have hderiv : ∀ x ∈ Set.uIcc sigma0 sigma1,
        HasDerivAt (fun x : ℝ => Complex.log ((↑x + c) - ρ)) (((↑x + c) - ρ)⁻¹) x := by
      intro x _
      have hpath : HasDerivAt (fun x : ℝ => ((↑x : ℂ) + c) - ρ) 1 x := by
        have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
        exact (h1.add_const c).sub_const ρ
      have hslit : ((↑x + c) - ρ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; exact Or.inr (hc x)
      have hd := hpath.clog_real hslit
      rwa [one_div] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine Continuous.inv₀ (by fun_prop) (fun x => ?_)
    rw [sub_ne_zero]; intro h
    exact hc x (by rw [h]; simp)
  have vert : ∀ c : ℂ, (∀ y : ℝ, ((c + ↑y * I) - ρ) ∈ Complex.slitPlane) →
      I • (∫ y in T0..T1, ((c + ↑y * I) - ρ)⁻¹)
        = Complex.log ((c + ↑T1 * I) - ρ) - Complex.log ((c + ↑T0 * I) - ρ) := by
    intro c hslit
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc T0 T1,
        HasDerivAt (fun y : ℝ => Complex.log ((c + ↑y * I) - ρ)) (I • ((c + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => (c + (↑y : ℂ) * I) - ρ) I y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add c).sub_const ρ
      have hd := hpath.clog_real (hslit y)
      rwa [div_eq_mul_inv, ← smul_eq_mul] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    have := hslit y
    rw [Complex.mem_slitPlane_iff] at this
    intro h; rw [h] at this; simp at this
  have hbot := horiz ((T0 : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have htop := horiz ((T1 : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have hright := vert ((sigma1 : ℝ) : ℂ) (by
    intro y; rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith)
  have hleftJ : I • (∫ y in T0..T1, (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = Complex.log (ρ - ((sigma0 : ℂ) + ↑T1 * I)) - Complex.log (ρ - ((sigma0 : ℂ) + ↑T0 * I)) := by
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc T0 T1,
        HasDerivAt (fun y : ℝ => Complex.log (ρ - ((sigma0 : ℂ) + ↑y * I)))
          (I • (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => ρ - ((sigma0 : ℂ) + (↑y : ℂ) * I)) (-I) y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add ((sigma0 : ℂ))).const_sub ρ
      have hslit : (ρ - ((sigma0 : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith
      have hd := hpath.clog_real hslit
      have hval : (-I) / (ρ - ((sigma0 : ℂ) + ↑y * I)) = I • (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹ := by
        rw [smul_eq_mul, div_eq_mul_inv,
          show ρ - ((sigma0 : ℂ) + ↑y * I) = -(((sigma0 : ℂ) + ↑y * I) - ρ) from by ring, inv_neg]
        ring
      rwa [hval] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    rw [sub_ne_zero]; intro h
    have : (((sigma0 : ℂ) + ↑y * I)).re = ρ.re := by rw [h]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this; linarith
  rw [hbot, htop, hright, hleftJ,
    show ρ - ((sigma0 : ℂ) + ↑T1 * I) = -((↑sigma0 + (T1 : ℂ) * I) - ρ) from by ring,
    show ρ - ((sigma0 : ℂ) + ↑T0 * I) = -((↑sigma0 + (T0 : ℂ) * I) - ρ) from by ring]
  have hAim : ((↑sigma0 + (T0 : ℂ) * I) - ρ).im < 0 := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  have hDim : 0 < ((↑sigma0 + (T1 : ℂ) * I) - ρ).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  linear_combination log_neg_sub_im_neg ((↑sigma0 + (T0 : ℂ) * I) - ρ) hAim
    - log_neg_sub_im_pos ((↑sigma0 + (T1 : ℂ) * I) - ρ) hDim

/-- **Generic residue-sum.**  Four-segment boundary integral of a Herglotz sum equals
    `2*pi*I*∑ m`, via `rect_winding_generic` per pole (strict interior) and Finset linearity. -/
theorem box_residue_sum_generic
    (sigma0 sigma1 T0 T1 : ℝ) {s : Finset ℂ} (m : ℂ → ℤ)
    (hin : ∀ ρ ∈ s, sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hb : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1)
    (ht : ∀ ρ ∈ s, IntervalIntegrable
      (fun x : ℝ => ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1)
    (hr : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1)
    (hl : ∀ ρ ∈ s, IntervalIntegrable
      (fun y : ℝ => (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) :
    (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
        - (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by
  rw [intervalIntegral.integral_finsetSum (fun ρ hρ => (hb ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (ht ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hr ρ hρ).const_mul (m ρ : ℂ)),
      intervalIntegral.integral_finsetSum (fun ρ hρ => (hl ρ hρ).const_mul (m ρ : ℂ))]
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨hre0, hre1, him0, him1⟩ := hin ρ hρ
  have hw := rect_winding_generic sigma0 sigma1 T0 T1 ρ hre0 hre1 him0 him1
  simp only [smul_eq_mul] at hw
  linear_combination (m ρ : ℂ) * hw

/-- **Generic analytic E-arg-principle.**  Four-segment boundary integral of a function holomorphic
    on the closed box vanishes.  Box instance of Mathlib
    `integral_boundary_rect_eq_zero_of_differentiableOn`, with the corner geometry as ordering
    hypotheses. -/
theorem rect_arg_principle_generic
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1) (f : ℂ → ℂ)
    (H : DifferentiableOn ℂ f (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1)) :
    (∫ x : ℝ in sigma0..sigma1, f (↑x + (T0 : ℂ) * I))
        - (∫ x : ℝ in sigma0..sigma1, f (↑x + (T1 : ℂ) * I))
        + I • (∫ y : ℝ in T0..T1, f ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y : ℝ in T0..T1, f ((sigma0 : ℂ) + ↑y * I)) = 0 := by
  have key := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((sigma0 : ℂ) + (T0 : ℂ) * I) ((sigma1 : ℂ) + (T1 : ℂ) * I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at key
  norm_num at key ⊢
  -- `key`'s hypothesis is stated over `[[sigma0, sigma1]] ×ℂ [[T0, T1]]`; convert to `Icc`.
  rw [Set.uIcc_of_le hsig, Set.uIcc_of_le hT] at key
  exact key H

/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/

/-- The support of `riemannZeta`'s divisor over `ball c R` is finite whenever `1 ∉ ball c R`:
    it sits inside the compact intersection `closedBall c R ∩ riemannZetaZeros`. -/
theorem divisor_ball_support_finite_of_one_notMem
    (c : ℂ) (R : ℝ) (hs1 : (1 : ℂ) ∉ Metric.ball c R) :
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).support.Finite := by
  set U := Metric.ball c R with hUdef
  have hUsub : U ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hζU : AnalyticOnNhd ℂ riemannZeta U := analyticOn_riemannZeta.mono hUsub
  have hZfin : ((Metric.closedBall c R) ∩ riemannZetaZeros).Finite :=
    (isCompact_closedBall c R).inter_riemannZetaZeros_finite
  apply hZfin.subset
  intro u hu
  rw [Function.mem_support] at hu
  have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
    (by rw [Function.mem_support]; exact hu)
  refine ⟨Metric.ball_subset_closedBall huU, ?_⟩
  rw [mem_riemannZetaZeros]
  by_contra hne
  apply hu
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU huU,
    (hζU u huU).analyticOrderAt_eq_zero.mpr hne]; simp

/-- The actual divisor-support Finset of `riemannZeta` over `ball c R` (needs `1 ∉ ball c R`). -/
noncomputable def zeroFinset (c : ℂ) (R : ℝ) (hs1 : (1 : ℂ) ∉ Metric.ball c R) : Finset ℂ :=
  (divisor_ball_support_finite_of_one_notMem c R hs1).toFinset

theorem mem_zeroFinset {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R) {ρ : ℂ} :
    ρ ∈ zeroFinset c R hs1 ↔
      ρ ∈ (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).support := by
  rw [zeroFinset, Set.Finite.mem_toFinset]

theorem zeta_blaschke_split_ball
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ)
    (hRpos : 0 < R)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R) :
    ∃ (E : ℂ → ℂ),
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ∧
      (∀ ρ ∈ zeroFinset c R hs1,
        (1 : ℤ) ≤ (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) ∧
      (∀ ρ ∈ Metric.ball c R, riemannZeta ρ = 0 → ρ ∈ zeroFinset c R hs1) ∧
      (∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ zeroFinset c R hs1,
          ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) / (z - ρ)) + E z) := by
  set U := Metric.ball c R with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsPreconnected U := (convex_ball c R).isPreconnected
  have hUsub : U ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hbox_sub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact hbox_ball z hz.1 hz.2
  have hζU : AnalyticOnNhd ℂ riemannZeta U := analyticOn_riemannZeta.mono hUsub
  have hMeroU : MeromorphicOn riemannZeta U := hζU.meromorphicOn
  -- Divisor support is finite: it sits inside `closedBall c R ∩ riemannZetaZeros`.
  set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) u with hDdef
  have hDnn : ∀ x, 0 ≤ D x := fun x => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζU x
  -- support point ⇒ zero of zeta.
  have hsupp_zero : ∀ u, u ∈ Function.support D → riemannZeta u = 0 := by
    intro u hu
    rw [Function.mem_support] at hu
    have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
      (by rw [Function.mem_support]; exact hu)
    by_contra hne
    apply hu
    simp only [hDdef]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU huU,
      (hζU u huU).analyticOrderAt_eq_zero.mpr hne]; simp
  have hZfin : ((Metric.closedBall c R) ∩ riemannZetaZeros).Finite :=
    (isCompact_closedBall c R).inter_riemannZetaZeros_finite
  have hDfin : (Function.support D).Finite := by
    apply hZfin.subset
    intro u hu
    have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
      (by rw [Function.mem_support]; rw [Function.mem_support] at hu; exact hu)
    exact ⟨Metric.ball_subset_closedBall huU, hsupp_zero u hu⟩
  have h₃f : (MeromorphicOn.divisor riemannZeta U).support.Finite := hDfin
  have h₂f : ∀ u : U, meromorphicOrderAt riemannZeta u ≠ ⊤ :=
    fun u => meromorphicOrderAt_zeta_ne_top u.1 (hUsub u.2)
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hMeroU.extract_zeros_poles h₂f h₃f
  set T : Finset ℂ := zeroFinset c R hs1 with hTdef
  -- `T = h₃f.toFinset`: both are `Set.Finite.toFinset` of the same support set.
  have hTmem : ∀ u, u ∈ T ↔ u ∈ (MeromorphicOn.divisor riemannZeta U).support := by
    intro u; rw [hTdef]; exact mem_zeroFinset hs1
  have hTsetEq : (T : Set ℂ) = Function.support D := by
    ext u; rw [Finset.mem_coe, hTmem u]
  -- Factorized-rational product reduced to a Finset product (verbatim structure from merged).
  have hPf_finset : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta U u))
      = fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) := by
    rw [Function.FactorizedRational.finprod_eq_fun (d := D) hDfin]
    ext w
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]
    · intro u hu
      rw [Finset.mem_coe, hTmem u]
      by_contra hc
      rw [Function.mem_support, not_not] at hc
      rw [Function.mem_mulSupport] at hu
      exact hu (by rw [show D u = (MeromorphicOn.divisor riemannZeta U) u from rfl, hc, zpow_zero])
  set Pf : ℂ → ℂ := fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) with hPfdef
  have hPf_an : AnalyticOnNhd ℂ Pf U := by
    rw [← hPf_finset]; intro x _; exact Function.FactorizedRational.analyticAt (hDnn x)
  set P : ℂ → ℂ := fun z => Pf z * g z with hPdef
  have hP_an : AnalyticOnNhd ℂ P U := fun x hx => (hPf_an x hx).mul (hg_an x hx)
  have hg_eqP : riemannZeta =ᶠ[Filter.codiscreteWithin U] P := by
    have hPeq : ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta U u)) • g) = P := by
      rw [hPf_finset]; ext w; simp [hPdef, hPfdef]
    rw [← hPeq]; exact hg_eq
  have hT_zero : ∀ u ∈ T, riemannZeta u = 0 := by
    intro u hu
    rw [hTmem u, Function.mem_support] at hu
    exact hsupp_zero u (by rw [Function.mem_support]; exact hu)
  -- Provide the existential witness `E := logDeriv g`.
  refine ⟨logDeriv g, ?_, ?_, ?_, ?_⟩
  · -- E holomorphic on the box (subset of U).
    have hE_an : AnalyticOnNhd ℂ (logDeriv g) U := by
      intro x hx
      have : logDeriv g = fun z => deriv g z / g z := by
        ext z; rw [logDeriv_apply]
      rw [this]
      exact (hg_an x hx).deriv.div (hg_an x hx) (hg_ne ⟨x, hx⟩)
    exact (hE_an.mono hbox_sub).differentiableOn
  · -- multiplicity `d ρ ≥ 1` at every support point.
    intro ρ hρ
    rw [hTmem ρ, Function.mem_support] at hρ
    have hρU : ρ ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
      (by rw [Function.mem_support]; exact hρ)
    have hρzero : riemannZeta ρ = 0 := hsupp_zero ρ (by rw [Function.mem_support]; exact hρ)
    have hAtρ : AnalyticAt ℂ riemannZeta ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt riemannZeta ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro hcontra
      exact meromorphicOrderAt_zeta_ne_top ρ (hUsub hρU)
        (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    have hDeq : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
        = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      have hda : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
          = ((analyticOrderAt riemannZeta ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda, ← Nat.cast_analyticOrderNatAt hfin]; rfl
    have hnat_ne : analyticOrderNatAt riemannZeta ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    show (1 : ℤ) ≤ (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
    rw [hDeq]
    have : 1 ≤ analyticOrderNatAt riemannZeta ρ := Nat.one_le_iff_ne_zero.mpr hnat_ne
    exact_mod_cast this
  · -- every zeta zero in U lies in the support.
    intro ρ hρU hρzero
    rw [hTmem ρ, Function.mem_support]
    have hAtρ : AnalyticAt ℂ riemannZeta ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt riemannZeta ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro hcontra
      exact meromorphicOrderAt_zeta_ne_top ρ (hUsub hρU)
        (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    have hDeq : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
        = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      have hda : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
          = ((analyticOrderAt riemannZeta ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda, ← Nat.cast_analyticOrderNatAt hfin]; rfl
    have hnat_ne : analyticOrderNatAt riemannZeta ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    rw [hDeq]
    exact_mod_cast hnat_ne
  · -- the split at each z ∈ U off the zeros.
    intro z hz hznz
    have hzroots : ∀ u ∈ T, z - u ≠ 0 := by
      intro u hu hcontra
      rw [sub_eq_zero] at hcontra
      exact hznz (by rw [hcontra]; exact hT_zero u hu)
    have hPfz : Pf z ≠ 0 := by
      rw [hPfdef]
      exact Finset.prod_ne_zero_iff.mpr (fun u hu => zpow_ne_zero _ (hzroots u hu))
    have hgz : g z ≠ 0 := hg_ne ⟨z, hz⟩
    have hPf_diff : DifferentiableAt ℂ Pf z := (hPf_an z hz).differentiableAt
    have hg_diff : DifferentiableAt ℂ g z := (hg_an z hz).differentiableAt
    have htrans : logDeriv riemannZeta z = logDeriv P z :=
      logDeriv_congr_of_codiscrete hζU hP_an hUopen hUconn hz hz hg_eqP
    -- The goal sum ranges over `zeroFinset c R hs1 = T` with divisor `= D`.
    rw [htrans, hPdef, logDeriv_mul z hPfz hgz hPf_diff hg_diff, hPfdef]
    rw [logDeriv_finset_prod D z hzroots]

/-! ## Part F: the parameterized capstone. -/

/-- **Parameterized box argument principle for `riemannZeta` over a variable ball `(c, R)`.**

    For any box `[sigma0, sigma1] x [T0, T1]` equipped with a valid Blaschke ball `(c, R)` (i.e.
    `0 < R`, the box lies inside `ball c R`, and `1 ∉ ball c R`), the ACTUAL divisor of
    `riemannZeta` over `ball c R` is nonneg (multiplicity `≥ 1` on its support `s`), captures every
    zero of `riemannZeta` inside the box, and its total equals the Arb winding integer `N`, where
    `N` is DERIVED from the boundary-winding hypothesis `hwind` via the argument principle (E-term
    vanishes, residues sum to `2*pi*I*∑ d`).

    Geometry enters ONLY as `hRpos`/`hbox_ball`/`hs1` (and the box-ordering, forced by strict
    interiority in the winding).  The split and E-holomorphicity are kernel-derived by
    `zeta_blaschke_split_ball` -- not assumed.  The residual inputs are the routine Arb boundary
    facts (edge non-vanishing, strict interiority of the zeros, integrability) and the winding value.

    conjecture1_proved = False. -/
theorem zeta_count_eq_winding_generic
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ)
    (hRpos : 0 < R)
    (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    -- H4: the boundary winding value of `logDeriv riemannZeta` (Arb / Task 9).
    (hwind : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
      = 2 * π * I * (N : ℂ))
    -- Routine Arb boundary hypotheses, stated about the ACTUAL divisor support `s`/divisor `d`.
    (hArb : ∀ (E : ℂ → ℂ),
      let s := zeroFinset c R hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) →
      (∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      -- edge non-vanishing (Arb enclosures)
      (∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0) ∧
      -- strict interiority of every divisor-support pole
      (∀ ρ ∈ s, sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) ∧
      -- residue-inverse integrability
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      -- residue-sum / E integrability
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (T0 : ℂ) * I)) volume sigma0 sigma1) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (T1 : ℂ) * I)) volume sigma0 sigma1) ∧
      (IntervalIntegrable (fun y : ℝ => E ((sigma1 : ℂ) + ↑y * I)) volume T0 T1) ∧
      (IntervalIntegrable (fun y : ℝ => E ((sigma0 : ℂ) + ↑y * I)) volume T0 T1)) :
    ∃ (s : Finset ℂ) (d : ℂ → ℤ),
      (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧
      (∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
        riemannZeta ρ = 0 → ρ ∈ s) ∧
      (∑ ρ ∈ s, d ρ) = N := by
  -- Kernel-derived split, E-holomorphy, divisor nonneg, box-zero capture.
  obtain ⟨E, hEholo, hd1, hzero_in, hker⟩ :=
    zeta_blaschke_split_ball sigma0 sigma1 T0 T1 c R hRpos hbox_ball hs1
  set s := zeroFinset c R hs1 with hs
  set d := (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) with hd
  refine ⟨s, d, hd1, ?_, ?_⟩
  · -- box zero ⇒ in s: the zero lies in ball c R (hbox_ball), hence in the divisor support.
    intro ρ hre him hρzero
    exact hzero_in ρ (hbox_ball ρ hre him) hρzero
  · -- ∑ d = N via the argument principle.
    obtain ⟨hnz_b, hnz_t, hnz_r, hnz_l, hin, hb, ht, hr, hl,
            hsb, hst, hsr, hsl, heb, het, her, hel⟩ := hArb E hEholo hker
    -- Edge points lie in `ball c R` (box ⊆ ball, uIcc = Icc since corners are ordered).
    have huIccσ : Set.uIcc sigma0 sigma1 = Set.Icc sigma0 sigma1 := Set.uIcc_of_le hsig
    have huIccT : Set.uIcc T0 T1 = Set.Icc T0 T1 := Set.uIcc_of_le hT
    -- re/im of an edge point.
    have hre_pt : ∀ (a b : ℝ), ((a : ℂ) + (b : ℂ) * I).re = a := by
      intro a b
      simp
    have him_pt : ∀ (a b : ℝ), ((a : ℂ) + (b : ℂ) * I).im = b := by
      intro a b
      simp
    have bmem : ∀ x ∈ Set.uIcc sigma0 sigma1, (↑x + (T0 : ℂ) * I) ∈ Metric.ball c R := by
      intro x hx; rw [huIccσ, Set.mem_Icc] at hx
      exact hbox_ball _ (by rw [hre_pt]; exact hx) (by rw [him_pt]; exact ⟨le_refl _, hT⟩)
    have tmem : ∀ x ∈ Set.uIcc sigma0 sigma1, (↑x + (T1 : ℂ) * I) ∈ Metric.ball c R := by
      intro x hx; rw [huIccσ, Set.mem_Icc] at hx
      exact hbox_ball _ (by rw [hre_pt]; exact hx) (by rw [him_pt]; exact ⟨hT, le_refl _⟩)
    have rmem : ∀ y ∈ Set.uIcc T0 T1, ((sigma1 : ℂ) + ↑y * I) ∈ Metric.ball c R := by
      intro y hy; rw [huIccT, Set.mem_Icc] at hy
      exact hbox_ball _ (by rw [hre_pt]; exact ⟨hsig, le_refl _⟩) (by rw [him_pt]; exact hy)
    have lmem : ∀ y ∈ Set.uIcc T0 T1, ((sigma0 : ℂ) + ↑y * I) ∈ Metric.ball c R := by
      intro y hy; rw [huIccT, Set.mem_Icc] at hy
      exact hbox_ball _ (by rw [hre_pt]; exact ⟨le_refl _, hsig⟩) (by rw [him_pt]; exact hy)
    -- Per-edge split identities in residue form, from the kernel split + boundary non-vanishing.
    have hsp_b : ∀ x ∈ Set.uIcc sigma0 sigma1,
        logDeriv riemannZeta (↑x + (T0 : ℂ) * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) + E (↑x + (T0 : ℂ) * I) := by
      intro x hx
      rw [hker _ (bmem x hx) (hnz_b x hx)]; simp only [div_eq_mul_inv]
    have hsp_t : ∀ x ∈ Set.uIcc sigma0 sigma1,
        logDeriv riemannZeta (↑x + (T1 : ℂ) * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) + E (↑x + (T1 : ℂ) * I) := by
      intro x hx
      rw [hker _ (tmem x hx) (hnz_t x hx)]; simp only [div_eq_mul_inv]
    have hsp_r : ∀ y ∈ Set.uIcc T0 T1,
        logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) + E ((sigma1 : ℂ) + ↑y * I) := by
      intro y hy
      rw [hker _ (rmem y hy) (hnz_r y hy)]; simp only [div_eq_mul_inv]
    have hsp_l : ∀ y ∈ Set.uIcc T0 T1,
        logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) + E ((sigma0 : ℂ) + ↑y * I) := by
      intro y hy
      rw [hker _ (lmem y hy) (hnz_l y hy)]; simp only [div_eq_mul_inv]
    -- Rewrite each boundary integral via the per-edge split.
    have eb : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        = (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
          + (∫ x in sigma0..sigma1, E (↑x + (T0 : ℂ) * I)) := by
      rw [← intervalIntegral.integral_add hsb heb]
      exact intervalIntegral.integral_congr (fun x hx => hsp_b x hx)
    have et : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        = (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
          + (∫ x in sigma0..sigma1, E (↑x + (T1 : ℂ) * I)) := by
      rw [← intervalIntegral.integral_add hst het]
      exact intervalIntegral.integral_congr (fun x hx => hsp_t x hx)
    have er : (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
        = (∫ y in T0..T1, ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
          + (∫ y in T0..T1, E ((sigma1 : ℂ) + ↑y * I)) := by
      rw [← intervalIntegral.integral_add hsr her]
      exact intervalIntegral.integral_congr (fun y hy => hsp_r y hy)
    have el : (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
        = (∫ y in T0..T1, ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
          + (∫ y in T0..T1, E ((sigma0 : ℂ) + ↑y * I)) := by
      rw [← intervalIntegral.integral_add hsl hel]
      exact intervalIntegral.integral_congr (fun y hy => hsp_l y hy)
    -- Bd(E) = 0 and Bd(residues) = 2*pi*I*∑ d.
    have hE0 := rect_arg_principle_generic sigma0 sigma1 T0 T1 hsig hT E hEholo
    have hRes := box_residue_sum_generic sigma0 sigma1 T0 T1 d hin hb ht hr hl
    rw [eb, et, er, el, smul_add, smul_add] at hwind
    have key : 2 * π * I * (∑ ρ ∈ s, (d ρ : ℂ)) = 2 * π * I * (N : ℂ) := by
      rw [← hRes]
      linear_combination hwind - hE0
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hsumC : (∑ ρ ∈ s, (d ρ : ℂ)) = (N : ℂ) := mul_left_cancel₀ h2pi key
    -- Cast back to ℤ: ∑ d ρ = N.
    have : ((∑ ρ ∈ s, d ρ : ℤ) : ℂ) = ((N : ℤ) : ℂ) := by push_cast; push_cast at hsumC; exact hsumC
    exact_mod_cast this

end RHInBoxAnalytic
