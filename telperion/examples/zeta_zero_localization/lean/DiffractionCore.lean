/-  DIFFRACTION CORE (Dyson/quasicrystal axis, QC2 brick 1): the WEIGHTED rectangle pole formula.

    The T-ladder counts zeros (`rect_winding_generic`: `Bd((·-ρ)⁻¹) = 2πi`, the `g ≡ 1` case).
    The Dyson/Weil axis needs WEIGHTED sums over zeros — `Σ_ρ g(ρ)` for analytic test weights —
    because the explicit formula IS the diffraction identity: weighted zero-sums on one side,
    Bragg peaks at `k·log p` (prime sums) on the other.  This brick proves the single-pole
    mechanism over a rectangle:

      `Bd(g·(·-ρ)⁻¹) = 2πi·g(ρ)`   (g holomorphic near the closed box, ρ strictly interior).

    Proof: the removable-singularity split `g(z)·(z-ρ)⁻¹ = dslope g ρ z + g(ρ)·(z-ρ)⁻¹` (off ρ);
    `dslope g ρ` is holomorphic ACROSS ρ (Mathlib `has_fpower_series_dslope_fslope`), so its
    boundary integral vanishes by the generic rectangle Goursat (`rect_arg_principle_generic`);
    the remainder is `g(ρ)` times the counting winding (`rect_winding_generic`).

    Downstream (QC ladder): QC2 brick 2 = finite-sum version over a zero Finset (mirrors
    `box_residue_sum_generic`); QC3 = the finite-height Guinand–Weil identity, pushing the
    right edge to `Re > 1` where Mathlib's `LSeries_vonMangoldt_eq` (`L Λ = -ζ'/ζ`) turns the
    contour into PRIME SUMS — the Bragg peaks, kernel-side.  The Archimedean term is already
    built (`ZeroFreeBridge.logDeriv_gammaR`, the θ-bridge).

    conjecture1_proved = False. -/
import Mathlib
import RHInBoxAnalytic
import ZetaZeroConfinement
import DlvpTheta
import LambdaLineReal

open Complex MeasureTheory Real
open scoped Topology

namespace DiffractionCore

/-- `dslope` of a function holomorphic on an open set is holomorphic there — INCLUDING at the
    base point (removable singularity via the shifted power series). -/
theorem differentiableOn_dslope_of_isOpen {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} {ρ : ℂ}
    (hρ : ρ ∈ U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (dslope g ρ) U := by
  intro z hz
  by_cases hzρ : z = ρ
  · subst hzρ
    obtain ⟨p, hp⟩ := (hg.analyticOnNhd hU) z hz
    exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt.differentiableWithinAt
  · exact ((differentiableAt_dslope_of_ne hzρ).mpr
      (hg.differentiableAt (hU.mem_nhds hz))).differentiableWithinAt

/-- **The weighted per-pole rectangle formula** (QC2 core): for `g` holomorphic on an open set
    containing the closed box and `ρ` strictly interior,
    `Bd(g·(·-ρ)⁻¹) = 2πi·g(ρ)` — the single-Bragg-peak mechanism of the diffraction axis. -/
theorem rect_weighted_pole_generic
    (sigma0 sigma1 T0 T1 : ℝ) (ρ : ℂ) {U : Set ℂ} (g : ℂ → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hsub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U)
    (hre0 : sigma0 < ρ.re) (hre1 : ρ.re < sigma1)
    (him0 : T0 < ρ.im) (him1 : ρ.im < T1) :
    (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
        - (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I * g ρ := by
  have hσ : sigma0 ≤ sigma1 := le_of_lt (lt_trans hre0 hre1)
  have hT : T0 ≤ T1 := le_of_lt (lt_trans him0 him1)
  have hρrect : ρ ∈ (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    rw [Complex.mem_reProdIm]
    exact ⟨⟨le_of_lt hre0, le_of_lt hre1⟩, ⟨le_of_lt him0, le_of_lt him1⟩⟩
  have hDU : DifferentiableOn ℂ (dslope g ρ) U :=
    differentiableOn_dslope_of_isOpen hU (hsub hρrect) hg
  have hDrect : DifferentiableOn ℂ (dslope g ρ)
      (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := hDU.mono hsub
  have hDcont : ContinuousOn (dslope g ρ)
      (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := hDrect.continuousOn
  -- Path membership: the four boundary segments lie in the closed box.
  have hmem_h : ∀ (c : ℝ), c ∈ Set.Icc T0 T1 → Set.MapsTo (fun t : ℝ => ((t : ℂ) + (c : ℂ) * I))
      (Set.uIcc sigma0 sigma1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro c hc t ht
    rw [Set.uIcc_of_le hσ] at ht
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using ht
    · simpa using hc
  have hmem_v : ∀ (c : ℝ), c ∈ Set.Icc sigma0 sigma1 → Set.MapsTo (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I))
      (Set.uIcc T0 T1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro c hc t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hc
    · simpa using ht
  -- Segment nonvanishing: boundary points differ from the strictly-interior ρ.
  have hne_h : ∀ (c : ℝ), c ≠ ρ.im → ∀ t : ℝ, ((t : ℂ) + (c : ℂ) * I) ≠ ρ := by
    intro c hc t h
    apply hc
    have := congrArg Complex.im h
    simpa using this
  have hne_v : ∀ (c : ℝ), c ≠ ρ.re → ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * I) ≠ ρ := by
    intro c hc t h
    apply hc
    have := congrArg Complex.re h
    simpa using this
  -- Integrability: dslope along each segment (continuity), inverse along each segment.
  have hDseg_h : ∀ (c : ℝ), c ∈ Set.Icc T0 T1 → IntervalIntegrable
      (fun t : ℝ => dslope g ρ ((t : ℂ) + (c : ℂ) * I)) volume sigma0 sigma1 := by
    intro c hc
    refine ContinuousOn.intervalIntegrable ?_
    exact hDcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h c hc)
  have hDseg_v : ∀ (c : ℝ), c ∈ Set.Icc sigma0 sigma1 → IntervalIntegrable
      (fun t : ℝ => dslope g ρ ((c : ℂ) + (t : ℂ) * I)) volume T0 T1 := by
    intro c hc
    refine ContinuousOn.intervalIntegrable ?_
    exact hDcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v c hc)
  have hVseg_h : ∀ (c : ℝ), c ≠ ρ.im → IntervalIntegrable
      (fun t : ℝ => (((t : ℂ) + (c : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1 := by
    intro c hc
    apply Continuous.intervalIntegrable
    exact Continuous.inv₀ (by fun_prop) (fun t => sub_ne_zero.mpr (hne_h c hc t))
  have hVseg_v : ∀ (c : ℝ), c ≠ ρ.re → IntervalIntegrable
      (fun t : ℝ => ((((c : ℂ)) + (t : ℂ) * I) - ρ)⁻¹) volume T0 T1 := by
    intro c hc
    apply Continuous.intervalIntegrable
    exact Continuous.inv₀ (by fun_prop) (fun t => sub_ne_zero.mpr (hne_v c hc t))
  -- The removable-singularity split, per segment.
  have hsplit : ∀ z : ℂ, z ≠ ρ →
      g z * (z - ρ)⁻¹ = dslope g ρ z + g ρ * (z - ρ)⁻¹ := by
    intro z hz
    rw [dslope_of_ne g hz, slope_def_field, div_eq_mul_inv]
    ring
  have hseg_h : ∀ (c : ℝ), c ∈ Set.Icc T0 T1 → c ≠ ρ.im →
      (∫ t in sigma0..sigma1, g ((t : ℂ) + (c : ℂ) * I) * (((t : ℂ) + (c : ℂ) * I) - ρ)⁻¹)
        = (∫ t in sigma0..sigma1, dslope g ρ ((t : ℂ) + (c : ℂ) * I))
          + g ρ * (∫ t in sigma0..sigma1, (((t : ℂ) + (c : ℂ) * I) - ρ)⁻¹) := by
    intro c hcmem hcne
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hDseg_h c hcmem) ((hVseg_h c hcne).const_mul (g ρ))]
    apply intervalIntegral.integral_congr
    intro t _
    exact hsplit _ (hne_h c hcne t)
  have hseg_v : ∀ (c : ℝ), c ∈ Set.Icc sigma0 sigma1 → c ≠ ρ.re →
      (∫ t in T0..T1, g ((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) - ρ)⁻¹)
        = (∫ t in T0..T1, dslope g ρ ((c : ℂ) + (t : ℂ) * I))
          + g ρ * (∫ t in T0..T1, ((((c : ℂ)) + (t : ℂ) * I) - ρ)⁻¹) := by
    intro c hcmem hcne
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hDseg_v c hcmem) ((hVseg_v c hcne).const_mul (g ρ))]
    apply intervalIntegral.integral_congr
    intro t _
    exact hsplit _ (hne_v c hcne t)
  -- Goursat for the dslope part, counting winding for the remainder.
  have hG := RHInBoxAnalytic.rect_arg_principle_generic sigma0 sigma1 T0 T1 hσ hT
    (dslope g ρ) hDrect
  have hW := RHInBoxAnalytic.rect_winding_generic sigma0 sigma1 T0 T1 ρ hre0 hre1 him0 him1
  rw [hseg_h T0 ⟨le_refl T0, hT⟩ (ne_of_lt him0),
    hseg_h T1 ⟨hT, le_refl T1⟩ (ne_of_gt him1),
    hseg_v sigma1 ⟨hσ, le_refl sigma1⟩ (ne_of_gt hre1),
    hseg_v sigma0 ⟨le_refl sigma0, hσ⟩ (ne_of_lt hre0)]
  simp only [smul_eq_mul] at hG hW ⊢
  linear_combination hG + g ρ * hW

/-- **The weighted residue sum** (QC2 brick 2): for a finite pole set strictly interior to the box
    and `g` holomorphic near the closed box,
    `Bd(Σ_ρ m(ρ)·g·(·-ρ)⁻¹) = 2πi·Σ_ρ m(ρ)·g(ρ)` — the finite diffraction pattern.  This is the
    zero-side shape the finite-height Guinand–Weil identity consumes (`m` the zeta divisor, `g`
    the test weight; the Blaschke `E`-part contributes `0` by Goursat since `g·E` is holomorphic). -/
theorem rect_weighted_residue_sum_generic
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    {s : Finset ℂ} (m : ℂ → ℤ) {U : Set ℂ} (g : ℂ → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hsub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U)
    (hin : ∀ ρ ∈ s, sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹))
      - (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹))
      + I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹))
      - I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹))
    = 2 * ↑π * I * ∑ ρ ∈ s, (m ρ : ℂ) * g ρ := by
  have hgcont : ContinuousOn g (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hg.mono hsub).continuousOn
  have hmem_h : ∀ (c : ℝ), c ∈ Set.Icc T0 T1 →
      Set.MapsTo (fun t : ℝ => ((t : ℂ) + (c : ℂ) * I))
        (Set.uIcc sigma0 sigma1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro c hc t ht
    rw [Set.uIcc_of_le hsig] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ht, by simpa using hc⟩
  have hmem_v : ∀ (c : ℝ), c ∈ Set.Icc sigma0 sigma1 →
      Set.MapsTo (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I))
        (Set.uIcc T0 T1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro c hc t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using hc, by simpa using ht⟩
  -- Edge-specific integrability of each summand (pole avoidance from strict interiority).
  have hb : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => (m ρ : ℂ)
      * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)) volume sigma0 sigma1 := by
    intro ρ hρ
    obtain ⟨_, _, h3, _⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h T0 ⟨le_refl _, hT⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at him
    linarith [h3, him]
  have ht : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => (m ρ : ℂ)
      * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)) volume sigma0 sigma1 := by
    intro ρ hρ
    obtain ⟨_, _, _, h4⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h T1 ⟨hT, le_refl _⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at him
    linarith [h4, him]
  have hr : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (m ρ : ℂ)
      * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)) volume T0 T1 := by
    intro ρ hρ
    obtain ⟨_, h2, _, _⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v sigma1 ⟨hsig, le_refl _⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at hre
    linarith [h2, hre]
  have hl : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (m ρ : ℂ)
      * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)) volume T0 T1 := by
    intro ρ hρ
    obtain ⟨h1, _, _, _⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v sigma0 ⟨le_refl _, hsig⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at hre
    linarith [h1, hre]
  rw [intervalIntegral.integral_finsetSum (fun ρ hρ => hb ρ hρ),
    intervalIntegral.integral_finsetSum (fun ρ hρ => ht ρ hρ),
    intervalIntegral.integral_finsetSum (fun ρ hρ => hr ρ hρ),
    intervalIntegral.integral_finsetSum (fun ρ hρ => hl ρ hρ)]
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨h1, h2, h3, h4⟩ := hin ρ hρ
  have hW := rect_weighted_pole_generic sigma0 sigma1 T0 T1 ρ g hU hg hsub h1 h2 h3 h4
  simp only [smul_eq_mul] at hW
  linear_combination (m ρ : ℂ) * hW

/-- **The weighted zeta boundary integral — the finite-height diffraction identity's zero side**
    (QC3 brick 3).  For a box inside a pole-free Blaschke ball, a holomorphic test weight `g`,
    Arb edge non-vanishing, and strict interiority of the ball's zero support:

      `Bd(g·logDeriv ζ) = 2πi · Σ_ρ d(ρ)·g(ρ)`

    over the ACTUAL divisor of `ζ` on the ball.  The Blaschke `E`-part dies by Goursat (`g·E`
    holomorphic); the Herglotz part is the weighted residue sum (brick 2).  UNLIKE the counting
    harness (`zeta_count_eq_winding_generic`), every integrability fact is DERIVED internally
    from continuity — the Arb trust surface here is only: edge non-vanishing + strict
    interiority.  QC3 continues by evaluating `Bd(g·logDeriv ζ)` with the right edge in
    `Re > 1` via `LSeries_vonMangoldt_eq` (prime sums — the Bragg peaks).
    conjecture1_proved = False. -/
theorem bd_weighted_logDeriv_zeta
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    {W : Set ℂ} (g : ℂ → ℂ) (hW : IsOpen W) (hg : DifferentiableOn ℂ g W)
    (hsubW : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ W)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
      - (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
      + I • (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I) * logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
      - I • (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I) * logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
    = 2 * ↑π * I * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) * g ρ) := by
  obtain ⟨E, hE, hd1, hcap, hker⟩ := RHInBoxAnalytic.zeta_blaschke_split_ball
    sigma0 sigma1 T0 T1 c R (by
      -- positive radius: the (nonempty) box sits inside the ball
      by_contra hR0
      push_neg at hR0
      have := hbox_ball ((sigma0 : ℂ) + (T0 : ℂ) * I)
        (by constructor <;> simp [hsig]) (by constructor <;> simp [hT])
      have hlt := Metric.mem_ball.mp this
      have : (0:ℝ) ≤ dist ((sigma0 : ℂ) + (T0 : ℂ) * I) c := dist_nonneg
      linarith) hbox_ball hs1
  set Z := RHInBoxAnalytic.zeroFinset c R hs1 with hZdef
  set d : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) with hddef
  have hbox_sub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ Metric.ball c R := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact hbox_ball z hz.1 hz.2
  -- ζ and deriv ζ are continuous on the box (box ⊆ ball avoids the pole `1`).
  have hballne : Metric.ball c R ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hζana : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) :=
    analyticOn_riemannZeta.mono hballne
  have hζcont : ContinuousOn riemannZeta (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hζana.differentiableOn.continuousOn).mono hbox_sub
  have hdζcont : ContinuousOn (deriv riemannZeta) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hζana.deriv.differentiableOn.continuousOn).mono hbox_sub
  have hgcont : ContinuousOn g (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hg.mono hsubW).continuousOn
  have hEcont : ContinuousOn E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := hE.continuousOn
  -- Edge path membership (box form), as in brick 2.
  have hmem_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 →
      Set.MapsTo (fun t : ℝ => ((t : ℂ) + (a : ℂ) * I))
        (Set.uIcc sigma0 sigma1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro a ha t ht
    rw [Set.uIcc_of_le hsig] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ht, by simpa using ha⟩
  have hmem_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 →
      Set.MapsTo (fun t : ℝ => ((a : ℂ) + (t : ℂ) * I))
        (Set.uIcc T0 T1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro a ha t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ha, by simpa using ht⟩
  -- The pointwise weighted split on ball points off the zeros.
  have hsplitpt : ∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
      g z * logDeriv riemannZeta z
        = (∑ ρ ∈ Z, (d ρ : ℂ) * (g z * ((z - ρ)⁻¹))) + g z * E z := by
    intro z hz hnz
    rw [hker z hz hnz, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [div_eq_mul_inv]
    ring
  -- Generic edge machinery: continuity ⟹ integrability for the three integrand families.
  have hIlog_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 →
      (∀ t ∈ Set.uIcc sigma0 sigma1, riemannZeta ((t : ℂ) + (a : ℂ) * I) ≠ 0) →
      IntervalIntegrable (fun t : ℝ => g ((t : ℂ) + (a : ℂ) * I)
        * logDeriv riemannZeta ((t : ℂ) + (a : ℂ) * I)) volume sigma0 sigma1 := by
    intro a ha hnz
    refine ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha)) ?_)
    have hEqfun : (fun t : ℝ => logDeriv riemannZeta ((t : ℂ) + (a : ℂ) * I))
        = fun t : ℝ => deriv riemannZeta ((t : ℂ) + (a : ℂ) * I)
            / riemannZeta ((t : ℂ) + (a : ℂ) * I) := by
      funext t; rw [logDeriv_apply]
    rw [hEqfun]
    exact ContinuousOn.div
      (hdζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      (hζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      hnz
  have hIlog_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 →
      (∀ t ∈ Set.uIcc T0 T1, riemannZeta ((a : ℂ) + (t : ℂ) * I) ≠ 0) →
      IntervalIntegrable (fun t : ℝ => g ((a : ℂ) + (t : ℂ) * I)
        * logDeriv riemannZeta ((a : ℂ) + (t : ℂ) * I)) volume T0 T1 := by
    intro a ha hnz
    refine ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha)) ?_)
    have hEqfun : (fun t : ℝ => logDeriv riemannZeta ((a : ℂ) + (t : ℂ) * I))
        = fun t : ℝ => deriv riemannZeta ((a : ℂ) + (t : ℂ) * I)
            / riemannZeta ((a : ℂ) + (t : ℂ) * I) := by
      funext t; rw [logDeriv_apply]
    rw [hEqfun]
    exact ContinuousOn.div
      (hdζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      (hζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      hnz
  have hIsum_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 → (∀ ρ ∈ Z, a ≠ ρ.im) →
      IntervalIntegrable (fun t : ℝ => ∑ ρ ∈ Z, (d ρ : ℂ)
        * (g ((t : ℂ) + (a : ℂ) * I) * (((t : ℂ) + (a : ℂ) * I) - ρ)⁻¹)) volume sigma0 sigma1 := by
    intro a ha hane
    refine ContinuousOn.intervalIntegrable (continuousOn_finsetSum Z fun ρ hρ => ?_)
    exact continuousOn_const.mul (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => (hane ρ hρ) (by
          have him := congrArg Complex.im h
          simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
            zero_add] at him
          exact him)))))
  have hIsum_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 → (∀ ρ ∈ Z, a ≠ ρ.re) →
      IntervalIntegrable (fun t : ℝ => ∑ ρ ∈ Z, (d ρ : ℂ)
        * (g ((a : ℂ) + (t : ℂ) * I) * (((a : ℂ) + (t : ℂ) * I) - ρ)⁻¹)) volume T0 T1 := by
    intro a ha hane
    refine ContinuousOn.intervalIntegrable (continuousOn_finsetSum Z fun ρ hρ => ?_)
    exact continuousOn_const.mul (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => (hane ρ hρ) (by
          have hre := congrArg Complex.re h
          simp only [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
            zero_add, sub_zero] at hre
          exact hre)))))
  have hIgE_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 → IntervalIntegrable
      (fun t : ℝ => g ((t : ℂ) + (a : ℂ) * I) * E ((t : ℂ) + (a : ℂ) * I)) volume sigma0 sigma1 := by
    intro a ha
    exact ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      (hEcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha)))
  have hIgE_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 → IntervalIntegrable
      (fun t : ℝ => g ((a : ℂ) + (t : ℂ) * I) * E ((a : ℂ) + (t : ℂ) * I)) volume T0 T1 := by
    intro a ha
    exact ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      (hEcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha)))
  -- Edge-splits of the weighted boundary integrals.
  have hane_b : ∀ ρ ∈ Z, T0 ≠ ρ.im := fun ρ hρ => ne_of_lt (hins ρ hρ).2.2.1
  have hane_t : ∀ ρ ∈ Z, T1 ≠ ρ.im := fun ρ hρ => ne_of_gt (hins ρ hρ).2.2.2
  have hane_r : ∀ ρ ∈ Z, sigma1 ≠ ρ.re := fun ρ hρ => ne_of_gt (hins ρ hρ).2.1
  have hane_l : ∀ ρ ∈ Z, sigma0 ≠ ρ.re := fun ρ hρ => ne_of_lt (hins ρ hρ).1
  have hsplit_h : ∀ (a : ℝ) (ha : a ∈ Set.Icc T0 T1),
      (∀ t ∈ Set.uIcc sigma0 sigma1, riemannZeta ((t : ℂ) + (a : ℂ) * I) ≠ 0) →
      (∀ ρ ∈ Z, a ≠ ρ.im) →
      (∫ t in sigma0..sigma1, g ((t : ℂ) + (a : ℂ) * I) * logDeriv riemannZeta ((t : ℂ) + (a : ℂ) * I))
        = (∫ t in sigma0..sigma1, ∑ ρ ∈ Z, (d ρ : ℂ)
            * (g ((t : ℂ) + (a : ℂ) * I) * (((t : ℂ) + (a : ℂ) * I) - ρ)⁻¹))
          + (∫ t in sigma0..sigma1, g ((t : ℂ) + (a : ℂ) * I) * E ((t : ℂ) + (a : ℂ) * I)) := by
    intro a ha hnz hane
    rw [← intervalIntegral.integral_add (hIsum_h a ha hane) (hIgE_h a ha)]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hsplitpt _ (hbox_sub (hmem_h a ha ht)) (hnz t ht)
  have hsplit_v : ∀ (a : ℝ) (ha : a ∈ Set.Icc sigma0 sigma1),
      (∀ t ∈ Set.uIcc T0 T1, riemannZeta ((a : ℂ) + (t : ℂ) * I) ≠ 0) →
      (∀ ρ ∈ Z, a ≠ ρ.re) →
      (∫ t in T0..T1, g ((a : ℂ) + (t : ℂ) * I) * logDeriv riemannZeta ((a : ℂ) + (t : ℂ) * I))
        = (∫ t in T0..T1, ∑ ρ ∈ Z, (d ρ : ℂ)
            * (g ((a : ℂ) + (t : ℂ) * I) * (((a : ℂ) + (t : ℂ) * I) - ρ)⁻¹))
          + (∫ t in T0..T1, g ((a : ℂ) + (t : ℂ) * I) * E ((a : ℂ) + (t : ℂ) * I)) := by
    intro a ha hnz hane
    rw [← intervalIntegral.integral_add (hIsum_v a ha hane) (hIgE_v a ha)]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hsplitpt _ (hbox_sub (hmem_v a ha ht)) (hnz t ht)
  -- Assemble: brick 2 on the Herglotz part, Goursat on the g·E part.
  have hSum := rect_weighted_residue_sum_generic sigma0 sigma1 T0 T1 hsig hT
    (s := Z) d g hW hg hsubW hins
  have hGE := RHInBoxAnalytic.rect_arg_principle_generic sigma0 sigma1 T0 T1 hsig hT
    (fun z => g z * E z) ((hg.mono hsubW).mul hE)
  rw [hsplit_h T0 ⟨le_refl _, hT⟩ hnzb hane_b,
    hsplit_h T1 ⟨hT, le_refl _⟩ hnzt hane_t,
    hsplit_v sigma1 ⟨hsig, le_refl _⟩ hnzr hane_r,
    hsplit_v sigma0 ⟨le_refl _, hsig⟩ hnzl hane_l]
  simp only [smul_eq_mul] at hSum hGE ⊢
  linear_combination hSum + hGE

/-! ## Brick 4 (P1): the prime keystone — `logDeriv ζ = −L(Λ)` on `Re s > 1`.

Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` supplies the arithmetic side whole:
`L(Λ) s = −ζ′(s)/ζ(s)` for `Re s > 1`.  Restated in the harness's `logDeriv` vocabulary, this is
the identity that lets `bd_weighted_logDeriv_zeta`'s RIGHT EDGE (placed in `Re > 1`) speak primes:
the edge integrand `g·logDeriv ζ` becomes `−g·Σ Λ(n) n^{−s}` — the Bragg peaks at `k·log p`,
awaiting only the series–integral interchange (P2: dominated convergence along the compact edge,
`|Λ(n)n^{−s}| = Λ(n)n^{−σ₁}` summable).  conjecture1_proved = False. -/

/-- **The prime keystone:** `logDeriv ζ(s) = −L(Λ)(s)` for `Re s > 1`. -/
theorem logDeriv_zeta_eq_neg_LSeries_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s
      = - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [logDeriv_apply,
    show LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      = - deriv riemannZeta s / riemannZeta s from h]
  ring

/-- The weighted right-edge integrand in prime form: for `1 < σ₁`, pointwise along the edge,
    `g·logDeriv ζ = −g·L(Λ)` — the shape P2's interchange turns into `−Σ_n Λ(n)·∫ g·n^{−s}`. -/
theorem right_edge_weighted_prime_integrand (sigma1 : ℝ) (hσ : 1 < sigma1) (g : ℂ → ℂ) (y : ℝ) :
    g ((sigma1 : ℂ) + y * I) * logDeriv riemannZeta ((sigma1 : ℂ) + y * I)
      = - (g ((sigma1 : ℂ) + y * I)
          * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ((sigma1 : ℂ) + y * I)) := by
  rw [logDeriv_zeta_eq_neg_LSeries_vonMangoldt (by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero]
    exact hσ)]
  ring

/-! ## Brick 5 (P2): the series–integral interchange on the right edge.

With the right edge at `Re = σ₁ > 1`, the weighted edge integral of `L(Λ)` expands TERMWISE:
`∫ g·L(Λ) = Σ'_n ∫ g·term(Λ, n)` — dominated convergence with the `y`-independent majorant
`C·‖term(Λ, σ₁, n)‖` (vertical-line norm invariance is Mathlib's `norm_term_eq`: the norm
depends only on `Re s`; summability is `LSeriesSummable_vonMangoldt` + `summable_norm_iff`).
Combined with brick 4 this makes the right edge of `bd_weighted_logDeriv_zeta` a sum of
prime-power integrals `−Σ Λ(n)·∫ g·n^{−s}` — the Bragg peaks.  conjecture1_proved = False. -/

/-- **The right-edge prime expansion** (series–integral interchange): for `1 < σ₁`,
    `∫ g·L(Λ) dy = Σ'_n ∫ g·term(Λ,n) dy` along the edge `Re = σ₁`, `y ∈ [T0, T1]`. -/
theorem right_edge_prime_expansion
    (sigma1 T0 T1 : ℝ) (hσ : 1 < sigma1) (hT : T0 ≤ T1)
    (g : ℂ → ℂ)
    (hgc : ContinuousOn (fun y : ℝ => g ((sigma1 : ℂ) + y * I)) (Set.uIcc T0 T1))
    (C : ℝ) (hC : ∀ y ∈ Set.uIcc T0 T1, ‖g ((sigma1 : ℂ) + y * I)‖ ≤ C) :
    (∫ y in T0..T1, g ((sigma1 : ℂ) + y * I)
        * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ((sigma1 : ℂ) + y * I))
      = ∑' n : ℕ, (∫ y in T0..T1, g ((sigma1 : ℂ) + y * I)
          * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((sigma1 : ℂ) + y * I) n) := by
  set vM : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) with hvM
  have hre : ∀ y : ℝ, ((sigma1 : ℂ) + y * I).re = sigma1 := by
    intro y
    simp
  have hsub' : Set.Ioc T0 T1 ⊆ Set.uIcc T0 T1 := by
    rw [Set.uIcc_of_le hT]
    exact Set.Ioc_subset_Icc_self
  have hσ' : 1 < ((sigma1 : ℂ)).re := by simpa using hσ
  have hsummC : Summable (fun n => LSeries.term vM (sigma1 : ℂ) n) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσ'
  have hsumm : Summable (fun n => ‖LSeries.term vM (sigma1 : ℂ) n‖) :=
    summable_norm_iff.mpr hsummC
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC T0 Set.left_mem_uIcc)
  -- pointwise: pull `g` inside the defining tsum of `LSeries`
  have hpt : Set.EqOn
      (fun y : ℝ => g ((sigma1 : ℂ) + y * I) * LSeries vM ((sigma1 : ℂ) + y * I))
      (fun y : ℝ => ∑' n : ℕ, g ((sigma1 : ℂ) + y * I)
        * LSeries.term vM ((sigma1 : ℂ) + y * I) n)
      (Set.uIcc T0 T1) := by
    intro y _
    simp only [LSeries]
    exact (tsum_mul_left).symm
  -- measurability of each summand on the edge
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => g ((sigma1 : ℂ) + y * I) * LSeries.term vM ((sigma1 : ℂ) + y * I) n)
      (MeasureTheory.volume.restrict (Set.Ioc T0 T1)) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul (hgc.mono hsub') ?_
    by_cases hn : n = 0
    · subst hn
      simp only [LSeries.term_zero]
      exact continuousOn_const
    · have hterm : (fun y : ℝ => LSeries.term vM ((sigma1 : ℂ) + y * I) n)
          = fun y : ℝ => vM n / ((n : ℂ) ^ ((sigma1 : ℂ) + y * I)) := by
        funext y
        rw [LSeries.term_of_ne_zero hn]
      rw [hterm]
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact (Continuous.const_cpow (by fun_prop)
          (Or.inl (Nat.cast_ne_zero.mpr hn))).continuousOn
      · intro y _
        rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
        exact Complex.exp_ne_zero _
  -- the dominated bound: each edge lintegral is at most `len · C·‖term(σ₁,n)‖`
  have hbound : ∀ n : ℕ,
      (∫⁻ y in Set.Ioc T0 T1, ‖g ((sigma1 : ℂ) + y * I)
          * LSeries.term vM ((sigma1 : ℂ) + y * I) n‖ₑ ∂MeasureTheory.volume)
        ≤ ENNReal.ofReal (C * ‖LSeries.term vM (sigma1 : ℂ) n‖)
            * ENNReal.ofReal (T1 - T0) := by
    intro n
    have hptb : ∀ y ∈ Set.Ioc T0 T1,
        ‖g ((sigma1 : ℂ) + y * I) * LSeries.term vM ((sigma1 : ℂ) + y * I) n‖ₑ
          ≤ ENNReal.ofReal (C * ‖LSeries.term vM (sigma1 : ℂ) n‖) := by
      intro y hy
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul]
      have h2 : ‖LSeries.term vM ((sigma1 : ℂ) + y * I) n‖
          = ‖LSeries.term vM (sigma1 : ℂ) n‖ := by
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre y, Complex.ofReal_re]
      rw [h2]
      exact mul_le_mul_of_nonneg_right (hC y (hsub' hy)) (norm_nonneg _)
    calc (∫⁻ y in Set.Ioc T0 T1, ‖g ((sigma1 : ℂ) + y * I)
            * LSeries.term vM ((sigma1 : ℂ) + y * I) n‖ₑ ∂MeasureTheory.volume)
        ≤ ∫⁻ _ in Set.Ioc T0 T1,
            ENNReal.ofReal (C * ‖LSeries.term vM (sigma1 : ℂ) n‖) ∂MeasureTheory.volume := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
          exact hptb y hy
      _ = ENNReal.ofReal (C * ‖LSeries.term vM (sigma1 : ℂ) n‖)
            * ENNReal.ofReal (T1 - T0) := by
          rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc]
  have hfin : (∑' n : ℕ, ∫⁻ y in Set.Ioc T0 T1, ‖g ((sigma1 : ℂ) + y * I)
      * LSeries.term vM ((sigma1 : ℂ) + y * I) n‖ₑ ∂MeasureTheory.volume) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg hC0 (norm_nonneg _)) (hsumm.mul_left C)]
    exact ENNReal.ofReal_ne_top
  -- assemble: congr to the tsum integrand, swap, restore interval form termwise
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_of_le hT,
    MeasureTheory.integral_tsum hmeas hfin]
  exact tsum_congr fun n => (intervalIntegral.integral_of_le hT).symm

/-! ## Brick 6 (ASSEMBLY): the finite-height explicit formula — zeros = primes + boundary.

Composing bricks 3, 4, 5: place the box's right edge at `Re = σ₁ > 1`.  Brick 3 evaluates the
weighted boundary integral as the ZERO side (`2πi·Σ d(ρ)g(ρ)` over the actual divisor); brick 4
turns the right-edge integrand into `−g·L(Λ)` pointwise; brick 5 expands it termwise into
PRIME-POWER integrals.  The result — every hypothesis explicit, every step kernel-checked:

  `2πi · Σ_ρ d(ρ)·g(ρ)  =  (bottom edge) − (top edge) − i·Σ′_n Λ(n)-term integrals − i·(left edge)`

the rectangular Guinand–Weil / explicit-formula identity at finite height: **weighted sums over
zeta zeros equal von Mangoldt (prime-power) sums plus three boundary integrals.**  The right-edge
zeta non-vanishing is DERIVED (`Re > 1`, `riemannZeta_ne_zero_of_one_le_re`), and the test-weight
edge bound is DERIVED (extreme value theorem on the compact edge) — the Arb trust surface is only:
three off-prime-side edge non-vanishings + strict interiority of the ball's zero support.

Classically the three remaining edges are estimated and sent to limits (`T0 → −∞` symmetrically,
`σ₀ → −∞` via the functional equation); here they stand as honest, explicit remainder terms.
conjecture1_proved = False. -/

/-- **The finite-height explicit formula on a rectangle** (assembly of bricks 3+4+5):
    for a box with right edge in `Re > 1`, weighted zero-sums equal prime-power sums plus
    the three remaining boundary integrals. -/
theorem rect_explicit_formula
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1) (hσ1 : 1 < sigma1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    {W : Set ℂ} (g : ℂ → ℂ) (hW : IsOpen W) (hg : DifferentiableOn ℂ g W)
    (hsubW : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ W)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    2 * ↑π * I * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) * g ρ)
      = (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        - I • (∑' n : ℕ, (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I)
            * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
                ((sigma1 : ℂ) + ↑y * I) n))
        - I • (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I)
            * logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I)) := by
  -- The right edge lies in `Re > 1`: zeta non-vanishing there is a THEOREM, not an input.
  have hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0 := by
    intro y _
    apply riemannZeta_ne_zero_of_one_le_re
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero]
    linarith
  -- Brick 3: the weighted boundary integral IS the zero side.
  have hBd := bd_weighted_logDeriv_zeta sigma0 sigma1 T0 T1 hsig hT c R hbox_ball hs1
    g hW hg hsubW hnzb hnzt hnzr hnzl hins
  -- `g` restricted to the right edge: continuous, hence bounded (extreme value theorem).
  have hσ1mem : sigma1 ∈ Set.Icc sigma0 sigma1 := ⟨hsig, le_refl _⟩
  have hmem_r : Set.MapsTo (fun t : ℝ => ((sigma1 : ℂ) + (t : ℂ) * I))
      (Set.uIcc T0 T1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using hσ1mem, by simpa using ht⟩
  have hgcont : ContinuousOn g (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hg.mono hsubW).continuousOn
  have hgc : ContinuousOn (fun y : ℝ => g ((sigma1 : ℂ) + y * I)) (Set.uIcc T0 T1) :=
    hgcont.comp (Continuous.continuousOn (by fun_prop)) hmem_r
  obtain ⟨y₀, hy₀, hmax⟩ := (isCompact_uIcc (a := T0) (b := T1)).exists_isMaxOn
    ⟨T0, Set.left_mem_uIcc⟩ hgc.norm
  -- Bricks 4+5: the right edge speaks primes.
  have hcongr : (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I)
        * logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
      = - (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I)
          * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((sigma1 : ℂ) + ↑y * I)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    exact right_edge_weighted_prime_integrand sigma1 hσ1 g y
  have hCbound : ∀ y ∈ Set.uIcc T0 T1,
      ‖g ((sigma1 : ℂ) + ↑y * I)‖ ≤ ‖g ((sigma1 : ℂ) + ↑y₀ * I)‖ :=
    fun y hy => hmax hy
  have hexp := right_edge_prime_expansion sigma1 T0 T1 hσ1 hT g hgc
    (‖g ((sigma1 : ℂ) + ↑y₀ * I)‖) hCbound
  rw [hcongr, hexp] at hBd
  simp only [smul_eq_mul] at hBd ⊢
  linear_combination -hBd

/-! ## Brick 7 (W1): the Bragg amplitude in closed form.

The prime-side integrals of `rect_explicit_formula` (constant weight `g ≡ 1`) evaluate in
CLOSED FORM: the `n`-th term is a pure oscillation of frequency `log n` —

  `∫_{T0}^{T1} Λ(n)·n^{−(σ+iy)} dy  =  [term at T1 − term at T0] / (−i·log n)`,

amplitude `Λ(n)·n^{−σ}/log n`, Bragg frequency `log n` (nonzero exactly at prime powers).
This is the diffraction pattern of the zeros, prime-side, as concrete arithmetic — the first
W1 (second-axis) brick: the formula meeting computable prime data.  conjecture1_proved = False. -/

/-- **The Bragg oscillation, integrated:** for `n ≥ 2`,
    `∫ y in T0..T1, term(Λ, σ+iy, n) = (term(σ+iT1) − term(σ+iT0)) / (−i·log n)`. -/
theorem integral_vonMangoldt_term (σ T0 T1 : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (∫ y in T0..T1, LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + y * I) n)
      = (LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) ((σ : ℂ) + T1 * I) n
          - LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) ((σ : ℂ) + T0 * I) n)
        / (-(I * (Real.log n : ℂ))) := by
  set vM : ℕ → ℂ := fun m => (ArithmeticFunction.vonMangoldt m : ℂ) with hvM
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlogC : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℂ)) = (((n : ℝ) : ℂ)) by push_cast; rfl,
      ← Complex.ofReal_log (by positivity : (0:ℝ) ≤ (n:ℝ))]
  set L : ℂ := ((Real.log n : ℝ) : ℂ) with hL
  have hLne : L ≠ 0 := by
    rw [hL]
    exact_mod_cast ne_of_gt hlogpos
  have hDne : (-(I * L)) ≠ 0 := by
    simp [Complex.I_ne_zero, hLne]
  -- The term as a function of the height, in exponential form.
  have hterm : ∀ y : ℝ, LSeries.term vM ((σ : ℂ) + y * I) n
      = (ArithmeticFunction.vonMangoldt n : ℂ)
          / Complex.exp (L * ((σ : ℂ) + y * I)) := by
    intro y
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hnC, hlogC]
  -- The antiderivative: `F y = term(σ+iy) / (−iL)`; its derivative is the term itself.
  have hF : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => LSeries.term vM ((σ : ℂ) + t * I) n / (-(I * L)))
      (LSeries.term vM ((σ : ℂ) + y * I) n) y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ) * I) I y := by
      simpa using h1.mul_const I
    have hpath : HasDerivAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) I y := h2.const_add _
    have harg : HasDerivAt (fun t : ℝ => L * ((σ : ℂ) + (t : ℂ) * I)) (L * I) y :=
      hpath.const_mul L
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (L * ((σ : ℂ) + (t : ℂ) * I)))
        (Complex.exp (L * ((σ : ℂ) + (y : ℂ) * I)) * (L * I)) y := harg.cexp
    have hdiv : HasDerivAt
        (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ)
          / Complex.exp (L * ((σ : ℂ) + (t : ℂ) * I)))
        ((0 * Complex.exp (L * ((σ : ℂ) + (y : ℂ) * I))
            - (ArithmeticFunction.vonMangoldt n : ℂ)
              * (Complex.exp (L * ((σ : ℂ) + (y : ℂ) * I)) * (L * I)))
          / (Complex.exp (L * ((σ : ℂ) + (y : ℂ) * I))) ^ 2) y :=
      (hasDerivAt_const y _).div hexp (Complex.exp_ne_zero _)
    have hcongr : (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ)
          / Complex.exp (L * ((σ : ℂ) + (t : ℂ) * I)))
        = fun t : ℝ => LSeries.term vM ((σ : ℂ) + t * I) n := by
      funext t
      rw [hterm t]
    rw [hcongr] at hdiv
    have hstep := hdiv.div_const (-(I * L))
    have heq : ((0 * Complex.exp (L * ((σ : ℂ) + (y : ℂ) * I))
            - (ArithmeticFunction.vonMangoldt n : ℂ)
              * (Complex.exp (L * ((σ : ℂ) + (y : ℂ) * I)) * (L * I)))
          / (Complex.exp (L * ((σ : ℂ) + (y : ℂ) * I))) ^ 2) / (-(I * L))
        = LSeries.term vM ((σ : ℂ) + y * I) n := by
      rw [hterm y]
      have hE := Complex.exp_ne_zero (L * ((σ : ℂ) + (y : ℂ) * I))
      field_simp
      ring
    exact heq ▸ hstep
  -- FTC.
  have hcont : IntervalIntegrable (fun y : ℝ => LSeries.term vM ((σ : ℂ) + y * I) n)
      MeasureTheory.volume T0 T1 := by
    apply Continuous.intervalIntegrable
    have : (fun y : ℝ => LSeries.term vM ((σ : ℂ) + y * I) n)
        = fun y : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ)
            / Complex.exp (L * ((σ : ℂ) + y * I)) := by
      funext y
      rw [hterm y]
    rw [this]
    exact continuous_const.div (by fun_prop) (fun y => Complex.exp_ne_zero _)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y) hcont
  rw [this]
  ring

/-! ## Brick 8 (EDGES-TO-LIMITS, structural half): the reflection identities — the LEFT edge
speaks primes and Archimedean, with ZERO Arb inputs.

The classical route sends the explicit formula's remaining edges to limits via the functional
equation: `Λ(1−s) = Λ(s)` reflects the left edge (`Re < 0`) into the prime region (`Re > 1`).
Here, kernel-side:

  * `logDeriv_completedZeta_reflect` — `(log Λ)′(1−s) = −(log Λ)′(s)` (the FE, differentiated);
  * `logDeriv_zeta_add_gammaR` — the split `(log Λ)′ = (log ζ)′ + (log Γℝ)′`;
  * `logDeriv_zeta_reflect` — the ζ reflection identity;
  * `left_edge_prime_reflection` — **for `Re s < 0`, `Im s ≠ 0`:**

      `(log ζ)′(s) = L(Λ)(1−s) − (log Γℝ)′(s) − (log Γℝ)′(1−s)`

    with EVERY hypothesis derived (`s ∉ {0,1}` from `Re < 0`; `ζ(s) ≠ 0` from the strip-location
    theorem; `ζ(1−s) ≠ 0` and `Γℝ(1−s) ≠ 0` from `Re(1−s) > 1`; `Γℝ(s) ≠ 0` from `Im ≠ 0`;
    the prime keystone at `1−s`).  The LEFT edge of any explicit-formula box in `Re < 0` is
    therefore prime sums (mirrored) + two Archimedean `ψ`-integrals (`logDeriv_gammaR` expands
    them into digammas — where the θ/Binet machinery lives) — **no ζ data, no Arb input**.

    Remaining for the full classical limit: the horizontal edges as `T → ∞`, which requires the
    `|ζ′/ζ| = O(log² T)` corridor lemma (zero-avoiding heights) — genuine further analysis,
    honestly out of scope here.  conjecture1_proved = False. -/

/-- The functional equation, log-differentiated: `(log Λ)′(1−s) = −(log Λ)′(s)`. -/
theorem logDeriv_completedZeta_reflect {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = - logDeriv completedRiemannZeta s := by
  have h10 : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have h11 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have hd1s : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta h10 h11
  have hsymm : (fun z : ℂ => completedRiemannZeta (1 - z)) = completedRiemannZeta :=
    funext fun z => completedRiemannZeta_one_sub z
  have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have hcomp : HasDerivAt (fun z : ℂ => completedRiemannZeta (1 - z))
      (deriv completedRiemannZeta (1 - s) * (-1)) s :=
    hd1s.hasDerivAt.comp s hinner
  have h1 := hcomp.deriv
  rw [hsymm] at h1
  have hkey : deriv completedRiemannZeta (1 - s) = - deriv completedRiemannZeta s := by
    linear_combination h1
  rw [logDeriv_apply, logDeriv_apply, completedRiemannZeta_one_sub, hkey]
  ring

/-- The split `(log Λ)′ = (log ζ)′ + (log Γℝ)′` at any `s ∉ {0,1}` with `ζ(s), Γℝ(s) ≠ 0`. -/
theorem logDeriv_zeta_add_gammaR {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    logDeriv completedRiemannZeta s = logDeriv riemannZeta s + logDeriv Gammaℝ s := by
  have hGdiff : DifferentiableAt ℂ Gammaℝ s := by
    have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m hm
      apply hG
      rw [Complex.Gammaℝ_eq_zero_iff]
      exact ⟨m, by linear_combination 2 * hm⟩
    have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    have hB : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
        (deriv Complex.Gamma (s / 2) * (1 / 2)) s :=
      ((Complex.differentiableAt_Gamma _ hpole).hasDerivAt).comp s hhalf
    have hGdef : Gammaℝ = fun z : ℂ => ZeroFreeBridge.gammaRArch z * Complex.Gamma (z / 2) := rfl
    rw [hGdef]
    exact ((ZeroFreeBridge.gammaRArch_hasDerivAt s).differentiableAt).mul hB.differentiableAt
  have hζdiff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hev : completedRiemannZeta =ᶠ[nhds s] fun z => riemannZeta z * Gammaℝ z := by
    filter_upwards [isOpen_ne.mem_nhds hs0, hGdiff.continuousAt.eventually_ne hG] with z hz0 hzG
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp
  rw [RHInBoxAnalytic.logDeriv_congr_nhds hev, logDeriv_mul s hζ hG hζdiff hGdiff]

/-- **The ζ reflection identity** (log-differentiated functional equation, split form). -/
theorem logDeriv_zeta_reflect {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0) (hζ1s : riemannZeta (1 - s) ≠ 0)
    (hGs : Gammaℝ s ≠ 0) (hG1s : Gammaℝ (1 - s) ≠ 0) :
    logDeriv riemannZeta (1 - s)
      = - logDeriv riemannZeta s - logDeriv Gammaℝ s - logDeriv Gammaℝ (1 - s) := by
  have h10 : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have h11 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have h1 := logDeriv_zeta_add_gammaR h10 h11 hζ1s hG1s
  have h2 := logDeriv_zeta_add_gammaR hs0 hs1 hζs hGs
  have h3 := logDeriv_completedZeta_reflect hs0 hs1
  linear_combination h3 - h1 - h2

/-- **THE LEFT EDGE SPEAKS PRIMES — zero Arb inputs.**  For `Re s < 0`, `Im s ≠ 0`:
    `(log ζ)′(s) = L(Λ)(1−s) − (log Γℝ)′(s) − (log Γℝ)′(1−s)` — every hypothesis derived. -/
theorem left_edge_prime_reflection {s : ℂ} (hre : s.re < 0) (him : s.im ≠ 0) :
    logDeriv riemannZeta s
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - s)
        - logDeriv Gammaℝ s - logDeriv Gammaℝ (1 - s) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have hre1s : 1 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hζs : riemannZeta s ≠ 0 := fun hz =>
    absurd (ZetaZeroConfinement.zeta_zero_re_mem_strip him hz).1 (by linarith)
  have hζ1s : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (le_of_lt hre1s)
  have hGs : Gammaℝ s ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    apply him
    rw [hn]
    simp
  have hG1s : Gammaℝ (1 - s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  -- reflect, then expand the mirror point (`Re > 1`) by the prime keystone
  have hrefl := logDeriv_zeta_reflect
    (fun h => hs1 (by linear_combination -h))   -- (1−s) ≠ 0 case reuses: apply at s' := 1−s
    (fun h => hs0 (by linear_combination -h))
    hζ1s (by rw [show (1:ℂ) - (1 - s) = s by ring]; exact hζs)
    hG1s (by rw [show (1:ℂ) - (1 - s) = s by ring]; exact hGs)
  rw [show (1:ℂ) - (1 - s) = s by ring] at hrefl
  have hkey := logDeriv_zeta_eq_neg_LSeries_vonMangoldt hre1s
  linear_combination hrefl - hkey

/-! ## Brick 9 (T3 ground — the ζ-side of Riemann–von Mangoldt): the box zero-count IS the
boundary winding of `ζ′/ζ`.

The `g ≡ 1` specialization of `bd_weighted_logDeriv_zeta`: the four-segment boundary integral of
`ζ′/ζ` around the box equals `2πi · (number of ζ-zeros in the box, with multiplicity)`.  This is
the argument principle for `ζ` in closed kernel form — the LEFT side of RvM
(`N(T) = θ(T)/π + 1 + S(T)`), which classically is obtained by taking this box to the half-line
`[1/2, ∞) × [0, T]` and splitting the boundary contour into the Γ-argument (→ `θ`, our
`riemannSiegelTheta` via the Archimedean bridge) and the ζ-argument remainder (→ `πS`).  The
half-line limit + the `S`-identification are the remaining research content
(see `docs/RVM_T3_T4_SCOPING`).  conjecture1_proved = False. -/

/-- **The argument principle for `ζ` on a box** (RvM zero-count side): the boundary winding of
    `ζ′/ζ` equals `2πi` times the box zero-count (actual divisor, with multiplicity). -/
theorem bd_logDeriv_zeta_eq_count
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
      - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
      + I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
      - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
    = 2 * ↑π * I * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) := by
  have h := bd_weighted_logDeriv_zeta sigma0 sigma1 T0 T1 hsig hT c R hbox_ball hs1
    (fun _ => (1 : ℂ)) isOpen_univ (differentiableOn_const 1) (Set.subset_univ _)
    hnzb hnzt hnzr hnzl hins
  simpa using h

/-! ## Brick 10 (the argument-change infrastructure — closing the T3 "true gap" branch-free).

RvM's `S(T)` was flagged as needing a continuous `arg`-along-a-path, absent from Mathlib.  But
the CONTINUOUS ARGUMENT CHANGE along a zero-avoiding path IS the imaginary part of the
log-derivative line integral — `Im ∫ f′/f = Δ arg f`, `Re ∫ f′/f = Δ log‖f‖` — with NO branch
function, exactly as `riemannSiegelTheta` was defined by an integral rather than a branch of
`logΓ`.  These definitions + the box identity (from `bd_logDeriv_zeta_eq_count` by taking `.im`)
give the argument principle in ARGUMENT-CHANGE form: total argument change around the box =
`2π · (zero-count)`.  This is the scaffold `S` sits on: as the box opens to the half-plane, the
vertical-edge argument change on the near-critical side becomes `π·S(T)` and the horizontal/Γ
contributions become `θ(T)`.  conjecture1_proved = False. -/

/-- Argument change of `f` UP the vertical segment `Re = σ`, `Im ∈ [T0,T1]`
    (`= Im ∫ f′/f · i dy = Re ∫ f′/f dy`, the `i`-rotation of the path derivative). -/
noncomputable def argChangeVert (f : ℂ → ℂ) (σ T0 T1 : ℝ) : ℝ :=
  (∫ y in T0..T1, logDeriv f ((σ : ℂ) + y * I)).re

/-- Argument change of `f` ALONG the horizontal segment `Im = T`, `Re ∈ [x0,x1]`
    (`= Im ∫ f′/f dx`, the path derivative being `1`). -/
noncomputable def argChangeHoriz (f : ℂ → ℂ) (T x0 x1 : ℝ) : ℝ :=
  (∫ x in x0..x1, logDeriv f ((x : ℂ) + T * I)).im

/-- **The argument principle in ARGUMENT-CHANGE form**: the total continuous argument change of
    `ζ` counterclockwise around the box `[σ0,σ1] × [T0,T1]` equals `2π · (box zero-count)` —
    branch-free, from `bd_logDeriv_zeta_eq_count` by taking imaginary parts.  The `S`/`θ`
    scaffold: no continuous `arg` function required. -/
theorem zeta_total_argChange_eq_count
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    argChangeHoriz riemannZeta T0 sigma0 sigma1
        - argChangeHoriz riemannZeta T1 sigma0 sigma1
        + argChangeVert riemannZeta sigma1 T0 T1
        - argChangeVert riemannZeta sigma0 T0 T1
      = 2 * π * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
          (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ) := by
  have hBd := bd_logDeriv_zeta_eq_count sigma0 sigma1 T0 T1 hsig hT c R hbox_ball hs1
    hnzb hnzt hnzr hnzl hins
  have him := congrArg Complex.im hBd
  set Bb := ∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I) with hBb
  set Bt := ∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I) with hBt
  set Br := ∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I) with hBr
  set Bl := ∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I) with hBl
  -- LHS `.im`: Im(Bb - Bt + I•Br - I•Bl) = Im Bb - Im Bt + Re Br - Re Bl.
  have hlhs : (Bb - Bt + I • Br - I • Bl).im
      = Bb.im - Bt.im + Br.re - Bl.re := by
    simp only [smul_eq_mul, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, one_mul, zero_mul, zero_add, mul_zero, sub_zero]
  -- RHS `.im`: Im(2πi · (N:ℝ→ℂ)) = 2π·N,  N a real cast of an integer sum.
  set Nsum : ℤ := ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
    ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) with hNsum
  have hcast : (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℂ))
      = ((Nsum : ℤ) : ℂ) := by rw [hNsum]; push_cast; ring
  have hrhs : (2 * ↑π * I * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ)).im
      = 2 * π * (Nsum : ℝ) := by
    rw [hcast,
      show (2 * (↑π : ℂ) * I * ((Nsum : ℤ) : ℂ))
        = (((2 * π * (Nsum : ℝ)) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.mul_I_im, Complex.ofReal_re]
  rw [hlhs] at him
  rw [hrhs] at him
  unfold argChangeHoriz argChangeVert
  rw [← hBb, ← hBt, ← hBr, ← hBl, him]
  have hsumcast : ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ)
      = (Nsum : ℝ) := by rw [hNsum]; push_cast; ring
  rw [hsumcast]

/-! ## Brick 11 (RvM bookkeeping, phase 1): `S(T)` defined branch-free, and
`θ(T)` IS the Archimedean argument-change up the critical line.

With the argChange vocabulary the classical objects become DEFINITIONS, not constructions:

  * `riemannS T` — the argument of `ζ` at `1/2 + iT` by continuous variation along the standard
    zero-avoiding path (`2 → 2 + iT → 1/2 + iT`), divided by `π`.  Branch-free: each leg is an
    `Im`/`Re` of a log-derivative integral.  (Total function; its RvM meaning requires the path
    to avoid zeros, i.e. `T` not a zero-ordinate — the classical caveat, honestly inherited.)
  * `theta_eq_argChangeVert_gammaR` — **`θ(T) = argChangeVert Γℝ (1/2) 0 T`**: the Riemann–Siegel
    phase IS the continuous Archimedean argument change up the critical line, welding the
    `DlvpTheta` campaign to the argument-principle machinery.  (Proof: the Archimedean bridge
    `thetaIntegrand_eq_re_logDeriv_gammaR` + `intervalIntegral_re`; integrability from the
    digamma ray continuity built in `DlvpTheta`.)

Remaining RvM assembly: the Λ-split of the box argument-change (linearity over
`logDeriv_zeta_add_gammaR`), the FE-fold, and the `s(s−1)/2` pole bookkeeping — assembly on
these pieces.  conjecture1_proved = False. -/

/-- **`S(T)`, branch-free**: `π·S(T)` is the continuous argument change of `ζ` along
    `2 → 2+iT → 1/2+iT`. -/
noncomputable def riemannS (T : ℝ) : ℝ :=
  (argChangeVert riemannZeta 2 0 T + argChangeHoriz riemannZeta T 2 (1/2)) / π

/-- The vertical leg at `Re = 2` starts at zero. -/
theorem argChangeVert_zero (f : ℂ → ℂ) (σ : ℝ) : argChangeVert f σ 0 0 = 0 := by
  unfold argChangeVert
  rw [intervalIntegral.integral_same]
  rfl

/-- The critical-line `Γℝ` log-derivative is continuous in the height (via the digamma ray). -/
theorem continuous_logDeriv_gammaR_line :
    Continuous (fun y : ℝ => logDeriv Gammaℝ ((1/2 : ℂ) + y * I)) := by
  have hfun : (fun y : ℝ => logDeriv Gammaℝ ((1/2 : ℂ) + y * I))
      = fun y : ℝ => -(Real.log Real.pi : ℂ) / 2
          + (1 / 2) * Complex.digamma (ZeroFreeBridge.thetaRay y) := by
    funext y
    have hhalf : ((1/2 : ℂ) + y * I) / 2 = ZeroFreeBridge.thetaRay y := by
      unfold ZeroFreeBridge.thetaRay
      push_cast
      ring
    have hs : 0 < (((1/2 : ℂ) + y * I) / 2).re := by
      rw [hhalf, ZeroFreeBridge.thetaRay_re]
      norm_num
    rw [ZeroFreeBridge.logDeriv_gammaR _ hs, hhalf]
  rw [hfun]
  refine continuous_const.add (continuous_const.mul ?_)
  refine continuous_iff_continuousAt.mpr fun y => ?_
  exact (ZeroFreeBridge.digamma_continuousAt_thetaRay y).comp
    ZeroFreeBridge.thetaRay_continuous.continuousAt

/-- **`θ` IS the Archimedean argument change up the critical line**:
    `riemannSiegelTheta T = argChangeVert Γℝ (1/2) 0 T`. -/
theorem theta_eq_argChangeVert_gammaR (T : ℝ) :
    ZeroFreeBridge.riemannSiegelTheta T = argChangeVert Gammaℝ (1/2) 0 T := by
  have hInt : IntervalIntegrable (fun y : ℝ => logDeriv Gammaℝ ((1/2 : ℂ) + y * I))
      MeasureTheory.volume 0 T :=
    continuous_logDeriv_gammaR_line.intervalIntegrable 0 T
  have h := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hInt
  simp only [RCLike.re_to_complex] at h
  unfold argChangeVert
  rw [show (((1/2 : ℝ)) : ℂ) = (1/2 : ℂ) by norm_num, ← h]
  unfold ZeroFreeBridge.riemannSiegelTheta
  apply intervalIntegral.integral_congr
  intro u _
  exact ZeroFreeBridge.thetaIntegrand_eq_re_logDeriv_gammaR u

/-! ## Brick 12 (RvM bookkeeping, phase 2): THE S-DIFFERENCE COUNTING IDENTITY.

Fold brick 10's box argument-principle into the continuous-argument function: define
`argZeta σ T` — the continuous argument of `ζ` at `σ + iT` along the standard route
`2 → 2+iT → σ+iT` (so `π·riemannS T = argZeta (1/2) T`).  Then for a box `[σ0, 2] × [T0, T1]`
with admissible boundary, the count identity becomes

  `2π · N_box  =  (argZeta σ0 T1 − argZeta σ0 T0)  −  argChangeVert ζ σ0 T0 T1`

— **the zero-count is the jump of the continuous argument at the left abscissa, minus the
left-edge remainder.**  The right edge (`Re = 2`) is absorbed by vertical additivity (its zeta
non-vanishing and integrability are THEOREMS), the horizontals by the route's definition.  At
`σ0` in zero-free territory the left edge is computable (reflection/primes); as `σ0 → 1/2` this
is the classical "`S` counts the zeros".  conjecture1_proved = False. -/

/-- The continuous argument of `ζ` at `σ + iT` along `2 → 2+iT → σ+iT` (branch-free). -/
noncomputable def argZeta (σ T : ℝ) : ℝ :=
  argChangeVert riemannZeta 2 0 T + argChangeHoriz riemannZeta T 2 σ

theorem riemannS_eq_argZeta (T : ℝ) : riemannS T = argZeta (1/2) T / π := rfl

/-- `logDeriv ζ` is continuous along the line `Re = 2` (analyticity + kernel non-vanishing). -/
theorem continuous_logDeriv_zeta_line2 :
    Continuous (fun y : ℝ => logDeriv riemannZeta ((2 : ℂ) + y * I)) := by
  have hne1 : ∀ y : ℝ, ((2 : ℂ) + y * I) ≠ 1 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
  have hana : ∀ y : ℝ, AnalyticAt ℂ riemannZeta ((2 : ℂ) + y * I) := fun y =>
    analyticOn_riemannZeta _ (hne1 y)
  have hnz : ∀ y : ℝ, riemannZeta ((2 : ℂ) + y * I) ≠ 0 := by
    intro y
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  have heq : (fun y : ℝ => logDeriv riemannZeta ((2 : ℂ) + y * I))
      = fun y : ℝ => deriv riemannZeta ((2 : ℂ) + y * I) / riemannZeta ((2 : ℂ) + y * I) := by
    funext y
    rw [logDeriv_apply]
  rw [heq]
  have hpath : Continuous (fun y : ℝ => (2 : ℂ) + y * I) := by fun_prop
  refine Continuous.div ?_ ?_ hnz
  · have hc : (fun y : ℝ => deriv riemannZeta ((2 : ℂ) + y * I))
        = (deriv riemannZeta) ∘ (fun y : ℝ => (2 : ℂ) + y * I) := rfl
    rw [hc]
    exact continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (g := deriv riemannZeta) (f := fun t : ℝ => (2 : ℂ) + t * I)
        ((hana y).deriv.continuousAt) hpath.continuousAt
  · have hc : (fun y : ℝ => riemannZeta ((2 : ℂ) + y * I))
        = riemannZeta ∘ (fun y : ℝ => (2 : ℂ) + y * I) := rfl
    rw [hc]
    exact continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (2 : ℂ) + t * I)
        ((hana y).continuousAt) hpath.continuousAt

/-- Vertical additivity of the argument change along `Re = 2`. -/
theorem argChangeVert_zeta_line2_add (T0 T1 : ℝ) :
    argChangeVert riemannZeta 2 0 T1
      = argChangeVert riemannZeta 2 0 T0 + argChangeVert riemannZeta 2 T0 T1 := by
  unfold argChangeVert
  rw [show (((2:ℝ)) : ℂ) = (2 : ℂ) by norm_num]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_logDeriv_zeta_line2.intervalIntegrable 0 T0)
    (continuous_logDeriv_zeta_line2.intervalIntegrable T0 T1),
    Complex.add_re]

/-- **THE S-DIFFERENCE COUNTING IDENTITY** (RvM engine): for a box `[σ0, 2] × [T0, T1]` with
    admissible boundary, `2π·N_box = (argZeta σ0 T1 − argZeta σ0 T0) − argChangeVert ζ σ0 T0 T1`.
    The zero-count IS the jump of the continuous argument, minus the left-edge remainder. -/
theorem count_eq_argZeta_diff_sub_left
    (sigma0 T0 T1 : ℝ) (hsig : sigma0 ≤ 2) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    2 * π * (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ))
      = (argZeta sigma0 T1 - argZeta sigma0 T0) - argChangeVert riemannZeta sigma0 T0 T1 := by
  have hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((2 : ℂ) + ↑y * I) ≠ 0 := by
    intro y _
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  have hcnt := zeta_total_argChange_eq_count sigma0 2 T0 T1 hsig hT c R
    (by simpa using hbox_ball) hs1 hnzb hnzt (by simpa using hnzr) hnzl hins
  -- unfold the argZeta difference: the 0→T verticals telescope, the horizontals flip sign.
  have hAV := argChangeVert_zeta_line2_add T0 T1
  have hflip1 : argChangeHoriz riemannZeta T0 2 sigma0
      = - argChangeHoriz riemannZeta T0 sigma0 2 := by
    unfold argChangeHoriz
    rw [intervalIntegral.integral_symm]
    simp
  have hflip2 : argChangeHoriz riemannZeta T1 2 sigma0
      = - argChangeHoriz riemannZeta T1 sigma0 2 := by
    unfold argChangeHoriz
    rw [intervalIntegral.integral_symm]
    simp
  unfold argZeta
  rw [hAV, hflip1, hflip2]
  -- 2πN = AH(T0,σ0,2) − AH(T1,σ0,2) + AV(2,T0,T1) − AV(σ0,T0,T1)  [hcnt]
  -- goal: 2πN = [AV(2,0,T0)+AV(2,T0,T1) − AH(T1,σ0,2)] − [AV(2,0,T0) − AH(T0,σ0,2)] − AV(σ0,T0,T1)
  linarith [hcnt]

/-! ## Brick 13a (the FE-fold toolkit): log-derivatives under conjugation.

The FE-fold turns the left-edge argument change into mirror-edge data at NEGATIVE heights;
Schwarz reflection (`f(s̄) = conj (f s)`) folds those back to positive heights.  Kernel form:
Mathlib's `HasDerivAt.star_conj` gives the anti-holomorphic chain rule, whence for any
conj-symmetric `f`, `logDeriv f (s̄) = conj (logDeriv f s)` — instantiated for `ζ`
(`riemannZeta_conj`) and `Γℝ` (proved here from `Gamma_conj` + `exp_conj`).  Since
`Re ∘ conj = Re`, every `argChangeVert` at a negative height mirrors to its positive-height
twin — the fold's computability toolkit.  conjecture1_proved = False. -/

/-- Schwarz-reflection derivative: if `f (conj z) = conj (f z)` everywhere and `f` is
    differentiable at `s`, then `deriv f (conj s) = conj (deriv f s)`. -/
theorem deriv_conj_of_conj_symm {f : ℂ → ℂ}
    (hsymm : ∀ z : ℂ, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    {s : ℂ} (hdf : DifferentiableAt ℂ f s) :
    deriv f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv f s) := by
  have h1 := hdf.hasDerivAt.star_conj
  have hfun : (star ∘ f ∘ (starRingEnd ℂ)) = f := by
    funext z
    simp only [Function.comp_apply]
    rw [hsymm z]
    simp
  rw [hfun] at h1
  have h2 : (starRingEnd ℂ) (deriv f s) = star (deriv f s) := rfl
  rw [h2]
  exact h1.deriv

/-- `logDeriv` under conjugation, for conj-symmetric differentiable `f`. -/
theorem logDeriv_conj_of_conj_symm {f : ℂ → ℂ}
    (hsymm : ∀ z : ℂ, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    {s : ℂ} (hdf : DifferentiableAt ℂ f s) :
    logDeriv f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv f s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_conj_of_conj_symm hsymm hdf, hsymm s, ← map_div₀]

/-- **`ζ` log-derivative under conjugation** (`s ≠ 1`). -/
theorem logDeriv_zeta_conj {s : ℂ} (hs : s ≠ 1) :
    logDeriv riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv riemannZeta s) :=
  logDeriv_conj_of_conj_symm (fun z => riemannZeta_conj z) (differentiableAt_riemannZeta hs)

/-- `Γℝ` is conj-symmetric: `Γℝ(s̄) = conj (Γℝ s)` (real π-power via `exp_conj`, `Gamma_conj`). -/
theorem gammaR_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have h1 : Gammaℝ ((starRingEnd ℂ) s)
      = ZeroFreeBridge.gammaRArch ((starRingEnd ℂ) s)
        * Complex.Gamma ((starRingEnd ℂ) s / 2) := rfl
  have h2 : Gammaℝ s = ZeroFreeBridge.gammaRArch s * Complex.Gamma (s / 2) := rfl
  have h3 := congrFun ZeroFreeBridge.gammaRArch_exp ((starRingEnd ℂ) s)
  have h4 := congrFun ZeroFreeBridge.gammaRArch_exp s
  rw [h1, h2, h3, h4]
  have hlog : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log Real.pi_pos.le]
  have h2c : ((starRingEnd ℂ) (2 : ℂ)) = 2 := map_ofNat _ 2
  rw [map_mul, ← Complex.exp_conj, ← Complex.Gamma_conj]
  congr 1
  · congr 1
    rw [map_mul, hlog, Complex.conj_ofReal, map_div₀, map_neg, h2c]
  · congr 1
    rw [map_div₀, h2c]

/-- **`Γℝ` log-derivative under conjugation** (off the poles, via `Im ≠ 0` or `Γℝ ≠ 0`). -/
theorem logDeriv_gammaR_conj {s : ℂ} (hG : Gammaℝ s ≠ 0) :
    logDeriv Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv Gammaℝ s) := by
  have hGdiff : DifferentiableAt ℂ Gammaℝ s := by
    have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m hm
      apply hG
      rw [Complex.Gammaℝ_eq_zero_iff]
      exact ⟨m, by linear_combination 2 * hm⟩
    have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    have hB : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
        (deriv Complex.Gamma (s / 2) * (1 / 2)) s :=
      ((Complex.differentiableAt_Gamma _ hpole).hasDerivAt).comp s hhalf
    have hGdef : Gammaℝ = fun z : ℂ => ZeroFreeBridge.gammaRArch z * Complex.Gamma (z / 2) := rfl
    rw [hGdef]
    exact ((ZeroFreeBridge.gammaRArch_hasDerivAt s).differentiableAt).mul hB.differentiableAt
  exact logDeriv_conj_of_conj_symm gammaR_conj hGdiff

/-! ## Brick 13b-infra (the FE-fold edge-integrability): `logDeriv ζ` and `logDeriv Γℝ`
continuous along GENERAL vertical lines.

The symmetric fold's `integral_congr` needs the four edge integrands continuous on arbitrary
vertical segments — not just the `Re = 1/2`, `Re = 2` lines hardcoded in bricks 11–12.  These
generalize those to any `Re = σ` (`σ > 1` for `ζ`, `σ > 0` for `Γℝ`), via a reusable general
digamma continuity (`digamma_continuousAt_of_re_pos`, absent from Mathlib).  With them, every
`argChangeVert` in the fold is a well-defined integral of a continuous function.
conjecture1_proved = False. -/

/-- **General digamma continuity**: `ψ` is continuous at every `z` with `Re z > 0`
    (`ψ = Γ′/Γ`, `Γ` analytic and nonzero on the right half-plane). -/
theorem digamma_continuousAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.digamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    intro m hm
    rw [hm] at hw
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hw
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hana : AnalyticAt ℂ Complex.Gamma z := (hdiff.analyticOnNhd hopen) z hz
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have heq : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [heq]
  exact (hana.deriv.continuousAt).div hana.continuousAt hne

/-- **`logDeriv Γℝ` continuous along the vertical line `Re = σ`, for `σ > 0`** (fold Γ-edges). -/
theorem continuous_logDeriv_gammaR_vLine {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun y : ℝ => logDeriv Gammaℝ ((σ : ℂ) + y * I)) := by
  have hfun : (fun y : ℝ => logDeriv Gammaℝ ((σ : ℂ) + y * I))
      = fun y : ℝ => -(Real.log Real.pi : ℂ) / 2
          + (1 / 2) * Complex.digamma (((σ : ℂ) + y * I) / 2) := by
    funext y
    have hs : 0 < (((σ : ℂ) + y * I) / 2).re := by
      simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
      positivity
    rw [ZeroFreeBridge.logDeriv_gammaR _ hs]
  rw [hfun]
  refine continuous_const.add (continuous_const.mul ?_)
  have hpath : Continuous (fun y : ℝ => ((σ : ℂ) + y * I) / 2) := by fun_prop
  have hc : (fun y : ℝ => Complex.digamma (((σ : ℂ) + y * I) / 2))
      = Complex.digamma ∘ (fun y : ℝ => ((σ : ℂ) + y * I) / 2) := rfl
  rw [hc]
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hzre : 0 < (((σ : ℂ) + y * I) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    positivity
  exact ContinuousAt.comp (g := Complex.digamma) (f := fun t : ℝ => ((σ : ℂ) + t * I) / 2)
    (digamma_continuousAt_of_re_pos hzre) hpath.continuousAt

/-- **`logDeriv ζ` continuous along the vertical line `Re = σ`, for `σ > 1`** (fold ζ-edges). -/
theorem continuous_logDeriv_zeta_vLine {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun y : ℝ => logDeriv riemannZeta ((σ : ℂ) + y * I)) := by
  have hne1 : ∀ y : ℝ, ((σ : ℂ) + y * I) ≠ 1 := by
    intro y h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re] at this
    norm_num at this
    linarith
  have hana : ∀ y : ℝ, AnalyticAt ℂ riemannZeta ((σ : ℂ) + y * I) := fun y =>
    analyticOn_riemannZeta _ (hne1 y)
  have hnz : ∀ y : ℝ, riemannZeta ((σ : ℂ) + y * I) ≠ 0 := by
    intro y
    apply riemannZeta_ne_zero_of_one_le_re
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have heq : (fun y : ℝ => logDeriv riemannZeta ((σ : ℂ) + y * I))
      = fun y : ℝ => deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I) := by
    funext y; rw [logDeriv_apply]
  rw [heq]
  have hpath : Continuous (fun y : ℝ => (σ : ℂ) + y * I) := by fun_prop
  refine Continuous.div ?_ ?_ hnz
  · have hc : (fun y : ℝ => deriv riemannZeta ((σ : ℂ) + y * I))
        = (deriv riemannZeta) ∘ (fun y : ℝ => (σ : ℂ) + y * I) := rfl
    rw [hc]
    exact continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (g := deriv riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I)
        ((hana y).deriv.continuousAt) hpath.continuousAt
  · have hc : (fun y : ℝ => riemannZeta ((σ : ℂ) + y * I))
        = riemannZeta ∘ (fun y : ℝ => (σ : ℂ) + y * I) := rfl
    rw [hc]
    exact continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I)
        ((hana y).continuousAt) hpath.continuousAt

/-! ## Brick 13b (THE SYMMETRIC FOLD IDENTITY): the left-edge argument change equals minus the
Archimedean argument changes, both edges at the same height.

Reflection (`logDeriv_zeta_reflect`) sends `σ₀ + iy ↦ (1−σ₀) − iy`; the conjugation toolkit
(`logDeriv_zeta_conj`, `logDeriv_gammaR_conj`) folds that `−iy` back to `+iy`, so the mirror
data lands on the `Re = 1−σ₀` line at the SAME positive height.  Taking real parts (RvM's
argument changes) gives, for `σ₀ < 0` and `y > 0`, the pointwise integrand of the fold
`AV(ζ,σ₀) + AV(ζ,1−σ₀) = −AV(Γℝ,σ₀) − AV(Γℝ,1−σ₀)`.  Every hypothesis is DERIVED: `ζ(σ₀+iy) ≠ 0`
from the strip-location theorem; `ζ((1−σ₀)+iy) ≠ 0` from `Re > 1`; the `Γℝ` non-vanishings from
`Im ≠ 0`.  conjecture1_proved = False. -/

/-- `Γℝ(s) ≠ 0` off the real axis (`s/2` avoids the Γ-poles). -/
theorem gammaR_ne_zero_of_im_ne {s : ℂ} (him : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Complex.Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  apply him
  rw [hn]
  simp

/-- **THE SYMMETRIC FOLD, pointwise**: for `σ₀ < 0`, `0 < y`, the sum of the `ζ` argument-change
    integrands on the reflected pair of lines equals minus the sum of the `Γℝ` ones. -/
theorem fold_pointwise {sigma0 y : ℝ} (hσ : sigma0 < 0) (hy : 0 < y) :
    (logDeriv riemannZeta ((sigma0 : ℂ) + y * I)).re
        + (logDeriv riemannZeta (((1 - sigma0 : ℝ) : ℂ) + y * I)).re
      = -(logDeriv Gammaℝ ((sigma0 : ℂ) + y * I)).re
        - (logDeriv Gammaℝ (((1 - sigma0 : ℝ) : ℂ) + y * I)).re := by
  set s : ℂ := (sigma0 : ℂ) + y * I with hs
  set s' : ℂ := ((1 - sigma0 : ℝ) : ℂ) + y * I with hs'
  have hsim : s.im = y := by rw [hs]; simp
  have hs'im : s'.im = y := by rw [hs']; simp
  have hsre : s.re = sigma0 := by rw [hs]; simp
  have hs're : s'.re = 1 - sigma0 := by rw [hs']; simp
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s' := by
    rw [hs, hs']
    apply Complex.ext <;> simp <;> ring
  have hsim0 : s.im ≠ 0 := by rw [hsim]; exact ne_of_gt hy
  have hs'im0 : s'.im ≠ 0 := by rw [hs'im]; exact ne_of_gt hy
  have hs0 : s ≠ 0 := fun h => hsim0 (by rw [h]; simp)
  have hs1 : s ≠ 1 := fun h => hsim0 (by rw [h]; simp)
  have hs'1 : s' ≠ 1 := fun h => hs'im0 (by rw [h]; simp)
  have hζs : riemannZeta s ≠ 0 := fun hz =>
    absurd (ZetaZeroConfinement.zeta_zero_re_mem_strip hsim0 hz).1 (by rw [hsre]; linarith)
  have hre'gt : 1 < s'.re := by rw [hs're]; linarith
  have hζ1s : riemannZeta (1 - s) ≠ 0 := by
    rw [hconj, riemannZeta_conj]
    exact fun h => (riemannZeta_ne_zero_of_one_le_re (le_of_lt hre'gt)) (by
      have := congrArg (starRingEnd ℂ) h; simpa using this)
  have hGs : Gammaℝ s ≠ 0 := gammaR_ne_zero_of_im_ne hsim0
  have hG1s : Gammaℝ (1 - s) ≠ 0 := by
    rw [hconj]; exact gammaR_ne_zero_of_im_ne (by rw [Complex.conj_im]; exact neg_ne_zero.mpr hs'im0)
  have hrefl := logDeriv_zeta_reflect hs0 hs1 hζs hζ1s hGs hG1s
  have hζfold : logDeriv riemannZeta (1 - s) = (starRingEnd ℂ) (logDeriv riemannZeta s') := by
    rw [hconj]; exact logDeriv_zeta_conj hs'1
  have hGfold : logDeriv Gammaℝ (1 - s) = (starRingEnd ℂ) (logDeriv Gammaℝ s') := by
    rw [hconj]; exact logDeriv_gammaR_conj (gammaR_ne_zero_of_im_ne hs'im0)
  rw [hζfold, hGfold] at hrefl
  have hre := congrArg Complex.re hrefl
  simp only [Complex.sub_re, Complex.neg_re, Complex.conj_re] at hre
  linarith [hre]

/-! ## Brick 13b-wrap (THE FOLD, integral form): `AV(ζ,σ₀)+AV(ζ,1−σ₀) = −AV(Γℝ,σ₀)−AV(Γℝ,1−σ₀)`.

Integrate `fold_pointwise` over a positive-height segment `0 < T0 ≤ T1` (the classical
zero-avoiding requirement).  Edge continuity off the real axis: `Γℝ` analytic where `Im ≠ 0`
(the `Γ`-poles are real), `ζ` continuous off its zeros; `intervalIntegral.integral_congr` +
`intervalIntegral_re` do the rest.  conjecture1_proved = False. -/

/-- `Γℝ` analytic off the real axis (`s/2` avoids the real `Γ`-poles). -/
theorem gammaR_analyticAt_of_im_ne {s : ℂ} (him : s.im ≠ 0) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {w : ℂ | w.im ≠ 0} :=
    isOpen_compl_singleton.preimage Complex.continuous_im
  have hdiff : DifferentiableOn ℂ Gammaℝ {w : ℂ | w.im ≠ 0} := by
    intro w hw
    have hwim : w.im ≠ 0 := hw
    have hpole : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
      intro m hm
      apply hwim
      have := congrArg Complex.im hm
      simp only [Complex.div_im, Complex.neg_im, Complex.natCast_im] at this
      simpa using this
    have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) w := by
      simpa using (hasDerivAt_id w).div_const 2
    have hB : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
        (deriv Complex.Gamma (w / 2) * (1 / 2)) w :=
      ((Complex.differentiableAt_Gamma _ hpole).hasDerivAt).comp w hhalf
    have hGdef : Gammaℝ = fun z : ℂ => ZeroFreeBridge.gammaRArch z * Complex.Gamma (z / 2) := rfl
    rw [hGdef]
    exact (((ZeroFreeBridge.gammaRArch_hasDerivAt w).differentiableAt).mul
      hB.differentiableAt).differentiableWithinAt
  exact (hdiff.analyticOnNhd hopen) s him

/-- `logDeriv Γℝ` continuous at any off-real point. -/
theorem logDeriv_gammaR_continuousAt_of_im_ne {s : ℂ} (him : s.im ≠ 0) :
    ContinuousAt (logDeriv Gammaℝ) s := by
  have hana := gammaR_analyticAt_of_im_ne him
  have hne := gammaR_ne_zero_of_im_ne him
  have heq : logDeriv Gammaℝ = fun w => deriv Gammaℝ w / Gammaℝ w := by
    funext w; rw [logDeriv_apply]
  rw [heq]
  exact (hana.deriv.continuousAt).div hana.continuousAt hne

/-- `logDeriv Γℝ` continuous on any positive-height vertical segment (ANY `σ`). -/
theorem continuousOn_logDeriv_gammaR_seg (σ T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1) :
    ContinuousOn (fun y : ℝ => logDeriv Gammaℝ ((σ : ℂ) + y * I)) (Set.uIcc T0 T1) := by
  rw [Set.uIcc_of_le hT]
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le hT0 hy.1
  have him : ((σ : ℂ) + y * I).im ≠ 0 := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simpa using ne_of_gt hy0
  exact (ContinuousAt.comp (g := logDeriv Gammaℝ) (f := fun t : ℝ => (σ : ℂ) + t * I)
    (logDeriv_gammaR_continuousAt_of_im_ne him) (by fun_prop)).continuousWithinAt

/-- `logDeriv ζ` continuous on a positive-height segment where `ζ` is nonvanishing. -/
theorem continuousOn_logDeriv_zeta_seg (σ T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (hz : ∀ y ∈ Set.Icc T0 T1, riemannZeta ((σ : ℂ) + y * I) ≠ 0) :
    ContinuousOn (fun y : ℝ => logDeriv riemannZeta ((σ : ℂ) + y * I)) (Set.uIcc T0 T1) := by
  rw [Set.uIcc_of_le hT]
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le hT0 hy.1
  have hne1 : ((σ : ℂ) + y * I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_im] at this
    exact absurd (by simpa using this) (ne_of_gt hy0)
  have hana : AnalyticAt ℂ riemannZeta ((σ : ℂ) + y * I) := analyticOn_riemannZeta _ hne1
  have hcAt : ContinuousAt (logDeriv riemannZeta) ((σ : ℂ) + y * I) := by
    have heq : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
      funext w; rw [logDeriv_apply]
    rw [heq]
    exact (hana.deriv.continuousAt).div hana.continuousAt (hz y hy)
  exact (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I)
    hcAt (by fun_prop)).continuousWithinAt

/-- **THE FOLD, integral form** (RvM stone 13b): for `σ₀ < 0` and a positive-height segment,
    `AV(ζ,σ₀) + AV(ζ,1−σ₀) = −AV(Γℝ,σ₀) − AV(Γℝ,1−σ₀)`. -/
theorem argChangeVert_fold {sigma0 T0 T1 : ℝ} (hσ : sigma0 < 0) (hT0 : 0 < T0) (hT : T0 ≤ T1) :
    argChangeVert riemannZeta sigma0 T0 T1 + argChangeVert riemannZeta (1 - sigma0) T0 T1
      = - argChangeVert Gammaℝ sigma0 T0 T1 - argChangeVert Gammaℝ (1 - sigma0) T0 T1 := by
  -- nonvanishing on the two ζ lines
  have hzσ0 : ∀ y ∈ Set.Icc T0 T1, riemannZeta ((sigma0 : ℂ) + y * I) ≠ 0 := by
    intro y hy hz
    have hy0 : 0 < y := lt_of_lt_of_le hT0 hy.1
    have him : ((sigma0 : ℂ) + y * I).im ≠ 0 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      simpa using ne_of_gt hy0
    have hre := (ZetaZeroConfinement.zeta_zero_re_mem_strip him hz).1
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at hre
    norm_num at hre
    linarith
  have hz1 : ∀ y ∈ Set.Icc T0 T1, riemannZeta (((1 - sigma0 : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro y _
    apply riemannZeta_ne_zero_of_one_le_re
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    linarith
  -- complex integrands continuousOn the segment
  have cζ0 := continuousOn_logDeriv_zeta_seg sigma0 T0 T1 hT0 hT hzσ0
  have cζ1 := continuousOn_logDeriv_zeta_seg (1 - sigma0) T0 T1 hT0 hT hz1
  have cΓ0 := continuousOn_logDeriv_gammaR_seg sigma0 T0 T1 hT0 hT
  have cΓ1 := continuousOn_logDeriv_gammaR_seg (1 - sigma0) T0 T1 hT0 hT
  -- complex integrabilities
  have iζ0 := cζ0.intervalIntegrable (μ := MeasureTheory.volume)
  have iζ1 := cζ1.intervalIntegrable (μ := MeasureTheory.volume)
  have iΓ0 := cΓ0.intervalIntegrable (μ := MeasureTheory.volume)
  have iΓ1 := cΓ1.intervalIntegrable (μ := MeasureTheory.volume)
  -- real (.re) integrabilities
  have rζ0 : IntervalIntegrable (fun y : ℝ => (logDeriv riemannZeta ((sigma0 : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 :=
    (Complex.continuous_re.comp_continuousOn cζ0).intervalIntegrable
  have rζ1 : IntervalIntegrable (fun y : ℝ => (logDeriv riemannZeta (((1 - sigma0 : ℝ) : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 :=
    (Complex.continuous_re.comp_continuousOn cζ1).intervalIntegrable
  have rΓ0 : IntervalIntegrable (fun y : ℝ => (logDeriv Gammaℝ ((sigma0 : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 :=
    (Complex.continuous_re.comp_continuousOn cΓ0).intervalIntegrable
  have rΓ1 : IntervalIntegrable (fun y : ℝ => (logDeriv Gammaℝ (((1 - sigma0 : ℝ) : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 :=
    (Complex.continuous_re.comp_continuousOn cΓ1).intervalIntegrable
  have rnegΓ0 : IntervalIntegrable (fun y : ℝ => -(logDeriv Gammaℝ ((sigma0 : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 := rΓ0.neg
  have rnegΓ1 : IntervalIntegrable (fun y : ℝ => -(logDeriv Gammaℝ (((1 - sigma0 : ℝ) : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 := rΓ1.neg
  -- (∫ f).re = ∫ f.re, four edges
  have eRe : ∀ (F : ℝ → ℂ),
      IntervalIntegrable F MeasureTheory.volume T0 T1 →
      (∫ y in T0..T1, F y).re = ∫ y in T0..T1, (F y).re := by
    intro F hI
    have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hI
    simp only [RCLike.re_to_complex] at this
    exact this.symm
  -- the pointwise fold, integrated
  have main : (∫ y in T0..T1, ((logDeriv riemannZeta ((sigma0 : ℂ) + y * I)).re
        + (logDeriv riemannZeta (((1 - sigma0 : ℝ) : ℂ) + y * I)).re))
      = ∫ y in T0..T1, (-(logDeriv Gammaℝ ((sigma0 : ℂ) + y * I)).re
        + -(logDeriv Gammaℝ (((1 - sigma0 : ℝ) : ℂ) + y * I)).re) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hT] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hT0 hy.1
    have hfp := fold_pointwise hσ hy0
    linarith [hfp]
  -- split LHS of `main` (a genuine sum of integrals)
  rw [intervalIntegral.integral_add rζ0 rζ1] at main
  -- split RHS of `main`: ∫(-a + -b) = ∫(-a) + ∫(-b) = -∫a - ∫b
  have hRHS : (∫ y in T0..T1, (-(logDeriv Gammaℝ ((sigma0 : ℂ) + y * I)).re
        + -(logDeriv Gammaℝ (((1 - sigma0 : ℝ) : ℂ) + y * I)).re))
      = -(∫ y in T0..T1, (logDeriv Gammaℝ ((sigma0 : ℂ) + y * I)).re)
        - (∫ y in T0..T1, (logDeriv Gammaℝ (((1 - sigma0 : ℝ) : ℂ) + y * I)).re) := by
    rw [intervalIntegral.integral_add rnegΓ0 rnegΓ1,
        intervalIntegral.integral_neg, intervalIntegral.integral_neg]
    ring
  rw [hRHS] at main
  unfold argChangeVert
  rw [eRe _ iζ0, eRe _ iζ1, eRe _ iΓ0, eRe _ iΓ1]
  linarith [main]

/-! ## Brick 14 (THE POLE "+1"): the winding of the pole factor `(·−1)⁻¹`.

RvM's `+1` is the contribution of the `s(s−1)/2` factor of `ξ` — equivalently, the single simple
pole of `ζ` (or zero of `s−1`) at `s = 1`.  In argument-change vocabulary: the total continuous
argument change of `fun s => s − 1` counterclockwise around any box containing `1` is exactly `2π`
(winding number `1`).  Read off `rect_winding_generic` at `ρ = 1` via `logDeriv (·−1) = (·−1)⁻¹`
and `.im`.  conjecture1_proved = False. -/

/-- `logDeriv (fun s => s − c) = (· − c)⁻¹`. -/
theorem logDeriv_sub_const (c z : ℂ) : logDeriv (fun s : ℂ => s - c) z = (z - c)⁻¹ := by
  have hd : HasDerivAt (fun s : ℂ => s - c) 1 z := (hasDerivAt_id z).sub_const c
  rw [logDeriv_apply, hd.deriv, one_div]

/-- **THE POLE "+1"**: total argument change of `fun s => s − 1` around a box containing `1`
    equals `2π` (winding number `1`) — the `+1` of `N(T) = θ(T)/π + 1 + S(T)`. -/
theorem pole_total_argChange (sigma0 sigma1 T0 T1 : ℝ)
    (hre0 : sigma0 < 1) (hre1 : 1 < sigma1) (him0 : T0 < 0) (him1 : 0 < T1) :
    argChangeHoriz (fun s => s - 1) T0 sigma0 sigma1
        - argChangeHoriz (fun s => s - 1) T1 sigma0 sigma1
        + argChangeVert (fun s => s - 1) sigma1 T0 T1
        - argChangeVert (fun s => s - 1) sigma0 T0 T1
      = 2 * π := by
  have hlog : ∀ z : ℂ, logDeriv (fun s : ℂ => s - 1) z = (z - 1)⁻¹ := fun z => logDeriv_sub_const 1 z
  have hw := RHInBoxAnalytic.rect_winding_generic sigma0 sigma1 T0 T1 1
    (by simpa using hre0) (by simpa using hre1) (by simpa using him0) (by simpa using him1)
  unfold argChangeHoriz argChangeVert
  simp only [hlog]
  set A := ∫ x in sigma0..sigma1, ((↑x + (T0 : ℂ) * I) - 1)⁻¹ with hA
  set B := ∫ x in sigma0..sigma1, ((↑x + (T1 : ℂ) * I) - 1)⁻¹ with hB
  set C := ∫ y in T0..T1, (((sigma1 : ℂ) + ↑y * I) - 1)⁻¹ with hC
  set D := ∫ y in T0..T1, (((sigma0 : ℂ) + ↑y * I) - 1)⁻¹ with hD
  have him := congrArg Complex.im hw
  rw [show (A - B + I • C - I • D).im = A.im - B.im + C.re - D.re by
        simp only [Complex.sub_im, Complex.add_im, smul_eq_mul, Complex.mul_im,
          Complex.I_im, Complex.I_re, one_mul, zero_mul, zero_add, mul_zero]] at him
  rw [show (2 * (↑π : ℂ) * I).im = 2 * π by
        simp only [Complex.mul_im, Complex.mul_re, Complex.I_im, Complex.I_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
        ring] at him
  linarith [him]

/-! ## Brick 15 (THE RvM BAND-DIFFERENCE CAPSTONE): the zero-count of a height band as explicit
edge argument-changes.

Combining the four RvM ingredients on the classical symmetric rectangle `[−1, 2] × [T0, T1]`
(`σ₀ = −1` ⟹ `1 − σ₀ = 2`, so the fold's mirror line IS the right edge):

  `2π · N_band  =  2·AV(ζ,2) + AH(ζ,T1,·,−1) − AH(ζ,T0,·,−1) + AV(Γℝ,−1) + AV(Γℝ,2)`

— `count_eq_argZeta_diff_sub_left` gives the count as the argZeta jump minus the left edge;
`argChangeVert_zeta_line2_add` telescopes the `Re = 2` verticals; `argChangeVert_fold` eliminates
the left edge in favour of the right edge + the two Archimedean edges.  This is the DIFFERENCE
(band) form of Riemann–von Mangoldt — the exact object the tiling/Turing height-ladder consumes
(`N(T1) − N(T0)`); the pole `+1` correctly does NOT appear (the pole `s = 1` sits at height `0`,
below the band `0 < T0`).  The full `N(T) = θ(T)/π + 1 + S(T)` is the `T0 → 0⁺` limit with the
real-axis base (where `pole_total_argChange` supplies the `+1`) and the ξ-doubling that identifies
the edge Archimedean terms with `θ` on the critical line — the honestly-remaining geometric
reduction.  conjecture1_proved = False. -/

/-- **RvM, band-difference form**: the ζ-zero count of `[−1,2] × [T0,T1]` (positive band) as an
    explicit combination of ζ- and Γℝ-argument-changes on the box edges. -/
theorem zero_count_band_edge_decomp (T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    2 * π * (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ))
      = 2 * argChangeVert riemannZeta 2 T0 T1
        + argChangeHoriz riemannZeta T1 2 (-1) - argChangeHoriz riemannZeta T0 2 (-1)
        + argChangeVert Gammaℝ (-1) T0 T1 + argChangeVert Gammaℝ 2 T0 T1 := by
  have hcount := count_eq_argZeta_diff_sub_left (-1) T0 T1 (by norm_num) hT c R
    hbox_ball hs1 hnzb hnzt hnzl hins
  have hfold := argChangeVert_fold (sigma0 := -1) (by norm_num) hT0 hT
  -- fold at σ₀ = -1 : 1 - (-1) = 2
  rw [show (1 : ℝ) - (-1) = 2 by norm_num] at hfold
  -- expand argZeta and telescope the Re = 2 verticals
  have hadd := argChangeVert_zeta_line2_add T0 T1
  unfold argZeta at hcount
  -- argZeta (-1) T1 - argZeta (-1) T0
  --   = (AV(ζ,2,0,T1) + AH(ζ,T1,2,-1)) - (AV(ζ,2,0,T0) + AH(ζ,T0,2,-1))
  -- AV(ζ,2,0,T1) - AV(ζ,2,0,T0) = AV(ζ,2,T0,T1)   [hadd]
  linarith [hcount, hfold, hadd]

/-! ## ξ-DOUBLING SESSION, step 1: the entire completed-zeta log-derivative reflection.

`Λ₀ = completedRiemannZeta₀` is ENTIRE (`differentiable_completedZeta₀`) with the clean functional
equation `Λ₀(1−s) = Λ₀(s)` (`completedRiemannZeta₀_one_sub`) — no `Γℝ` factor, no poles at `0, 1`.
Differentiating the FE gives the reflection identity `logDeriv Λ₀ (1−s) = −logDeriv Λ₀ s`, valid
everywhere (junk-equal at zeros).

CORRECTION (2026-09-09): an earlier version of this note claimed "Λ₀'s zeros in the strip are
exactly the nontrivial ζ-zeros".  That is FALSE.  `completedRiemannZeta_eq` gives
`Λ = Λ₀ − 1/s − 1/(1−s)` with `Λ = Γℝ·ζ`, so at a nontrivial zero `ρ` (where `Λ(ρ) = 0`) one has
`Λ₀(ρ) = 1/ρ + 1/(1−ρ) = 1/(ρ(1−ρ)) ≠ 0`.  The ENTIRE function carrying the nontrivial zeros is
`ξ(s) = ½ s(s−1) Λ(s) = ½ s(s−1) Λ₀(s) + ½`, NOT `Λ₀` itself.  Consequently a `Λ₀`
argument-principle count would count the WRONG set — the correct count side is the `ζ` argument
principle already assembled (`bd_logDeriv_zeta_eq_count` → `zero_count_band_edge_decomp`).  The
reflection/fold lemmas below remain TRUE (pure FE + conjugation identities, no zero claim) but are
NOT on the RvM critical path; they are kept as honest, verified auxiliary identities.
conjecture1_proved = False. -/

/-- **The entire completed-zeta reflection**: `logDeriv Λ₀ (1−s) = −logDeriv Λ₀ s`. -/
theorem logDeriv_completedZeta₀_reflect (s : ℂ) :
    logDeriv completedRiemannZeta₀ (1 - s) = - logDeriv completedRiemannZeta₀ s := by
  have hsymm : (fun z : ℂ => completedRiemannZeta₀ (1 - z)) = completedRiemannZeta₀ :=
    funext completedRiemannZeta₀_one_sub
  have hd : DifferentiableAt ℂ completedRiemannZeta₀ (1 - s) :=
    differentiable_completedZeta₀ _
  have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have hcomp : HasDerivAt (fun z : ℂ => completedRiemannZeta₀ (1 - z))
      (deriv completedRiemannZeta₀ (1 - s) * (-1)) s :=
    hd.hasDerivAt.comp s hinner
  have h1 := hcomp.deriv
  rw [hsymm] at h1
  have hkey : deriv completedRiemannZeta₀ (1 - s) = - deriv completedRiemannZeta₀ s := by
    linear_combination h1
  rw [logDeriv_apply, logDeriv_apply, completedRiemannZeta₀_one_sub, hkey]
  ring

/-! ## ξ-DOUBLING SESSION, step 2: the entire fold — Λ₀ argument-change is anti-symmetric across
`Re = 1/2`, with NO Archimedean remainder.

`Λ₀` is conj-symmetric (`ZetaZeroLocalization.completedRiemannZeta₀_conj`) and entire, so the
reflection (step 1) + conjugation fold to the SAME positive height give, for ALL `s`:

  `Re(logDeriv Λ₀ (σ+iy)) + Re(logDeriv Λ₀ ((1−σ)+iy)) = 0`

— RHS `0`, no `σ`/`y` constraints, no `Γℝ` terms (they live inside `Λ₀`).  A clean anti-symmetry of
`Λ₀`'s log-derivative across the critical line.  NB (see the step-1 CORRECTION): this folds `Λ₀`'s
OWN argument change, and `Λ₀`'s zeros are NOT the nontrivial ζ-zeros, so this is a true auxiliary
identity rather than an RvM-count ingredient.  The RvM fold that IS on the critical path is
`argChangeVert_fold` (the `ζ + Γℝ` split), already wired into `zero_count_band_edge_decomp`.
conjecture1_proved = False. -/

/-- `Λ₀` log-derivative under conjugation. -/
theorem logDeriv_completedZeta₀_conj (s : ℂ) :
    logDeriv completedRiemannZeta₀ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (logDeriv completedRiemannZeta₀ s) :=
  logDeriv_conj_of_conj_symm (fun z => ZetaZeroLocalization.completedRiemannZeta₀_conj z)
    (differentiable_completedZeta₀ s)

/-- **THE ENTIRE FOLD, pointwise**: `Λ₀`'s argument-change integrand is anti-symmetric across the
    critical line — sum over the reflected pair of lines is `0`, for every `σ, y`. -/
theorem fold_pointwise_zeta₀ (sigma y : ℝ) :
    (logDeriv completedRiemannZeta₀ ((sigma : ℂ) + y * I)).re
      + (logDeriv completedRiemannZeta₀ (((1 - sigma : ℝ) : ℂ) + y * I)).re = 0 := by
  set s : ℂ := (sigma : ℂ) + y * I with hs
  set s' : ℂ := ((1 - sigma : ℝ) : ℂ) + y * I with hs'
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s' := by
    rw [hs, hs']
    apply Complex.ext <;> simp <;> ring
  have hrefl := logDeriv_completedZeta₀_reflect s
  rw [hconj, logDeriv_completedZeta₀_conj s'] at hrefl
  have hre := congrArg Complex.re hrefl
  simp only [Complex.conj_re, Complex.neg_re] at hre
  linarith [hre]

/-! ## ξ-DOUBLING SESSION, step 4: the θ/S split of the completed-zeta argument change.

The RvM decomposition `N(T) = θ(T)/π + 1 + S(T)` is, structurally, the statement that the
argument change of the completed zeta up a vertical line splits as `Γℝ-part (→ θ) + ζ-part (→ πS)`.
That split is exactly `logDeriv_zeta_add_gammaR` integrated: on any positive-height vertical segment
where `ζ` is nonvanishing (`Γℝ ≠ 0` and `s ∉ {0,1}` are AUTOMATIC there, from `Im ≠ 0`),

  `AV(Λ, σ) = AV(ζ, σ) + AV(Γℝ, σ)`      (`argChangeVert_completedZeta_split`)

with `Λ = completedRiemannZeta`.  Specialised to the critical line and combined with
`theta_eq_argChangeVert_gammaR` (θ IS `AV(Γℝ, 1/2)`) and the Γℝ-line additivity, this gives the
**band form of RvM's θ/S structure, kernel-exact**:

  `AV(Λ, 1/2, T0, T1) = AV(ζ, 1/2, T0, T1) + (θ T1 − θ T0)`
      (`completedZeta_argChange_critical_eq_zeta_add_theta`)

— the completed-zeta argument change up a critical-line band is the ζ argument change (which is
`π·ΔS`) plus the θ increment.  This is the honest θ/S identification: the Archimedean part of the
completed-zeta winding IS `θ`, the ζ part IS `πS`.  The literal `N(T) = θ/π + 1 + S` (the `T0 → 0⁺`
base case, where `pole_total_argChange` supplies the `+1`, and the reorganisation onto the
zero-avoiding `S`-path) remains the honestly-scoped remainder.  conjecture1_proved = False. -/

/-- **The completed-zeta vertical argument-change split** (step 4 engine): on a positive-height
    segment where `ζ` is nonvanishing, `AV(Λ, σ) = AV(ζ, σ) + AV(Γℝ, σ)`.  The `Γℝ ≠ 0` and
    `s ∉ {0,1}` side-conditions of `logDeriv_zeta_add_gammaR` are discharged automatically from
    `Im ≠ 0` (positive height). -/
theorem argChangeVert_completedZeta_split (σ T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (hζ : ∀ y ∈ Set.Icc T0 T1, riemannZeta ((σ : ℂ) + y * I) ≠ 0) :
    argChangeVert completedRiemannZeta σ T0 T1
      = argChangeVert riemannZeta σ T0 T1 + argChangeVert Gammaℝ σ T0 T1 := by
  have cζ := continuousOn_logDeriv_zeta_seg σ T0 T1 hT0 hT hζ
  have cΓ := continuousOn_logDeriv_gammaR_seg σ T0 T1 hT0 hT
  have iζ := cζ.intervalIntegrable (μ := MeasureTheory.volume)
  have iΓ := cΓ.intervalIntegrable (μ := MeasureTheory.volume)
  have hpt : Set.EqOn (fun y : ℝ => logDeriv completedRiemannZeta ((σ : ℂ) + y * I))
      (fun y : ℝ => logDeriv riemannZeta ((σ : ℂ) + y * I)
        + logDeriv Gammaℝ ((σ : ℂ) + y * I)) (Set.uIcc T0 T1) := by
    intro y hy
    rw [Set.uIcc_of_le hT] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hT0 hy.1
    have him : ((σ : ℂ) + y * I).im ≠ 0 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      simpa using ne_of_gt hy0
    have hs0 : ((σ : ℂ) + y * I) ≠ 0 := by
      intro h; apply him; rw [h]; simp
    have hs1 : ((σ : ℂ) + y * I) ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.one_im] at hi
      exact absurd (by simpa using hi) (ne_of_gt hy0)
    have hGne : Gammaℝ ((σ : ℂ) + y * I) ≠ 0 := gammaR_ne_zero_of_im_ne him
    exact logDeriv_zeta_add_gammaR hs0 hs1 (hζ y hy) hGne
  unfold argChangeVert
  have hcongr : (∫ y in T0..T1, logDeriv completedRiemannZeta ((σ : ℂ) + y * I))
      = ∫ y in T0..T1, (logDeriv riemannZeta ((σ : ℂ) + y * I)
          + logDeriv Gammaℝ ((σ : ℂ) + y * I)) :=
    intervalIntegral.integral_congr hpt
  rw [hcongr, intervalIntegral.integral_add iζ iΓ, Complex.add_re]

/-- Γℝ-line argument-change additivity (θ increment), from the whole-line continuity of
    `logDeriv Γℝ` on the critical line — valid down to height `0` (no `Γℝ` pole/zero there). -/
theorem argChangeVert_gammaR_line_add (T0 T1 : ℝ) :
    argChangeVert Gammaℝ (1/2) 0 T1
      = argChangeVert Gammaℝ (1/2) 0 T0 + argChangeVert Gammaℝ (1/2) T0 T1 := by
  unfold argChangeVert
  rw [show (((1/2 : ℝ)) : ℂ) = (1/2 : ℂ) by norm_num]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_logDeriv_gammaR_line.intervalIntegrable 0 T0)
    (continuous_logDeriv_gammaR_line.intervalIntegrable T0 T1),
    Complex.add_re]

/-- **THE θ/S SPLIT ON A CRITICAL-LINE BAND** (RvM θ-identification): the completed-zeta argument
    change up `[T0,T1]` on the critical line is the `ζ` argument change (`= π·ΔS`) plus the `θ`
    increment.  This is the kernel-exact band form of the `θ + πS` structure of `N(T)`. -/
theorem completedZeta_argChange_critical_eq_zeta_add_theta (T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (hζ : ∀ y ∈ Set.Icc T0 T1, riemannZeta (((1/2 : ℝ) : ℂ) + y * I) ≠ 0) :
    argChangeVert completedRiemannZeta (1/2) T0 T1
      = argChangeVert riemannZeta (1/2) T0 T1
        + (ZeroFreeBridge.riemannSiegelTheta T1 - ZeroFreeBridge.riemannSiegelTheta T0) := by
  have hsplit := argChangeVert_completedZeta_split (1/2) T0 T1 hT0 hT hζ
  have hθadd := argChangeVert_gammaR_line_add T0 T1
  rw [theta_eq_argChangeVert_gammaR, theta_eq_argChangeVert_gammaR, hsplit]
  linarith [hθadd]

/-! ## The pole "+1", first stone: extracting `ζ`'s simple pole at `s = 1` from its log-derivative.

RvM's `+1` is the pole of `ζ` at `s = 1`.  The honest way to expose it (given the holomorphic
Blaschke machinery `bd_logDeriv_zeta_eq_count` STRUCTURALLY excludes `s = 1`, via `hs1 : 1 ∉ ball`)
is the meromorphic factorisation `ζ(s) = h(s)/(s − 1)` with `h(s) = ζ(s)·(s − 1)` analytic across
`s = 1` (`h(1) = 1`, the residue) and `h`'s zeros in the strip EXACTLY `ζ`'s zeros (`s − 1 ≠ 0`
off `1`).  Log-differentiating (where `ζ ≠ 0`, `s ≠ 1`):

  `(log ζ)′(s) = (log h)′(s) − (s − 1)⁻¹`

— the `−(s − 1)⁻¹` is the pole term whose box-winding is `−2π` (equivalently `+2π` for `h`'s
factor), i.e. the `+1`, supplied by `pole_total_argChange`.  This is the pointwise stone; the
remaining gap for the literal `+1` is the argument principle for `h` (entire across `s = 1`,
same zeros) — a meromorphic re-instantiation of the holomorphic core, honestly out of brick scope.
conjecture1_proved = False. -/

/-- **The pole extraction**: `(log ζ)′(s) = (log(ζ·(·−1)))′(s) − (s−1)⁻¹` for `s ≠ 1`, `ζ(s) ≠ 0`.
    Exhibits `ζ`'s simple pole at `s = 1` as the `−(s−1)⁻¹` term; `ζ·(·−1)` is the pole-free
    (analytic-across-`1`) companion with the same strip zeros. -/
theorem logDeriv_zeta_pole_extract {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s
      = logDeriv (fun z : ℂ => riemannZeta z * (z - 1)) s - (s - 1)⁻¹ := by
  have hd_zeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hd_sub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
    ((hasDerivAt_id s).sub_const 1).differentiableAt
  have hsub_ne : (s - 1) ≠ 0 := sub_ne_zero.mpr hs1
  have hmul : logDeriv (fun z : ℂ => riemannZeta z * (z - 1)) s
      = logDeriv riemannZeta s + (s - 1)⁻¹ := by
    have h := logDeriv_mul (f := riemannZeta) (g := fun z : ℂ => z - 1) s
      hζ hsub_ne hd_zeta hd_sub
    simp only [logDeriv_sub_const] at h
    exact h
  rw [hmul]; ring

/-! ## The pole-free companion `H = (s−1)·ζ(s)`, ENTIRE — the analytic foundation of the `+1`.

The pole-extraction (`logDeriv_zeta_pole_extract`) reduces the `+1` to the argument principle for
`h(s) = (s−1)·ζ(s)`, but that principle needs `h` ANALYTIC across `s = 1` (the holomorphic Blaschke
core cannot see a pole).  `ζ` has a simple pole at `1`, so `(s−1)·ζ(s)` has a REMOVABLE singularity:
`riemannZeta_residue_one` gives `(s−1)·ζ(s) → 1` as `s → 1`.  Defining

  `zetaPoleCompanion = update (fun z => (z−1)·ζ(z)) 1 1`

the removable-singularity theorem (`analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`)
makes it ENTIRE, with `H(1) = 1 ≠ 0` and zeros EXACTLY `ζ`'s non-`1` zeros.  This is the complete
analytic prerequisite the `h`-argument-principle stands on — everything except the (large)
re-instantiation of the Blaschke winding-count for `H`, which is the honestly-remaining lift.
conjecture1_proved = False. -/

/-- The pole-free companion `H(s) = (s−1)·ζ(s)`, with the removable singularity at `1` filled by
    its residue `H(1) = 1`. -/
noncomputable def zetaPoleCompanion : ℂ → ℂ :=
  Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

/-- Off `1`, the companion IS `(s−1)·ζ(s)`. -/
theorem zetaPoleCompanion_apply_of_ne {z : ℂ} (hz : z ≠ 1) :
    zetaPoleCompanion z = (z - 1) * riemannZeta z := by
  rw [zetaPoleCompanion, Function.update_of_ne hz]

/-- At `1` the companion equals the residue `1`. -/
theorem zetaPoleCompanion_one : zetaPoleCompanion 1 = 1 := by
  rw [zetaPoleCompanion, Function.update_self]

/-- **The removable singularity**: the companion is analytic at `1` (residue fills the pole). -/
theorem analyticAt_zetaPoleCompanion_one : AnalyticAt ℂ zetaPoleCompanion 1 := by
  apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz1 : z ≠ 1 := hz
    have heq : zetaPoleCompanion =ᶠ[nhds z] fun w : ℂ => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
      exact zetaPoleCompanion_apply_of_ne hw
    rw [heq.differentiableAt_iff]
    have hd_sub : DifferentiableAt ℂ (fun w : ℂ => w - 1) z :=
      ((hasDerivAt_id z).sub_const 1).differentiableAt
    exact hd_sub.mul (differentiableAt_riemannZeta hz1)
  · rw [zetaPoleCompanion, continuousAt_update_same]
    exact riemannZeta_residue_one

/-- **The companion is ENTIRE**: analytic at every point (product off `1`, removable at `1`). -/
theorem analyticAt_zetaPoleCompanion (z : ℂ) : AnalyticAt ℂ zetaPoleCompanion z := by
  rcases eq_or_ne z 1 with rfl | hz1
  · exact analyticAt_zetaPoleCompanion_one
  · have heq : zetaPoleCompanion =ᶠ[nhds z] fun w : ℂ => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
      exact zetaPoleCompanion_apply_of_ne hw
    have hsub : AnalyticAt ℂ (fun w : ℂ => w - 1) z :=
      (analyticAt_id).sub analyticAt_const
    exact (hsub.mul (analyticOn_riemannZeta z hz1)).congr heq.symm

/-- `H` is differentiable on all of `ℂ` (entire). -/
theorem differentiable_zetaPoleCompanion : Differentiable ℂ zetaPoleCompanion :=
  fun z => (analyticAt_zetaPoleCompanion z).differentiableAt

/-- **The zeros of the companion are EXACTLY `ζ`'s non-`1` zeros**: `H z = 0 ↔ z ≠ 1 ∧ ζ z = 0`.
    (`H(1) = 1 ≠ 0`; off `1`, `H = (s−1)·ζ` vanishes iff `ζ` does.) -/
theorem zetaPoleCompanion_eq_zero_iff {z : ℂ} :
    zetaPoleCompanion z = 0 ↔ z ≠ 1 ∧ riemannZeta z = 0 := by
  rcases eq_or_ne z 1 with rfl | hz1
  · rw [zetaPoleCompanion_one]
    simp
  · rw [zetaPoleCompanion_apply_of_ne hz1, mul_eq_zero]
    have hsub : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
    simp [hsub, hz1]

/-! ## The `H`-argument-principle prerequisites: the three ζ-specific inputs, ported to `H`.

The Blaschke winding-count core (`zeta_blaschke_split_ball`, `zeta_count_eq_winding_generic`) is
generic Mathlib machinery (`extract_zeros_poles`, `FactorizedRational`, `logDeriv_congr_of_codiscrete`)
wrapped around exactly THREE `ζ`-specific facts.  Here they are supplied for the ENTIRE companion
`H = zetaPoleCompanion`, which — being entire — satisfies each MORE cleanly than `ζ` (no pole to
dodge, so `H` is meromorphic on the whole CLOSED ball, and its order is finite on all of `ℂ`):

  1. `analyticOnNhd_zetaPoleCompanion`  — `H` analytic on any set (`ζ` needed `{1}ᶜ`).
  2. `meromorphicOrderAt_zetaPoleCompanion_ne_top` — order `≠ ⊤` EVERYWHERE (`ζ` needed `{1}ᶜ`;
     seeded here from `H(1) = 1 ≠ 0` on the connected `univ`).
  3. `divisor_zetaPoleCompanion_ball_support_finite` — divisor finite on any ball, via the GENERIC
     `MeromorphicOn.divisor_ball_support_finite` (`H` meromorphic on the closed ball since entire;
     `ζ` had to use the bespoke `IsCompact.inter_riemannZetaZeros_finite` to avoid `s = 1`).

With these three, the generic Blaschke count instantiates at `H` — the honestly-remaining lift being
the (mechanical, large) generic re-parameterisation of the winding-count proof itself.
conjecture1_proved = False. -/

/-- `H` is analytic on any set (entire). -/
theorem analyticOnNhd_zetaPoleCompanion (U : Set ℂ) :
    AnalyticOnNhd ℂ zetaPoleCompanion U :=
  fun z _ => analyticAt_zetaPoleCompanion z

/-- **Prerequisite 2**: `H`'s meromorphic order is finite everywhere (entire, not identically `0`
    since `H(1) = 1`).  Seeded from `1` on the connected `univ`. -/
theorem meromorphicOrderAt_zetaPoleCompanion_ne_top (u : ℂ) :
    meromorphicOrderAt zetaPoleCompanion u ≠ ⊤ := by
  have hMero : MeromorphicOn zetaPoleCompanion (Set.univ : Set ℂ) :=
    fun z _ => (analyticAt_zetaPoleCompanion z).meromorphicAt
  have hAt1 : AnalyticAt ℂ zetaPoleCompanion 1 := analyticAt_zetaPoleCompanion_one
  have hne1 : zetaPoleCompanion 1 ≠ 0 := by rw [zetaPoleCompanion_one]; exact one_ne_zero
  have hord1 : meromorphicOrderAt zetaPoleCompanion 1 ≠ ⊤ := by
    rw [hAt1.meromorphicOrderAt_eq, hAt1.analyticOrderAt_eq_zero.mpr hne1]; simp
  exact hMero.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 1) (Set.mem_univ u) hord1

/-- **Prerequisite 3**: `H`'s divisor has finite support on any ball — the GENERIC finiteness
    lemma applies because `H` is entire (hence meromorphic on the whole closed ball). -/
theorem divisor_zetaPoleCompanion_ball_support_finite (c : ℂ) (R : ℝ) :
    (MeromorphicOn.divisor zetaPoleCompanion (Metric.ball c R)).support.Finite := by
  have hMero : MeromorphicOn zetaPoleCompanion (Metric.closedBall c R) :=
    fun z _ => (analyticAt_zetaPoleCompanion z).meromorphicAt
  exact hMero.divisor_ball_support_finite

/-! ## THE PORT: the generic Blaschke split, then instantiated at `H`.

`zeta_blaschke_split_ball` (RHInBoxAnalytic) is written against `riemannZeta` by name but its proof
is generic Mathlib machinery over exactly the three prerequisites just supplied for `H`.  Here is
that proof re-parameterised to an ARBITRARY analytic `f` (`analytic_blaschke_split_ball`), then
instantiated at `H = zetaPoleCompanion` (`zetaPoleCompanion_blaschke_split_ball`).  The instantiation
is a one-liner precisely because the three prereqs are in hand.  This is the structural core of the
`h`-argument-principle; the remaining winding-count capstone is the same substitution over
`zeta_count_eq_winding_generic`.  conjecture1_proved = False. -/

/-- **Generic Blaschke split on a ball** (the `riemannZeta`-free `zeta_blaschke_split_ball`): for any
    `f` analytic on `ball c R` with finite divisor and finite meromorphic order, `logDeriv f`
    splits as a residue sum over its zeros plus a holomorphic `E`-part on the box. -/
theorem analytic_blaschke_split_ball
    (f : ℂ → ℂ) (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ)
    (hfU : AnalyticOnNhd ℂ f (Metric.ball c R))
    (h₂f : ∀ u ∈ Metric.ball c R, meromorphicOrderAt f u ≠ ⊤)
    (h₃f : (MeromorphicOn.divisor f (Metric.ball c R)).support.Finite)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R) :
    ∃ (E : ℂ → ℂ),
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ∧
      (∀ ρ ∈ h₃f.toFinset,
        (1 : ℤ) ≤ (MeromorphicOn.divisor f (Metric.ball c R) : ℂ → ℤ) ρ) ∧
      (∀ ρ ∈ Metric.ball c R, f ρ = 0 → ρ ∈ h₃f.toFinset) ∧
      (∀ z ∈ Metric.ball c R, f z ≠ 0 →
        logDeriv f z = (∑ ρ ∈ h₃f.toFinset,
          ((MeromorphicOn.divisor f (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) / (z - ρ)) + E z) := by
  set U := Metric.ball c R with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsPreconnected U := (convex_ball c R).isPreconnected
  have hbox_sub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact hbox_ball z hz.1 hz.2
  have hζU : AnalyticOnNhd ℂ f U := hfU
  have hMeroU : MeromorphicOn f U := hζU.meromorphicOn
  set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor f U : ℂ → ℤ) u with hDdef
  have hDnn : ∀ x, 0 ≤ D x := fun x => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζU x
  have hsupp_zero : ∀ u, u ∈ Function.support D → f u = 0 := by
    intro u hu
    rw [Function.mem_support] at hu
    have huU : u ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain
      (by rw [Function.mem_support]; exact hu)
    by_contra hne
    apply hu
    simp only [hDdef]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU huU,
      (hζU u huU).analyticOrderAt_eq_zero.mpr hne]; simp
  have hDfin : (Function.support D).Finite := h₃f
  have h₂f' : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := fun u => h₂f u.1 u.2
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hMeroU.extract_zeros_poles h₂f' h₃f
  set T : Finset ℂ := h₃f.toFinset with hTdef
  have hTmem : ∀ u, u ∈ T ↔ u ∈ (MeromorphicOn.divisor f U).support := by
    intro u; rw [hTdef, Set.Finite.mem_toFinset]
  have hPf_finset : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f U u))
      = fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) := by
    rw [Function.FactorizedRational.finprod_eq_fun (d := D) hDfin]
    ext w
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]
    · intro u hu
      rw [Finset.mem_coe, hTmem u]
      by_contra hc
      rw [Function.mem_support, not_not] at hc
      rw [Function.mem_mulSupport] at hu
      exact hu (by rw [show D u = (MeromorphicOn.divisor f U) u from rfl, hc, zpow_zero])
  set Pf : ℂ → ℂ := fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) with hPfdef
  have hPf_an : AnalyticOnNhd ℂ Pf U := by
    rw [← hPf_finset]; intro x _; exact Function.FactorizedRational.analyticAt (hDnn x)
  set P : ℂ → ℂ := fun z => Pf z * g z with hPdef
  have hP_an : AnalyticOnNhd ℂ P U := fun x hx => (hPf_an x hx).mul (hg_an x hx)
  have hg_eqP : f =ᶠ[Filter.codiscreteWithin U] P := by
    have hPeq : ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f U u)) • g) = P := by
      rw [hPf_finset]; ext w; simp [hPdef, hPfdef]
    rw [← hPeq]; exact hg_eq
  have hT_zero : ∀ u ∈ T, f u = 0 := by
    intro u hu
    rw [hTmem u, Function.mem_support] at hu
    exact hsupp_zero u (by rw [Function.mem_support]; exact hu)
  refine ⟨logDeriv g, ?_, ?_, ?_, ?_⟩
  · have hE_an : AnalyticOnNhd ℂ (logDeriv g) U := by
      intro x hx
      have : logDeriv g = fun z => deriv g z / g z := by
        ext z; rw [logDeriv_apply]
      rw [this]
      exact (hg_an x hx).deriv.div (hg_an x hx) (hg_ne ⟨x, hx⟩)
    exact (hE_an.mono hbox_sub).differentiableOn
  · intro ρ hρ
    rw [hTmem ρ, Function.mem_support] at hρ
    have hρU : ρ ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain
      (by rw [Function.mem_support]; exact hρ)
    have hρzero : f ρ = 0 := hsupp_zero ρ (by rw [Function.mem_support]; exact hρ)
    have hAtρ : AnalyticAt ℂ f ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt f ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    have hfin : analyticOrderAt f ρ ≠ ⊤ := by
      intro hcontra
      exact h₂f ρ hρU (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    have hDeq : (MeromorphicOn.divisor f U : ℂ → ℤ) ρ
        = (analyticOrderNatAt f ρ : ℤ) := by
      have hda : (MeromorphicOn.divisor f U : ℂ → ℤ) ρ
          = ((analyticOrderAt f ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda, ← Nat.cast_analyticOrderNatAt hfin]; rfl
    have hnat_ne : analyticOrderNatAt f ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    show (1 : ℤ) ≤ (MeromorphicOn.divisor f U : ℂ → ℤ) ρ
    rw [hDeq]
    have : 1 ≤ analyticOrderNatAt f ρ := Nat.one_le_iff_ne_zero.mpr hnat_ne
    exact_mod_cast this
  · intro ρ hρU hρzero
    rw [hTmem ρ, Function.mem_support]
    have hAtρ : AnalyticAt ℂ f ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt f ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    have hfin : analyticOrderAt f ρ ≠ ⊤ := by
      intro hcontra
      exact h₂f ρ hρU (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    have hDeq : (MeromorphicOn.divisor f U : ℂ → ℤ) ρ
        = (analyticOrderNatAt f ρ : ℤ) := by
      have hda : (MeromorphicOn.divisor f U : ℂ → ℤ) ρ
          = ((analyticOrderAt f ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda, ← Nat.cast_analyticOrderNatAt hfin]; rfl
    have hnat_ne : analyticOrderNatAt f ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    rw [hDeq]
    exact_mod_cast hnat_ne
  · intro z hz hznz
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
    have htrans : logDeriv f z = logDeriv P z :=
      RHInBoxAnalytic.logDeriv_congr_of_codiscrete hζU hP_an hUopen hUconn hz hz hg_eqP
    rw [htrans, hPdef, logDeriv_mul z hPfz hgz hPf_diff hg_diff, hPfdef]
    rw [RHInBoxAnalytic.logDeriv_finset_prod D z hzroots]

/-- **The Blaschke split for `H`** — the `zeta_blaschke_split_ball` analog, instantiated from the
    three ported prerequisites.  `H = zetaPoleCompanion`. -/
theorem zetaPoleCompanion_blaschke_split_ball
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R) :
    ∃ (E : ℂ → ℂ),
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ∧
      (∀ ρ ∈ (divisor_zetaPoleCompanion_ball_support_finite c R).toFinset,
        (1 : ℤ) ≤ (MeromorphicOn.divisor zetaPoleCompanion (Metric.ball c R) : ℂ → ℤ) ρ) ∧
      (∀ ρ ∈ Metric.ball c R, zetaPoleCompanion ρ = 0 →
        ρ ∈ (divisor_zetaPoleCompanion_ball_support_finite c R).toFinset) ∧
      (∀ z ∈ Metric.ball c R, zetaPoleCompanion z ≠ 0 →
        logDeriv zetaPoleCompanion z
          = (∑ ρ ∈ (divisor_zetaPoleCompanion_ball_support_finite c R).toFinset,
            ((MeromorphicOn.divisor zetaPoleCompanion (Metric.ball c R) : ℂ → ℤ) ρ : ℂ)
              / (z - ρ)) + E z) :=
  analytic_blaschke_split_ball zetaPoleCompanion sigma0 sigma1 T0 T1 c R
    (analyticOnNhd_zetaPoleCompanion _)
    (fun u _ => meromorphicOrderAt_zetaPoleCompanion_ne_top u)
    (divisor_zetaPoleCompanion_ball_support_finite c R)
    hbox_ball

/-- **Generic box argument principle** (the `riemannZeta`-free `zeta_count_eq_winding_generic`): for
    any analytic `f` with finite divisor/order, if the boundary winding of `logDeriv f` is `2πiN`
    then the total divisor of `f` over the box equals `N` (and every box zero is captured).  The
    routine Arb boundary facts are bundled in `hArb`; the split is kernel-derived. -/
theorem analytic_count_eq_winding_generic
    (f : ℂ → ℂ) (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ)
    (hfU : AnalyticOnNhd ℂ f (Metric.ball c R))
    (h₂f : ∀ u ∈ Metric.ball c R, meromorphicOrderAt f u ≠ ⊤)
    (h₃f : (MeromorphicOn.divisor f (Metric.ball c R)).support.Finite)
    (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hwind : (∫ x in sigma0..sigma1, logDeriv f (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv f (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv f ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv f ((sigma0 : ℂ) + ↑y * I))
      = 2 * π * I * (N : ℂ))
    (hArb : ∀ (E : ℂ → ℂ),
      let s := h₃f.toFinset
      let d := (MeromorphicOn.divisor f (Metric.ball c R) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) →
      (∀ z ∈ Metric.ball c R, f z ≠ 0 →
        logDeriv f z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc sigma0 sigma1, f (↑x + (T0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc sigma0 sigma1, f (↑x + (T1 : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc T0 T1, f ((sigma1 : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc T0 T1, f ((sigma0 : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
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
        f ρ = 0 → ρ ∈ s) ∧
      (∑ ρ ∈ s, d ρ) = N := by
  obtain ⟨E, hEholo, hd1, hzero_in, hker⟩ :=
    analytic_blaschke_split_ball f sigma0 sigma1 T0 T1 c R hfU h₂f h₃f hbox_ball
  set s := h₃f.toFinset with hs
  set d := (MeromorphicOn.divisor f (Metric.ball c R) : ℂ → ℤ) with hd
  refine ⟨s, d, hd1, ?_, ?_⟩
  · intro ρ hre him hρzero
    exact hzero_in ρ (hbox_ball ρ hre him) hρzero
  · obtain ⟨hnz_b, hnz_t, hnz_r, hnz_l, hin, hb, ht, hr, hl,
            hsb, hst, hsr, hsl, heb, het, her, hel⟩ := hArb E hEholo hker
    have huIccσ : Set.uIcc sigma0 sigma1 = Set.Icc sigma0 sigma1 := Set.uIcc_of_le hsig
    have huIccT : Set.uIcc T0 T1 = Set.Icc T0 T1 := Set.uIcc_of_le hT
    have hre_pt : ∀ (a b : ℝ), ((a : ℂ) + (b : ℂ) * I).re = a := by intro a b; simp
    have him_pt : ∀ (a b : ℝ), ((a : ℂ) + (b : ℂ) * I).im = b := by intro a b; simp
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
    have hsp_b : ∀ x ∈ Set.uIcc sigma0 sigma1,
        logDeriv f (↑x + (T0 : ℂ) * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) + E (↑x + (T0 : ℂ) * I) := by
      intro x hx
      rw [hker _ (bmem x hx) (hnz_b x hx)]; simp only [div_eq_mul_inv]
    have hsp_t : ∀ x ∈ Set.uIcc sigma0 sigma1,
        logDeriv f (↑x + (T1 : ℂ) * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) + E (↑x + (T1 : ℂ) * I) := by
      intro x hx
      rw [hker _ (tmem x hx) (hnz_t x hx)]; simp only [div_eq_mul_inv]
    have hsp_r : ∀ y ∈ Set.uIcc T0 T1,
        logDeriv f ((sigma1 : ℂ) + ↑y * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) + E ((sigma1 : ℂ) + ↑y * I) := by
      intro y hy
      rw [hker _ (rmem y hy) (hnz_r y hy)]; simp only [div_eq_mul_inv]
    have hsp_l : ∀ y ∈ Set.uIcc T0 T1,
        logDeriv f ((sigma0 : ℂ) + ↑y * I)
          = (∑ ρ ∈ s, (d ρ : ℂ) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) + E ((sigma0 : ℂ) + ↑y * I) := by
      intro y hy
      rw [hker _ (lmem y hy) (hnz_l y hy)]; simp only [div_eq_mul_inv]
    have eb : (∫ x in sigma0..sigma1, logDeriv f (↑x + (T0 : ℂ) * I))
        = (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
          + (∫ x in sigma0..sigma1, E (↑x + (T0 : ℂ) * I)) := by
      rw [← intervalIntegral.integral_add hsb heb]
      exact intervalIntegral.integral_congr (fun x hx => hsp_b x hx)
    have et : (∫ x in sigma0..sigma1, logDeriv f (↑x + (T1 : ℂ) * I))
        = (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
          + (∫ x in sigma0..sigma1, E (↑x + (T1 : ℂ) * I)) := by
      rw [← intervalIntegral.integral_add hst het]
      exact intervalIntegral.integral_congr (fun x hx => hsp_t x hx)
    have er : (∫ y in T0..T1, logDeriv f ((sigma1 : ℂ) + ↑y * I))
        = (∫ y in T0..T1, ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
          + (∫ y in T0..T1, E ((sigma1 : ℂ) + ↑y * I)) := by
      rw [← intervalIntegral.integral_add hsr her]
      exact intervalIntegral.integral_congr (fun y hy => hsp_r y hy)
    have el : (∫ y in T0..T1, logDeriv f ((sigma0 : ℂ) + ↑y * I))
        = (∫ y in T0..T1, ∑ ρ ∈ s, (d ρ : ℂ) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
          + (∫ y in T0..T1, E ((sigma0 : ℂ) + ↑y * I)) := by
      rw [← intervalIntegral.integral_add hsl hel]
      exact intervalIntegral.integral_congr (fun y hy => hsp_l y hy)
    have hE0 := RHInBoxAnalytic.rect_arg_principle_generic sigma0 sigma1 T0 T1 hsig hT E hEholo
    have hRes := RHInBoxAnalytic.box_residue_sum_generic sigma0 sigma1 T0 T1 d hin hb ht hr hl
    rw [eb, et, er, el, smul_add, smul_add] at hwind
    have key : 2 * π * I * (∑ ρ ∈ s, (d ρ : ℂ)) = 2 * π * I * (N : ℂ) := by
      rw [← hRes]
      linear_combination hwind - hE0
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hsumC : (∑ ρ ∈ s, (d ρ : ℂ)) = (N : ℂ) := mul_left_cancel₀ h2pi key
    have : ((∑ ρ ∈ s, d ρ : ℤ) : ℂ) = ((N : ℤ) : ℂ) := by
      push_cast; push_cast at hsumC; exact hsumC
    exact_mod_cast this

/-! ## THE +1, item 1: the integrated pole extraction on the box boundary.

Lifting `logDeriv_zeta_pole_extract` (`ζ′/ζ = H′/H − (·−1)⁻¹`) from pointwise to the contour: for a
box with `s = 1` strictly interior and `ζ` non-vanishing on the four edges,

  `Bd(logDeriv ζ) = Bd(logDeriv H) − 2πi`

— the pole's boundary winding is exactly `2πi` (`rect_winding_generic` at `ρ = 1`), so `ζ`'s
meromorphic boundary winding is `H`'s holomorphic one minus the pole.  Together with the count
(`analytic_count_eq_winding_generic` at `H`) this is `N_ζ = N_H − 1` — the RvM `+1`.
conjecture1_proved = False. -/

/-- `logDeriv H` is continuous wherever `H ≠ 0` (`H` entire). -/
theorem continuousAt_logDeriv_zetaPoleCompanion {z : ℂ} (hz : zetaPoleCompanion z ≠ 0) :
    ContinuousAt (logDeriv zetaPoleCompanion) z := by
  have hAt := analyticAt_zetaPoleCompanion z
  have heq : logDeriv zetaPoleCompanion
      = fun w => deriv zetaPoleCompanion w / zetaPoleCompanion w := by
    funext w; rw [logDeriv_apply]
  rw [heq]
  exact (hAt.deriv.continuousAt).div hAt.continuousAt hz

/-- **The edge identity**: `logDeriv ζ = logDeriv H − (·−1)⁻¹` at any `z ≠ 1` with `ζ z ≠ 0`.
    (`logDeriv_zeta_pole_extract` with `H = (·−1)·ζ` off `1` via `logDeriv_congr_nhds`.) -/
theorem logDeriv_zeta_eq_companion_sub_pole {z : ℂ} (hz : z ≠ 1) (hζ : riemannZeta z ≠ 0) :
    logDeriv riemannZeta z = logDeriv zetaPoleCompanion z - (z - 1)⁻¹ := by
  have hprod := logDeriv_zeta_pole_extract hz hζ
  have hHeq : logDeriv zetaPoleCompanion z
      = logDeriv (fun w : ℂ => riemannZeta w * (w - 1)) z := by
    apply RHInBoxAnalytic.logDeriv_congr_nhds
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    rw [zetaPoleCompanion_apply_of_ne hw, mul_comm]
  rw [hHeq]; exact hprod

/-- Continuity of `logDeriv H` along a `ℂ`-valued real path where `H ≠ 0`. -/
theorem contOn_logDerivH_path (γ : ℝ → ℂ) (hγ : Continuous γ) (a b : ℝ)
    (hne : ∀ t ∈ Set.uIcc a b, zetaPoleCompanion (γ t) ≠ 0) :
    ContinuousOn (fun t => logDeriv zetaPoleCompanion (γ t)) (Set.uIcc a b) := by
  intro t ht
  exact ((continuousAt_logDeriv_zetaPoleCompanion (hne t ht)).comp hγ.continuousAt).continuousWithinAt

/-- Continuity of `(·−1)⁻¹` along a path avoiding `1`. -/
theorem contOn_invSub_path (γ : ℝ → ℂ) (hγ : Continuous γ) (a b : ℝ)
    (hne : ∀ t ∈ Set.uIcc a b, γ t ≠ 1) :
    ContinuousOn (fun t => (γ t - 1)⁻¹) (Set.uIcc a b) := by
  intro t ht
  exact ((hγ.continuousAt.sub continuousAt_const).inv₀
    (sub_ne_zero.mpr (hne t ht))).continuousWithinAt

/-- **THE +1, item 1**: the integrated pole extraction — `ζ`'s boundary winding is `H`'s minus the
    pole's `2πi`.  `s = 1` strictly interior (`σ0 < 1 < σ1`, `T0 < 0 < T1`), `ζ ≠ 0` on the edges. -/
theorem bd_logDeriv_zeta_eq_bd_companion_sub_pole
    (sigma0 sigma1 T0 T1 : ℝ)
    (hσ0 : sigma0 < 1) (hσ1 : 1 < sigma1) (hT0 : T0 < 0) (hT1 : 0 < T1)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0) :
    ((∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I)))
      = ((∫ x in sigma0..sigma1, logDeriv zetaPoleCompanion (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv zetaPoleCompanion (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv zetaPoleCompanion ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv zetaPoleCompanion ((sigma0 : ℂ) + ↑y * I)))
        - 2 * ↑π * I := by
  -- edge points avoid `1` (strict interiority)
  have hne1_b : ∀ x : ℝ, ((x : ℂ) + (T0 : ℂ) * I) ≠ 1 := by
    intro x h; have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero, Complex.one_im] at hi
    linarith
  have hne1_t : ∀ x : ℝ, ((x : ℂ) + (T1 : ℂ) * I) ≠ 1 := by
    intro x h; have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero, Complex.one_im] at hi
    linarith
  have hne1_r : ∀ y : ℝ, ((sigma1 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro y h; have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, Complex.one_re] at hr
    linarith
  have hne1_l : ∀ y : ℝ, ((sigma0 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro y h; have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, Complex.one_re] at hr
    linarith
  -- `H ≠ 0` on the edges (from `ζ ≠ 0` and `pt ≠ 1`)
  have hHb : ∀ x ∈ Set.uIcc sigma0 sigma1, zetaPoleCompanion (↑x + (T0 : ℂ) * I) ≠ 0 :=
    fun x hx h0 => hnzb x hx (zetaPoleCompanion_eq_zero_iff.mp h0).2
  have hHt : ∀ x ∈ Set.uIcc sigma0 sigma1, zetaPoleCompanion (↑x + (T1 : ℂ) * I) ≠ 0 :=
    fun x hx h0 => hnzt x hx (zetaPoleCompanion_eq_zero_iff.mp h0).2
  have hHr : ∀ y ∈ Set.uIcc T0 T1, zetaPoleCompanion ((sigma1 : ℂ) + ↑y * I) ≠ 0 :=
    fun y hy h0 => hnzr y hy (zetaPoleCompanion_eq_zero_iff.mp h0).2
  have hHl : ∀ y ∈ Set.uIcc T0 T1, zetaPoleCompanion ((sigma0 : ℂ) + ↑y * I) ≠ 0 :=
    fun y hy h0 => hnzl y hy (zetaPoleCompanion_eq_zero_iff.mp h0).2
  -- integrabilities (H, inv) on the four edges
  have cpb : Continuous (fun t : ℝ => (↑t + (T0 : ℂ) * I)) := by fun_prop
  have cpt : Continuous (fun t : ℝ => (↑t + (T1 : ℂ) * I)) := by fun_prop
  have cpr : Continuous (fun t : ℝ => ((sigma1 : ℂ) + ↑t * I)) := by fun_prop
  have cpl : Continuous (fun t : ℝ => ((sigma0 : ℂ) + ↑t * I)) := by fun_prop
  have iHb := (contOn_logDerivH_path _ cpb sigma0 sigma1 hHb).intervalIntegrable
    (μ := MeasureTheory.volume)
  have iHt := (contOn_logDerivH_path _ cpt sigma0 sigma1 hHt).intervalIntegrable
    (μ := MeasureTheory.volume)
  have iHr := (contOn_logDerivH_path _ cpr T0 T1 hHr).intervalIntegrable
    (μ := MeasureTheory.volume)
  have iHl := (contOn_logDerivH_path _ cpl T0 T1 hHl).intervalIntegrable
    (μ := MeasureTheory.volume)
  have iVb := (contOn_invSub_path _ cpb sigma0 sigma1 (fun x _ => hne1_b x)).intervalIntegrable
    (μ := MeasureTheory.volume)
  have iVt := (contOn_invSub_path _ cpt sigma0 sigma1 (fun x _ => hne1_t x)).intervalIntegrable
    (μ := MeasureTheory.volume)
  have iVr := (contOn_invSub_path _ cpr T0 T1 (fun y _ => hne1_r y)).intervalIntegrable
    (μ := MeasureTheory.volume)
  have iVl := (contOn_invSub_path _ cpl T0 T1 (fun y _ => hne1_l y)).intervalIntegrable
    (μ := MeasureTheory.volume)
  -- per-edge: ∫ logDeriv ζ = ∫ logDeriv H − ∫ (·−1)⁻¹
  have ebot : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
      = (∫ x in sigma0..sigma1, logDeriv zetaPoleCompanion (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, ((↑x + (T0 : ℂ) * I) - 1)⁻¹) := by
    rw [← intervalIntegral.integral_sub iHb iVb]
    exact intervalIntegral.integral_congr
      (fun x hx => logDeriv_zeta_eq_companion_sub_pole (hne1_b x) (hnzb x hx))
  have etop : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
      = (∫ x in sigma0..sigma1, logDeriv zetaPoleCompanion (↑x + (T1 : ℂ) * I))
        - (∫ x in sigma0..sigma1, ((↑x + (T1 : ℂ) * I) - 1)⁻¹) := by
    rw [← intervalIntegral.integral_sub iHt iVt]
    exact intervalIntegral.integral_congr
      (fun x hx => logDeriv_zeta_eq_companion_sub_pole (hne1_t x) (hnzt x hx))
  have erig : (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
      = (∫ y in T0..T1, logDeriv zetaPoleCompanion ((sigma1 : ℂ) + ↑y * I))
        - (∫ y in T0..T1, (((sigma1 : ℂ) + ↑y * I) - 1)⁻¹) := by
    rw [← intervalIntegral.integral_sub iHr iVr]
    exact intervalIntegral.integral_congr
      (fun y hy => logDeriv_zeta_eq_companion_sub_pole (hne1_r y) (hnzr y hy))
  have elef : (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
      = (∫ y in T0..T1, logDeriv zetaPoleCompanion ((sigma0 : ℂ) + ↑y * I))
        - (∫ y in T0..T1, (((sigma0 : ℂ) + ↑y * I) - 1)⁻¹) := by
    rw [← intervalIntegral.integral_sub iHl iVl]
    exact intervalIntegral.integral_congr
      (fun y hy => logDeriv_zeta_eq_companion_sub_pole (hne1_l y) (hnzl y hy))
  -- the pole's boundary winding = 2πi
  have hwind_pole := RHInBoxAnalytic.rect_winding_generic sigma0 sigma1 T0 T1 1
    (by simpa using hσ0) (by simpa using hσ1) (by simpa using hT0) (by simpa using hT1)
  rw [ebot, etop, erig, elef]
  simp only [smul_eq_mul] at hwind_pole ⊢
  linear_combination -hwind_pole

/-! ## THE +1, item 2: discharge the routine `hArb` integrabilities, then wire `N_ζ = N_H − 1`.

The generic count's `hArb` bundle mixes genuinely-external facts (edge non-vanishing = Arb
enclosures; strict interiority of the zeros = geometry) with ROUTINE integrabilities that follow
from continuity.  Here the routine ones are discharged (four helpers below), leaving a wiring lemma
`zetaPoleCompanion_count_eq_winding_with_pole` that takes only the external facts + the `ζ` boundary
winding value `M`, and concludes the box zero-count of `H` (= `ζ`'s zeros, since `H`'s zeros are
`ζ`'s non-`1` zeros) is `M + 1` — the RvM `+1`, assembled from item 1 + the count at `H`.
conjecture1_proved = False. -/

/-- `(·−ρ)⁻¹` is interval-integrable along a horizontal segment at height `b ≠ ρ.im`. -/
theorem intervalIntegrable_inv_sub_horiz {ρ : ℂ} {b : ℝ} (hb : b ≠ ρ.im) (a0 a1 : ℝ) :
    IntervalIntegrable (fun x : ℝ => ((↑x + (b : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume a0 a1 := by
  apply Continuous.intervalIntegrable
  refine Continuous.inv₀ (by fun_prop) ?_
  intro x hc
  have hi := congrArg Complex.im hc
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add,
    add_zero, Complex.zero_im] at hi
  exact hb (by linarith)

/-- `(·−ρ)⁻¹` is interval-integrable along a vertical segment at abscissa `a ≠ ρ.re`. -/
theorem intervalIntegrable_inv_sub_vert {ρ : ℂ} {a : ℝ} (ha : a ≠ ρ.re) (b0 b1 : ℝ) :
    IntervalIntegrable (fun y : ℝ => (((a : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume b0 b1 := by
  apply Continuous.intervalIntegrable
  refine Continuous.inv₀ (by fun_prop) ?_
  intro y hc
  have hr := congrArg Complex.re hc
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    zero_mul, add_zero, Complex.zero_re] at hr
  exact ha (by linarith)

/-- A function differentiable on the closed box is interval-integrable along a horizontal edge. -/
theorem intervalIntegrable_diffBox_horiz {E : ℂ → ℂ} {b σ0 σ1 T0 T1 : ℝ}
    (hb : b ∈ Set.Icc T0 T1) (hσ : σ0 ≤ σ1)
    (hE : DifferentiableOn ℂ E (Set.Icc σ0 σ1 ×ℂ Set.Icc T0 T1)) :
    IntervalIntegrable (fun x : ℝ => E (↑x + (b : ℂ) * I)) MeasureTheory.volume σ0 σ1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hσ]
  refine (hE.continuousOn).comp (Continuous.continuousOn (by fun_prop)) ?_
  intro x hx
  rw [Complex.mem_reProdIm]
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
    exact hx
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    exact hb

/-- A function differentiable on the closed box is interval-integrable along a vertical edge. -/
theorem intervalIntegrable_diffBox_vert {E : ℂ → ℂ} {a σ0 σ1 T0 T1 : ℝ}
    (ha : a ∈ Set.Icc σ0 σ1) (hT : T0 ≤ T1)
    (hE : DifferentiableOn ℂ E (Set.Icc σ0 σ1 ×ℂ Set.Icc T0 T1)) :
    IntervalIntegrable (fun y : ℝ => E ((a : ℂ) + ↑y * I)) MeasureTheory.volume T0 T1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hT]
  refine (hE.continuousOn).comp (Continuous.continuousOn (by fun_prop)) ?_
  intro y hy
  rw [Complex.mem_reProdIm]
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
    exact ha
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    exact hy

/-- A finite sum of interval-integrable functions is interval-integrable (stated in the
    `fun x => ∑ …` form matching the generic count's `hArb` bundle). -/
theorem intervalIntegrable_finsetSum {ι : Type*} (t : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ}
    (h : ∀ i ∈ t, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ t, f i x) MeasureTheory.volume a b := by
  classical
  induction t using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact intervalIntegrable_const
  | @insert j t hj ih =>
      simp only [Finset.sum_insert hj]
      exact (h j (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **THE +1, WIRED**: for a box with `s = 1` strictly interior, `ζ` non-vanishing on the edges,
    every `H`-zero strictly interior, and the `ζ` boundary winding equal to `2πiM`, the box
    zero-count of `H` (= `ζ`'s non-`1` zeros) is `M + 1`.  The routine `hArb` integrabilities are
    discharged internally; only the external Arb/geometry facts remain hypotheses.  This is the
    meromorphic argument principle for `ζ` with the pole at `1` contributing the RvM `+1`. -/
theorem zetaPoleCompanion_count_eq_winding_with_pole
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (M : ℤ)
    (hσ0 : sigma0 < 1) (hσ1 : 1 < sigma1) (hT0 : T0 < 0) (hT1 : 0 < T1)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hin : ∀ ρ ∈ (divisor_zetaPoleCompanion_ball_support_finite c R).toFinset,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hwindζ : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
      = 2 * π * I * (M : ℂ)) :
    ∃ (s : Finset ℂ) (d : ℂ → ℤ),
      (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧
      (∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
        zetaPoleCompanion ρ = 0 → ρ ∈ s) ∧
      (∑ ρ ∈ s, d ρ) = M + 1 := by
  have hsig : sigma0 ≤ sigma1 := by linarith
  have hT : T0 ≤ T1 := by linarith
  -- item 1 + the ζ winding give the H winding = 2πi(M+1)
  have hitem1 := bd_logDeriv_zeta_eq_bd_companion_sub_pole sigma0 sigma1 T0 T1
    hσ0 hσ1 hT0 hT1 hnzb hnzt hnzr hnzl
  have hwindH : (∫ x in sigma0..sigma1, logDeriv zetaPoleCompanion (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv zetaPoleCompanion (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv zetaPoleCompanion ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv zetaPoleCompanion ((sigma0 : ℂ) + ↑y * I))
      = 2 * π * I * (((M + 1 : ℤ)) : ℂ) := by
    rw [hwindζ] at hitem1
    push_cast
    push_cast at hitem1
    linear_combination -hitem1
  -- discharge hArb and apply the generic count with N := M + 1
  refine analytic_count_eq_winding_generic zetaPoleCompanion sigma0 sigma1 T0 T1 c R (M + 1)
    (analyticOnNhd_zetaPoleCompanion _)
    (fun u _ => meromorphicOrderAt_zetaPoleCompanion_ne_top u)
    (divisor_zetaPoleCompanion_ball_support_finite c R) hsig hT hbox_ball hwindH ?_
  intro E _s _d hEholo _hker
  -- H ≠ 0 on the edges (from ζ ≠ 0 and pt ≠ 1 inside eq_zero_iff)
  have hHb : ∀ x ∈ Set.uIcc sigma0 sigma1, zetaPoleCompanion (↑x + (T0 : ℂ) * I) ≠ 0 :=
    fun x hx h0 => hnzb x hx (zetaPoleCompanion_eq_zero_iff.mp h0).2
  have hHt : ∀ x ∈ Set.uIcc sigma0 sigma1, zetaPoleCompanion (↑x + (T1 : ℂ) * I) ≠ 0 :=
    fun x hx h0 => hnzt x hx (zetaPoleCompanion_eq_zero_iff.mp h0).2
  have hHr : ∀ y ∈ Set.uIcc T0 T1, zetaPoleCompanion ((sigma1 : ℂ) + ↑y * I) ≠ 0 :=
    fun y hy h0 => hnzr y hy (zetaPoleCompanion_eq_zero_iff.mp h0).2
  have hHl : ∀ y ∈ Set.uIcc T0 T1, zetaPoleCompanion ((sigma0 : ℂ) + ↑y * I) ≠ 0 :=
    fun y hy h0 => hnzl y hy (zetaPoleCompanion_eq_zero_iff.mp h0).2
  refine ⟨hHb, hHt, hHr, hHl, hin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ρ hρ => intervalIntegrable_inv_sub_horiz (ne_of_lt (hin ρ hρ).2.2.1) _ _
  · exact fun ρ hρ => intervalIntegrable_inv_sub_horiz ((ne_of_lt (hin ρ hρ).2.2.2).symm) _ _
  · exact fun ρ hρ => intervalIntegrable_inv_sub_vert ((ne_of_lt (hin ρ hρ).2.1).symm) _ _
  · exact fun ρ hρ => intervalIntegrable_inv_sub_vert (ne_of_lt (hin ρ hρ).1) _ _
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_horiz (ne_of_lt (hin ρ hρ).2.2.1) _ _).const_mul _)
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_horiz ((ne_of_lt (hin ρ hρ).2.2.2).symm) _ _).const_mul _)
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_vert ((ne_of_lt (hin ρ hρ).2.1).symm) _ _).const_mul _)
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_vert (ne_of_lt (hin ρ hρ).1) _ _).const_mul _)
  · exact intervalIntegrable_diffBox_horiz ⟨le_refl _, hT⟩ hsig hEholo
  · exact intervalIntegrable_diffBox_horiz ⟨hT, le_refl _⟩ hsig hEholo
  · exact intervalIntegrable_diffBox_vert ⟨hsig, le_refl _⟩ hT hEholo
  · exact intervalIntegrable_diffBox_vert ⟨le_refl _, hsig⟩ hT hEholo

/-- **THE MEROMORPHIC ARGUMENT PRINCIPLE FOR `ζ`, stated over `ζ`'s own zeros.**  For a box with
    `s = 1` strictly interior, `ζ ≠ 0` on the edges, all interior zeros strict, and `ζ` boundary
    winding `2πiM`: there is a finite set `s` of box zeros of `ζ` (each with multiplicity `≥ 1`,
    capturing every box `ζ`-zero) whose total multiplicity is `M + 1`.  The `+1` is the pole of `ζ`
    at `1` (via `riemannZeta_one_ne_zero`, box `ζ`-zeros avoid `1`, so they coincide with `H`'s).
    This is the RvM `+1` as a statement purely about `ζ`. -/
theorem zeta_strip_zero_count_with_pole
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (M : ℤ)
    (hσ0 : sigma0 < 1) (hσ1 : 1 < sigma1) (hT0 : T0 < 0) (hT1 : 0 < T1)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hin : ∀ ρ ∈ (divisor_zetaPoleCompanion_ball_support_finite c R).toFinset,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hwindζ : (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
      = 2 * π * I * (M : ℂ)) :
    ∃ (s : Finset ℂ) (d : ℂ → ℤ),
      (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧
      (∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
        riemannZeta ρ = 0 → ρ ∈ s) ∧
      (∑ ρ ∈ s, d ρ) = M + 1 := by
  obtain ⟨s, d, hd1, hcapH, hsum⟩ := zetaPoleCompanion_count_eq_winding_with_pole
    sigma0 sigma1 T0 T1 c R M hσ0 hσ1 hT0 hT1 hbox_ball hnzb hnzt hnzr hnzl hin hwindζ
  refine ⟨s, d, hd1, ?_, hsum⟩
  intro ρ hre him hζ0
  have hρ1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hζ0
  exact hcapH ρ hre him (zetaPoleCompanion_eq_zero_iff.mpr ⟨hρ1, hζ0⟩)

/-! ## Toward the literal RvM: the CONJUGATION fold (one of the two symmetry folds).

RvM's `Δ_box arg = 2·(…)` uses two symmetries of the completed zeta: the reflection `s ↦ 1−s`
(`argChangeVert_fold`, already merged) and the Schwarz conjugation `s ↦ s̄` folding the lower half
onto the upper.  Here is the conjugation fold, generically: for any `f` with `f(s̄) = conj(f s)`,
differentiable along the line, and with `logDeriv f` integrable on `[−T,T]`,

  `AV(f, σ, −T, T) = 2 · AV(f, σ, 0, T)`

— because `Re(logDeriv f (σ + iy))` is EVEN in `y` (`logDeriv f (σ − iy) = conj(logDeriv f(σ+iy))`,
and `Re ∘ conj = Re`).  Applies to `ζ`, `Γℝ`, and `Λ₀` (all Schwarz-symmetric) on zero-free
segments.  The remaining literal-RvM work is the reflection-side `θ + πS` identification and the
`T0 → 0⁺` base — still genuine construction, not claimed.  conjecture1_proved = False. -/

/-- **The conjugation (Schwarz) fold of the vertical argument change**: for `f(s̄) = conj(f s)`,
    `AV(f, σ, −T, T) = 2·AV(f, σ, 0, T)`.  The lower half mirrors the upper. -/
theorem argChangeVert_conj_double (f : ℂ → ℂ) (σ T : ℝ) (hT : 0 ≤ T)
    (hconj : ∀ z : ℂ, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hdiff : ∀ y : ℝ, DifferentiableAt ℂ f ((σ : ℂ) + y * I))
    (hint : IntervalIntegrable (fun y : ℝ => logDeriv f ((σ : ℂ) + y * I))
      MeasureTheory.volume (-T) T) :
    argChangeVert f σ (-T) T = 2 * argChangeVert f σ 0 T := by
  -- evenness of the real-part integrand
  have heven : ∀ y : ℝ, (logDeriv f ((σ : ℂ) + ((-y : ℝ) : ℂ) * I)).re
      = (logDeriv f ((σ : ℂ) + ((y : ℝ) : ℂ) * I)).re := by
    intro y
    have hs : ((σ : ℂ) + ((-y : ℝ) : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + ((y : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hs, logDeriv_conj_of_conj_symm hconj (hdiff y), Complex.conj_re]
  -- integrability on the two half-segments
  have hint1 : IntervalIntegrable (fun y : ℝ => logDeriv f ((σ : ℂ) + y * I))
      MeasureTheory.volume (-T) 0 :=
    hint.mono_set (by
      rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ 0), Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
      exact Set.Icc_subset_Icc_right hT)
  have hint2 : IntervalIntegrable (fun y : ℝ => logDeriv f ((σ : ℂ) + y * I))
      MeasureTheory.volume 0 T :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hT, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
      exact Set.Icc_subset_Icc_left (by linarith : (-T : ℝ) ≤ 0))
  unfold argChangeVert
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, Complex.add_re]
  have hre1 := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hint1
  have hre2 := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hint2
  simp only [RCLike.re_to_complex] at hre1 hre2
  rw [← hre1, ← hre2]
  have hcn := intervalIntegral.integral_comp_neg
    (fun y : ℝ => (logDeriv f ((σ : ℂ) + (y : ℂ) * I)).re) (a := 0) (b := T)
  simp only [neg_zero] at hcn
  have hswap : (∫ y in (-T)..0, (logDeriv f ((σ : ℂ) + (y : ℂ) * I)).re)
      = ∫ y in (0 : ℝ)..T, (logDeriv f ((σ : ℂ) + (y : ℂ) * I)).re := by
    rw [← hcn]
    exact intervalIntegral.integral_congr (fun y _ => heven y)
  rw [hswap]; ring

/-! ## THE θ IDENTIFICATION: the Archimedean part of the right-half path IS Riemann–Siegel `θ`.

The reflection-side of RvM needs `θ`.  The key fact — provable, not just scaffolded — is that `Γℝ` is
analytic AND non-vanishing on the whole rectangle `[1/2,2] × [0,T]` (its poles are at `Re ≤ 0`, it
never vanishes), so `logDeriv Γℝ` is holomorphic there and its rectangle winding is `0`
(`rect_arg_principle_generic`).  Since `Γℝ` is real on the real axis (bottom edge contributes `0`
to the argument change), this forces the Archimedean argument change along the right-half path
`2 → 2+iT → 1/2+iT` to equal `θ(T) = AV(Γℝ,1/2,0,T)`:

  `AV(Γℝ,2,0,T) + AH(Γℝ,T,2,1/2) = θ(T)`.

This is the θ half of the `θ + πS` identification.  (The `πS` half is `logDeriv_zeta_add_gammaR`
integrated along the same path, `Δ_L ζ = πS`; the `+1` is the pole, handled separately.)
conjecture1_proved = False. -/

/-- `Γℝ` is analytic on the right half-plane `Re > 0` (its `Γ(s/2)` poles are at `Re ≤ 0`). -/
theorem gammaR_analyticAt_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Gammaℝ {w : ℂ | 0 < w.re} := by
    intro w hw
    have hwre : 0 < w.re := hw
    have hpole : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.neg_re, Complex.natCast_re] at hre
      have h2 : (w / 2).re = w.re / 2 := by
        rw [div_eq_mul_inv, Complex.mul_re]
        simp [Complex.inv_re, Complex.normSq]
        ring
      rw [h2] at hre
      nlinarith [hwre, Nat.cast_nonneg (α := ℝ) m]
    have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) w := by
      simpa using (hasDerivAt_id w).div_const 2
    have hB : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
        (deriv Complex.Gamma (w / 2) * (1 / 2)) w :=
      ((Complex.differentiableAt_Gamma _ hpole).hasDerivAt).comp w hhalf
    have hGdef : Gammaℝ = fun z : ℂ => ZeroFreeBridge.gammaRArch z * Complex.Gamma (z / 2) := rfl
    rw [hGdef]
    exact (((ZeroFreeBridge.gammaRArch_hasDerivAt w).differentiableAt).mul
      hB.differentiableAt).differentiableWithinAt
  exact (hdiff.analyticOnNhd hopen) s hs

/-- `logDeriv Γℝ` continuous at any point with `Re > 0`. -/
theorem continuousAt_logDeriv_gammaR_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (logDeriv Gammaℝ) s := by
  have hana := gammaR_analyticAt_of_re_pos hs
  have hne := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have heq : logDeriv Gammaℝ = fun w => deriv Gammaℝ w / Gammaℝ w := by
    funext w; rw [logDeriv_apply]
  rw [heq]
  exact (hana.deriv.continuousAt).div hana.continuousAt hne

/-- `logDeriv Γℝ` is REAL on the positive real axis (`Γℝ` real there, via conjugation symmetry). -/
theorem logDeriv_gammaR_im_zero {x : ℝ} (hx : 0 < x) : (logDeriv Gammaℝ (x : ℂ)).im = 0 := by
  have hG : Gammaℝ (x : ℂ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hx)
  have hc := logDeriv_gammaR_conj hG
  rw [Complex.conj_ofReal] at hc
  have hi := congrArg Complex.im hc
  rw [Complex.conj_im] at hi
  linarith

set_option maxHeartbeats 1000000 in
/-- **THE θ IDENTIFICATION**: the Archimedean argument change along `2 → 2+iT → 1/2+iT` equals
    Riemann–Siegel `θ(T)`.  Proof: `Γℝ` holomorphic + non-vanishing on `[1/2,2]×[0,T]` ⟹ its
    rectangle winding is `0`; the real-axis bottom edge contributes `0`; rearrange. -/
theorem archimedean_pathL_eq_theta (T : ℝ) (hT : 0 < T) :
    argChangeVert Gammaℝ 2 0 T + argChangeHoriz Gammaℝ T 2 (1/2)
      = ZeroFreeBridge.riemannSiegelTheta T := by
  -- `logDeriv Γℝ` holomorphic on the closed rectangle `[1/2,2] × [0,T]`
  have hdiffOn : DifferentiableOn ℂ (logDeriv Gammaℝ)
      (Set.Icc (1/2 : ℝ) 2 ×ℂ Set.Icc (0 : ℝ) T) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    have hzre : 0 < z.re := by have h := hz.1.1; norm_num at h; linarith
    have hana := gammaR_analyticAt_of_re_pos hzre
    have hne := Complex.Gammaℝ_ne_zero_of_re_pos hzre
    have heq : logDeriv Gammaℝ = fun w => deriv Gammaℝ w / Gammaℝ w := by
      funext w; rw [logDeriv_apply]
    rw [heq]
    exact ((hana.deriv.differentiableAt).div hana.differentiableAt hne).differentiableWithinAt
  have hrect := RHInBoxAnalytic.rect_arg_principle_generic (1/2) 2 0 T (by norm_num) (le_of_lt hT)
    (logDeriv Gammaℝ) hdiffOn
  -- take imaginary parts: the four-edge argument-change relation
  have him := congrArg Complex.im hrect
  set Ib := ∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ (↑x + ((0 : ℝ) : ℂ) * I) with hIb
  set It := ∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ (↑x + (T : ℂ) * I) with hIt
  set Ir := ∫ y in (0 : ℝ)..T, logDeriv Gammaℝ (((2 : ℝ) : ℂ) + ↑y * I) with hIr
  set Il := ∫ y in (0 : ℝ)..T, logDeriv Gammaℝ (((1/2 : ℝ) : ℂ) + ↑y * I) with hIl
  rw [show (Ib - It + I • Ir - I • Il).im = Ib.im - It.im + Ir.re - Il.re by
        simp only [Complex.sub_im, Complex.add_im, smul_eq_mul, Complex.mul_im,
          Complex.I_im, Complex.I_re, one_mul, zero_mul, zero_add, mul_zero, sub_zero],
      Complex.zero_im] at him
  -- bottom edge (real axis) contributes `0`
  have hbot0 : Ib.im = 0 := by
    have hintb : IntervalIntegrable (fun x : ℝ => logDeriv Gammaℝ (↑x + ((0 : ℝ) : ℂ) * I))
        MeasureTheory.volume (1/2) 2 := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
      have hxre : 0 < ((x : ℂ) + ((0 : ℝ) : ℂ) * I).re := by
        simpa using (by linarith [hx.1] : (0:ℝ) < x)
      exact (ContinuousAt.comp (g := logDeriv Gammaℝ)
        (f := fun t : ℝ => (↑t + ((0 : ℝ) : ℂ) * I))
        (continuousAt_logDeriv_gammaR_of_re_pos hxre) (by fun_prop)).continuousWithinAt
    have hre0 : Ib.im = ∫ x in (1/2 : ℝ)..2, (logDeriv Gammaℝ (↑x + ((0 : ℝ) : ℂ) * I)).im := by
      have h := intervalIntegral.intervalIntegral_im (𝕜 := ℂ) hintb
      simp only [RCLike.im_to_complex] at h
      rw [hIb]; exact h.symm
    rw [hre0]
    have hz0 : (∫ x in (1/2 : ℝ)..2, (logDeriv Gammaℝ (↑x + ((0 : ℝ) : ℂ) * I)).im)
        = ∫ _x in (1/2 : ℝ)..2, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      show (logDeriv Gammaℝ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0
      rw [show ((x : ℂ) + ((0 : ℝ) : ℂ) * I) = ((x : ℝ) : ℂ) by
        simp only [Complex.ofReal_zero, zero_mul, add_zero]]
      exact logDeriv_gammaR_im_zero hx0
    rw [hz0]; simp
  -- identify the edges with AV/AH and θ
  have hθ : ZeroFreeBridge.riemannSiegelTheta T = Il.re := by
    rw [theta_eq_argChangeVert_gammaR]; unfold argChangeVert; rw [← hIl]
  have hAVr : argChangeVert Gammaℝ 2 0 T = Ir.re := by
    unfold argChangeVert; rw [← hIr]
  have hAHt : argChangeHoriz Gammaℝ T 2 (1/2) = -It.im := by
    unfold argChangeHoriz
    rw [intervalIntegral.integral_symm, Complex.neg_im, ← hIt]
  rw [hAVr, hAHt, hθ]
  rw [hbot0] at him
  linarith

/-! ## THE πS HALF + THE Δ_L Λ = θ + πS COMBINE.

The `ζ` part of the completed-zeta argument change along `L : 2 → 2+iT → 1/2+iT` is `πS(T)` (this is
essentially how `riemannS` is defined), and the `Γℝ` part is `θ(T)` (`archimedean_pathL_eq_theta`).
Splitting `logDeriv Λ = logDeriv ζ + logDeriv Γℝ` (`logDeriv_zeta_add_gammaR`) along both legs of `L`
and adding:

  `AV(Λ,2,0,T) + AH(Λ,T,2,1/2) = θ(T) + π·S(T)`.

Requires `ζ ≠ 0` on the height-`T` horizontal `[1/2,2]×{T}` — the classical "T not a zero ordinate"
caveat, honestly inherited.  conjecture1_proved = False. -/

/-- `logDeriv Γℝ` continuous along the line `Re = 2`. -/
theorem continuous_logDeriv_gammaR_line2 :
    Continuous (fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + y * I)) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hre : 0 < ((2 : ℂ) + ↑y * I).re := by simp
  exact ContinuousAt.comp (g := logDeriv Gammaℝ) (f := fun t : ℝ => ((2 : ℂ) + t * I))
    (continuousAt_logDeriv_gammaR_of_re_pos hre) (by fun_prop)

/-- **Vertical split on `Re = 2`**: `AV(Λ,2,0,T) = AV(ζ,2,0,T) + AV(Γℝ,2,0,T)`. -/
theorem argChangeVert_completedZeta_line2_split (T : ℝ) :
    argChangeVert completedRiemannZeta 2 0 T
      = argChangeVert riemannZeta 2 0 T + argChangeVert Gammaℝ 2 0 T := by
  unfold argChangeVert
  rw [show (((2 : ℝ)) : ℂ) = (2 : ℂ) by norm_num]
  have iζ := continuous_logDeriv_zeta_line2.intervalIntegrable (μ := MeasureTheory.volume) 0 T
  have iΓ := continuous_logDeriv_gammaR_line2.intervalIntegrable (μ := MeasureTheory.volume) 0 T
  have hpt : ∀ y : ℝ, logDeriv completedRiemannZeta ((2 : ℂ) + y * I)
      = logDeriv riemannZeta ((2 : ℂ) + y * I) + logDeriv Gammaℝ ((2 : ℂ) + y * I) := by
    intro y
    have hs0 : ((2 : ℂ) + y * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hs1 : ((2 : ℂ) + y * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hζ : riemannZeta ((2 : ℂ) + y * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    have hG : Gammaℝ ((2 : ℂ) + y * I) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
    exact logDeriv_zeta_add_gammaR hs0 hs1 hζ hG
  rw [intervalIntegral.integral_congr (g := fun y => logDeriv riemannZeta ((2 : ℂ) + y * I)
        + logDeriv Gammaℝ ((2 : ℂ) + y * I)) (fun y _ => hpt y),
      intervalIntegral.integral_add iζ iΓ, Complex.add_re]

/-- **Horizontal split on `Im = T`** (`ζ ≠ 0` on the segment): `AH(Λ,T,2,1/2) = AH(ζ,T,2,1/2) +
    AH(Γℝ,T,2,1/2)`. -/
theorem argChangeHoriz_completedZeta_height_split (T : ℝ) (hT : 0 < T)
    (hζT : ∀ x ∈ Set.uIcc (2 : ℝ) (1/2), riemannZeta (↑x + (T : ℂ) * I) ≠ 0) :
    argChangeHoriz completedRiemannZeta T 2 (1/2)
      = argChangeHoriz riemannZeta T 2 (1/2) + argChangeHoriz Gammaℝ T 2 (1/2) := by
  unfold argChangeHoriz
  have cζ : ContinuousOn (fun x : ℝ => logDeriv riemannZeta (↑x + (T : ℂ) * I))
      (Set.uIcc (2 : ℝ) (1/2)) := by
    intro x hx
    have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
      intro h; have hi := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero, Complex.one_im] at hi
      linarith
    have hana : AnalyticAt ℂ riemannZeta ((x : ℂ) + (T : ℂ) * I) := analyticOn_riemannZeta _ hne1
    have hcAt : ContinuousAt (logDeriv riemannZeta) ((x : ℂ) + (T : ℂ) * I) := by
      have heq : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
        funext w; rw [logDeriv_apply]
      rw [heq]; exact (hana.deriv.continuousAt).div hana.continuousAt (hζT x hx)
    exact (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun t : ℝ => ((t : ℂ) + (T : ℂ) * I))
      hcAt (by fun_prop)).continuousWithinAt
  have cΓ : ContinuousOn (fun x : ℝ => logDeriv Gammaℝ (↑x + (T : ℂ) * I))
      (Set.uIcc (2 : ℝ) (1/2)) := by
    intro x hx
    have him : ((x : ℂ) + (T : ℂ) * I).im ≠ 0 := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      linarith
    exact (ContinuousAt.comp (g := logDeriv Gammaℝ) (f := fun t : ℝ => ((t : ℂ) + (T : ℂ) * I))
      (logDeriv_gammaR_continuousAt_of_im_ne him) (by fun_prop)).continuousWithinAt
  have iζ := cζ.intervalIntegrable (μ := MeasureTheory.volume)
  have iΓ := cΓ.intervalIntegrable (μ := MeasureTheory.volume)
  have hpt : Set.EqOn (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (T : ℂ) * I))
      (fun x : ℝ => logDeriv riemannZeta (↑x + (T : ℂ) * I)
        + logDeriv Gammaℝ (↑x + (T : ℂ) * I)) (Set.uIcc (2 : ℝ) (1/2)) := by
    intro x hx
    have him : ((x : ℂ) + (T : ℂ) * I).im ≠ 0 := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      linarith
    have hs0 : ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
      intro h; apply him; rw [h]; simp
    have hs1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
      intro h; apply him; rw [h]; simp
    exact logDeriv_zeta_add_gammaR hs0 hs1 (hζT x hx) (gammaR_ne_zero_of_im_ne him)
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add iζ iΓ, Complex.add_im]

/-- **Δ_L Λ = θ + πS**: the completed-zeta argument change along `2 → 2+iT → 1/2+iT` is `θ(T)` plus
    `π·S(T)`.  (`ζ ≠ 0` on the height-`T` horizontal — the classical zero-ordinate caveat.) -/
theorem completedZeta_pathL_eq_theta_add_piS (T : ℝ) (hT : 0 < T)
    (hζT : ∀ x ∈ Set.uIcc (2 : ℝ) (1/2), riemannZeta (↑x + (T : ℂ) * I) ≠ 0) :
    argChangeVert completedRiemannZeta 2 0 T + argChangeHoriz completedRiemannZeta T 2 (1/2)
      = ZeroFreeBridge.riemannSiegelTheta T + π * riemannS T := by
  have hAV := argChangeVert_completedZeta_line2_split T
  have hAH := argChangeHoriz_completedZeta_height_split T hT hζT
  have hArch := archimedean_pathL_eq_theta T hT
  have hS : π * riemannS T
      = argChangeVert riemannZeta 2 0 T + argChangeHoriz riemannZeta T 2 (1/2) := by
    rw [riemannS]; field_simp
  rw [hAV, hAH]
  linarith

/-! ## THE COMPLETED-ZETA REFLECTION-CONJUGATION FOLD (left-right edge gear of `Δ_box = 2·Δ_L`).

`Λ = completedRiemannZeta` satisfies `Λ(1−s) = Λ(s)` and `Λ(s̄) = conj Λ(s)` (the latter built here
from `completedRiemannZeta_eq` + `Λ₀`'s conjugation symmetry + conj-of-reciprocal — Mathlib has no
direct lemma).  Unlike `Λ₀`, `Λ`'s strip zeros ARE `ζ`'s zeros (`Λ = Γℝ·ζ`, `Γℝ ≠ 0` in the strip).
Combining reflection + conjugation gives the clean left-right fold, for `Im = y > 0`:

  `Re(logDeriv Λ (σ+iy)) + Re(logDeriv Λ ((1−σ)+iy)) = 0`

— the completed-zeta analog of `fold_pointwise_zeta₀`, on the object with the RIGHT zeros.  This is
the reflection gear that collapses the box's left half onto its right (`Δ_box = 2·Δ_L`); the
remaining literal-`N(T)` work is the box argument principle for `Λ` with its poles at `0,1`
(the source of the `+1`) and the `T0→0⁺` base.  conjecture1_proved = False. -/

/-- **`Λ` is conjugation-symmetric**: `Λ(s̄) = conj Λ(s)` (from `Λ = Λ₀ − 1/s − 1/(1−s)`, `Λ₀`
    conj-symmetric, and conj-of-reciprocal). -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq,
    ZetaZeroLocalization.completedRiemannZeta₀_conj]
  simp only [map_sub, map_div₀, map_one]

/-- `Λ` log-derivative under conjugation (`s ∉ {0,1}`). -/
theorem logDeriv_completedZeta_conj {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (logDeriv completedRiemannZeta s) :=
  logDeriv_conj_of_conj_symm (fun z => completedRiemannZeta_conj z)
    (differentiableAt_completedZeta hs0 hs1)

/-- **THE COMPLETED-ZETA FOLD, pointwise** (`Im = y > 0`): `Re(logDeriv Λ(σ+iy)) +
    Re(logDeriv Λ((1−σ)+iy)) = 0`. -/
theorem fold_pointwise_completedZeta (sigma y : ℝ) (hy : 0 < y) :
    (logDeriv completedRiemannZeta ((sigma : ℂ) + y * I)).re
      + (logDeriv completedRiemannZeta (((1 - sigma : ℝ) : ℂ) + y * I)).re = 0 := by
  set s : ℂ := (sigma : ℂ) + y * I with hsdef
  set s' : ℂ := ((1 - sigma : ℝ) : ℂ) + y * I with hs'def
  have hsim : s.im = y := by rw [hsdef]; simp
  have hs'im : s'.im = y := by rw [hs'def]; simp
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsim; simp at hsim; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsim; simp at hsim; linarith
  have hs'0 : s' ≠ 0 := by intro h; rw [h] at hs'im; simp at hs'im; linarith
  have hs'1 : s' ≠ 1 := by intro h; rw [h] at hs'im; simp at hs'im; linarith
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s' := by
    rw [hsdef, hs'def]; apply Complex.ext <;> simp <;> ring
  have hrefl := logDeriv_completedZeta_reflect hs0 hs1
  rw [hconj, logDeriv_completedZeta_conj hs'0 hs'1] at hrefl
  have hre := congrArg Complex.re hrefl
  simp only [Complex.conj_re, Complex.neg_re] at hre
  linarith [hre]

/-! ## THE ξ FUNCTION — ENTIRE, WITH NO REMOVABLE-SINGULARITY WORK.

The classical `ξ(s) = ½ s(s−1) Λ(s)` (`Λ = completedRiemannZeta`, poles at `0,1`) is entire because
the `s(s−1)` factor kills both poles.  Rather than build that via two removable-singularity limits,
use the exact identity `ξ(s) = ½ s(s−1) Λ₀(s) + ½` (the pole corrections `−1/s − 1/(1−s)` of
`completedRiemannZeta_eq` cancel algebraically against `s(s−1)`).  Since `Λ₀` is ALREADY entire
(`differentiable_completedZeta₀`), this definition is MANIFESTLY entire — no limits.  It is symmetric
(`ξ(1−s)=ξ(s)`, since `½s(s−1)` and `Λ₀` both are) and conj-symmetric, and equals the classical
`½s(s−1)Λ` off `{0,1}`.  Its strip zeros are exactly the nontrivial `ζ`-zeros — the entire,
symmetric object RvM's box argument principle wants.  conjecture1_proved = False. -/

/-- **The Riemann `ξ`**, defined via the entire `Λ₀` (so manifestly entire):
    `ξ(s) = ½ s(s−1) Λ₀(s) + ½ = ½ s(s−1) Λ(s)`. -/
noncomputable def xiTele (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1)) * completedRiemannZeta₀ s + 1 / 2

/-- `ξ` is ENTIRE (no removable singularities — `Λ₀` is already entire). -/
theorem differentiable_xiTele : Differentiable ℂ xiTele := by
  have hpoly : Differentiable ℂ (fun s : ℂ => (1 / 2) * (s * (s - 1))) := by fun_prop
  exact (hpoly.mul differentiable_completedZeta₀).add_const _

/-- **`ξ(s) = ½ s(s−1) Λ(s)`** off the poles (`s ∉ {0,1}`): the classical form. -/
theorem xiTele_eq_completedZeta_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiTele s = (1 / 2) * (s * (s - 1)) * completedRiemannZeta s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr fun h => hs1 h.symm
  unfold xiTele
  rw [completedRiemannZeta_eq]
  field_simp
  ring

/-- **`ξ` is symmetric**: `ξ(1−s) = ξ(s)` (both `½s(s−1)` and `Λ₀` are `s↦1−s`-symmetric). -/
theorem xiTele_one_sub (s : ℂ) : xiTele (1 - s) = xiTele s := by
  unfold xiTele
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- **`ξ` is conjugation-symmetric**: `ξ(s̄) = conj ξ(s)`. -/
theorem xiTele_conj (s : ℂ) : xiTele ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiTele s) := by
  unfold xiTele
  rw [ZetaZeroLocalization.completedRiemannZeta₀_conj]
  simp only [map_add, map_mul, map_sub, map_one, map_div₀, map_ofNat]

/-- **`ξ`'s zeros off `{0,1}` are exactly `ζ`'s zeros** in the analytic-`Λ` region: for `s ∉ {0,1}`
    with `Γℝ s ≠ 0` (e.g. `Re s > 0`), `ξ s = 0 ↔ ζ s = 0`.  (`½s(s−1) ≠ 0` off `{0,1}`,
    `Λ = Γℝ·ζ`.) -/
theorem xiTele_eq_zero_iff {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    xiTele s = 0 ↔ riemannZeta s = 0 := by
  have hfac : (1 / 2 : ℂ) * (s * (s - 1)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
  have hΛ : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs0]; field_simp
  rw [xiTele_eq_completedZeta_mul hs0 hs1, hΛ]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hA | hζΓ
    · exact absurd hA hfac
    · rcases mul_eq_zero.mp hζΓ with hζ | hΓ0
      · exact hζ
      · exact absurd hΓ0 hG
  · intro h; rw [h]; ring

/-! ## BRICK 1: the ξ box argument principle — ξ zero-count = boundary winding.

`ξ` is entire, so it meets the three prerequisites of the generic Blaschke count more cleanly than
`ζ` did (no pole to dodge, order finite everywhere seeded from `ξ(1) = ½ ≠ 0`).  Instantiating
`analytic_count_eq_winding_generic` at `ξ` gives: for a box with `ξ ≠ 0` on the edges and its zeros
strictly interior, if the boundary winding of `logDeriv ξ` is `2πiN` then the box zero-count of `ξ`
is `N` — no `+1` (unlike the `ζ` route, `ξ` is entire, no pole enclosed).  Via `xiTele_eq_zero_iff`,
those box zeros are the nontrivial `ζ`-zeros.  conjecture1_proved = False. -/

/-- `ξ` analytic on any set (entire). -/
theorem analyticOnNhd_xiTele (U : Set ℂ) : AnalyticOnNhd ℂ xiTele U :=
  fun z _ => (differentiable_xiTele.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)

/-- `ξ` analytic at every point. -/
theorem analyticAt_xiTele (z : ℂ) : AnalyticAt ℂ xiTele z :=
  analyticOnNhd_xiTele Set.univ z (Set.mem_univ z)

/-- **Prereq 2**: `ξ`'s meromorphic order is finite everywhere (entire, not `≡ 0` since
    `ξ(1) = ½`). -/
theorem meromorphicOrderAt_xiTele_ne_top (u : ℂ) : meromorphicOrderAt xiTele u ≠ ⊤ := by
  have hMero : MeromorphicOn xiTele (Set.univ : Set ℂ) :=
    fun z _ => (analyticAt_xiTele z).meromorphicAt
  have hAt1 : AnalyticAt ℂ xiTele 1 := analyticAt_xiTele 1
  have hne1 : xiTele 1 ≠ 0 := by
    have h : xiTele 1 = 1 / 2 := by unfold xiTele; ring
    rw [h]; norm_num
  have hord1 : meromorphicOrderAt xiTele 1 ≠ ⊤ := by
    rw [hAt1.meromorphicOrderAt_eq, hAt1.analyticOrderAt_eq_zero.mpr hne1]; simp
  exact hMero.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 1) (Set.mem_univ u) hord1

/-- **Prereq 3**: `ξ`'s divisor is finite on any ball (entire ⟹ meromorphic on the closed ball). -/
theorem divisor_xiTele_ball_support_finite (c : ℂ) (R : ℝ) :
    (MeromorphicOn.divisor xiTele (Metric.ball c R)).support.Finite := by
  have hMero : MeromorphicOn xiTele (Metric.closedBall c R) :=
    fun z _ => (analyticAt_xiTele z).meromorphicAt
  exact hMero.divisor_ball_support_finite

/-- **THE ξ BOX ARGUMENT PRINCIPLE**: for a box with `ξ ≠ 0` on the edges, its zeros strictly
    interior, and `ξ` boundary winding `2πiN`, the box zero-count of `ξ` is `N` (no `+1`: `ξ` is
    entire).  All `hArb` integrabilities discharged internally. -/
theorem xiTele_count_eq_winding
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ)
    (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, xiTele (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, xiTele (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, xiTele ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, xiTele ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hin : ∀ ρ ∈ (divisor_xiTele_ball_support_finite c R).toFinset,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hwind : (∫ x in sigma0..sigma1, logDeriv xiTele (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv xiTele (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, logDeriv xiTele ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, logDeriv xiTele ((sigma0 : ℂ) + ↑y * I))
      = 2 * π * I * (N : ℂ)) :
    ∃ (s : Finset ℂ) (d : ℂ → ℤ),
      (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧
      (∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
        xiTele ρ = 0 → ρ ∈ s) ∧
      (∑ ρ ∈ s, d ρ) = N := by
  refine analytic_count_eq_winding_generic xiTele sigma0 sigma1 T0 T1 c R N
    (analyticOnNhd_xiTele _) (fun u _ => meromorphicOrderAt_xiTele_ne_top u)
    (divisor_xiTele_ball_support_finite c R) hsig hT hbox_ball hwind ?_
  intro E _s _d hEholo _hker
  refine ⟨hnzb, hnzt, hnzr, hnzl, hin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ρ hρ => intervalIntegrable_inv_sub_horiz (ne_of_lt (hin ρ hρ).2.2.1) _ _
  · exact fun ρ hρ => intervalIntegrable_inv_sub_horiz ((ne_of_lt (hin ρ hρ).2.2.2).symm) _ _
  · exact fun ρ hρ => intervalIntegrable_inv_sub_vert ((ne_of_lt (hin ρ hρ).2.1).symm) _ _
  · exact fun ρ hρ => intervalIntegrable_inv_sub_vert (ne_of_lt (hin ρ hρ).1) _ _
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_horiz (ne_of_lt (hin ρ hρ).2.2.1) _ _).const_mul _)
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_horiz ((ne_of_lt (hin ρ hρ).2.2.2).symm) _ _).const_mul _)
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_vert ((ne_of_lt (hin ρ hρ).2.1).symm) _ _).const_mul _)
  · exact intervalIntegrable_finsetSum _ (fun ρ hρ =>
      (intervalIntegrable_inv_sub_vert (ne_of_lt (hin ρ hρ).1) _ _).const_mul _)
  · exact intervalIntegrable_diffBox_horiz ⟨le_refl _, hT⟩ hsig hEholo
  · exact intervalIntegrable_diffBox_horiz ⟨hT, le_refl _⟩ hsig hEholo
  · exact intervalIntegrable_diffBox_vert ⟨hsig, le_refl _⟩ hT hEholo
  · exact intervalIntegrable_diffBox_vert ⟨le_refl _, hsig⟩ hT hEholo

/-! ## BRICK 3 (pointwise): the `logDeriv ξ` split — the pole/`+1` factor separated from `Λ`.

`ξ = ½s(s−1)·Λ` off `{0,1}`, so `logDeriv ξ = logDeriv[½s(s−1)] + logDeriv Λ`.  The polynomial's
log-derivative is `1/s + 1/(s−1)` (the `½` drops), whose argument change along the right-half path
is the `+1`; the `Λ` part's is `θ + πS` (`completedZeta_pathL_eq_theta_add_piS`).
conjecture1_proved = False. -/

/-- `logDeriv[½s(s−1)] = 1/s + 1/(s−1)` (the constant `½` drops out of the log-derivative). -/
theorem logDeriv_halfPoly {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv (fun z : ℂ => (1 / 2) * (z * (z - 1))) s = s⁻¹ + (s - 1)⁻¹ := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hid : HasDerivAt (fun z : ℂ => z) 1 s := hasDerivAt_id' (x := s)
  have hprod : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
    hid.mul (hid.sub_const 1)
  have hd : HasDerivAt (fun z : ℂ => (1 / 2) * (z * (z - 1)))
      ((1 / 2) * (1 * (s - 1) + s * 1)) s := hprod.const_mul (1 / 2)
  rw [logDeriv_apply, hd.deriv]
  field_simp

/-- **The `logDeriv ξ` split**: `logDeriv ξ (s) = (1/s + 1/(s−1)) + logDeriv Λ (s)` for `s ∉ {0,1}`,
    `ζ s ≠ 0`, `Γℝ s ≠ 0`. -/
theorem logDeriv_xiTele_split {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    logDeriv xiTele s = (s⁻¹ + (s - 1)⁻¹) + logDeriv completedRiemannZeta s := by
  have hΛ : completedRiemannZeta s ≠ 0 := by
    have hval : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
      rw [riemannZeta_def_of_ne_zero hs0]; field_simp
    rw [hval]; exact mul_ne_zero hζ hG
  have hfac : (1 / 2 : ℂ) * (s * (s - 1)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
  have heq : xiTele =ᶠ[nhds s]
      fun z : ℂ => ((1 / 2) * (z * (z - 1))) * completedRiemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
    exact xiTele_eq_completedZeta_mul hz0 hz1
  rw [RHInBoxAnalytic.logDeriv_congr_nhds heq,
    logDeriv_mul s hfac hΛ (by fun_prop) (differentiableAt_completedZeta hs0 hs1),
    logDeriv_halfPoly hs0 hs1]

/-! ## BRICK 3 (integral): the pole factor's path argument change IS the `+1`.

`Δ_L arg(·−r)` along `L : 2 → 2+iT → ½+iT` telescopes (shared corner `2+iT` cancels; start `2−r`
is positive-real, arg `0`) to `arg((½−r)+iT)`, for real `r < 2`.  Summing the two pole factors
`r = 0, 1` (`logDeriv[½s(s−1)] = (·)⁻¹ + (·−1)⁻¹`) gives `arg(½+iT) + arg(−½+iT) = π` — the RvM `+1`
(after `÷π`), a boundary-log computation, not a winding number.  conjecture1_proved = False. -/


/-- **`Δ_L arg(·−ρ)` along the L-path** (`ρ` with `Im ρ = 0`, `Re ρ < 2`): telescopes to
    `arg((½−ρ)+iT)`. -/
theorem argChangeL_sub_const (ρ : ℂ) (T : ℝ) (hT : 0 < T) (hρim : ρ.im = 0) (hρre : ρ.re < 2) :
    argChangeVert (fun z : ℂ => z - ρ) 2 0 T
      + argChangeHoriz (fun z : ℂ => z - ρ) T 2 (1/2)
      = (((1/2 : ℝ) : ℂ) + (T : ℂ) * I - ρ).arg := by
  have hreV : ∀ y : ℝ, ((2:ℂ)+(y:ℂ)*I-ρ).re = 2 - ρ.re := by intro y; simp
  have himH : ∀ x : ℝ, ((x:ℂ)+(T:ℂ)*I-ρ).im = T - ρ.im := by intro x; simp
  -- VERTICAL leg antiderivative (Re = 2 − Re ρ > 0 ⇒ slitPlane)
  have hFderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.log ((2:ℂ)+(y:ℂ)*I-ρ))
      (I • ((2:ℂ)+(y:ℂ)*I-ρ)⁻¹) y := by
    intro y
    have hpath : HasDerivAt (fun y : ℝ => (2:ℂ)+(y:ℂ)*I-ρ) I y := by
      have h1 : HasDerivAt (fun y:ℝ => (y:ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
      have h2 : HasDerivAt (fun y:ℝ => (y:ℂ)*I) I y := by simpa using h1.mul_const I
      exact (h2.const_add (2:ℂ)).sub_const ρ
    have hslit : ((2:ℂ)+(y:ℂ)*I-ρ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; rw [hreV y]; linarith
    have hd := hpath.clog_real hslit
    rw [div_eq_mul_inv, ← smul_eq_mul] at hd
    exact hd
  have hcontVpath : Continuous (fun y : ℝ => (2:ℂ)+(y:ℂ)*I-ρ) :=
    (continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)).sub continuous_const
  have hcontV : Continuous (fun y : ℝ => I • ((2:ℂ)+(y:ℂ)*I-ρ)⁻¹) :=
    (hcontVpath.inv₀ (fun y => by
      intro hc; have := congrArg Complex.re hc; rw [hreV y] at this; simp at this; linarith)).const_smul I
  have hV : I • (∫ y in (0:ℝ)..T, ((2:ℂ)+(y:ℂ)*I-ρ)⁻¹)
      = Complex.log ((2:ℂ)+(T:ℂ)*I-ρ) - Complex.log ((2:ℂ)+((0:ℝ):ℂ)*I-ρ) := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hFderiv y)
      (hcontV.intervalIntegrable _ _)
  -- HORIZONTAL leg antiderivative (Im = T > 0 ⇒ slitPlane)
  have hGderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.log ((x:ℂ)+(T:ℂ)*I-ρ))
      (((x:ℂ)+(T:ℂ)*I-ρ)⁻¹) x := by
    intro x
    have hpath : HasDerivAt (fun x:ℝ => (x:ℂ)+(T:ℂ)*I-ρ) 1 x := by
      have h1 : HasDerivAt (fun x:ℝ => (x:ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
      exact (h1.add_const ((T:ℂ)*I)).sub_const ρ
    have hslit : ((x:ℂ)+(T:ℂ)*I-ρ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right; rw [himH x, hρim, sub_zero]; exact ne_of_gt hT
    have hd := hpath.clog_real hslit
    rwa [one_div] at hd
  have hcontHpath : Continuous (fun x : ℝ => (x:ℂ)+(T:ℂ)*I-ρ) :=
    ((Complex.continuous_ofReal).add continuous_const).sub continuous_const
  have hcontH : Continuous (fun x : ℝ => ((x:ℂ)+(T:ℂ)*I-ρ)⁻¹) :=
    hcontHpath.inv₀ (fun x => by
      intro hc; have := congrArg Complex.im hc; rw [himH x, hρim, sub_zero] at this
      exact (ne_of_gt hT) this)
  have hH : (∫ x in (2:ℝ)..(1/2), ((x:ℂ)+(T:ℂ)*I-ρ)⁻¹)
      = Complex.log (((1/2:ℝ):ℂ)+(T:ℂ)*I-ρ) - Complex.log (((2:ℝ):ℂ)+(T:ℂ)*I-ρ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hGderiv x)
      (hcontH.intervalIntegrable _ _)
  unfold argChangeVert argChangeHoriz
  rw [show (((2:ℝ)):ℂ) = (2:ℂ) by norm_num]
  rw [intervalIntegral.integral_congr (g := fun y => ((2:ℂ)+(y:ℂ)*I-ρ)⁻¹)
        (fun y _ => logDeriv_sub_const ρ _),
      intervalIntegral.integral_congr (g := fun x => ((x:ℂ)+(T:ℂ)*I-ρ)⁻¹)
        (fun x _ => logDeriv_sub_const ρ _)]
  have hAV : (∫ y in (0:ℝ)..T, ((2:ℂ)+(y:ℂ)*I-ρ)⁻¹).re
      = (Complex.log ((2:ℂ)+(T:ℂ)*I-ρ) - Complex.log ((2:ℂ)+((0:ℝ):ℂ)*I-ρ)).im := by
    have h := congrArg Complex.im hV
    simpa [Complex.mul_im] using h
  rw [hAV, hH]
  have hcorner : Complex.log ((2:ℂ)+(T:ℂ)*I-ρ) = Complex.log (((2:ℝ):ℂ)+(T:ℂ)*I-ρ) := by
    norm_num
  have hstart : (Complex.log ((2:ℂ)+((0:ℝ):ℂ)*I-ρ)).im = 0 := by
    rw [Complex.log_im, Complex.arg_eq_zero_iff]
    refine ⟨?_, ?_⟩
    · have : ((2:ℂ)+((0:ℝ):ℂ)*I-ρ).re = 2 - ρ.re := by simp
      rw [this]; linarith
    · have : ((2:ℂ)+((0:ℝ):ℂ)*I-ρ).im = -ρ.im := by simp
      rw [this, hρim, neg_zero]
  rw [hcorner, Complex.sub_im, Complex.sub_im, hstart]
  simp only [Complex.log_im]
  ring

/-- **THE `+1`, path form**: `Δ_L arg[½s(s−1)] = π`. -/
theorem pole_pathL_eq_pi (T : ℝ) (hT : 0 < T) :
    argChangeVert (fun z : ℂ => (1 / 2) * (z * (z - 1))) 2 0 T
      + argChangeHoriz (fun z : ℂ => (1 / 2) * (z * (z - 1))) T 2 (1/2) = π := by
  have h0 := argChangeL_sub_const 0 T hT (by simp) (by simp)
  have h1 := argChangeL_sub_const 1 T hT (by simp) (by norm_num)
  have hsplitV : ∀ y : ℝ, logDeriv (fun z : ℂ => (1/2)*(z*(z-1))) ((2:ℂ)+(y:ℂ)*I)
      = logDeriv (fun z:ℂ=>z-(0:ℂ)) ((2:ℂ)+(y:ℂ)*I)
        + logDeriv (fun z:ℂ=>z-(1:ℂ)) ((2:ℂ)+(y:ℂ)*I) := by
    intro y
    have hne0 : ((2:ℂ)+(y:ℂ)*I) ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
    have hne1 : ((2:ℂ)+(y:ℂ)*I) ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this
    rw [logDeriv_halfPoly hne0 hne1, logDeriv_sub_const, logDeriv_sub_const, sub_zero]
  have hsplitH : ∀ x : ℝ, logDeriv (fun z : ℂ => (1/2)*(z*(z-1))) ((x:ℂ)+(T:ℂ)*I)
      = logDeriv (fun z:ℂ=>z-(0:ℂ)) ((x:ℂ)+(T:ℂ)*I)
        + logDeriv (fun z:ℂ=>z-(1:ℂ)) ((x:ℂ)+(T:ℂ)*I) := by
    intro x
    have him : ((x:ℂ)+(T:ℂ)*I).im ≠ 0 := by
      have h : ((x:ℂ)+(T:ℂ)*I).im = T := by simp
      rw [h]; exact ne_of_gt hT
    have hne0 : ((x:ℂ)+(T:ℂ)*I) ≠ 0 := by intro h; apply him; rw [h]; simp
    have hne1 : ((x:ℂ)+(T:ℂ)*I) ≠ 1 := by intro h; apply him; rw [h]; simp
    rw [logDeriv_halfPoly hne0 hne1, logDeriv_sub_const, logDeriv_sub_const, sub_zero]
  have cpV : Continuous (fun y : ℝ => (2:ℂ)+(y:ℂ)*I) :=
    continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)
  have cpH : Continuous (fun x : ℝ => (x:ℂ)+(T:ℂ)*I) :=
    (Complex.continuous_ofReal).add continuous_const
  have iv0 : IntervalIntegrable (fun y:ℝ => logDeriv (fun z:ℂ=>z-(0:ℂ)) ((2:ℂ)+(y:ℂ)*I))
      MeasureTheory.volume 0 T := by
    have he : (fun y:ℝ => logDeriv (fun z:ℂ=>z-(0:ℂ)) ((2:ℂ)+(y:ℂ)*I))
        = fun y:ℝ => ((2:ℂ)+(y:ℂ)*I)⁻¹ := by funext y; rw [logDeriv_sub_const, sub_zero]
    rw [he]; apply Continuous.intervalIntegrable
    exact cpV.inv₀ (fun y => by intro h; have := congrArg Complex.re h; simp at this)
  have iv1 : IntervalIntegrable (fun y:ℝ => logDeriv (fun z:ℂ=>z-(1:ℂ)) ((2:ℂ)+(y:ℂ)*I))
      MeasureTheory.volume 0 T := by
    have he : (fun y:ℝ => logDeriv (fun z:ℂ=>z-(1:ℂ)) ((2:ℂ)+(y:ℂ)*I))
        = fun y:ℝ => ((2:ℂ)+(y:ℂ)*I-1)⁻¹ := by funext y; rw [logDeriv_sub_const]
    rw [he]; apply Continuous.intervalIntegrable
    refine Continuous.inv₀ (f := fun y:ℝ => (2:ℂ)+(y:ℂ)*I-1)
      (cpV.sub continuous_const) (fun y => ?_)
    intro hz
    have hre1 : ((2:ℂ)+(y:ℂ)*I-1).re = 1 := by simp; norm_num
    rw [hz] at hre1; simp at hre1
  have ih0 : IntervalIntegrable (fun x:ℝ => logDeriv (fun z:ℂ=>z-(0:ℂ)) ((x:ℂ)+(T:ℂ)*I))
      MeasureTheory.volume 2 (1/2) := by
    have he : (fun x:ℝ => logDeriv (fun z:ℂ=>z-(0:ℂ)) ((x:ℂ)+(T:ℂ)*I))
        = fun x:ℝ => ((x:ℂ)+(T:ℂ)*I)⁻¹ := by funext x; rw [logDeriv_sub_const, sub_zero]
    rw [he]; apply Continuous.intervalIntegrable
    refine cpH.inv₀ (fun x => ?_)
    intro h; have h2 := congrArg Complex.im h; simp at h2; linarith
  have ih1 : IntervalIntegrable (fun x:ℝ => logDeriv (fun z:ℂ=>z-(1:ℂ)) ((x:ℂ)+(T:ℂ)*I))
      MeasureTheory.volume 2 (1/2) := by
    have he : (fun x:ℝ => logDeriv (fun z:ℂ=>z-(1:ℂ)) ((x:ℂ)+(T:ℂ)*I))
        = fun x:ℝ => ((x:ℂ)+(T:ℂ)*I-1)⁻¹ := by funext x; rw [logDeriv_sub_const]
    rw [he]; apply Continuous.intervalIntegrable
    refine Continuous.inv₀ (f := fun x:ℝ => (x:ℂ)+(T:ℂ)*I-1)
      (cpH.sub continuous_const) (fun x => ?_)
    intro hz
    apply ne_of_gt hT
    have h2 := congrArg Complex.im hz
    simpa using h2
  have hAVsplit : argChangeVert (fun z:ℂ=>(1/2)*(z*(z-1))) 2 0 T
      = argChangeVert (fun z:ℂ=>z-(0:ℂ)) 2 0 T + argChangeVert (fun z:ℂ=>z-(1:ℂ)) 2 0 T := by
    unfold argChangeVert
    rw [show (((2:ℝ)):ℂ) = (2:ℂ) by norm_num,
      intervalIntegral.integral_congr (g := fun y => logDeriv (fun z:ℂ=>z-(0:ℂ)) ((2:ℂ)+(y:ℂ)*I)
        + logDeriv (fun z:ℂ=>z-(1:ℂ)) ((2:ℂ)+(y:ℂ)*I)) (fun y _ => hsplitV y),
      intervalIntegral.integral_add iv0 iv1, Complex.add_re]
  have hAHsplit : argChangeHoriz (fun z:ℂ=>(1/2)*(z*(z-1))) T 2 (1/2)
      = argChangeHoriz (fun z:ℂ=>z-(0:ℂ)) T 2 (1/2) + argChangeHoriz (fun z:ℂ=>z-(1:ℂ)) T 2 (1/2) := by
    unfold argChangeHoriz
    rw [intervalIntegral.integral_congr (g := fun x => logDeriv (fun z:ℂ=>z-(0:ℂ)) ((x:ℂ)+(T:ℂ)*I)
        + logDeriv (fun z:ℂ=>z-(1:ℂ)) ((x:ℂ)+(T:ℂ)*I)) (fun x _ => hsplitH x),
      intervalIntegral.integral_add ih0 ih1, Complex.add_im]
  -- arg(½+iT) + arg(−½+iT) = π (reflection pair, via log_neg_sub_im_neg + arg_conj)
  have harg : (((1/2:ℝ):ℂ)+(T:ℂ)*I-(0:ℂ)).arg + (((1/2:ℝ):ℂ)+(T:ℂ)*I-(1:ℂ)).arg = π := by
    set w : ℂ := ((1/2:ℝ):ℂ)+(T:ℂ)*I with hw
    set x : ℂ := ((1/2:ℝ):ℂ)-(T:ℂ)*I with hx
    have e0 : (((1/2:ℝ):ℂ)+(T:ℂ)*I-(0:ℂ)) = w := by rw [hw]; ring
    have e1 : (((1/2:ℝ):ℂ)+(T:ℂ)*I-(1:ℂ)) = -x := by rw [hx]; push_cast; ring
    have hxim : x.im < 0 := by
      have hxi : x.im = -T := by rw [hx]; simp
      rw [hxi]; linarith
    have hlog := RHInBoxAnalytic.log_neg_sub_im_neg x hxim
    have him : (-x).arg - x.arg = π := by
      have h := congrArg Complex.im hlog
      rw [Complex.sub_im, Complex.log_im, Complex.log_im] at h
      simpa [Complex.mul_im] using h
    have hconj : x = (starRingEnd ℂ) w := by
      rw [hx, hw]; apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
    have hwne : w.arg ≠ π := by
      intro h; have hlt := (Complex.arg_eq_pi_iff.mp h).1
      rw [hw] at hlt
      have hre : (((1/2:ℝ):ℂ)+(T:ℂ)*I).re = 1/2 := by simp
      rw [hre] at hlt; norm_num at hlt
    have hxarg : x.arg = -w.arg := by
      rw [hconj, Complex.arg_conj, if_neg hwne]
    rw [e0, e1]
    linarith [him, hxarg]
  rw [hAVsplit, hAHsplit]
  linarith [h0, h1, harg]


/-! ## BRICK 3 (assemble): `Δ_L ξ = π + θ + πS`.

Integrating the pointwise `logDeriv_xiTele_split` (`logDeriv ξ = logDeriv[½s(s−1)] + logDeriv Λ`)
along the right-half path `L : 2 → 2+iT → ½+iT`: the `½s(s−1)` part contributes `π`
(`pole_pathL_eq_pi`), the `Λ` part contributes `θ + πS` (`completedZeta_pathL_eq_theta_add_piS`).
`ζ ≠ 0` on the height-`T` horizontal is the classical zero-ordinate caveat.
conjecture1_proved = False. -/

theorem xiTele_pathL_eq (T : ℝ) (hT : 0 < T)
    (hζT : ∀ x ∈ Set.uIcc (2 : ℝ) (1/2), riemannZeta (↑x + (T : ℂ) * I) ≠ 0) :
    argChangeVert xiTele 2 0 T + argChangeHoriz xiTele T 2 (1/2)
      = π + (ZeroFreeBridge.riemannSiegelTheta T + π * riemannS T) := by
  -- path continuities
  have cpV : Continuous (fun y : ℝ => (2:ℂ)+(y:ℂ)*I) :=
    continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)
  -- Re=2 nonvanishing facts
  have hne0V : ∀ y : ℝ, ((2:ℂ)+(y:ℂ)*I) ≠ 0 := fun y => by
    intro h; have := congrArg Complex.re h; simp at this
  have hne1V : ∀ y : ℝ, ((2:ℂ)+(y:ℂ)*I) ≠ 1 := fun y => by
    intro h; have := congrArg Complex.re h; simp at this
  have hζV : ∀ y : ℝ, riemannZeta ((2:ℂ)+(y:ℂ)*I) ≠ 0 := fun y =>
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hGV : ∀ y : ℝ, Gammaℝ ((2:ℂ)+(y:ℂ)*I) ≠ 0 := fun y =>
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  -- VERTICAL leg continuities
  have chpV : Continuous (fun y:ℝ => logDeriv (fun z:ℂ=>(1/2)*(z*(z-1))) ((2:ℂ)+(y:ℂ)*I)) := by
    have he : (fun y:ℝ => logDeriv (fun z:ℂ=>(1/2)*(z*(z-1))) ((2:ℂ)+(y:ℂ)*I))
        = fun y:ℝ => ((2:ℂ)+(y:ℂ)*I)⁻¹ + ((2:ℂ)+(y:ℂ)*I-1)⁻¹ := by
      funext y; rw [logDeriv_halfPoly (hne0V y) (hne1V y)]
    rw [he]
    refine Continuous.add (cpV.inv₀ hne0V) ?_
    refine Continuous.inv₀ (f := fun y:ℝ => (2:ℂ)+(y:ℂ)*I-1) (cpV.sub continuous_const) (fun y => ?_)
    intro hz
    have hre1 : ((2:ℂ)+(y:ℂ)*I-1).re = 1 := by simp; norm_num
    rw [hz] at hre1; simp at hre1
  have cΛV : Continuous (fun y:ℝ => logDeriv completedRiemannZeta ((2:ℂ)+(y:ℂ)*I)) := by
    have he : (fun y:ℝ => logDeriv completedRiemannZeta ((2:ℂ)+(y:ℂ)*I))
        = fun y:ℝ => logDeriv riemannZeta ((2:ℂ)+(y:ℂ)*I) + logDeriv Gammaℝ ((2:ℂ)+(y:ℂ)*I) := by
      funext y; exact logDeriv_zeta_add_gammaR (hne0V y) (hne1V y) (hζV y) (hGV y)
    rw [he]; exact continuous_logDeriv_zeta_line2.add continuous_logDeriv_gammaR_line2
  -- VERTICAL split: AV(ξ) = AV(hp) + AV(Λ)
  have hptV : ∀ y : ℝ, logDeriv xiTele ((2:ℂ)+(y:ℂ)*I)
      = logDeriv (fun z:ℂ=>(1/2)*(z*(z-1))) ((2:ℂ)+(y:ℂ)*I)
        + logDeriv completedRiemannZeta ((2:ℂ)+(y:ℂ)*I) := by
    intro y
    rw [logDeriv_xiTele_split (hne0V y) (hne1V y) (hζV y) (hGV y),
      logDeriv_halfPoly (hne0V y) (hne1V y)]
  have hAV : argChangeVert xiTele 2 0 T
      = argChangeVert (fun z:ℂ=>(1/2)*(z*(z-1))) 2 0 T + argChangeVert completedRiemannZeta 2 0 T := by
    unfold argChangeVert
    rw [show (((2:ℝ)):ℂ)=(2:ℂ) by norm_num,
      intervalIntegral.integral_congr (fun y _ => hptV y),
      intervalIntegral.integral_add (chpV.intervalIntegrable _ _) (cΛV.intervalIntegrable _ _),
      Complex.add_re]
  -- HORIZONTAL leg: nonvanishing + continuities on the segment (Im = T)
  have himH : ∀ x : ℝ, ((x:ℂ)+(T:ℂ)*I).im ≠ 0 := fun x => by
    have h : ((x:ℂ)+(T:ℂ)*I).im = T := by simp
    rw [h]; exact ne_of_gt hT
  have hne0H : ∀ x : ℝ, ((x:ℂ)+(T:ℂ)*I) ≠ 0 := fun x => by
    intro h; apply himH x; rw [h]; simp
  have hne1H : ∀ x : ℝ, ((x:ℂ)+(T:ℂ)*I) ≠ 1 := fun x => by
    intro h; apply himH x; rw [h]; simp
  have hGH : ∀ x : ℝ, Gammaℝ ((x:ℂ)+(T:ℂ)*I) ≠ 0 := fun x =>
    gammaR_ne_zero_of_im_ne (himH x)
  have chpH : ContinuousOn (fun x:ℝ => logDeriv (fun z:ℂ=>(1/2)*(z*(z-1))) ((x:ℂ)+(T:ℂ)*I))
      (Set.uIcc (2:ℝ) (1/2)) := by
    have he : Set.EqOn (fun x:ℝ => logDeriv (fun z:ℂ=>(1/2)*(z*(z-1))) ((x:ℂ)+(T:ℂ)*I))
        (fun x:ℝ => ((x:ℂ)+(T:ℂ)*I)⁻¹ + ((x:ℂ)+(T:ℂ)*I-1)⁻¹) (Set.uIcc (2:ℝ) (1/2)) := by
      intro x _; dsimp only; rw [logDeriv_halfPoly (hne0H x) (hne1H x)]
    apply ContinuousOn.congr _ he
    have cpH : Continuous (fun x:ℝ => (x:ℂ)+(T:ℂ)*I) :=
      (Complex.continuous_ofReal).add continuous_const
    refine (cpH.inv₀ hne0H).continuousOn.add ?_
    refine (Continuous.inv₀ (f := fun x:ℝ => (x:ℂ)+(T:ℂ)*I-1) (cpH.sub continuous_const)
      (fun x => ?_)).continuousOn
    intro hz; apply ne_of_gt hT
    have h2 := congrArg Complex.im hz; simpa using h2
  have cΛH : ContinuousOn (fun x:ℝ => logDeriv completedRiemannZeta ((x:ℂ)+(T:ℂ)*I))
      (Set.uIcc (2:ℝ) (1/2)) := by
    have he : Set.EqOn (fun x:ℝ => logDeriv completedRiemannZeta ((x:ℂ)+(T:ℂ)*I))
        (fun x:ℝ => logDeriv riemannZeta ((x:ℂ)+(T:ℂ)*I) + logDeriv Gammaℝ ((x:ℂ)+(T:ℂ)*I))
        (Set.uIcc (2:ℝ) (1/2)) := by
      intro x hx; exact logDeriv_zeta_add_gammaR (hne0H x) (hne1H x) (hζT x hx) (hGH x)
    apply ContinuousOn.congr _ he
    have cζ : ContinuousOn (fun x:ℝ => logDeriv riemannZeta ((x:ℂ)+(T:ℂ)*I)) (Set.uIcc (2:ℝ) (1/2)) := by
      intro x hx
      have hana : AnalyticAt ℂ riemannZeta ((x:ℂ)+(T:ℂ)*I) := analyticOn_riemannZeta _ (hne1H x)
      have hcAt : ContinuousAt (logDeriv riemannZeta) ((x:ℂ)+(T:ℂ)*I) := by
        have heq : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
          funext w; rw [logDeriv_apply]
        rw [heq]; exact (hana.deriv.continuousAt).div hana.continuousAt (hζT x hx)
      exact (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun t:ℝ => ((t:ℂ)+(T:ℂ)*I))
        hcAt (by fun_prop)).continuousWithinAt
    have cΓ : ContinuousOn (fun x:ℝ => logDeriv Gammaℝ ((x:ℂ)+(T:ℂ)*I)) (Set.uIcc (2:ℝ) (1/2)) := by
      intro x hx
      exact (ContinuousAt.comp (g := logDeriv Gammaℝ) (f := fun t:ℝ => ((t:ℂ)+(T:ℂ)*I))
        (logDeriv_gammaR_continuousAt_of_im_ne (himH x)) (by fun_prop)).continuousWithinAt
    exact cζ.add cΓ
  -- HORIZONTAL split: AH(ξ) = AH(hp) + AH(Λ)
  have hptH : Set.EqOn (fun x:ℝ => logDeriv xiTele ((x:ℂ)+(T:ℂ)*I))
      (fun x:ℝ => logDeriv (fun z:ℂ=>(1/2)*(z*(z-1))) ((x:ℂ)+(T:ℂ)*I)
        + logDeriv completedRiemannZeta ((x:ℂ)+(T:ℂ)*I)) (Set.uIcc (2:ℝ) (1/2)) := by
    intro x hx
    dsimp only
    rw [logDeriv_xiTele_split (hne0H x) (hne1H x) (hζT x hx) (hGH x),
      logDeriv_halfPoly (hne0H x) (hne1H x)]
  have hAH : argChangeHoriz xiTele T 2 (1/2)
      = argChangeHoriz (fun z:ℂ=>(1/2)*(z*(z-1))) T 2 (1/2) + argChangeHoriz completedRiemannZeta T 2 (1/2) := by
    unfold argChangeHoriz
    rw [intervalIntegral.integral_congr hptH,
      intervalIntegral.integral_add (chpH.intervalIntegrable) (cΛH.intervalIntegrable),
      Complex.add_im]
  have hpole := pole_pathL_eq_pi T hT
  have hΛ := completedZeta_pathL_eq_theta_add_piS T hT hζT
  rw [hAV, hAH]
  linarith [hpole, hΛ]

/-! ## BRICK 2 (the ξ folds): reflection + conjugation of `logDeriv ξ`.

`ξ` is entire, `ξ(1−s) = ξ(s)` (`xiTele_one_sub`), `ξ(s̄) = conj ξ(s)` (`xiTele_conj`).  Differentiating
the reflection gives `logDeriv ξ (1−s) = −logDeriv ξ s`; combined with conjugation, the vertical
argument-change integrand is anti-symmetric across `Re = ½`:

  `Re(logDeriv ξ (σ+iy)) + Re(logDeriv ξ ((1−σ)+iy)) = 0`

— the entire, pole-free fold (RHS exactly `0`, no `Γℝ` remainder) on the object whose zeros are the
nontrivial `ζ`-zeros.  This is the reflection symmetry that collapses the RvM box's left half onto
its right.  The full `Δ_box ξ = 2·Δ_L ξ` additionally needs the bottom-edge reality (`ξ` real on the
real axis) and the top-edge horizontal reflection — the honestly-remaining geometric reduction.
conjecture1_proved = False. -/

/-- **The ξ reflection**: `logDeriv ξ (1−s) = −logDeriv ξ s` (differentiate `ξ(1−s)=ξ(s)`). -/
theorem logDeriv_xiTele_reflect (s : ℂ) :
    logDeriv xiTele (1 - s) = - logDeriv xiTele s := by
  have hsymm : (fun z : ℂ => xiTele (1 - z)) = xiTele := funext xiTele_one_sub
  have hd : DifferentiableAt ℂ xiTele (1 - s) := differentiable_xiTele _
  have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have hcomp : HasDerivAt (fun z : ℂ => xiTele (1 - z)) (deriv xiTele (1 - s) * (-1)) s :=
    hd.hasDerivAt.comp s hinner
  have h1 := hcomp.deriv
  rw [hsymm] at h1
  have hkey : deriv xiTele (1 - s) = - deriv xiTele s := by linear_combination h1
  rw [logDeriv_apply, logDeriv_apply, xiTele_one_sub, hkey]; ring

/-- `ξ` log-derivative under conjugation. -/
theorem logDeriv_xiTele_conj (s : ℂ) :
    logDeriv xiTele ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv xiTele s) :=
  logDeriv_conj_of_conj_symm (fun z => xiTele_conj z) (differentiable_xiTele s)

/-- **THE ξ FOLD, pointwise**: `Re(logDeriv ξ (σ+iy)) + Re(logDeriv ξ ((1−σ)+iy)) = 0`. -/
theorem fold_pointwise_xiTele (sigma y : ℝ) :
    (logDeriv xiTele ((sigma : ℂ) + y * I)).re
      + (logDeriv xiTele (((1 - sigma : ℝ) : ℂ) + y * I)).re = 0 := by
  set s : ℂ := (sigma : ℂ) + y * I with hs
  set s' : ℂ := ((1 - sigma : ℝ) : ℂ) + y * I with hs'
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s' := by
    rw [hs, hs']; apply Complex.ext <;> simp <;> ring
  have hrefl := logDeriv_xiTele_reflect s
  rw [hconj, logDeriv_xiTele_conj s'] at hrefl
  have hre := congrArg Complex.re hrefl
  simp only [Complex.conj_re, Complex.neg_re] at hre
  linarith [hre]

/-! ## BRICK 2 (B): the vertical fold integrated — `AV(ξ,σ₀) + AV(ξ,1−σ₀) = 0`.

Integrating `fold_pointwise_xiTele` over a zero-free vertical band: the two mirror vertical edges of
the RvM box cancel.  For the symmetric box `[−1,2]` (`1−(−1)=2`) this is `AV(ξ,−1) + AV(ξ,2) = 0`.
`ξ ≠ 0` on the edges is the classical zero-free-contour caveat.  conjecture1_proved = False. -/

/-- `logDeriv ξ` continuous on a vertical segment where `ξ ≠ 0` (`ξ` entire). -/
theorem continuousOn_logDeriv_xiTele_seg (σ T0 T1 : ℝ) (hT : T0 ≤ T1)
    (hz : ∀ y ∈ Set.Icc T0 T1, xiTele ((σ : ℂ) + y * I) ≠ 0) :
    ContinuousOn (fun y : ℝ => logDeriv xiTele ((σ : ℂ) + y * I)) (Set.uIcc T0 T1) := by
  rw [Set.uIcc_of_le hT]
  intro y hy
  have hana : AnalyticAt ℂ xiTele ((σ : ℂ) + y * I) := analyticAt_xiTele _
  have hcAt : ContinuousAt (logDeriv xiTele) ((σ : ℂ) + y * I) := by
    have heq : logDeriv xiTele = fun w => deriv xiTele w / xiTele w := by
      funext w; rw [logDeriv_apply]
    rw [heq]; exact (hana.deriv.continuousAt).div hana.continuousAt (hz y hy)
  exact (ContinuousAt.comp (g := logDeriv xiTele) (f := fun t : ℝ => (σ : ℂ) + t * I)
    hcAt (by fun_prop)).continuousWithinAt

/-- **The ξ vertical fold, integrated**: `AV(ξ,σ₀,T0,T1) + AV(ξ,1−σ₀,T0,T1) = 0`
    (`ξ ≠ 0` on both mirror edges). -/
theorem argChangeVert_xiTele_fold (sigma0 T0 T1 : ℝ) (hT : T0 ≤ T1)
    (hzL : ∀ y ∈ Set.Icc T0 T1, xiTele ((sigma0 : ℂ) + y * I) ≠ 0)
    (hzR : ∀ y ∈ Set.Icc T0 T1, xiTele (((1 - sigma0 : ℝ) : ℂ) + y * I) ≠ 0) :
    argChangeVert xiTele sigma0 T0 T1 + argChangeVert xiTele (1 - sigma0) T0 T1 = 0 := by
  have cL := continuousOn_logDeriv_xiTele_seg sigma0 T0 T1 hT hzL
  have cR := continuousOn_logDeriv_xiTele_seg (1 - sigma0) T0 T1 hT hzR
  have iL := cL.intervalIntegrable (μ := MeasureTheory.volume)
  have iR := cR.intervalIntegrable (μ := MeasureTheory.volume)
  have rL : IntervalIntegrable (fun y : ℝ => (logDeriv xiTele ((sigma0 : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 :=
    (Complex.continuous_re.comp_continuousOn cL).intervalIntegrable
  have rR : IntervalIntegrable
      (fun y : ℝ => (logDeriv xiTele (((1 - sigma0 : ℝ) : ℂ) + y * I)).re)
      MeasureTheory.volume T0 T1 :=
    (Complex.continuous_re.comp_continuousOn cR).intervalIntegrable
  have eRe : ∀ (F : ℝ → ℂ), IntervalIntegrable F MeasureTheory.volume T0 T1 →
      (∫ y in T0..T1, F y).re = ∫ y in T0..T1, (F y).re := by
    intro F hI
    have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hI
    simp only [RCLike.re_to_complex] at this
    exact this.symm
  have main : (∫ y in T0..T1, ((logDeriv xiTele ((sigma0 : ℂ) + y * I)).re
        + (logDeriv xiTele (((1 - sigma0 : ℝ) : ℂ) + y * I)).re)) = ∫ _y in T0..T1, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro y _
    exact fold_pointwise_xiTele sigma0 y
  rw [intervalIntegral.integral_add rL rR, intervalIntegral.integral_zero] at main
  unfold argChangeVert
  rw [eRe _ iL, eRe _ iR]
  linarith [main]

/-! ## BRICK 2 (A): the bottom edge vanishes — `ξ` real on the real axis.

`ξ(x̄) = conj ξ(x)` (`xiTele_conj`); at real `x`, `x̄ = x`, so `ξ(x)` is real, hence `logDeriv ξ(x)`
is real (`Im = 0`).  The bottom edge of the RvM box lies on the real axis, so its horizontal
argument change is `0`.  `ξ ≠ 0` on the edge is the zero-free-contour caveat.
conjecture1_proved = False. -/

/-- `logDeriv ξ` is REAL on the real axis. -/
theorem logDeriv_xiTele_im_zero (x : ℝ) : (logDeriv xiTele ((x : ℂ))).im = 0 := by
  have h := logDeriv_xiTele_conj ((x : ℝ) : ℂ)
  rw [Complex.conj_ofReal] at h
  have h2 := congrArg Complex.im h
  rw [Complex.conj_im] at h2
  linarith

/-- **The bottom edge vanishes**: `argChangeHoriz ξ 0 σ0 σ1 = 0` (`ξ` real on the real axis). -/
theorem argChangeHoriz_xiTele_realAxis (σ0 σ1 : ℝ) (hσ : σ0 ≤ σ1)
    (hz : ∀ x ∈ Set.Icc σ0 σ1, xiTele ((x : ℂ)) ≠ 0) :
    argChangeHoriz xiTele 0 σ0 σ1 = 0 := by
  have hpt : ∀ x : ℝ, ((x : ℂ) + ((0:ℝ) : ℂ) * I) = ((x : ℝ) : ℂ) := by intro x; simp
  have hcont : ContinuousOn (fun x : ℝ => logDeriv xiTele ((x : ℝ) : ℂ)) (Set.uIcc σ0 σ1) := by
    rw [Set.uIcc_of_le hσ]
    intro x hx
    have hana : AnalyticAt ℂ xiTele ((x : ℝ) : ℂ) := analyticAt_xiTele _
    have hcAt : ContinuousAt (logDeriv xiTele) ((x : ℝ) : ℂ) := by
      have heq : logDeriv xiTele = fun w => deriv xiTele w / xiTele w := by
        funext w; rw [logDeriv_apply]
      rw [heq]; exact (hana.deriv.continuousAt).div hana.continuousAt (hz x hx)
    exact (hcAt.comp (Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume)
  unfold argChangeHoriz
  have hcongr : (∫ x in σ0..σ1, logDeriv xiTele ((x : ℂ) + ((0:ℝ) : ℂ) * I))
      = ∫ x in σ0..σ1, logDeriv xiTele ((x : ℝ) : ℂ) :=
    intervalIntegral.integral_congr (fun x _ => by rw [hpt x])
  rw [hcongr]
  have eIm : (∫ x in σ0..σ1, logDeriv xiTele ((x : ℝ) : ℂ)).im
      = ∫ x in σ0..σ1, (logDeriv xiTele ((x : ℝ) : ℂ)).im := by
    have := intervalIntegral.intervalIntegral_im (𝕜 := ℂ) hint
    simp only [RCLike.im_to_complex] at this
    exact this.symm
  rw [eIm]
  have hz2 : (∫ x in σ0..σ1, (logDeriv xiTele ((x : ℝ) : ℂ)).im) = ∫ _x in σ0..σ1, (0:ℝ) :=
    intervalIntegral.integral_congr (fun x _ => logDeriv_xiTele_im_zero x)
  rw [hz2, intervalIntegral.integral_zero]

end DiffractionCore
