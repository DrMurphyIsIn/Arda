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

end DiffractionCore
