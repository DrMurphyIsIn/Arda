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
    exact (has_fpower_series_dslope_fslope hp).analyticAt.differentiableAt.differentiableWithinAt
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
    refine MeasureTheory.ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
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

end DiffractionCore
