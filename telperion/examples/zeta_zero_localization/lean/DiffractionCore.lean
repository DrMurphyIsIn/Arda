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

end DiffractionCore
