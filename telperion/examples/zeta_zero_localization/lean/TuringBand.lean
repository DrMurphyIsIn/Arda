/-  THE TURING BAND TEMPLATE (T5): per-band total zero count from the RvM edge
    decomposition -- the drop-in replacement for the four-edge winding certificate.

    `DiffractionCore.zero_count_band_edge_decomp` (brick 15, #374) expresses the
    band zero count as five EDGE argument-changes:

      2π·N_band = 2·AV(ζ,2) + AH(ζ,T1,2,-1) - AH(ζ,T0,2,-1) + AV(Γℝ,-1) + AV(Γℝ,2)

    Here we consume it with ARB-ENCLOSED edge values: the five argument-change
    quantities carry rational interval enclosures as documented non-kernel
    hypotheses (the SAME trust class as the previous route's `hwind` boundary
    integral value), and the kernel pins the integer count by interval
    arithmetic + rational π bounds (`Real.pi_gt_d2` / `Real.pi_lt_d4`).

    What this ELIMINATES vs the winding route: the two in-strip vertical edge
    integrals (the √T-expensive Arb input) and the 17-conjunct `hArb`
    integrability game -- the count now needs no interior contour data at all.
    The on-line half (`hLine` sign-change zeros) is unchanged; the conclusion
    shape is IDENTICAL to `rh_in_box_of_certificate`, so the height-chain glue
    consumes T5 bands with no changes.

    Trust boundary: KERNEL = the RvM edge decomposition + Blaschke split +
    interval/π arithmetic + the count-exhaustion core; ARB NON-KERNEL INPUT =
    the five edge enclosures, edge non-vanishing, zero confinement, and the
    on-line zeros.  conjecture1_proved = False. -/
import Mathlib
import DiffractionCore
import RHInBoxCore

open Complex MeasureTheory intervalIntegral

namespace TuringBand

/-- **T5 count pinning**: the band zero count (with multiplicity) equals `N`,
    from rational interval enclosures of the five RvM edge argument-changes.

    `hpinL`/`hpinH` are rational side conditions dischargeable by `norm_num`:
    with `π ∈ (3.14, 3.1416)` and `1 ≤ N` they squeeze
    `N - 1 < (count) < N + 1`, and the count is an integer. -/
theorem band_count_eq
    (T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ) (N : ℕ) (hN1 : 1 ≤ N)
    (L1 H1 L2 H2 L3 H3 L4 H4 L5 H5 : ℝ)
    (hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1)
    (hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2)
    (hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3)
    (hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4)
    (hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5)
    (hpinL : 2 * 3.1416 * ((N : ℝ) - 1) < 2 * L1 + L2 - H3 + L4 + L5)
    (hpinH : 2 * H1 + H2 - L3 + H4 + H5 < 2 * 3.14 * ((N : ℝ) + 1)) :
    (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) = (N : ℤ) := by
  have hdecomp := DiffractionCore.zero_count_band_edge_decomp T0 T1 hT0 hT c R
    hbox_ball hs1 hnzb hnzt hnzl hins
  set Sz : ℤ := ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ with hSz
  have hSreal : (2 : ℝ) * Real.pi * (Sz : ℝ)
      = 2 * DiffractionCore.argChangeVert riemannZeta 2 T0 T1
        + DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1)
        - DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1)
        + DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
        + DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 := by
    have hcast : ((Sz : ℤ) : ℝ) = ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ) := by
      rw [hSz]; push_cast; ring
    rw [hcast]; exact hdecomp
  have hpigt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpilt : Real.pi < 3.1416 := Real.pi_lt_d4
  -- squeeze: 2π(N-1) < 2π·Sz < 2π(N+1)
  have hlo : 2 * Real.pi * ((N : ℝ) - 1) < 2 * Real.pi * (Sz : ℝ) := by
    have h1 : 2 * Real.pi * ((N : ℝ) - 1) ≤ 2 * 3.1416 * ((N : ℝ) - 1) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      nlinarith [hN0, hpilt]
    have h2 : 2 * L1 + L2 - H3 + L4 + L5 ≤ 2 * Real.pi * (Sz : ℝ) := by
      rw [hSreal]
      obtain ⟨l1, h1'⟩ := hAV2; obtain ⟨l2, h2'⟩ := hAHt; obtain ⟨l3, h3'⟩ := hAHb
      obtain ⟨l4, h4'⟩ := hAG1; obtain ⟨l5, h5'⟩ := hAG2
      linarith
    linarith
  have hhi : 2 * Real.pi * (Sz : ℝ) < 2 * Real.pi * ((N : ℝ) + 1) := by
    have h1 : 2 * 3.14 * ((N : ℝ) + 1) ≤ 2 * Real.pi * ((N : ℝ) + 1) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      nlinarith [hN0, hpigt]
    have h2 : 2 * Real.pi * (Sz : ℝ) ≤ 2 * H1 + H2 - L3 + H4 + H5 := by
      rw [hSreal]
      obtain ⟨l1, h1'⟩ := hAV2; obtain ⟨l2, h2'⟩ := hAHt; obtain ⟨l3, h3'⟩ := hAHb
      obtain ⟨l4, h4'⟩ := hAG1; obtain ⟨l5, h5'⟩ := hAG2
      linarith
    linarith
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hltN : ((N : ℝ) - 1) < (Sz : ℝ) := by
    have := (mul_lt_mul_left hpipos).mp (by linarith [hlo] :
      2 * Real.pi * ((N : ℝ) - 1) < 2 * Real.pi * (Sz : ℝ))
    linarith [this]
  have hgtN : (Sz : ℝ) < ((N : ℝ) + 1) := by
    have := (mul_lt_mul_left hpipos).mp (by linarith [hhi] :
      2 * Real.pi * (Sz : ℝ) < 2 * Real.pi * ((N : ℝ) + 1))
    linarith [this]
  have hzlt : (N : ℤ) - 1 < Sz := by exact_mod_cast hltN
  have hzgt : Sz < (N : ℤ) + 1 := by exact_mod_cast hgtN
  omega

/-- **T5 band template**: every zeta zero in the box `[σ0,σ1] × [T0,T1]` lies on
    the critical line, from (i) the five Arb edge enclosures pinning the total
    count `N` and (ii) `N` distinct on-line zeros.  The conclusion shape is
    identical to `RHInBox.rh_in_box_of_certificate` — the height chain consumes
    both interchangeably.  conjecture1_proved = False. -/
theorem turing_band_on_line
    (sigma0 sigma1 T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (hs0 : (-1 : ℝ) ≤ sigma0) (hs2 : sigma1 ≤ 2)
    (c : ℂ) (R : ℝ) (hRpos : 0 < R) (N : ℕ) (hN1 : 1 ≤ N)
    (L1 H1 L2 H2 L3 H3 L4 H4 L5 H5 : ℝ)
    (hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1)
    (hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2)
    (hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3)
    (hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4)
    (hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5)
    (hpinL : 2 * 3.1416 * ((N : ℝ) - 1) < 2 * L1 + L2 - H3 + L4 + L5)
    (hpinH : 2 * H1 + H2 - L3 + H4 + H5 < 2 * 3.14 * ((N : ℝ) + 1))
    (T : Finset ℂ)
    (hTline : ∀ z ∈ T, z.re = 1 / 2)
    (hTzero : ∀ z ∈ T, riemannZeta z = 0)
    (hTbox : ∀ z ∈ T, (sigma0 ≤ z.re ∧ z.re ≤ sigma1) ∧ (T0 ≤ z.im ∧ z.im ≤ T1))
    (hcard : (N : ℤ) = (T.card : ℤ)) :
    ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  obtain ⟨E, _hE, hd1, hzin_ball, _hsplit⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (-1) 2 T0 T1 c R hRpos hbox_ball hs1
  have hcnt := band_count_eq T0 T1 hT0 hT c R N hN1 L1 H1 L2 H2 L3 H3 L4 H4 L5 H5
    hbox_ball hs1 hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
  have hball_of_box : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) →
      (T0 ≤ ρ.im ∧ ρ.im ≤ T1) → ρ ∈ Metric.ball c R := fun ρ hre him =>
    hbox_ball ρ ⟨le_trans hs0 hre.1, le_trans hre.2 hs2⟩ him
  have hTsub : T ⊆ RHInBoxAnalytic.zeroFinset c R hs1 := fun z hz =>
    hzin_ball z (hball_of_box z (hTbox z hz).1 (hTbox z hz).2) (hTzero z hz)
  have hcount' : (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) = (T.card : ℤ) := by
    rw [hcnt, hcard]
  have hzero_in : ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1 := fun ρ hre him hz =>
    hzin_ball ρ (hball_of_box ρ hre him) hz
  exact RHInBoxCore.rh_in_box_core sigma0 sigma1 T0 T1
    (RHInBoxAnalytic.zeroFinset c R hs1) T
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ)
    hd1 hTsub hTline hcount' hzero_in

end TuringBand
