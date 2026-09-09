/-
RvMLiCountBridge — the shared argument-principle engine behind BOTH the zero-count
N(T) and the Li coefficients λ_n.

The Riemann–von Mangoldt count and Li's coefficients are the SAME functional — a
weighted winding of ξ'/ξ — read with different test weights:

  * weight `g ≡ 1`            → the zero-count N(T)  (our RvM development).
  * weight `g = liWeight n`   → the finite Li partial sum Σ_{ρ∈box} (1−(1−1/ρ)^n),
                                whose T→∞ limit is `2·λ_n` (upstream
                                `paired_sum_formula_of_mtest_and_cauchy`,
                                absolutely convergent over the paired zeros).

This file lands the shared engine at the level it is *reachable*:

  * `analytic_weighted_count_eq_winding` — for any analytic `f` and holomorphic
    weight `g`, the weighted boundary winding equals `2πi · Σ_ρ mult(ρ)·g(ρ)`.
    Instantiating `f = riemannXi` gives the finite Li partial sum as a contour
    integral (weight `liWeight n`), the same engine that gives N(T) (weight 1).
  * `liWeight`, `liWeight_analyticAt` — the Li test weight and its analyticity off
    `s = 0`, so the engine applies on any strip box avoiding the origin.
  * `liWeight_at_zero` — the engine's weight value at a zero IS the Li summand.

HONEST SCOPE — the three strata of the N(T) ↔ λ_n bridge.

  STRATUM 1 (this file, reachable & built): N(T) and the finite Li partial sum are
  ONE weighted argument principle, differing only in the test weight.  Kernel-level.

  STRATUM 2 (reachable engineering, NOT built here): finite box-sum → full λ_n.
  Upstream gives λ_n = ½ ∑'_ρ liPairedSummand as an ABSOLUTELY convergent sum over
  the paired zeros (from `Summable (1/‖ρ‖²)`).  So any cofinal box-exhaustion limit
  equals λ_n.  Remaining bricks: handle the weight's pole at `s=0` (a keyhole/residue
  term), match `MeromorphicOn.divisor riemannXi` to upstream's `NontrivialZero`
  index, and take the `HasSum`-along-exhaustion limit.  No research obstruction —
  bounded engineering.  NOTE: N(T) is NOT load-bearing here; upstream's absolute
  convergence carries the limit.  N(T) only DESCRIBES the number of terms.

  STRATUM 3 (RESEARCH PROGRAM, where N(T) IS load-bearing): the deep bridge is the
  Weil explicit formula  Σ_ρ h(ρ) = [archimedean transform of h] − Σ_{prime powers} …
  Specialising `h ≡ 1` recovers RvM (built).  Specialising `h = liWeight n` recovers
  the Bombieri–Lagarias arithmetic formula: λ_n = (archimedean main term ~ (n/2)log n,
  from Γℝ, set by the zero DENSITY dN(T) ~ (1/2π)log(T/2π)) + (prime sum from ζ'/ζ).
  HERE the density N(T) determines λ_n's main term.  We already hold the prime
  keystone on this island — `logDeriv_zeta_eq_neg_LSeries_vonMangoldt`,
  `right_edge_prime_expansion`, `integral_vonMangoldt_term` (the Bragg peaks).  The
  missing mathematics is the GENERAL-test-function explicit formula (contour-shift +
  archimedean transform for arbitrary `h`) and the asymptotic extraction of the main
  term — the analytic core of the subject, not a mechanical port.

conjecture1_proved = False.  Nothing here proves or approaches RiemannHypothesis.
-/
import RvMDiffractionCore
import LiPositivity

namespace DiffractionCore

open Complex MeasureTheory Real

/-- **The Li test weight** `g_n(s) = 1 − (1 − 1/s)^n`.  Evaluated at a nontrivial
    zero ρ it is the Li summand `1 − (1 − 1/ρ)^n`; it is the weight that turns the
    ξ'/ξ winding into the (finite) Li partial sum. -/
noncomputable def liWeight (n : ℕ) (s : ℂ) : ℂ := 1 - (1 - 1 / s) ^ n

/-- `liWeight n` is analytic at every `s ≠ 0` (its only singularity is the pole of
    `1/s` at the origin), so the weighted argument principle applies on any box that
    avoids `s = 0` — in particular any box inside the critical strip. -/
theorem liWeight_analyticAt {n : ℕ} {s : ℂ} (hs : s ≠ 0) : AnalyticAt ℂ (liWeight n) s := by
  unfold liWeight
  exact analyticAt_const.sub (((analyticAt_const.sub ((analyticAt_const).div analyticAt_id hs))).pow n)

/-- `liWeight n` is holomorphic on any open set avoiding `0`. -/
theorem liWeight_differentiableOn {n : ℕ} {U : Set ℂ} (hU : (0 : ℂ) ∉ U) :
    DifferentiableOn ℂ (liWeight n) U :=
  fun z hz => ((liWeight_analyticAt (n := n) (fun h => hU (h ▸ hz))).differentiableAt).differentiableWithinAt

/-- **The weight value at a zero IS the Li summand.**  This is the hinge: the
    argument-principle weight, sampled at ρ, returns exactly the term of the
    Bombieri–Lagarias sum. -/
theorem liWeight_at_zero (n : ℕ) (ρ : ℂ) : liWeight n ρ = 1 - (1 - 1 / ρ) ^ n := rfl

/-- **THE WEIGHTED ARGUMENT PRINCIPLE** (the shared engine): for analytic `f` with
    finite divisor and a weight `g` holomorphic on a neighbourhood `U` of the box,
    if `f ≠ 0` on the edges and its zeros are strictly interior, the weighted
    boundary winding of `logDeriv f` equals `2πi · Σ_ρ mult(ρ)·g(ρ)`.

    With `g ≡ 1` this is the zero-count (RvM); with `g = liWeight n` it is the finite
    Li partial sum.  The `hArb` integrability bundle mirrors the unweighted
    `analytic_count_eq_winding_generic`, with the weight `g` threaded through. -/
theorem analytic_weighted_count_eq_winding
    (f g : ℂ → ℂ) (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) {U : Set ℂ}
    (hfU : AnalyticOnNhd ℂ f (Metric.ball c R))
    (h₂f : ∀ u ∈ Metric.ball c R, meromorphicOrderAt f u ≠ ⊤)
    (h₃f : (MeromorphicOn.divisor f (Metric.ball c R)).support.Finite)
    (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hUopen : IsOpen U) (hgU : DifferentiableOn ℂ g U)
    (hboxU : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U)
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
        (fun x : ℝ => g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹) volume sigma0 sigma1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) volume T0 T1) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹))
          volume sigma0 sigma1) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹))
          volume sigma0 sigma1) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹))
          volume T0 T1) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹))
          volume T0 T1) ∧
      (IntervalIntegrable (fun x : ℝ => g (↑x + (T0 : ℂ) * I) * E (↑x + (T0 : ℂ) * I)) volume sigma0 sigma1) ∧
      (IntervalIntegrable (fun x : ℝ => g (↑x + (T1 : ℂ) * I) * E (↑x + (T1 : ℂ) * I)) volume sigma0 sigma1) ∧
      (IntervalIntegrable (fun y : ℝ => g ((sigma1 : ℂ) + ↑y * I) * E ((sigma1 : ℂ) + ↑y * I)) volume T0 T1) ∧
      (IntervalIntegrable (fun y : ℝ => g ((sigma0 : ℂ) + ↑y * I) * E ((sigma0 : ℂ) + ↑y * I)) volume T0 T1)) :
    (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * logDeriv f (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * logDeriv f (↑x + (T1 : ℂ) * I))
        + I • (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I) * logDeriv f ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I) * logDeriv f ((sigma0 : ℂ) + ↑y * I))
      = 2 * ↑π * I * ∑ ρ ∈ h₃f.toFinset,
          ((MeromorphicOn.divisor f (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) * g ρ := by
  obtain ⟨E, hEholo, _hd1, _hzero_in, hker⟩ :=
    analytic_blaschke_split_ball f sigma0 sigma1 T0 T1 c R hfU h₂f h₃f hbox_ball
  set s := h₃f.toFinset with hs
  set d := (MeromorphicOn.divisor f (Metric.ball c R) : ℂ → ℤ) with hd
  obtain ⟨hnz_b, hnz_t, hnz_r, hnz_l, hin, hb, ht, hr, hl,
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
  -- per edge: g·logDeriv f = Σ d·(g/(z−ρ)) + g·E
  have hsp_b : ∀ x ∈ Set.uIcc sigma0 sigma1,
      g (↑x + (T0 : ℂ) * I) * logDeriv f (↑x + (T0 : ℂ) * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹))
          + g (↑x + (T0 : ℂ) * I) * E (↑x + (T0 : ℂ) * I) := by
    intro x hx
    rw [hker _ (bmem x hx) (hnz_b x hx)]
    simp only [div_eq_mul_inv, Finset.mul_sum, mul_add]; ring_nf
  have hsp_t : ∀ x ∈ Set.uIcc sigma0 sigma1,
      g (↑x + (T1 : ℂ) * I) * logDeriv f (↑x + (T1 : ℂ) * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹))
          + g (↑x + (T1 : ℂ) * I) * E (↑x + (T1 : ℂ) * I) := by
    intro x hx
    rw [hker _ (tmem x hx) (hnz_t x hx)]
    simp only [div_eq_mul_inv, Finset.mul_sum, mul_add]; ring_nf
  have hsp_r : ∀ y ∈ Set.uIcc T0 T1,
      g ((sigma1 : ℂ) + ↑y * I) * logDeriv f ((sigma1 : ℂ) + ↑y * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹))
          + g ((sigma1 : ℂ) + ↑y * I) * E ((sigma1 : ℂ) + ↑y * I) := by
    intro y hy
    rw [hker _ (rmem y hy) (hnz_r y hy)]
    simp only [div_eq_mul_inv, Finset.mul_sum, mul_add]; ring_nf
  have hsp_l : ∀ y ∈ Set.uIcc T0 T1,
      g ((sigma0 : ℂ) + ↑y * I) * logDeriv f ((sigma0 : ℂ) + ↑y * I)
        = (∑ ρ ∈ s, (d ρ : ℂ) * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹))
          + g ((sigma0 : ℂ) + ↑y * I) * E ((sigma0 : ℂ) + ↑y * I) := by
    intro y hy
    rw [hker _ (lmem y hy) (hnz_l y hy)]
    simp only [div_eq_mul_inv, Finset.mul_sum, mul_add]; ring_nf
  have eb : (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * logDeriv f (↑x + (T0 : ℂ) * I))
      = (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (d ρ : ℂ) * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹))
        + (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * E (↑x + (T0 : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add hsb heb]
    exact intervalIntegral.integral_congr (fun x hx => hsp_b x hx)
  have et : (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * logDeriv f (↑x + (T1 : ℂ) * I))
      = (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (d ρ : ℂ) * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹))
        + (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * E (↑x + (T1 : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add hst het]
    exact intervalIntegral.integral_congr (fun x hx => hsp_t x hx)
  have er : (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I) * logDeriv f ((sigma1 : ℂ) + ↑y * I))
      = (∫ y in T0..T1, ∑ ρ ∈ s, (d ρ : ℂ) * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹))
        + (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I) * E ((sigma1 : ℂ) + ↑y * I)) := by
    rw [← intervalIntegral.integral_add hsr her]
    exact intervalIntegral.integral_congr (fun y hy => hsp_r y hy)
  have el : (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I) * logDeriv f ((sigma0 : ℂ) + ↑y * I))
      = (∫ y in T0..T1, ∑ ρ ∈ s, (d ρ : ℂ) * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹))
        + (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I) * E ((sigma0 : ℂ) + ↑y * I)) := by
    rw [← intervalIntegral.integral_add hsl hel]
    exact intervalIntegral.integral_congr (fun y hy => hsp_l y hy)
  -- g·E holomorphic on the box ⇒ its winding vanishes
  have hgE_holo : DifferentiableOn ℂ (fun z => g z * E z) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hgU.mono hboxU).mul hEholo
  have hgE0 := RHInBoxAnalytic.rect_arg_principle_generic sigma0 sigma1 T0 T1 hsig hT
    (fun z => g z * E z) hgE_holo
  -- weighted residue sum
  have hRes := rect_weighted_residue_sum_generic sigma0 sigma1 T0 T1 hsig hT d g hUopen hgU hboxU hin
  rw [eb, et, er, el, smul_add, smul_add]
  linear_combination hRes + hgE0

end DiffractionCore
