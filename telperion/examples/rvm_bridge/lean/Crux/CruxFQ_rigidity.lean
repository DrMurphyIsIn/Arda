/-
CruxFQ_rigidity.lean -- crux-fq workflow, BUILDER for the RIGIDITY seat.
"Zero-side quasicrystal rigidity for the Guinand-Weil pair."

conjecture1_proved = False. Nothing here proves RH, reduces it, or moves a wall clause. Every
theorem that mentions `RiemannHypothesis` is an equivalence, or an implication from a hypothesis
that is itself RH-equivalent: these are circularity certificates, not routes.

Checked by: `cd telperion/examples/rvm_bridge/lean && lake env lean Crux/CruxFQ_rigidity.lean`
(Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 fbdc36bb; imports the corpus module `E6Bridge9`).
No `sorry`, `admit`, `native_decide`, new `axiom`, `opaque`, or `set_option`. Every
`#print axioms` line at the end reports exactly `[propext, Classical.choice, Quot.sound]`.

CONVENTIONS. Tests are the corpus class `WeilExplicit.IsWeilTest` (smooth, compactly supported
`g : ℝ → ℂ`). The zero-side transform is `gwHat g r = ∫ g(u) e^{iru} du`, equal to the corpus
`weilKernel g (1/2 + i r)` (`weilKernel_line_eq_gwHat`) and to `paperFT g r`. A "Guinand partner"
(`IsGuinandPartner E Pr μ`) is a measure `μ ≥ 0` on `ℝ` with `∫ ĝ dμ = E g - Pr g` for every test
whose transform is `μ`-integrable; `E` is the common pole+archimedean functional, `Pr` the prime
side. "Test-tempered" (`IsTestTempered μ`) means every Weil-test transform is `μ`-integrable;
"tempered" means `∫ (1 + r²)⁻¹ dμ < ∞`, which implies it (`isTestTempered_of_tempered`). One of
the two is ASSUMED where used (the seat's Lemma G, which derives temperedness from positivity, is
not formalized); under RH, zeta's zero measure `Z_ζ` is test-tempered (proved here).

WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
 1. LEMMA M, the zero-side antichain (`guinand_antichain_le`, the seat's statement verbatim;
    also `antichain_core`, `guinand_antichain`, `guinand_antichain_measure`). If `(μ₁, P₁)` and
    `(μ₂, P₂)` are Guinand pairs with the same `E`, `μ₁ ≤ μ₂`, `μ₂` tempered, `P₁, P₂ ≥ 0` locally
    finite, `P₁{0} = 0` and `∫_{0<|u|<1} |u|⁻¹ dP₁ < ∞`, then `μ₁ = μ₂` and `P₁ = P₂`. No
    functional equation is used; `E` is arbitrary. The proof tests with `ψ_d ⋆ ψ_d` (smooth bump
    autocorrelations, `testFn`): their transforms are `ψ̂_d(r/2π)² ∈ [0,1]` and tend to `1`, and
    their prime-side mass tends to `0`; Fatou finishes (`measure_eq_zero_of_kd`).
 2. Zeta instances with the corpus `archSide`/`primeSide` (`IsZetaPartner`): no real zeros can be
    added to (`zeta_partner_no_added_zeros`) or deleted from (`zeta_partner_no_deleted_zeros`) a
    test-tempered positive zeta partner while keeping a positive prime side; positive zeta partners
    form an antichain (`zeta_partners_antichain`). The prime gap `(-log 2, log 2)` does the work.
 3. Negative controls (`antichain_negative_controls`): an atom of the smaller prime side at
    `u = 0` (a conductor-type term) or a signed prime side breaks the antichain (Lebesgue measure
    vs `0`, via Fourier inversion `integral_gwHat_volume`). Both hypotheses are load-bearing.
 4. CIRCULARITY CERTIFICATES (verdict (b) of the seat's ledger, now both directions in the kernel).
    `zeta_positive_partner_iff_rh`: zeta has a test-tempered positive real Guinand partner iff RH.
    `⟹` is `zeta_partner_implies_rh` (Weil positivity, then the corpus theorem
    `RvMBridge9.weil_positivity_implies_rh`); `⟸` builds `Z_ζ = Σ_ρ m_ρ δ_{Im ρ}`
    (`zetaZeroMeasure`, over the corpus `zetaZeroConfig`) and reads the corpus explicit formula on
    the line (`zetaZeroMeasure_isZetaPartner_of_rh`). Under RH `Z_ζ` is maximal and minimal among
    positive partners (`zetaZeroMeasure_extremal_of_rh`). Finite resolution: one resolution gives
    only window Weil positivity (`window_partner_weil_positivity`); partners at every resolution
    exist iff RH (`all_windows_iff_rh`).
 5. QUANTITATIVE THEOREM A (Fejer form of the seat's Lemma 8.1): for `ν ≥ 0` with no mass in
    `(-1,1) \ {0}`, the Poisson self-duality defect on the single Fejer test equals the
    `sinc²`-mass of `ν` off `0` (`fejer_defect_identity`, `poisson_defect_eq`), and bounds the mass
    at distance `≥ ε` from `ℤ` in `|x| ≤ R` by `(π²R²/4ε²) · defect` (`offInteger_mass_le`).
    The Fejer pair `fourier_tri` is copied from `CruxFQ_PoissonRigidity.lean` (KERNEL seat).
 6. THEOREM E, the kernel-checkable half. Bohr means of finite unimodular power sums
    (`bohr_mean`); a power sum tending to `0` is `0` (`unimodular_powerSum_coeff_eq_zero`); it
    exceeds every level below `max |a_i|` infinitely often
    (`unimodular_powerSum_frequently_large`, `leeYang_powerSum_frequently_large`,
    `leeYang_powerSum_not_tendsto_zero`); hence zeta's local Bragg sequence `-p^{-m/2}` is not a
    unimodular power sum, with any complex (e.g. signed integer) weights
    (`zeta_bragg_not_unimodular`). The Kurasov-Sarnak reality mechanism in two frequencies
    (`ks_real_zeros`) and the seat's explicit example `PLY = 1 + z₁/2 + z₂/2 + z₁z₂`: Lee-Yang
    (`PLY_leeYang`), not a product of one-variable factors (`PLY_not_product`, mixed coefficient
    `3/4`), all zeros of `PLY(2^{ix}, 3^{ix})` real (`PLY_real_zeros`).
 7. COROLLARY E.3, the local dictionary (`local_zero_re`, `local_zero_exists`,
    `local_dictionary`): local zeros of `∏(1 - a_j p^{-s})` sit on `Re s = log|a_j|/log p`; all on
    `Re s = 1/2` iff every `|a_j| = √p`. `quadratic_leeYang_fails` and
    `zoo_local_factors_not_leeYang` place the golden fake (`c = √5`) and `W1(29,11)`
    (`c = 11/√29`) on the non-Lee-Yang side.
 8. Capstone `rigidity_capstone`.

WHAT THIS FILE DOES NOT ESTABLISH:
 - Theorem D (a positive prime side with some zero-multiset partner under zeta's archimedean term is
   `P_ζ`) and Corollary D1 (integer-valued classification): they rest on round 1's Theorem A, whose
   Step 2 (FE implies the Poisson identity) is not formalized, and on Hadamard-product growth
   bounds. PAPER-PROOF only.
 - Corollary D2 (the continuous Beurling partner `μ_cont` is negative on `[1, 5.8]`): Arb-certified
   outside the kernel (`n4_arb_mu_cont.py`), not here. Proposition 3.6 (tempered signed partner
   iff RH): paper only.
 - Theorem E(i) (Euler support forces a product and lattice zero sets): it needs the
   Kurasov-Sarnak Fourier formula for the zero measure, which is not formalized here.
 - Lemma G (automatic temperedness), the Krein direction of Proposition K (window positivity
   implies a window partner), `∫ (1 + r²)⁻¹ dZ_ζ < ∞` under RH (only test-temperedness of `Z_ζ` is
   proved), and every literature claim (Miller 2002, Bondarenko-Radchenko-Seip,
   Baake-Spindeler-Strungaru, novelty).
 - Anything about where the zeros of `riemannZeta` lie.
-/
import Mathlib
import E6Bridge9

open MeasureTheory Filter Topology Set
open scoped FourierTransform

noncomputable section

namespace CruxFQRigidity

/-! ## 1. Conventions -/

/-- The zero-side transform in the Guinand-Weil convention, `ĝ(r) = ∫ g(u) e^{iru} du`. -/
def gwHat (g : ℝ → ℂ) (r : ℝ) : ℂ := ∫ u : ℝ, g u * Complex.exp (↑(r * u) * Complex.I)

lemma gwHat_eq_fourier (g : ℝ → ℂ) (r : ℝ) :
    gwHat g r = 𝓕 g (-(r / (2 * Real.pi))) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold gwHat
  congr 1
  funext u
  have h : (-2 * Real.pi * u * -(r / (2 * Real.pi))) = r * u := by
    field_simp
  rw [h, smul_eq_mul, mul_comm]

/-- The corpus zero-side kernel on the critical line is `gwHat`. -/
lemma weilKernel_line_eq_gwHat (g : ℝ → ℂ) (r : ℝ) :
    WeilExplicit.weilKernel g (1 / 2 + (r : ℂ) * Complex.I) = gwHat g r := by
  unfold WeilExplicit.weilKernel gwHat
  congr 1
  funext u
  congr 2
  push_cast
  ring

lemma integrable_of_test {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) : Integrable g :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

lemma test_deriv {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) :
    WeilExplicit.IsWeilTest (deriv g) := by
  refine ⟨?_, hg.2.deriv⟩
  have := hg.1.iterate_deriv 1
  simpa using this

lemma norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ u, ‖f u‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext u
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- Two integrations by parts: `‖𝓕 g ξ‖ (1 + ξ²) ≤ C` for a Weil test `g`. -/
lemma fourier_decay {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖𝓕 g ξ‖ * (1 + ξ ^ 2) ≤ C := by
  have hg1 := test_deriv hg
  have hg2 := test_deriv hg1
  have hd0 : Differentiable ℝ g := hg.1.differentiable (by simp)
  have hd1 : Differentiable ℝ (deriv g) := hg1.1.differentiable (by simp)
  have e1 := Real.fourier_deriv (integrable_of_test hg) hd0 (integrable_of_test hg1)
  have e2 := Real.fourier_deriv (integrable_of_test hg1) hd1 (integrable_of_test hg2)
  have hA : 0 ≤ ∫ u, ‖g u‖ := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ ∫ u, ‖deriv (deriv g) u‖ := integral_nonneg fun _ => norm_nonneg _
  refine ⟨(∫ u, ‖g u‖) + ∫ u, ‖deriv (deriv g) u‖, add_nonneg hA hB, fun ξ => ?_⟩
  have h0 := norm_fourier_le g ξ
  have h2 := norm_fourier_le (deriv (deriv g)) ξ
  rw [e2] at h2
  simp only at h2
  rw [e1] at h2
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * Real.pi * |ξ| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Complex.norm_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [norm_smul, norm_smul, hn] at h2
  have hF := norm_nonneg (𝓕 g ξ)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hξ2 : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
  have key : ξ ^ 2 * ‖𝓕 g ξ‖ ≤ ∫ u, ‖deriv (deriv g) u‖ := by
    have h4 : 4 * Real.pi ^ 2 * (ξ ^ 2 * ‖𝓕 g ξ‖) ≤ ∫ u, ‖deriv (deriv g) u‖ := by
      rw [← hξ2]; nlinarith
    have h5 : ξ ^ 2 * ‖𝓕 g ξ‖ ≤ 4 * Real.pi ^ 2 * (ξ ^ 2 * ‖𝓕 g ξ‖) := by
      have : 0 ≤ ξ ^ 2 * ‖𝓕 g ξ‖ := mul_nonneg (sq_nonneg _) hF
      have hp : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith
      exact le_mul_of_one_le_left this hp
    linarith
  nlinarith

lemma continuous_gwHat_of_integrable {g : ℝ → ℂ} (hg : Integrable g) : Continuous (gwHat g) := by
  have : gwHat g = fun r => 𝓕 g (-(r / (2 * Real.pi))) := funext (gwHat_eq_fourier g)
  rw [this]
  exact (continuous_fourier_of_integrable hg).comp (by fun_prop)

/-- Tempered positive measures integrate the zero-side transform of every Weil test. -/
lemma integrable_gwHat {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) {μ : Measure ℝ}
    (htemp : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ) : Integrable (gwHat g) μ := by
  obtain ⟨C, hC0, hC⟩ := fourier_decay hg
  refine Integrable.mono' (htemp.const_mul (4 * Real.pi ^ 2 * C))
    (continuous_gwHat_of_integrable (integrable_of_test hg)).aestronglyMeasurable
    (ae_of_all _ fun r => ?_)
  rw [gwHat_eq_fourier]
  set ξ := -(r / (2 * Real.pi)) with hξ
  have hb := hC ξ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hr : 1 + r ^ 2 ≤ 4 * Real.pi ^ 2 * (1 + ξ ^ 2) := by
    have : 4 * Real.pi ^ 2 * (1 + ξ ^ 2) = 4 * Real.pi ^ 2 + r ^ 2 := by
      rw [hξ]; field_simp; ring
    rw [this]; nlinarith [Real.pi_gt_three]
  have hpos : 0 < 1 + r ^ 2 := by positivity
  rw [show 4 * Real.pi ^ 2 * C * (1 + r ^ 2)⁻¹ = 4 * Real.pi ^ 2 * C / (1 + r ^ 2) by ring]
  rw [le_div_iff₀ hpos]
  have hF := norm_nonneg (𝓕 g ξ)
  calc ‖𝓕 g ξ‖ * (1 + r ^ 2) ≤ ‖𝓕 g ξ‖ * (4 * Real.pi ^ 2 * (1 + ξ ^ 2)) :=
        mul_le_mul_of_nonneg_left hr hF
    _ = 4 * Real.pi ^ 2 * (‖𝓕 g ξ‖ * (1 + ξ ^ 2)) := by ring
    _ ≤ 4 * Real.pi ^ 2 * C := mul_le_mul_of_nonneg_left hb (by positivity)

/-- `μ` integrates the zero-side transform of every Weil test ("test-tempered"). Implied by
`∫ (1 + r²)⁻¹ dμ < ∞` (`isTestTempered_of_tempered`); this is all the Guinand identity needs. -/
def IsTestTempered (μ : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → Integrable (gwHat g) μ

lemma isTestTempered_of_tempered {μ : Measure ℝ}
    (htemp : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ) : IsTestTempered μ :=
  fun _ hg => integrable_gwHat hg htemp

/-! ## 2. The smooth autocorrelation test family -/

/-- The bump of outer radius `d` (inner radius `d/2`); a fixed placeholder when `d ≤ 0`. -/
def bump (d : ℝ) : ContDiffBump (0 : ℝ) :=
  if h : 0 < d then ⟨d / 2, d, by positivity, by linarith⟩
  else ⟨1 / 2, 1, by norm_num, by norm_num⟩

lemma bump_rIn {d : ℝ} (hd : 0 < d) : (bump d).rIn = d / 2 := by
  rw [bump, dif_pos hd]

lemma bump_rOut {d : ℝ} (hd : 0 < d) : (bump d).rOut = d := by
  rw [bump, dif_pos hd]

/-- `ψ_d`: smooth, even, `≥ 0`, supported in `(-d, d)`, `∫ ψ_d = 1`, `ψ_d ≤ 1/d`. -/
def psi (d : ℝ) : ℝ → ℝ := (bump d).normed volume

lemma psi_nonneg (d u : ℝ) : 0 ≤ psi d u := (bump d).nonneg_normed u

lemma psi_integral (d : ℝ) : ∫ u, psi d u = 1 := (bump d).integral_normed

lemma psi_neg (d u : ℝ) : psi d (-u) = psi d u := (bump d).normed_neg u

lemma psi_contDiff (d : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psi d) :=
  (bump d).contDiff_normed

lemma psi_continuous (d : ℝ) : Continuous (psi d) := (bump d).continuous_normed

lemma psi_hasCompactSupport (d : ℝ) : HasCompactSupport (psi d) :=
  (bump d).hasCompactSupport_normed

lemma psi_integrable (d : ℝ) : Integrable (psi d) :=
  (psi_continuous d).integrable_of_hasCompactSupport (psi_hasCompactSupport d)

lemma psi_eq_zero {d u : ℝ} (hd : 0 < d) (hu : d ≤ |u|) : psi d u = 0 := by
  have hs := (bump d).support_normed_eq (μ := volume)
  have : u ∉ Function.support (psi d) := by
    unfold psi
    rw [hs, bump_rOut hd, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact hu
  exact Function.notMem_support.mp this

lemma psi_le {d : ℝ} (hd : 0 < d) (u : ℝ) : psi d u ≤ 1 / d := by
  have h := (bump d).normed_le_div_measure_closedBall_rIn volume u
  rw [bump_rIn hd] at h
  have hv : volume.real (Metric.closedBall (0 : ℝ) (d / 2)) = d := by
    rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hv] at h
  exact h

/-- `tconv d = ψ_d ⋆ ψ_d` (real). -/
def tconv (d : ℝ) : ℝ → ℝ := convolution (psi d) (psi d) (ContinuousLinearMap.mul ℝ ℝ) volume

lemma tconv_apply (d u : ℝ) : tconv d u = ∫ t, psi d t * psi d (u - t) := by
  simp [tconv, convolution_def]

lemma tconv_nonneg (d u : ℝ) : 0 ≤ tconv d u := by
  rw [tconv_apply]
  exact integral_nonneg fun t => mul_nonneg (psi_nonneg d t) (psi_nonneg d _)

lemma integrable_psi_mul_psi (d u : ℝ) : Integrable (fun t => psi d t * psi d (u - t)) := by
  have hc : Continuous (fun t => psi d t * psi d (u - t)) := by
    have := psi_continuous d
    fun_prop
  exact hc.integrable_of_hasCompactSupport ((psi_hasCompactSupport d).mul_right)

lemma tconv_le {d : ℝ} (hd : 0 < d) (u : ℝ) : tconv d u ≤ 1 / d := by
  rw [tconv_apply]
  calc ∫ t, psi d t * psi d (u - t) ≤ ∫ t, psi d t * (1 / d) := by
        refine integral_mono (integrable_psi_mul_psi d u) ((psi_integrable d).mul_const _) ?_
        intro t
        exact mul_le_mul_of_nonneg_left (psi_le hd _) (psi_nonneg d t)
    _ = 1 / d := by rw [integral_mul_const, psi_integral, one_mul]

lemma tconv_eq_zero {d u : ℝ} (hd : 0 < d) (hu : 2 * d ≤ |u|) : tconv d u = 0 := by
  rw [tconv_apply]
  have : (fun t => psi d t * psi d (u - t)) = fun _ => 0 := by
    funext t
    by_cases ht : d ≤ |t|
    · rw [psi_eq_zero hd ht, zero_mul]
    · push Not at ht
      have : d ≤ |u - t| := by
        have := abs_sub_abs_le_abs_sub u t
        linarith
      rw [psi_eq_zero hd this, mul_zero]
  rw [this, integral_zero]

lemma tconv_contDiff (d : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tconv d) :=
  (psi_hasCompactSupport d).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    (psi_contDiff d) (psi_integrable d).locallyIntegrable

lemma tconv_hasCompactSupport (d : ℝ) : HasCompactSupport (tconv d) :=
  (psi_hasCompactSupport d).convolution (ContinuousLinearMap.mul ℝ ℝ) (psi_hasCompactSupport d)

lemma tconv_continuous (d : ℝ) : Continuous (tconv d) := (tconv_contDiff d).continuous

/-- The test `testFn d = ψ_d ⋆ ψ_d` as a complex Weil test. -/
def testFn (d : ℝ) : ℝ → ℂ := fun u => (tconv d u : ℂ)

lemma testFn_isWeilTest (d : ℝ) : WeilExplicit.IsWeilTest (testFn d) := by
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (tconv_contDiff d)
  · exact (tconv_hasCompactSupport d).comp_left Complex.ofReal_zero

/-- Complexified `ψ_d`. -/
def psiC (d : ℝ) : ℝ → ℂ := fun u => (psi d u : ℂ)

lemma psiC_integrable (d : ℝ) : Integrable (psiC d) := (psi_integrable d).ofReal

lemma testFn_eq_conv (d : ℝ) :
    testFn d = convolution (psiC d) (psiC d) (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext u
  simp only [testFn, tconv_apply, convolution_def, psiC, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  congr 1
  funext t
  push_cast
  rfl

/-- `ψ̂_d(ξ) = ∫ ψ_d(u) cos(2πuξ) du` (real, since `ψ_d` is even). -/
def psiHat (d ξ : ℝ) : ℝ := ∫ u, psi d u * Real.cos (2 * Real.pi * u * ξ)

/-- The integrand of `𝓕 ψ_d`. -/
def fInt (d ξ v : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * (psi d v : ℂ)

lemma fInt_continuous (d ξ : ℝ) : Continuous (fInt d ξ) := by
  have := psi_continuous d
  unfold fInt
  fun_prop

lemma fInt_integrable (d ξ : ℝ) : Integrable (fInt d ξ) := by
  refine (fInt_continuous d ξ).integrable_of_hasCompactSupport ?_
  have : HasCompactSupport (fun v => (psi d v : ℂ)) :=
    (psi_hasCompactSupport d).comp_left Complex.ofReal_zero
  exact this.mul_left

lemma fInt_add_neg (d ξ v : ℝ) :
    fInt d ξ v + fInt d ξ (-v) = ((2 * (psi d v * Real.cos (2 * Real.pi * v * ξ)) : ℝ) : ℂ) := by
  simp only [fInt, psi_neg]
  have hc := Complex.two_cos (2 * Real.pi * v * ξ)
  push_cast
  rw [show (-2 * (Real.pi : ℂ) * -(v : ℂ) * (ξ : ℂ) * Complex.I)
      = (2 * (Real.pi : ℂ) * (v : ℂ) * (ξ : ℂ)) * Complex.I by ring,
    show (-2 * (Real.pi : ℂ) * (v : ℂ) * (ξ : ℂ) * Complex.I)
      = -(2 * (Real.pi : ℂ) * (v : ℂ) * (ξ : ℂ)) * Complex.I by ring]
  linear_combination -(psi d v : ℂ) * hc

lemma fourier_psiC (d ξ : ℝ) : 𝓕 (psiC d) ξ = (psiHat d ξ : ℂ) := by
  have h1 : 𝓕 (psiC d) ξ = ∫ v, fInt d ξ v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    rfl
  have hneg : ∫ v, fInt d ξ (-v) = ∫ v, fInt d ξ v := integral_neg_eq_self (fInt d ξ) volume
  have hi' : Integrable (fun v => fInt d ξ (-v)) := (fInt_integrable d ξ).comp_neg
  have hsum : ∫ v, (fInt d ξ v + fInt d ξ (-v)) = 2 * ∫ v, fInt d ξ v := by
    rw [integral_add (fInt_integrable d ξ) hi', hneg]; ring
  have h2 : ∫ v, (fInt d ξ v + fInt d ξ (-v)) = ((2 * psiHat d ξ : ℝ) : ℂ) := by
    simp_rw [fInt_add_neg]
    rw [integral_complex_ofReal, integral_const_mul]
    rfl
  rw [hsum] at h2
  rw [h1]
  have h3 : (2 : ℂ) * ∫ v, fInt d ξ v = 2 * ((psiHat d ξ : ℝ) : ℂ) := by rw [h2]; push_cast; ring
  exact mul_left_cancel₀ two_ne_zero h3

lemma fourier_testFn (d ξ : ℝ) : 𝓕 (testFn d) ξ = ((psiHat d ξ ^ 2 : ℝ) : ℂ) := by
  rw [testFn_eq_conv, Real.fourier_mul_convolution_eq (psiC_integrable d) (psiC_integrable d),
    fourier_psiC]
  push_cast
  ring

lemma gwHat_testFn (d r : ℝ) :
    gwHat (testFn d) r = ((psiHat d (-(r / (2 * Real.pi))) ^ 2 : ℝ) : ℂ) := by
  rw [gwHat_eq_fourier, fourier_testFn]

lemma integrable_psi_cos (d ξ : ℝ) :
    Integrable (fun u => psi d u * Real.cos (2 * Real.pi * u * ξ)) := by
  have hc : Continuous (fun u => psi d u * Real.cos (2 * Real.pi * u * ξ)) := by
    have := psi_continuous d
    fun_prop
  exact hc.integrable_of_hasCompactSupport (psi_hasCompactSupport d).mul_right

lemma abs_psiHat_le (d ξ : ℝ) : |psiHat d ξ| ≤ 1 := by
  unfold psiHat
  calc |∫ u, psi d u * Real.cos (2 * Real.pi * u * ξ)|
      ≤ ∫ u, |psi d u * Real.cos (2 * Real.pi * u * ξ)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, psi d u := by
        refine integral_mono (integrable_psi_cos d ξ).abs (psi_integrable d) ?_
        · intro u
          dsimp only
          rw [abs_mul, abs_of_nonneg (psi_nonneg d u)]
          exact mul_le_of_le_one_right (psi_nonneg d u) (Real.abs_cos_le_one _)
    _ = 1 := psi_integral d

lemma one_sub_psiHat_le {d : ℝ} (hd : 0 < d) (ξ : ℝ) :
    1 - psiHat d ξ ≤ 2 * Real.pi ^ 2 * d ^ 2 * ξ ^ 2 := by
  have h1 : 1 - psiHat d ξ = ∫ u, psi d u * (1 - Real.cos (2 * Real.pi * u * ξ)) := by
    have e : (1 : ℝ) - psiHat d ξ = (∫ u, psi d u) - psiHat d ξ := by rw [psi_integral]
    rw [e, psiHat, ← integral_sub (psi_integrable d) (integrable_psi_cos d ξ)]
    congr 1
    funext u
    ring
  rw [h1]
  have hint : Integrable (fun u => psi d u * (1 - Real.cos (2 * Real.pi * u * ξ))) :=
    ((psi_integrable d).sub (integrable_psi_cos d ξ)).congr
      (Eventually.of_forall fun u => by simp only [Pi.sub_apply]; ring)
  calc ∫ u, psi d u * (1 - Real.cos (2 * Real.pi * u * ξ))
      ≤ ∫ u, psi d u * (2 * Real.pi ^ 2 * d ^ 2 * ξ ^ 2) := by
        refine integral_mono hint ((psi_integrable d).mul_const _) ?_
        intro u
        dsimp only
        by_cases hu : d ≤ |u|
        · rw [psi_eq_zero hd hu, zero_mul, zero_mul]
        · push Not at hu
          refine mul_le_mul_of_nonneg_left ?_ (psi_nonneg d u)
          have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * u * ξ)
          have hu2 : u ^ 2 ≤ d ^ 2 := by
            have := sq_abs u
            nlinarith [abs_nonneg u]
          have : (2 * Real.pi * u * ξ) ^ 2 / 2 ≤ 2 * Real.pi ^ 2 * d ^ 2 * ξ ^ 2 := by
            have e : (2 * Real.pi * u * ξ) ^ 2 / 2 = 2 * Real.pi ^ 2 * u ^ 2 * ξ ^ 2 := by ring
            rw [e]
            have hp : 0 ≤ 2 * Real.pi ^ 2 * ξ ^ 2 := by positivity
            nlinarith
          linarith
    _ = 2 * Real.pi ^ 2 * d ^ 2 * ξ ^ 2 := by rw [integral_mul_const, psi_integral, one_mul]

lemma tendsto_psiHat_sq (ξ : ℝ) :
    Tendsto (fun d => psiHat d ξ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hup : ∀ d, psiHat d ξ ≤ 1 := fun d => (abs_le.mp (abs_psiHat_le d ξ)).2
  have hlow : ∀ᶠ d in 𝓝[>] (0 : ℝ), 1 - 2 * Real.pi ^ 2 * d ^ 2 * ξ ^ 2 ≤ psiHat d ξ := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have := one_sub_psiHat_le hd ξ
    linarith
  have hlim : Tendsto (fun d : ℝ => 1 - 2 * Real.pi ^ 2 * d ^ 2 * ξ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun d : ℝ => 1 - 2 * Real.pi ^ 2 * d ^ 2 * ξ ^ 2) := by fun_prop
    have := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
      sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun d => psiHat d ξ) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow
      (Eventually.of_forall hup)
  simpa using h1.pow 2

/-! ## 3. Guinand partners and the antichain theorem (Lemma M) -/

/-- `IsGuinandPartner E Pr μ`: the measure `μ` on `ℝ` (a positive real zero side) satisfies the
Guinand-Weil identity with pole+archimedean functional `E` and prime-side functional `Pr`:
`∫ ĝ dμ = E g - Pr g` for every Weil test `g` whose zero-side transform is `μ`-integrable. -/
def IsGuinandPartner (E Pr : (ℝ → ℂ) → ℂ) (μ : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → Integrable (gwHat g) μ →
    ∫ r, gwHat g r ∂μ = E g - Pr g

/-- The dual kernel of the test family: `k_d(r) = ψ̂_d(r/2π)^2 ∈ [0,1]`, `→ 1` as `d → 0`. -/
def kd (d r : ℝ) : ℝ := psiHat d (-(r / (2 * Real.pi))) ^ 2

lemma kd_nonneg (d r : ℝ) : 0 ≤ kd d r := sq_nonneg _

lemma gwHat_testFn_kd (d r : ℝ) : gwHat (testFn d) r = ((kd d r : ℝ) : ℂ) := gwHat_testFn d r

lemma integral_gwHat_testFn (μ : Measure ℝ) (d : ℝ) :
    ∫ r, gwHat (testFn d) r ∂μ = ((∫ r, kd d r ∂μ : ℝ) : ℂ) := by
  simp_rw [gwHat_testFn_kd]
  exact integral_complex_ofReal

lemma integrable_kd {μ : Measure ℝ} (htemp : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ) (d : ℝ) :
    Integrable (kd d) μ := by
  refine (integrable_gwHat (testFn_isWeilTest d) htemp).re.congr
    (Eventually.of_forall fun r => ?_)
  simp [gwHat_testFn_kd]

/-- **The Fatou step (kernel).** A measure whose `k_d`-integrals are eventually below a quantity
tending to `0` as `d → 0⁺` is the zero measure (since `k_d → 1` pointwise). -/
lemma measure_eq_zero_of_kd {ρ : Measure ℝ} (hk : ∀ d, Integrable (kd d) ρ) {δ : ℝ → ℝ}
    (hle : ∀ᶠ d in 𝓝[>] (0 : ℝ), ∫ r, kd d r ∂ρ ≤ δ d)
    (hδ : Tendsto δ (𝓝[>] (0 : ℝ)) (𝓝 0)) : ρ = 0 := by
  have hmeas : ∀ d, AEMeasurable (fun r => ENNReal.ofReal (kd d r)) ρ :=
    fun d => (hk d).aemeasurable.ennreal_ofReal
  have hfatou := lintegral_liminf_le' (μ := ρ) (u := 𝓝[>] (0 : ℝ)) hmeas
  have hlim : ∀ r, liminf (fun d => ENNReal.ofReal (kd d r)) (𝓝[>] (0 : ℝ)) = 1 := by
    intro r
    have h := ENNReal.tendsto_ofReal (tendsto_psiHat_sq (-(r / (2 * Real.pi))))
    rw [ENNReal.ofReal_one] at h
    exact h.liminf_eq
  simp_rw [hlim, lintegral_one] at hfatou
  have hle' : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      ∫⁻ r, ENNReal.ofReal (kd d r) ∂ρ ≤ ENNReal.ofReal (δ d) := by
    filter_upwards [hle] with d hd
    rw [← ofReal_integral_eq_lintegral_ofReal (hk d) (ae_of_all _ fun r => kd_nonneg d r)]
    exact ENNReal.ofReal_le_ofReal hd
  have htend : Tendsto (fun d => ENNReal.ofReal (δ d)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hδ
    rwa [ENNReal.ofReal_zero] at this
  have hlimle : liminf (fun d => ∫⁻ r, ENNReal.ofReal (kd d r) ∂ρ) (𝓝[>] (0 : ℝ)) ≤ 0 := by
    calc liminf (fun d => ∫⁻ r, ENNReal.ofReal (kd d r) ∂ρ) (𝓝[>] (0 : ℝ))
        ≤ liminf (fun d => ENNReal.ofReal (δ d)) (𝓝[>] (0 : ℝ)) := liminf_le_liminf hle'
      _ = 0 := htend.liminf_eq
  have huniv : ρ univ = 0 := le_antisymm (hfatou.trans hlimle) zero_le
  exact Measure.measure_univ_eq_zero.mp huniv

/-- **Antichain core (kernel).** Two Guinand partners with a common functional `E`, the second
obtained from the first by adding a measure `ρ`: if the second prime side is `≥ 0` on the test
family and the first has no mass at `u = 0` at the test scale, then `ρ = 0`. -/
theorem antichain_core {E Pr₁ Pr₂ : (ℝ → ℂ) → ℂ} {μ ρ : Measure ℝ}
    (h₁ : IsGuinandPartner E Pr₁ μ) (h₂ : IsGuinandPartner E Pr₂ (μ + ρ))
    (htest : IsTestTempered (μ + ρ))
    (hpos : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 ≤ (Pr₂ (testFn d)).re)
    (hsmall : Tendsto (fun d => (Pr₁ (testFn d)).re) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ρ = 0 := by
  have hint : ∀ d, Integrable (gwHat (testFn d)) (μ + ρ) :=
    fun d => htest _ (testFn_isWeilTest d)
  have hintμ : ∀ d, Integrable (gwHat (testFn d)) μ :=
    fun d => (integrable_add_measure.mp (hint d)).1
  have hintρ : ∀ d, Integrable (gwHat (testFn d)) ρ :=
    fun d => (integrable_add_measure.mp (hint d)).2
  have hkρ : ∀ d, Integrable (kd d) ρ := by
    intro d
    refine (hintρ d).re.congr (Eventually.of_forall fun r => ?_)
    simp [gwHat_testFn_kd]
  have hid : ∀ d, ∫ r, kd d r ∂ρ = (Pr₁ (testFn d)).re - (Pr₂ (testFn d)).re := by
    intro d
    have e1 := h₁ _ (testFn_isWeilTest d) (hintμ d)
    have e2 := h₂ _ (testFn_isWeilTest d) (hint d)
    rw [integral_add_measure (hintμ d) (hintρ d), e1] at e2
    have e3 : ∫ r, gwHat (testFn d) r ∂ρ = Pr₁ (testFn d) - Pr₂ (testFn d) := by
      linear_combination e2
    rw [integral_gwHat_testFn] at e3
    have := congrArg Complex.re e3
    simpa using this
  refine measure_eq_zero_of_kd hkρ (δ := fun d => (Pr₁ (testFn d)).re) ?_ hsmall
  filter_upwards [hpos] with d hd
  rw [hid d]
  linarith

/-- A prime side given by a measure `P`: `Pr g = ∫ g dP`. -/
def measPr (P : Measure ℝ) : (ℝ → ℂ) → ℂ := fun g => ∫ u, g u ∂P

lemma measPr_testFn_re (P : Measure ℝ) (d : ℝ) :
    (measPr P (testFn d)).re = ∫ u, tconv d u ∂P := by
  simp only [measPr, testFn]
  rw [integral_complex_ofReal, Complex.ofReal_re]

lemma measPr_testFn_nonneg (P : Measure ℝ) (d : ℝ) : 0 ≤ (measPr P (testFn d)).re := by
  rw [measPr_testFn_re]
  exact integral_nonneg (tconv_nonneg d)

lemma tconv_le_inv {d u : ℝ} (hd : 0 < d) (hu0 : u ≠ 0) (hu : |u| < 2 * d) :
    tconv d u ≤ 2 * |u|⁻¹ := by
  have h1 := tconv_le hd u
  have hpos : 0 < |u| := abs_pos.mpr hu0
  have h2 : 1 / d ≤ 2 * |u|⁻¹ := by
    rw [div_le_iff₀ hd]
    have e : |u|⁻¹ * |u| = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith [inv_pos.mpr hpos]
  linarith

/-- A positive prime side with no atom at `0` and `∫_{0<|u|<1} |u|⁻¹ dP < ∞` is invisible to the
test family in the limit `d → 0`. -/
lemma measPr_testFn_tendsto {P : Measure ℝ} (h0 : P {0} = 0)
    (hint : IntegrableOn (fun u : ℝ => |u|⁻¹) (Ioo (-1) 1) P) :
    Tendsto (fun d => (measPr P (testFn d)).re) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simp_rw [measPr_testFn_re]
  have hne : ∀ᵐ u ∂P, u ≠ 0 := by
    have : ∀ᵐ u ∂P, u ∉ ({0} : Set ℝ) := measure_eq_zero_iff_ae_notMem.mp h0
    filter_upwards [this] with u hu
    simpa using hu
  have key := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := 𝓝[>] (0 : ℝ))
    (F := fun d u => tconv d u) (f := fun _ => (0 : ℝ))
    (fun u => 2 * (Ioo (-1 : ℝ) 1).indicator (fun u => |u|⁻¹) u) ?_ ?_ ?_ ?_
  · simpa using key
  · exact Eventually.of_forall fun d => (tconv_continuous d).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with d hd
    filter_upwards [hne] with u hu
    rw [Real.norm_of_nonneg (tconv_nonneg d u)]
    by_cases h : |u| < 2 * d
    · have hmem : u ∈ Ioo (-1 : ℝ) 1 := by
        rw [mem_Ioo, ← abs_lt]
        linarith [hd.2]
      rw [indicator_of_mem hmem]
      exact tconv_le_inv hd.1 hu h
    · push Not at h
      rw [tconv_eq_zero hd.1 h]
      have : 0 ≤ (Ioo (-1 : ℝ) 1).indicator (fun u => |u|⁻¹) u :=
        indicator_nonneg (fun u _ => inv_nonneg.mpr (abs_nonneg u)) u
      linarith
  · exact (hint.integrable_indicator measurableSet_Ioo).const_mul 2
  · filter_upwards [hne] with u hu
    have hpos : 0 < |u| := abs_pos.mpr hu
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < |u| / 2 by positivity)] with d hd
    rw [tconv_eq_zero hd.1 (by linarith [hd.2])]

/-- **LEMMA M (kernel): positive Guinand partners cannot be nested.** -/
theorem guinand_antichain {E : (ℝ → ℂ) → ℂ} {μ ρ P₁ P₂ : Measure ℝ}
    (h₁ : IsGuinandPartner E (measPr P₁) μ) (h₂ : IsGuinandPartner E (measPr P₂) (μ + ρ))
    (htest : IsTestTempered (μ + ρ))
    (h0 : P₁ {0} = 0) (hint : IntegrableOn (fun u : ℝ => |u|⁻¹) (Ioo (-1) 1) P₁) :
    ρ = 0 ∧ ∀ g, WeilExplicit.IsWeilTest g → ∫ u, g u ∂P₁ = ∫ u, g u ∂P₂ := by
  have hρ := antichain_core h₁ h₂ htest
    (Eventually.of_forall fun d => measPr_testFn_nonneg P₂ d) (measPr_testFn_tendsto h0 hint)
  refine ⟨hρ, fun g hg => ?_⟩
  subst hρ
  rw [add_zero] at h₂ htest
  have hi := htest g hg
  have e : E g - measPr P₁ g = E g - measPr P₂ g := (h₁ g hg hi).symm.trans (h₂ g hg hi)
  simpa [measPr] using e

/-! ### From agreement on Weil tests to equality of measures -/

/-- Smooth bumps `= 1` on `closedBall c (r + 1/(n+1))`, `= 0` off `ball c (r + 2/(n+1))`. -/
def shrinkBump (c r : ℝ) (hr : 0 ≤ r) (n : ℕ) : ContDiffBump c :=
  ⟨r + 1 / ((n : ℝ) + 1), r + 2 / ((n : ℝ) + 1), by positivity, by
    have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have e : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
    rw [e]; linarith⟩

lemma tendsto_integral_shrinkBump (P : Measure ℝ) [IsLocallyFiniteMeasure P] (c r : ℝ)
    (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => ∫ u, shrinkBump c r hr n u ∂P) atTop
      (𝓝 (P.real (Metric.closedBall c r))) := by
  rw [← integral_indicator_one measurableSet_closedBall]
  refine tendsto_integral_of_dominated_convergence
    ((Metric.closedBall c (r + 2)).indicator 1) (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact (shrinkBump c r hr n).continuous.aestronglyMeasurable
  · refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    exact integrableOn_const measure_closedBall_lt_top.ne
  · refine ae_of_all _ fun u => ?_
    set f := shrinkBump c r hr n
    rw [Real.norm_of_nonneg f.nonneg]
    by_cases hu : u ∈ Metric.closedBall c (r + 2)
    · rw [indicator_of_mem hu]
      exact f.le_one
    · rw [indicator_of_notMem hu]
      apply le_of_eq
      apply f.zero_of_le_dist
      rw [Metric.mem_closedBall, not_le] at hu
      have h1 : 2 / ((n : ℝ) + 1) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      show r + 2 / ((n : ℝ) + 1) ≤ dist u c
      linarith
  · refine ae_of_all _ fun u => ?_
    by_cases hu : u ∈ Metric.closedBall c r
    · rw [indicator_of_mem hu]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      symm
      apply (shrinkBump c r hr n).one_of_mem_closedBall
      rw [Metric.mem_closedBall] at hu ⊢
      show dist u c ≤ r + 1 / ((n : ℝ) + 1)
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · rw [indicator_of_notMem hu]
      rw [Metric.mem_closedBall, not_le] at hu
      have hpos : 0 < (dist u c - r) / 2 := by linarith
      have hev := (tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _ hpos
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      symm
      apply (shrinkBump c r hr n).zero_of_le_dist
      show r + 2 / ((n : ℝ) + 1) ≤ dist u c
      have e : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
      rw [e]
      linarith

/-- Two locally finite measures on `ℝ` that agree on every Weil test are equal. -/
theorem measure_eq_of_integral_test_eq {P₁ P₂ : Measure ℝ} [IsLocallyFiniteMeasure P₁]
    [IsLocallyFiniteMeasure P₂]
    (h : ∀ g, WeilExplicit.IsWeilTest g → ∫ u, g u ∂P₁ = ∫ u, g u ∂P₂) : P₁ = P₂ := by
  refine Measure.ext_of_Icc P₁ P₂ (fun a b hab => ?_)
  have hr : 0 ≤ (b - a) / 2 := by linarith
  have hIcc : Icc a b = Metric.closedBall ((a + b) / 2) ((b - a) / 2) := by
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> ring
  have heq : ∀ n, ∫ u, shrinkBump ((a + b) / 2) ((b - a) / 2) hr n u ∂P₁
      = ∫ u, shrinkBump ((a + b) / 2) ((b - a) / 2) hr n u ∂P₂ := by
    intro n
    set f := shrinkBump ((a + b) / 2) ((b - a) / 2) hr n
    have hg : WeilExplicit.IsWeilTest (fun u => ((f u : ℝ) : ℂ)) :=
      ⟨Complex.ofRealCLM.contDiff.comp f.contDiff,
        f.hasCompactSupport.comp_left Complex.ofReal_zero⟩
    have := h _ hg
    rw [integral_complex_ofReal, integral_complex_ofReal] at this
    exact_mod_cast this
  have h1 := tendsto_integral_shrinkBump P₁ ((a + b) / 2) ((b - a) / 2) hr
  have h2 := tendsto_integral_shrinkBump P₂ ((a + b) / 2) ((b - a) / 2) hr
  have hlim := tendsto_nhds_unique h1 (Tendsto.congr (fun n => (heq n).symm) h2)
  rw [hIcc]
  exact (ENNReal.toReal_eq_toReal_iff' measure_closedBall_lt_top.ne
    measure_closedBall_lt_top.ne).mp hlim

/-- **LEMMA M, full form (kernel).** Nested positive Guinand partners with a common
archimedean/pole functional coincide, and so do their (locally finite) prime sides. -/
theorem guinand_antichain_measure {E : (ℝ → ℂ) → ℂ} {μ ρ P₁ P₂ : Measure ℝ}
    [IsLocallyFiniteMeasure P₁] [IsLocallyFiniteMeasure P₂]
    (h₁ : IsGuinandPartner E (measPr P₁) μ) (h₂ : IsGuinandPartner E (measPr P₂) (μ + ρ))
    (htest : IsTestTempered (μ + ρ))
    (h0 : P₁ {0} = 0) (hint : IntegrableOn (fun u : ℝ => |u|⁻¹) (Ioo (-1) 1) P₁) :
    ρ = 0 ∧ P₁ = P₂ :=
  ⟨(guinand_antichain h₁ h₂ htest h0 hint).1,
    measure_eq_of_integral_test_eq (guinand_antichain h₁ h₂ htest h0 hint).2⟩

/-- Tempered measures are finite on compact intervals. -/
lemma measure_Icc_lt_top_of_tempered {μ : Measure ℝ}
    (htemp : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ) {a b : ℝ} : μ (Icc a b) < ⊤ := by
  set R := max |a| |b|
  have hε : 0 < (1 + R ^ 2)⁻¹ := by positivity
  refine lt_of_le_of_lt (measure_mono ?_) (htemp.measure_norm_ge_lt_top hε)
  intro x hx
  simp only [Set.mem_ofPred_eq]
  have hxR : |x| ≤ R := abs_le_max_abs_abs hx.1 hx.2
  have hx2 : x ^ 2 ≤ R ^ 2 := by
    have := sq_abs x
    nlinarith [abs_nonneg x]
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (by linarith)

/-- **LEMMA M, order form (kernel), the seat's statement verbatim.** If `(μ₁, P₁)` and `(μ₂, P₂)`
are Guinand pairs with a common functional `E`, `μ₁ ≤ μ₂`, `μ₂` tempered, `P₁, P₂ ≥ 0` locally
finite, `P₁{0} = 0` and `∫_{0<|u|<1} |u|⁻¹ dP₁ < ∞`, then `μ₁ = μ₂` and `P₁ = P₂`. -/
theorem guinand_antichain_le {E : (ℝ → ℂ) → ℂ} {μ₁ μ₂ P₁ P₂ : Measure ℝ}
    [IsLocallyFiniteMeasure P₁] [IsLocallyFiniteMeasure P₂]
    (h₁ : IsGuinandPartner E (measPr P₁) μ₁) (h₂ : IsGuinandPartner E (measPr P₂) μ₂)
    (hle : μ₁ ≤ μ₂) (htemp : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ₂)
    (h0 : P₁ {0} = 0) (hint : IntegrableOn (fun u : ℝ => |u|⁻¹) (Ioo (-1) 1) P₁) :
    μ₁ = μ₂ ∧ P₁ = P₂ := by
  have htemp₁ : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ₁ := htemp.mono_measure hle
  have hid : ∀ d, ∫ r, kd d r ∂μ₂ - ∫ r, kd d r ∂μ₁
      = (measPr P₁ (testFn d)).re - (measPr P₂ (testFn d)).re := by
    intro d
    have e1 := h₁ _ (testFn_isWeilTest d) (integrable_gwHat (testFn_isWeilTest d) htemp₁)
    have e2 := h₂ _ (testFn_isWeilTest d) (integrable_gwHat (testFn_isWeilTest d) htemp)
    rw [integral_gwHat_testFn] at e1 e2
    have e3 : (((∫ r, kd d r ∂μ₂) - ∫ r, kd d r ∂μ₁ : ℝ) : ℂ)
        = measPr P₁ (testFn d) - measPr P₂ (testFn d) := by
      push_cast
      rw [e1, e2]
      ring
    have := congrArg Complex.re e3
    simpa using this
  have hwin : ∀ a b : ℝ, μ₁ (Icc a b) = μ₂ (Icc a b) := by
    intro a b
    set K := Icc a b
    have hK : MeasurableSet K := measurableSet_Icc
    have : IsFiniteMeasure (μ₁.restrict K) :=
      isFiniteMeasure_restrict.mpr (lt_of_le_of_lt (hle K)
        (measure_Icc_lt_top_of_tempered htemp)).ne
    have : IsFiniteMeasure (μ₂.restrict K) :=
      isFiniteMeasure_restrict.mpr (measure_Icc_lt_top_of_tempered htemp).ne
    have hleK : μ₁.restrict K ≤ μ₂.restrict K := Measure.restrict_mono subset_rfl hle
    set ρ := μ₂.restrict K - μ₁.restrict K
    have hsplit : ρ + μ₁.restrict K = μ₂.restrict K := Measure.sub_add_cancel_of_le hleK
    have hρle : ρ ≤ μ₂ := by
      calc ρ ≤ ρ + μ₁.restrict K := Measure.le_add_right le_rfl
        _ = μ₂.restrict K := hsplit
        _ ≤ μ₂ := Measure.restrict_le_self
    have hkρ : ∀ d, Integrable (kd d) ρ := fun d => (integrable_kd htemp d).mono_measure hρle
    have hkμ₁ : ∀ d, Integrable (kd d) μ₁ := fun d => integrable_kd htemp₁ d
    have hkμ₂ : ∀ d, Integrable (kd d) μ₂ := fun d => integrable_kd htemp d
    have hρ0 : ρ = 0 := by
      refine measure_eq_zero_of_kd hkρ (δ := fun d => (measPr P₁ (testFn d)).re) ?_
        (measPr_testFn_tendsto h0 hint)
      refine Eventually.of_forall fun d => ?_
      have hρint : ∫ r, kd d r ∂ρ = ∫ r in K, kd d r ∂μ₂ - ∫ r in K, kd d r ∂μ₁ := by
        have := integral_add_measure (hkρ d) ((hkμ₁ d).restrict (s := K))
        rw [hsplit] at this
        linarith
      have hc : ∫ r in Kᶜ, kd d r ∂μ₁ ≤ ∫ r in Kᶜ, kd d r ∂μ₂ :=
        integral_mono_measure (Measure.restrict_mono subset_rfl hle)
          (ae_of_all _ fun r => kd_nonneg d r) (hkμ₂ d).restrict
      have h1 := integral_add_compl hK (hkμ₁ d)
      have h2 := integral_add_compl hK (hkμ₂ d)
      have h3 := hid d
      have h4 := measPr_testFn_nonneg P₂ d
      show ∫ r, kd d r ∂ρ ≤ (measPr P₁ (testFn d)).re
      linarith
    have : μ₂.restrict K = μ₁.restrict K := by rw [← hsplit, hρ0, zero_add]
    have hu := congrArg (fun ν : Measure ℝ => ν univ) this
    simp only [Measure.restrict_apply_univ] at hu
    exact hu.symm
  have hμ : μ₁ = μ₂ := by
    refine Measure.ext_of_Icc' μ₁ μ₂ (fun a b _ => ?_) (fun a b _ => hwin a b)
    exact (lt_of_le_of_lt (hle _) (measure_Icc_lt_top_of_tempered htemp)).ne
  refine ⟨hμ, measure_eq_of_integral_test_eq fun g hg => ?_⟩
  subst hμ
  have hi := integrable_gwHat hg htemp
  have e : E g - measPr P₁ g = E g - measPr P₂ g := (h₁ g hg hi).symm.trans (h₂ g hg hi)
  simpa [measPr] using e

/-! ### Zeta's own explicit-formula data (the corpus `archSide`, `primeSide`) -/

/-- **The prime-side gap (kernel; reproved from CruxFQ_ZeroSideFejer).** -/
theorem primeSide_eq_zero_of_gap {g : ℝ → ℂ} (hg : ∀ u : ℝ, Real.log 2 ≤ |u| → g u = 0) :
    WeilExplicit.primeSide g = 0 := by
  unfold WeilExplicit.primeSide
  have hterm : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (g (Real.log n) + g (-Real.log n)) = 0 := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hlog : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hpos : 0 ≤ Real.log n := le_trans (Real.log_nonneg (by norm_num)) hlog
      have h1 : g (Real.log n) = 0 := hg _ (by rw [abs_of_nonneg hpos]; exact hlog)
      have h2 : g (-Real.log n) = 0 := hg _ (by rw [abs_neg, abs_of_nonneg hpos]; exact hlog)
      rw [h1, h2]; simp
  simp only [hterm, tsum_zero]

lemma primeSide_testFn_eventually :
    ∀ᶠ d in 𝓝[>] (0 : ℝ), WeilExplicit.primeSide (testFn d) = 0 := by
  have hl : 0 < Real.log 2 / 2 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  filter_upwards [Ioo_mem_nhdsGT hl] with d hd
  refine primeSide_eq_zero_of_gap fun u hu => ?_
  simp only [testFn]
  rw [tconv_eq_zero hd.1 (by linarith [hd.2]), Complex.ofReal_zero]

/-- A positive measure `μ` on `ℝ` is a **real Guinand partner of zeta** if it reproduces zeta's
explicit formula (the corpus `archSide` and `primeSide`, conductor 1) on every Weil test. -/
def IsZetaPartner (μ : Measure ℝ) : Prop :=
  IsGuinandPartner WeilExplicit.archSide WeilExplicit.primeSide μ

/-- **No real zeros can be added to a positive zeta partner (kernel).** If `μ` reproduces zeta's
explicit formula, `μ + ρ` reproduces the formula with zeta's archimedean side and ANY positive
prime side `P`, and `μ + ρ` is tempered, then `ρ = 0`. -/
theorem zeta_partner_no_added_zeros {μ ρ P : Measure ℝ} (h₁ : IsZetaPartner μ)
    (h₂ : IsGuinandPartner WeilExplicit.archSide (measPr P) (μ + ρ))
    (htest : IsTestTempered (μ + ρ)) : ρ = 0 := by
  refine antichain_core h₁ h₂ htest (Eventually.of_forall fun d => measPr_testFn_nonneg P d) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [primeSide_testFn_eventually] with d hd
  rw [hd, Complex.zero_re]

/-- **No real zeros can be deleted from a positive zeta partner (kernel).** If `μ + ρ` reproduces
zeta's explicit formula and `μ` reproduces the formula with zeta's archimedean side and a
positive prime side `P` with no atom at `0` and `∫_{0<|u|<1} |u|⁻¹ dP < ∞`, then `ρ = 0`. -/
theorem zeta_partner_no_deleted_zeros {μ ρ P : Measure ℝ}
    (h₁ : IsGuinandPartner WeilExplicit.archSide (measPr P) μ) (h0 : P {0} = 0)
    (hint : IntegrableOn (fun u : ℝ => |u|⁻¹) (Ioo (-1) 1) P) (h₂ : IsZetaPartner (μ + ρ))
    (htest : IsTestTempered (μ + ρ)) : ρ = 0 := by
  refine antichain_core h₁ h₂ htest ?_ (measPr_testFn_tendsto h0 hint)
  filter_upwards [primeSide_testFn_eventually] with d hd
  rw [hd, Complex.zero_re]

/-- Positive zeta partners form an antichain. -/
theorem zeta_partners_antichain {μ ρ : Measure ℝ} (h₁ : IsZetaPartner μ)
    (h₂ : IsZetaPartner (μ + ρ)) (htest : IsTestTempered (μ + ρ)) :
    ρ = 0 := by
  refine antichain_core h₁ h₂ htest ?_ ?_
  · filter_upwards [primeSide_testFn_eventually] with d hd
    rw [hd, Complex.zero_re]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [primeSide_testFn_eventually] with d hd
    rw [hd, Complex.zero_re]


/-- The corpus transform `paperFT` on the real line is `gwHat`. -/
lemma paperFT_eq_gwHat (g : ℝ → ℂ) (r : ℝ) : Zeta23.paperFT g (r : ℂ) = gwHat g r := by
  unfold Zeta23.paperFT gwHat
  congr 1
  funext u
  congr 2
  push_cast
  ring

/-- On the real line the transform of a Hermitian autocorrelation is `|ĝ|²` (from the corpus). -/
lemma gwHat_autocorr {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) (r : ℝ) :
    gwHat (WeilExplicit.autocorr g) r = ((‖gwHat g r‖ ^ 2 : ℝ) : ℂ) := by
  rw [← weilKernel_line_eq_gwHat, RvMBridge5.weilKernel_autocorr_line hg, paperFT_eq_gwHat]
  push_cast
  ring

/-- **Circularity certificate Z1 (kernel).** A tempered positive measure on `ℝ` reproducing
zeta's explicit formula (the corpus `archSide`/`primeSide`) forces RH: its zero-side pairing of a
Hermitian autocorrelation is `∫ |ĝ|² dμ ≥ 0`, which is Weil positivity, and the corpus theorem
`RvMBridge9.weil_positivity_implies_rh` converts that into Mathlib's `RiemannHypothesis`.
So "zeta's zero side is a positive real Guinand partner" is not a route to RH: it IS RH. -/
theorem zeta_partner_implies_rh {μ : Measure ℝ} (h : IsZetaPartner μ)
    (htest : IsTestTempered μ) : RiemannHypothesis := by
  apply RvMBridge9.weil_positivity_implies_rh
  intro g hg
  have hac := RvMBridge5.isWeilTest_autocorr hg
  have e := h _ hac (htest _ hac)
  unfold WeilExplicit.weilForm
  rw [← e]
  simp_rw [gwHat_autocorr hg]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun r => sq_nonneg _

/-! ### Finite resolution (Proposition K, the direction that is a theorem here) -/

/-- `μ` is a positive real Guinand partner of zeta **at resolution `L`**: it reproduces zeta's
explicit formula for every Weil test supported in `(-L, L)`. -/
def IsZetaWindowPartner (L : ℝ) (μ : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → (∀ u : ℝ, L ≤ |u| → g u = 0) →
    Integrable (gwHat g) μ → ∫ r, gwHat g r ∂μ = WeilExplicit.archSide g - WeilExplicit.primeSide g

lemma autocorr_eq_zero_of_support {g : ℝ → ℂ} {L : ℝ} (hsupp : ∀ u : ℝ, L / 2 ≤ |u| → g u = 0)
    {u : ℝ} (hu : L ≤ |u|) : WeilExplicit.autocorr g u = 0 := by
  unfold WeilExplicit.autocorr
  have : (fun v : ℝ => g v * (starRingEnd ℂ) (g (v - u))) = fun _ => 0 := by
    funext v
    by_cases hv : L / 2 ≤ |v|
    · rw [hsupp v hv, zero_mul]
    · push Not at hv
      have : L / 2 ≤ |v - u| := by
        have := abs_sub_abs_le_abs_sub u v
        rw [abs_sub_comm] at this
        linarith
      rw [hsupp _ this, map_zero, mul_zero]
  rw [this, integral_zero]

/-- **A window partner gives window Weil positivity (kernel).** -/
theorem window_partner_weil_positivity {L : ℝ} {μ : Measure ℝ} (h : IsZetaWindowPartner L μ)
    (htest : IsTestTempered μ) {g : ℝ → ℂ}
    (hg : WeilExplicit.IsWeilTest g) (hsupp : ∀ u : ℝ, L / 2 ≤ |u| → g u = 0) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  have hac := RvMBridge5.isWeilTest_autocorr hg
  have e := h _ hac (fun u hu => autocorr_eq_zero_of_support hsupp hu)
    (htest _ hac)
  unfold WeilExplicit.weilForm
  rw [← e]
  simp_rw [gwHat_autocorr hg]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun r => sq_nonneg _

/-- **All resolutions together are RH (kernel).** If zeta has a tempered positive real partner at
every resolution `L > 0` (possibly a different one for each `L`), then RH. Each single resolution
certifies nothing (the seat's zero-side fooling lemma: Davenport-Heilbronn has positive window
partners at small resolution, COMPUTED); the family over all `L` is Weil positivity. -/
theorem all_windows_implies_rh
    (h : ∀ L : ℝ, 0 < L → ∃ μ : Measure ℝ, IsZetaWindowPartner L μ ∧ IsTestTempered μ) :
    RiemannHypothesis := by
  apply RvMBridge9.weil_positivity_implies_rh
  intro g hg
  obtain ⟨R, hR⟩ := hg.2.isCompact.isBounded.subset_closedBall 0
  have hL : 0 < 2 * (|R| + 1) := by positivity
  obtain ⟨μ, hμ, htest⟩ := h _ hL
  refine window_partner_weil_positivity hμ htest hg (fun u hu => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  have h2 : R ≤ |R| := le_abs_self R
  linarith

/-- Conversely every positive zeta partner is a window partner at every resolution. -/
lemma zetaPartner_window {μ : Measure ℝ} (h : IsZetaPartner μ) (L : ℝ) :
    IsZetaWindowPartner L μ := fun g hg _ hi => h g hg hi

/-! ### The converse: under RH, zeta's own zero measure is a positive real partner -/

lemma carrier_countable : (Zeta23.zetaZeroConfig.carrier).Countable := by
  have hsub : Zeta23.zetaZeroConfig.carrier ⊆ ⋃ n : ℤ, (Zeta23.zetaZeroConfig.carrier ∩
      {ρ : ℂ | (n : ℝ) < ρ.im ∧ ρ.im ≤ (n : ℝ) + 1}) := by
    intro ρ hρ
    refine mem_iUnion.mpr ⟨⌈ρ.im⌉ - 1, hρ, ?_, ?_⟩
    · push_cast
      linarith [Int.ceil_lt_add_one ρ.im]
    · push_cast
      linarith [Int.le_ceil ρ.im]
  exact (countable_iUnion fun n => (Zeta23.zetaZeroConfig.finite_window _ _).countable).mono hsub

instance : Countable Zeta23.zetaZeroConfig.carrier := carrier_countable.to_subtype

/-- The zero measure of zeta on the ordinate line, `Z_ζ = Σ_ρ m_ρ δ_{Im ρ}` over the nontrivial
zeros (corpus `zetaZeroConfig`). Positive and unconditional; it is zeta's zero multiset as a real
measure exactly when every nontrivial zero has real part `1/2`. -/
def zetaZeroMeasure : Measure ℝ :=
  Measure.sum (fun ρ : Zeta23.zetaZeroConfig.carrier =>
    ((Zeta23.zetaZeroConfig.mult ρ : ℕ) : ENNReal) • Measure.dirac (ρ : ℂ).im)

lemma gammaOf_eq_im_of_rh (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ Zeta23.zetaZeroConfig.carrier) : Zeta23.gammaOf ρ = ((ρ.im : ℝ) : ℂ) := by
  have h := RvMBridge5.eq_half_add_im_of_rh hRH hρ
  unfold Zeta23.gammaOf
  have e : ρ - 1 / 2 = ((ρ.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [h]
    ring
  rw [e, mul_div_assoc, div_self Complex.I_ne_zero, mul_one]

/-- Zeta's explicit formula read on the real line, under RH (from the corpus). -/
lemma zeta_EF_real_of_rh (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : WeilExplicit.IsWeilTest g) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zetaZeroConfig.mult ρ : ℂ) * gwHat g (ρ : ℂ).im) ∧
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
          (Zeta23.zetaZeroConfig.mult ρ : ℂ) * gwHat g (ρ : ℂ).im
        = WeilExplicit.archSide g - WeilExplicit.primeSide g := by
  obtain ⟨hsum, heq⟩ :=
    Zeta23.WeilEF.EF_lit_zetaZeroConfig g (RvMBridge4.contDiff_two_of_test hg) hg.2
  have hfun : (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT g (Zeta23.gammaOf ρ))
      = fun ρ : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult ρ : ℂ) * gwHat g (ρ : ℂ).im := by
    funext ρ
    rw [gammaOf_eq_im_of_rh hRH ρ.2, paperFT_eq_gwHat]
  rw [hfun] at hsum heq
  exact ⟨hsum, heq.trans (RvMBridge4.archSide_sub_primeSide hg).symm⟩

lemma zetaZeroMeasure_integrable_of_rh (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : WeilExplicit.IsWeilTest g) : Integrable (gwHat g) zetaZeroMeasure := by
  obtain ⟨hsum, -⟩ := zeta_EF_real_of_rh hRH hg
  have hn := (summable_norm_iff (E := ℂ)).mpr hsum
  unfold zetaZeroMeasure
  refine integrable_sum_dirac (fun ρ => ENNReal.natCast_ne_top _) ?_
  refine hn.congr fun ρ => ?_
  rw [norm_mul, Complex.norm_natCast, ENNReal.toReal_natCast]

lemma integral_zetaZeroMeasure_of_rh (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : WeilExplicit.IsWeilTest g) :
    ∫ r, gwHat g r ∂zetaZeroMeasure = WeilExplicit.archSide g - WeilExplicit.primeSide g := by
  obtain ⟨-, heq⟩ := zeta_EF_real_of_rh hRH hg
  unfold zetaZeroMeasure
  rw [integral_sum_dirac (fun ρ => ENNReal.natCast_ne_top _), ← heq]
  refine tsum_congr fun ρ => ?_
  rw [ENNReal.toReal_natCast, Complex.real_smul]
  push_cast
  ring

/-- Under RH, `Z_ζ` is a test-tempered positive real Guinand partner of zeta (kernel). -/
theorem zetaZeroMeasure_isZetaPartner_of_rh (hRH : RiemannHypothesis) :
    IsZetaPartner zetaZeroMeasure ∧ IsTestTempered zetaZeroMeasure :=
  ⟨fun _ hg _ => integral_zetaZeroMeasure_of_rh hRH hg,
    fun _ hg => zetaZeroMeasure_integrable_of_rh hRH hg⟩

/-- **Z1, both directions (kernel).** Zeta has a test-tempered positive real Guinand partner iff
RH. The zero-side positivity clause is RH itself, in a new coordinate system. -/
theorem zeta_positive_partner_iff_rh :
    (∃ μ : Measure ℝ, IsZetaPartner μ ∧ IsTestTempered μ) ↔ RiemannHypothesis :=
  ⟨fun ⟨_, h, ht⟩ => zeta_partner_implies_rh h ht,
    fun hRH => ⟨zetaZeroMeasure, zetaZeroMeasure_isZetaPartner_of_rh hRH⟩⟩

/-- **Under RH, `Z_ζ` is maximal and minimal among positive partners (kernel).** No positive
measure can be added to it keeping a positive prime side, and none can be removed from it leaving
a partner whose positive prime side has no atom at `0` and `∫_{0<|u|<1} |u|⁻¹ dP < ∞`. -/
theorem zetaZeroMeasure_extremal_of_rh (hRH : RiemannHypothesis) :
    (∀ ρ P : Measure ℝ,
      IsGuinandPartner WeilExplicit.archSide (measPr P) (zetaZeroMeasure + ρ) →
      IsTestTempered (zetaZeroMeasure + ρ) → ρ = 0) ∧
    (∀ μ ρ P : Measure ℝ, IsGuinandPartner WeilExplicit.archSide (measPr P) μ → P {0} = 0 →
      IntegrableOn (fun u : ℝ => |u|⁻¹) (Ioo (-1) 1) P → μ + ρ = zetaZeroMeasure → ρ = 0) := by
  obtain ⟨hZ, hZt⟩ := zetaZeroMeasure_isZetaPartner_of_rh hRH
  refine ⟨fun ρ P h₂ ht => zeta_partner_no_added_zeros hZ h₂ ht, ?_⟩
  intro μ ρ P h₁ h0 hint hsum
  rw [← hsum] at hZ hZt
  exact zeta_partner_no_deleted_zeros h₁ h0 hint hZ hZt

/-- **Finite resolutions, both directions (kernel).** Test-tempered positive real partners of
zeta at every resolution exist iff RH (`⟸`: `Z_ζ` serves at every resolution). -/
theorem all_windows_iff_rh :
    (∀ L : ℝ, 0 < L → ∃ μ : Measure ℝ, IsZetaWindowPartner L μ ∧ IsTestTempered μ) ↔
      RiemannHypothesis :=
  ⟨all_windows_implies_rh, fun hRH L _ =>
    ⟨zetaZeroMeasure, zetaPartner_window (zetaZeroMeasure_isZetaPartner_of_rh hRH).1 L,
      (zetaZeroMeasure_isZetaPartner_of_rh hRH).2⟩⟩

/-! ### Negative controls for Lemma M: both prime-side hypotheses are load-bearing -/

lemma integrable_fourier_of_test {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) :
    Integrable (𝓕 g) := by
  obtain ⟨C, hC0, hC⟩ := fourier_decay hg
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (continuous_fourier_of_integrable (integrable_of_test hg)).aestronglyMeasurable
    (ae_of_all _ fun ξ => ?_)
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  rw [show C * (1 + ξ ^ 2)⁻¹ = C / (1 + ξ ^ 2) by ring, le_div_iff₀ hpos]
  exact hC ξ

/-- Lebesgue measure pairs with the zero-side transform as `2π δ₀` (Fourier inversion, kernel). -/
lemma integral_gwHat_volume {g : ℝ → ℂ} (hg : WeilExplicit.IsWeilTest g) :
    ∫ r, gwHat g r = 2 * Real.pi * g 0 := by
  simp_rw [gwHat_eq_fourier]
  have h1 : ∫ r : ℝ, 𝓕 g (-(r / (2 * Real.pi))) = |2 * Real.pi| • ∫ y : ℝ, 𝓕 g (-y) :=
    Measure.integral_comp_div (fun y => 𝓕 g (-y)) (2 * Real.pi)
  have h2 : ∫ y : ℝ, 𝓕 g (-y) = ∫ y : ℝ, 𝓕 g y := integral_neg_eq_self (𝓕 g) volume
  have h3 : ∫ y : ℝ, 𝓕 g y = g 0 := by
    have hinv := (integrable_of_test hg).fourierInv_fourier_eq (integrable_fourier_of_test hg)
      (hg.1.continuous.continuousAt (x := 0))
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  rw [h1, h2, h3, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  ring

/-- **Negative controls (kernel).** (a) An atom of the smaller partner's prime side at `u = 0`
(a conductor-type term) breaks the antichain: with `E g = 2π g(0)`, the zero measure is a partner
with prime side `2π δ₀ ≥ 0`, Lebesgue measure is a partner with prime side `0`, and
`0 ≤ volume ≠ 0`. (b) A signed prime side breaks it too: with `E = 0`, `0` is a partner with
prime side `0` and Lebesgue measure a partner with prime side `-2π δ₀`. -/
theorem antichain_negative_controls :
    (IsGuinandPartner (fun g => 2 * Real.pi * g 0)
        (measPr (ENNReal.ofReal (2 * Real.pi) • Measure.dirac 0)) 0 ∧
      IsGuinandPartner (fun g => 2 * Real.pi * g 0) (measPr 0) (0 + volume) ∧
      (ENNReal.ofReal (2 * Real.pi) • Measure.dirac (0 : ℝ)) {0} ≠ 0) ∧
    (IsGuinandPartner (fun _ => 0) (fun _ => 0) 0 ∧
      IsGuinandPartner (fun _ => 0) (fun g => -(2 * Real.pi * g 0)) (0 + volume)) ∧
    Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) ((0 : Measure ℝ) + volume) ∧
    (volume : Measure ℝ) ≠ 0 := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro g hg _
    simp only [integral_zero_measure, measPr]
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hpi, Complex.real_smul]
    push_cast
    ring
  · intro g hg _
    simp only [zero_add, measPr, integral_zero_measure, sub_zero]
    exact integral_gwHat_volume hg
  · simp [Measure.smul_apply, Real.pi_pos]
  · intro g _ _
    simp
  · intro g hg _
    rw [zero_add, integral_gwHat_volume hg]
    ring
  · rw [zero_add]; exact integrable_inv_one_add_sq
  · intro h
    have := Real.volume_univ
    rw [h] at this
    simp at this

/-! ## 4. Quantitative Theorem A (Fejer form of the seat's Lemma 8.1)

The Fejer pair `(tri, sinc²)` below is copied verbatim from `CruxFQ_PoissonRigidity.lean`
(li_positivity island, KERNEL seat), so that this file is self-contained. -/

section FejerPair

open Real Complex

/-- The Fejer triangle `tri x = max 0 (1 - |x|)`. -/
def tri (x : ℝ) : ℝ := max 0 (1 - |x|)

/-- `fej ξ = sinc(π ξ)^2`, the Fourier transform of the triangle. -/
def fej (ξ : ℝ) : ℝ := Real.sinc (π * ξ) ^ 2

lemma tri_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : tri x = 1 - |x| := by
  unfold tri; exact max_eq_right (by linarith)

lemma tri_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  unfold tri; exact max_eq_left (by linarith)

lemma continuous_tri : Continuous tri := by
  unfold tri; fun_prop

/-- The real cosine integral: `∫₀¹ 2(1-x)cos(2πξx) dx = sinc(πξ)^2`. -/
lemma cos_integral (ξ : ℝ) :
    ∫ x in (0:ℝ)..1, 2 * (1 - x) * Real.cos (2 * π * ξ * x) = fej ξ := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    have : ∫ x in (0:ℝ)..1, 2 * (1 - x) = 1 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
      simp; norm_num
    rw [this]; simp [fej]
  · set c : ℝ := 2 * π * ξ with hc
    have hc0 : c ≠ 0 := by rw [hc]; exact mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hξ
    let G : ℝ → ℝ := fun x => 2 * ((1 - x) * Real.sin (c * x) / c - Real.cos (c * x) / c ^ 2)
    have hG : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt G (2 * (1 - x) * Real.cos (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun x : ℝ => c * x) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have hs : HasDerivAt (fun x : ℝ => Real.sin (c * x)) (Real.cos (c * x) * c) x := h1.sin
      have hco : HasDerivAt (fun x : ℝ => Real.cos (c * x)) (-Real.sin (c * x) * c) x := h1.cos
      have hl : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have := (((hl.mul hs).div_const c).sub (hco.div_const (c ^ 2))).const_mul 2
      have hderiv : 2 * ((-1 * Real.sin (c * x) + (1 - x) * (Real.cos (c * x) * c)) / c
          - -Real.sin (c * x) * c / c ^ 2) = 2 * (1 - x) * Real.cos (c * x) := by
        field_simp
        ring
      exact this.congr_deriv hderiv
    have hint : IntervalIntegrable (fun x : ℝ => 2 * (1 - x) * Real.cos (c * x)) volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint
    simp only [c] at this ⊢
    rw [this]
    simp only [G, mul_zero, Real.sin_zero, Real.cos_zero, mul_one, sub_self, zero_mul, zero_div,
      zero_sub]
    unfold fej
    rw [Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero hξ)]
    have hcos : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      rw [show 2 * π * ξ = 2 * (π * ξ) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    rw [hcos]
    field_simp
    ring


/-- The integrand of the Fourier transform of the triangle. -/
def triIntegrand (ξ : ℝ) (v : ℝ) : ℂ :=
  Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • ((tri v : ℝ) : ℂ)

lemma continuous_triIntegrand (ξ : ℝ) : Continuous (triIntegrand ξ) := by
  unfold triIntegrand
  have := continuous_tri
  fun_prop

/-- **The Fourier pair (kernel).** `𝓕 tri = sinc(π ·)^2`. -/
theorem fourier_tri (ξ : ℝ) : 𝓕 (fun x : ℝ => ((tri x : ℝ) : ℂ)) ξ = ((fej ξ : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  change ∫ v, triIntegrand ξ v = _
  have hsupp : ∀ v, v ∉ Ioc (-1:ℝ) 1 → triIntegrand ξ v = 0 := by
    intro v hv
    have : 1 ≤ |v| := by
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with hv | hv
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [triIntegrand, tri_of_one_le_abs this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have hint : ∀ a b : ℝ, IntervalIntegrable (triIntegrand ξ) volume a b :=
    fun a b => (continuous_triIntegrand ξ).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hint _ _) (hint _ _)]
  have h1 : ∫ x in (-1:ℝ)..0, triIntegrand ξ x = ∫ x in (0:ℝ)..1, triIntegrand ξ (-x) := by
    rw [intervalIntegral.integral_comp_neg]; norm_num
  have hint' : IntervalIntegrable (fun x => triIntegrand ξ (-x)) volume 0 1 :=
    ((continuous_triIntegrand ξ).comp continuous_neg).intervalIntegrable 0 1
  rw [h1, ← intervalIntegral.integral_add hint' (hint _ _)]
  have h2 : EqOn (fun x => triIntegrand ξ (-x) + triIntegrand ξ x)
      (fun x => ((2 * (1 - x) * Real.cos (2 * π * ξ * x) : ℝ) : ℂ)) (uIcc 0 1) := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hx2 : |-x| ≤ 1 := by rw [abs_neg]; exact hx1
    simp only [triIntegrand, tri_of_abs_le hx1, tri_of_abs_le hx2, abs_neg, abs_of_nonneg hx.1,
      smul_eq_mul]
    push_cast
    have hc := Complex.two_cos (2 * π * ξ * x)
    rw [show (-2 * (π:ℂ) * -(x:ℂ) * (ξ:ℂ) * I) = 2 * (π:ℂ) * (ξ:ℂ) * (x:ℂ) * I by ring,
      show (-2 * (π:ℂ) * (x:ℂ) * (ξ:ℂ) * I) = -(2 * (π:ℂ) * (ξ:ℂ) * (x:ℂ)) * I by ring]
    linear_combination ((x:ℂ) - 1) * hc
  rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_ofReal, cos_integral]


/-! ## Pointwise facts -/

lemma tri_nonneg (x : ℝ) : 0 ≤ tri x := le_max_left _ _

lemma tri_zero : tri 0 = 1 := by simp [tri]

lemma one_le_abs_intCast {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ |(n : ℝ)| := by
  have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
  exact_mod_cast this

lemma tri_intCast {n : ℤ} (hn : n ≠ 0) : tri n = 0 := tri_of_one_le_abs (one_le_abs_intCast hn)

lemma fej_nonneg (ξ : ℝ) : 0 ≤ fej ξ := sq_nonneg _

lemma fej_zero : fej 0 = 1 := by simp [fej]

lemma fej_intCast {n : ℤ} (hn : n ≠ 0) : fej n = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold fej
  rw [Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero hn'), mul_comm, Real.sin_int_mul_pi]
  simp

lemma exists_int_of_fej_eq_zero {ξ : ℝ} (h : fej ξ = 0) : ∃ n : ℤ, ξ = n := by
  unfold fej at h
  have hs : Real.sinc (π * ξ) = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
  by_cases hξ : ξ = 0
  · exact ⟨0, by simp [hξ]⟩
  · rw [Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero hξ), div_eq_zero_iff] at hs
    rcases hs with hs | hs
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
      refine ⟨n, ?_⟩
      have : (n : ℝ) * π = ξ * π := by rw [hn]; ring
      exact (mul_right_cancel₀ pi_ne_zero this).symm
    · exact absurd hs (mul_ne_zero pi_ne_zero hξ)

lemma continuous_fej : Continuous fej := by
  unfold fej; fun_prop


end FejerPair

lemma tri_ae_eq_indicator {ν : Measure ℝ} (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    (fun x => tri x) =ᵐ[ν] ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) := by
  have hsub : {x : ℝ | tri x ≠ ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x} ⊆ Ioo (-1) 1 \ {0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    by_cases h0 : x = 0
    · subst h0
      simp [tri_zero] at hx
    · have hxi : ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x = 0 := by
        rw [indicator_of_notMem (by simpa using h0)]
      rw [hxi] at hx
      refine ⟨?_, by simpa using h0⟩
      rw [mem_Ioo, ← abs_lt]
      by_contra hc
      push Not at hc
      exact hx (tri_of_one_le_abs hc)
  exact measure_mono_null hsub hgap

/-- **Fejer defect identity (kernel).** For a positive locally finite `ν` with no mass in
`(-1,1) \ {0}` and `sinc²`-integrable: `∫ fej dν - ∫ tri dν = ∫_{x ≠ 0} fej dν`. -/
theorem fejer_defect_identity {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hint : Integrable fej ν)
    (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    ∫ x, fej x ∂ν - ∫ x, tri x ∂ν = ∫ x in ({0} : Set ℝ)ᶜ, fej x ∂ν := by
  have htri : ∫ x, tri x ∂ν = ν.real {0} := by
    rw [integral_congr_ae (tri_ae_eq_indicator hgap)]
    rw [integral_indicator_const _ (measurableSet_singleton 0), smul_eq_mul, mul_one]
  have hsplit := integral_add_compl (measurableSet_singleton (0 : ℝ)) hint
  rw [integral_singleton, fej_zero, smul_eq_mul, mul_one] at hsplit
  rw [htri, ← hsplit]
  ring

/-- **Poisson-defect form (kernel).** The self-duality defect of `ν` on the single Fejer test,
`∫ 𝓕 tri dν - ∫ tri dν`, equals the `sinc²`-weighted mass of `ν` off `0`. -/
theorem poisson_defect_eq {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hint : Integrable fej ν)
    (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    (∫ ξ, 𝓕 (fun x : ℝ => ((tri x : ℝ) : ℂ)) ξ ∂ν) - ∫ x, ((tri x : ℝ) : ℂ) ∂ν
      = ((∫ x in ({0} : Set ℝ)ᶜ, fej x ∂ν : ℝ) : ℂ) := by
  simp_rw [fourier_tri]
  rw [integral_complex_ofReal, integral_complex_ofReal, ← fejer_defect_identity hint hgap]
  push_cast
  ring

lemma abs_sin_pi_ge {x ε : ℝ} (hxZ : ∀ n : ℤ, ε ≤ |x - n|) : 2 * ε ≤ |Real.sin (Real.pi * x)| := by
  set t := x - round x with ht
  have ht1 : |t| ≤ 1 / 2 := abs_sub_round x
  have ht2 : ε ≤ |t| := hxZ (round x)
  have hsx : Real.sin (Real.pi * x) = (-1) ^ (round x) * Real.sin (Real.pi * t) := by
    rw [← Real.sin_add_int_mul_pi]
    congr 1
    rw [ht]; ring
  have habs : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * t)| := by
    rw [hsx, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [habs]
  have hpi := Real.pi_pos
  have key : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    rcases le_total 0 t with h | h
    · have h1 : Real.pi * t ≤ Real.pi / 2 := by
        rw [abs_of_nonneg h] at ht1; nlinarith
      have := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * t) h1
      rw [abs_of_nonneg h]
      have e : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
      rw [e] at this
      exact this.trans (le_abs_self _)
    · have h1 : Real.pi * (-t) ≤ Real.pi / 2 := by
        rw [abs_of_nonpos h] at ht1; nlinarith
      have := Real.mul_le_sin (by nlinarith : 0 ≤ Real.pi * (-t)) h1
      rw [abs_of_nonpos h]
      have e : 2 / Real.pi * (Real.pi * (-t)) = 2 * (-t) := by field_simp
      rw [e, show Real.pi * (-t) = -(Real.pi * t) by ring, Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  linarith

/-- `sinc²` is bounded below away from the integers on a window. -/
lemma fej_lower {x R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hxR : |x| ≤ R)
    (hxZ : ∀ n : ℤ, ε ≤ |x - n|) : 4 * ε ^ 2 / (Real.pi ^ 2 * R ^ 2) ≤ fej x := by
  have hx0 : x ≠ 0 := by
    intro h
    have := hxZ 0
    simp [h] at this
    linarith
  have hs := abs_sin_pi_ge hxZ
  unfold fej
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx0), div_pow]
  have hpi := Real.pi_pos
  have hsq : (2 * ε) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
    have h2 : 0 ≤ 2 * ε := by positivity
    calc (2 * ε) ^ 2 ≤ |Real.sin (Real.pi * x)| ^ 2 := pow_le_pow_left₀ h2 hs 2
      _ = Real.sin (Real.pi * x) ^ 2 := sq_abs _
  have hden : (Real.pi * x) ^ 2 ≤ Real.pi ^ 2 * R ^ 2 := by
    rw [mul_pow]
    have : x ^ 2 ≤ R ^ 2 := by
      have := sq_abs x
      nlinarith [abs_nonneg x]
    nlinarith [sq_nonneg Real.pi]
  have hdpos : 0 < (Real.pi * x) ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hdpos]
  nlinarith [sq_nonneg ε]

/-- **Quantitative Theorem A (kernel).** The Poisson self-duality defect on the single Fejer test
controls the mass of `ν` away from the integers: for every window `|x| ≤ R` and distance `ε`,
`(4ε²/(π²R²)) · ν{|x| ≤ R, dist(x, ℤ) ≥ ε} ≤ ∫ fej dν - ∫ tri dν`. Exact self-duality on this one
test (defect `0`) puts `ν` on `ℤ`. -/
theorem offInteger_mass_le {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hint : Integrable fej ν)
    (hgap : ν (Ioo (-1) 1 \ {0}) = 0) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ENNReal.ofReal (4 * ε ^ 2 / (Real.pi ^ 2 * R ^ 2)) *
        ν {x : ℝ | |x| ≤ R ∧ ∀ n : ℤ, ε ≤ |x - n|}
      ≤ ENNReal.ofReal (∫ x, fej x ∂ν - ∫ x, tri x ∂ν) := by
  set S := {x : ℝ | |x| ≤ R ∧ ∀ n : ℤ, ε ≤ |x - n|}
  set c := 4 * ε ^ 2 / (Real.pi ^ 2 * R ^ 2)
  have hS0 : S ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx h0
    have := hx.2 0
    simp only [mem_singleton_iff] at h0
    simp [h0] at this
    linarith
  rw [fejer_defect_identity hint hgap]
  rw [ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (ae_of_all _ fun x => fej_nonneg x)]
  calc ENNReal.ofReal c * ν S = ∫⁻ _ in S, ENNReal.ofReal c ∂ν := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (fej x) ∂ν := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' ?_]
        · exact ae_of_all _ fun x hx => ENNReal.ofReal_le_ofReal (fej_lower hR hε hx.1 hx.2)
        · -- measurability of S
          have h1 : MeasurableSet {x : ℝ | |x| ≤ R} := measurableSet_le (by fun_prop) (by fun_prop)
          have h2 : MeasurableSet {x : ℝ | ∀ n : ℤ, ε ≤ |x - n|} := by
            have : {x : ℝ | ∀ n : ℤ, ε ≤ |x - n|} = ⋂ n : ℤ, {x : ℝ | ε ≤ |x - n|} := by
              ext x; simp
            rw [this]
            exact MeasurableSet.iInter fun n => measurableSet_le (by fun_prop) (by fun_prop)
          exact h1.inter h2
    _ ≤ ∫⁻ x in ({0} : Set ℝ)ᶜ, ENNReal.ofReal (fej x) ∂ν := lintegral_mono_set hS0

/-! ## 5. Theorem E: unimodular power sums (Bohr means) and the Lee-Yang/Euler divide -/

lemma cesaro_geom {q : ℂ} (hq : ‖q‖ = 1) (hq1 : q ≠ 1) :
    Tendsto (fun M : ℕ => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, q ^ m) atTop (𝓝 0) := by
  have hq0 : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq1)
  have hbd : ∀ M : ℕ, ‖∑ m ∈ Finset.range M, q ^ m‖ ≤ 2 / ‖q - 1‖ := by
    intro M
    rw [geom_sum_eq hq1, norm_div]
    have : ‖q ^ M - 1‖ ≤ 2 := by
      calc ‖q ^ M - 1‖ ≤ ‖q ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hq, one_pow, norm_one]; norm_num
    exact div_le_div_of_nonneg_right this (norm_nonneg _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (g := fun M : ℕ => (2 / ‖q - 1‖) * (M : ℝ)⁻¹)
    (fun M => norm_nonneg _) (fun M => ?_) ?_
  · rw [norm_mul, norm_inv, Complex.norm_natCast, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd M) (inv_nonneg.mpr (Nat.cast_nonneg M))
  · have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 / ‖q - 1‖)
    simpa using this

lemma cesaro_one :
    Tendsto (fun M : ℕ => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, (1 : ℂ) ^ m) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  field_simp

/-- **Bohr mean (kernel).** For finitely many distinct unimodular frequencies `ζ i`, the Cesaro
mean of `s_m · conj(ζ j)^m`, `s_m = Σ a_i ζ_i^m`, converges to the coefficient `a j`. -/
theorem bohr_mean {ι : Type*} [DecidableEq ι] {S : Finset ι} {ζ : ι → ℂ}
    (hζ : ∀ i ∈ S, ‖ζ i‖ = 1) (hinj : Set.InjOn ζ S) (a : ι → ℂ) {j : ι} (hj : j ∈ S) :
    Tendsto (fun M : ℕ => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
      (∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m) atTop (𝓝 (a j)) := by
  have hsplit : ∀ M : ℕ, (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
      (∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m
      = ∑ i ∈ S, a i * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, (ζ i * starRingEnd ℂ (ζ j)) ^ m) := by
    intro M
    simp_rw [Finset.sum_mul, mul_pow]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hlim : ∀ i ∈ S, Tendsto (fun M : ℕ => a i * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
      (ζ i * starRingEnd ℂ (ζ j)) ^ m)) atTop (𝓝 (if i = j then a i else 0)) := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have h1 : ζ i * starRingEnd ℂ (ζ i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ i hi]
        norm_num
      rw [h1]
      simpa using cesaro_one.const_mul (a i)
    · rw [if_neg hij]
      have hq : ‖ζ i * starRingEnd ℂ (ζ j)‖ = 1 := by
        rw [norm_mul, Complex.norm_conj, hζ i hi, hζ j hj, one_mul]
      have hq1 : ζ i * starRingEnd ℂ (ζ j) ≠ 1 := by
        intro h
        apply hij
        apply hinj hi hj
        have hjj : ζ j * starRingEnd ℂ (ζ j) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ j hj]
          norm_num
        calc ζ i = ζ i * (ζ j * starRingEnd ℂ (ζ j)) := by rw [hjj, mul_one]
          _ = (ζ i * starRingEnd ℂ (ζ j)) * ζ j := by ring
          _ = ζ j := by rw [h, one_mul]
      simpa using (cesaro_geom hq hq1).const_mul (a i)
  have hsum := tendsto_finsetSum S hlim
  rw [Finset.sum_ite_eq' S j (fun i => a i), if_pos hj] at hsum
  exact hsum.congr fun M => (hsplit M).symm

/-- **Almost-periodic rigidity (kernel).** A finite unimodular power sum with distinct frequencies
that tends to `0` has all coefficients `0`. -/
theorem unimodular_powerSum_coeff_eq_zero {ι : Type*} [DecidableEq ι] {S : Finset ι} {ζ : ι → ℂ}
    (hζ : ∀ i ∈ S, ‖ζ i‖ = 1) (hinj : Set.InjOn ζ S) (a : ι → ℂ)
    (h : Tendsto (fun m : ℕ => ∑ i ∈ S, a i * ζ i ^ m) atTop (𝓝 0)) : ∀ i ∈ S, a i = 0 := by
  intro j hj
  have h1 := bohr_mean hζ hinj a hj
  have h2 : Tendsto (fun m : ℕ => (∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ m : ℕ, ‖(starRingEnd ℂ (ζ j)) ^ m‖ = 1 := by
      intro m; rw [norm_pow, Complex.norm_conj, hζ j hj, one_pow]
    simp_rw [norm_mul, hb, mul_one]
    exact tendsto_zero_iff_norm_tendsto_zero.mp h
  have h3 := h2.cesaro_smul
  have h4 : Tendsto (fun M : ℕ => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
      (∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m) atTop (𝓝 0) := by
    refine h3.congr fun M => ?_
    rw [Complex.real_smul]
    push_cast
    ring
  exact tendsto_nhds_unique h1 h4

/-- **Quantitative non-decay (kernel).** A finite unimodular power sum with distinct frequencies
exceeds, infinitely often, every level below the modulus of any of its coefficients:
`limsup_m |Σ a_i ζ_i^m| ≥ max_i |a_i|`. -/
theorem unimodular_powerSum_frequently_large {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {ζ : ι → ℂ} (hζ : ∀ i ∈ S, ‖ζ i‖ = 1) (hinj : Set.InjOn ζ S) (a : ι → ℂ) {j : ι}
    (hj : j ∈ S) {c : ℝ} (hc : c < ‖a j‖) :
    ∃ᶠ m in atTop, c < ‖∑ i ∈ S, a i * ζ i ^ m‖ := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp hcon
  have hnt : ∀ m : ℕ, ‖(∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m‖
      = ‖∑ i ∈ S, a i * ζ i ^ m‖ := by
    intro m
    rw [norm_mul, norm_pow, Complex.norm_conj, hζ j hj, one_pow, mul_one]
  have hc0 : 0 ≤ c := by
    have := hm0 m0 le_rfl
    push Not at this
    exact (norm_nonneg _).trans this
  set K : ℝ := ∑ m ∈ Finset.range m0, ‖∑ i ∈ S, a i * ζ i ^ m‖ with hK
  have hbound : ∀ M : ℕ, 0 < M → ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
      (∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m‖ ≤ c + K / M := by
    intro M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hterm : ∀ m : ℕ, ‖∑ i ∈ S, a i * ζ i ^ m‖
        ≤ c + (if m < m0 then ‖∑ i ∈ S, a i * ζ i ^ m‖ else 0) := by
      intro m
      split_ifs with h
      · linarith
      · have := hm0 m (by omega)
        push Not at this
        linarith
    have hsum : ∑ m ∈ Finset.range M, ‖∑ i ∈ S, a i * ζ i ^ m‖ ≤ M * c + K := by
      calc ∑ m ∈ Finset.range M, ‖∑ i ∈ S, a i * ζ i ^ m‖
          ≤ ∑ m ∈ Finset.range M,
              (c + (if m < m0 then ‖∑ i ∈ S, a i * ζ i ^ m‖ else 0)) :=
            Finset.sum_le_sum fun m _ => hterm m
        _ = M * c + ∑ m ∈ Finset.range M,
              (if m < m0 then ‖∑ i ∈ S, a i * ζ i ^ m‖ else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ M * c + K := by
            gcongr
            rw [← Finset.sum_filter]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => norm_nonneg _)
            intro m hm
            simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
            exact hm.2
    calc ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, (∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m‖
        = (M : ℝ)⁻¹ * ‖∑ m ∈ Finset.range M,
            (∑ i ∈ S, a i * ζ i ^ m) * (starRingEnd ℂ (ζ j)) ^ m‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, ‖∑ i ∈ S, a i * ζ i ^ m‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hMpos.le)
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun m _ => hnt m
      _ ≤ (M : ℝ)⁻¹ * (M * c + K) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hMpos.le)
      _ = c + K / M := by field_simp
  have hlim := (bohr_mean hζ hinj a hj).norm
  have hlim2 : Tendsto (fun M : ℕ => c + K / (M : ℝ)) atTop (𝓝 c) := by
    have := (tendsto_const_nhds (x := K)).div_atTop tendsto_natCast_atTop_atTop
    simpa using this.const_add c
  have hle : ‖a j‖ ≤ c := by
    refine le_of_tendsto_of_tendsto hlim hlim2 ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact hbound M (by omega)
  linarith

/-- **Corollary E.2 (kernel): zeta's local Bragg sequence is not a unimodular power sum.**
For `p > 1` there is no finite family of distinct unimodular numbers `ζ i` and complex weights
`a i` (e.g. signed integer multiplicities: zeros minus poles) with
`Σ a_i ζ_i^m = -p^{-m/2}` for every `m ≥ 1`. (Zeta's Guinand-Weil Bragg coefficient at
`m log p` is `-(log p) p^{-m/2}`; a Kurasov-Sarnak quasicrystal with Euler support has
coefficient `(log p) · s_m` with `s_m` a unimodular power sum, Theorem E(iii).) -/
theorem zeta_bragg_not_unimodular {p : ℝ} (hp : 1 < p) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (ζ : ι → ℂ) (hζ : ∀ i ∈ S, ‖ζ i‖ = 1) (hinj : Set.InjOn ζ S) (a : ι → ℂ) :
    ¬ ∀ m : ℕ, ∑ i ∈ S, a i * ζ i ^ (m + 1) = -(((Real.sqrt p)⁻¹ ^ (m + 1) : ℝ) : ℂ) := by
  intro h
  have hsq : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hp
  have hq0 : 0 ≤ (Real.sqrt p)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg p)
  have hq1 : (Real.sqrt p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsq
  set b : ι → ℂ := fun i => a i * ζ i
  have hb : ∀ m : ℕ, ∑ i ∈ S, b i * ζ i ^ m = -(((Real.sqrt p)⁻¹ ^ (m + 1) : ℝ) : ℂ) := by
    intro m
    rw [← h m]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [b]
    ring
  have htend : Tendsto (fun m : ℕ => ∑ i ∈ S, b i * ζ i ^ m) atTop (𝓝 0) := by
    simp_rw [hb]
    have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
    have h1 := (Complex.continuous_ofReal.tendsto 0).comp h0
    simpa using h1.neg
  have hzero := unimodular_powerSum_coeff_eq_zero hζ hinj b htend
  have h0 := hb 0
  rw [Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_mul])] at h0
  have hsp : 0 < Real.sqrt p := by linarith
  have hpos : 0 < (Real.sqrt p)⁻¹ ^ (0 + 1) := by positivity
  have h0' := congrArg Complex.re h0
  simp only [Complex.zero_re, Complex.neg_re, Complex.ofReal_re] at h0'
  linarith

/-- **Theorem E(iii) non-decay (kernel).** If a nonzero polynomial has all roots unimodular and at
least one root, the inverse-root power sums `s_m = Σ_{roots w} w^{-m}` do not tend to `0`. -/
theorem leeYang_powerSum_not_tendsto_zero {P : Polynomial ℂ} (hroots : ∀ w ∈ P.roots, ‖w‖ = 1)
    (hne : P.roots ≠ 0) :
    ¬ Tendsto (fun m : ℕ => (P.roots.map (fun w => w⁻¹ ^ m)).sum) atTop (𝓝 0) := by
  intro h
  classical
  have hrepr : ∀ m : ℕ, (P.roots.map (fun w => w⁻¹ ^ m)).sum
      = ∑ w ∈ P.roots.toFinset, ((P.roots.count w : ℕ) : ℂ) * w⁻¹ ^ m := by
    intro m
    rw [Finset.sum_multiset_map_count]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [nsmul_eq_mul]
  simp_rw [hrepr] at h
  have hζ : ∀ w ∈ P.roots.toFinset, ‖w⁻¹‖ = 1 := by
    intro w hw
    rw [norm_inv, hroots w (Multiset.mem_toFinset.mp hw), inv_one]
  have hinj : Set.InjOn (fun w : ℂ => w⁻¹) (P.roots.toFinset : Set ℂ) :=
    fun x _ y _ hxy => inv_injective hxy
  have hz := unimodular_powerSum_coeff_eq_zero (ζ := fun w : ℂ => w⁻¹) hζ hinj
    (fun w => ((P.roots.count w : ℕ) : ℂ)) h
  obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hne
  have hc := hz w (Multiset.mem_toFinset.mpr hw)
  have hpos : 0 < P.roots.count w := Multiset.count_pos.mpr hw
  simp only [Nat.cast_eq_zero] at hc
  omega

/-- **Theorem E(iii), quantitative (kernel).** For a polynomial whose roots are all unimodular,
the inverse-root power sums exceed every `c < mult(w)` infinitely often, for each root `w`; in
particular `|s_m| > 1 - ε` for infinitely many `m`. Zeta's local sequence `-p^{-m/2}` tends to `0`. -/
theorem leeYang_powerSum_frequently_large {P : Polynomial ℂ} (hroots : ∀ w ∈ P.roots, ‖w‖ = 1)
    {w : ℂ} (hw : w ∈ P.roots) {c : ℝ} (hc : c < P.roots.count w) :
    ∃ᶠ m in atTop, c < ‖(P.roots.map (fun w => w⁻¹ ^ m)).sum‖ := by
  classical
  have hrepr : ∀ m : ℕ, (P.roots.map (fun w => w⁻¹ ^ m)).sum
      = ∑ v ∈ P.roots.toFinset, ((P.roots.count v : ℕ) : ℂ) * v⁻¹ ^ m := by
    intro m
    rw [Finset.sum_multiset_map_count]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [nsmul_eq_mul]
  simp_rw [hrepr]
  have hζ : ∀ v ∈ P.roots.toFinset, ‖v⁻¹‖ = 1 := by
    intro v hv
    rw [norm_inv, hroots v (Multiset.mem_toFinset.mp hv), inv_one]
  have hinj : Set.InjOn (fun v : ℂ => v⁻¹) (P.roots.toFinset : Set ℂ) :=
    fun x _ y _ hxy => inv_injective hxy
  refine unimodular_powerSum_frequently_large (ζ := fun v : ℂ => v⁻¹) hζ hinj
    (fun v => ((P.roots.count v : ℕ) : ℂ)) (Multiset.mem_toFinset.mpr hw) ?_
  rw [Complex.norm_natCast]
  exact hc

/-- **Kurasov-Sarnak mechanism (kernel, two frequencies).** If `P` has no zeros in
`D² ∪ E²` (Lee-Yang) and `ℓ₁, ℓ₂ > 0`, every zero of `x ↦ P(e^{iℓ₁x}, e^{iℓ₂x})` is real. -/
theorem ks_real_zeros {P : ℂ → ℂ → ℂ}
    (hLY : ∀ z₁ z₂ : ℂ, ((‖z₁‖ < 1 ∧ ‖z₂‖ < 1) ∨ (1 < ‖z₁‖ ∧ 1 < ‖z₂‖)) → P z₁ z₂ ≠ 0)
    {ℓ₁ ℓ₂ : ℝ} (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) {x : ℂ}
    (hx : P (Complex.exp (Complex.I * ℓ₁ * x)) (Complex.exp (Complex.I * ℓ₂ * x)) = 0) :
    x.im = 0 := by
  have hn : ∀ ℓ : ℝ, ‖Complex.exp (Complex.I * ℓ * x)‖ = Real.exp (-(ℓ * x.im)) := by
    intro ℓ
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  rcases lt_trichotomy x.im 0 with hlt | heq | hgt
  · exfalso
    refine hLY _ _ (Or.inr ⟨?_, ?_⟩) hx
    · rw [hn]; exact Real.one_lt_exp_iff.mpr (by nlinarith)
    · rw [hn]; exact Real.one_lt_exp_iff.mpr (by nlinarith)
  · exact heq
  · exfalso
    refine hLY _ _ (Or.inl ⟨?_, ?_⟩) hx
    · rw [hn]; exact Real.exp_lt_one_iff.mpr (by nlinarith)
    · rw [hn]; exact Real.exp_lt_one_iff.mpr (by nlinarith)

/-- The explicit two-prime Lee-Yang polynomial of the seat's N2 example,
`det(I + diag(z₁,z₂)U)` for the rotation `U` by `π/3`. -/
def PLY (z₁ z₂ : ℂ) : ℂ := 1 + z₁ / 2 + z₂ / 2 + z₁ * z₂

/-- `PLY` is Lee-Yang: no zeros in `D² ∪ E²` (kernel). -/
theorem PLY_leeYang :
    ∀ z₁ z₂ : ℂ, ((‖z₁‖ < 1 ∧ ‖z₂‖ < 1) ∨ (1 < ‖z₁‖ ∧ 1 < ‖z₂‖)) → PLY z₁ z₂ ≠ 0 := by
  intro z₁ z₂ hz h
  have e : z₂ * (1 + 2 * z₁) = -(2 + z₁) := by
    unfold PLY at h
    linear_combination 2 * h
  have en := congrArg Complex.normSq e
  rw [Complex.normSq_mul, Complex.normSq_neg] at en
  have hA : Complex.normSq (2 + z₁) = (2 + z₁.re) ^ 2 + z₁.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hB : Complex.normSq (1 + 2 * z₁) = (1 + 2 * z₁.re) ^ 2 + (2 * z₁.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have h1 : ‖z₁‖ ^ 2 = z₁.re ^ 2 + z₁.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h2 : ‖z₂‖ ^ 2 = Complex.normSq z₂ := (Complex.normSq_eq_norm_sq z₂).symm
  rw [hA, hB] at en
  have hBnn : 0 ≤ (1 + 2 * z₁.re) ^ 2 + (2 * z₁.im) ^ 2 := by positivity
  rcases hz with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha2 : ‖z₁‖ ^ 2 < 1 := by nlinarith [norm_nonneg z₁]
    have hb2 : Complex.normSq z₂ < 1 := by rw [← h2]; nlinarith [norm_nonneg z₂]
    have hn2 : 0 ≤ Complex.normSq z₂ := Complex.normSq_nonneg z₂
    nlinarith
  · have ha2 : 1 < ‖z₁‖ ^ 2 := by nlinarith [norm_nonneg z₁]
    have hb2 : 1 < Complex.normSq z₂ := by rw [← h2]; nlinarith [norm_nonneg z₂]
    nlinarith

/-- `PLY` is not a product of one-variable factors (kernel): `PLY = PLY(·,0)·PLY(0,·) + (3/4) z₁z₂`,
so its mixed log-coefficient `c₁₁ = 3/4 ≠ 0` (the Bragg peak at `log 6` in the KS formula). -/
theorem PLY_not_product : ¬ ∃ F G : ℂ → ℂ, ∀ z₁ z₂, PLY z₁ z₂ = F z₁ * G z₂ := by
  rintro ⟨F, G, h⟩
  have e1 := h 1 1
  have e2 := h 1 0
  have e3 := h 0 1
  have e4 := h 0 0
  simp only [PLY] at e1 e2 e3 e4
  norm_num at e1 e2 e3 e4
  -- PLY 1 1 * PLY 0 0 = PLY 1 0 * PLY 0 1
  have : F 1 * G 1 * (F 0 * G 0) = F 1 * G 0 * (F 0 * G 1) := by ring
  rw [← e1, ← e2, ← e3, ← e4] at this
  norm_num at this

lemma PLY_decomp (z₁ z₂ : ℂ) : PLY z₁ z₂ = PLY z₁ 0 * PLY 0 z₂ + (3 / 4) * (z₁ * z₂) := by
  unfold PLY; ring

/-- All zeros of `x ↦ PLY(2^{ix}, 3^{ix})` are real (kernel). -/
theorem PLY_real_zeros {x : ℂ}
    (hx : PLY (Complex.exp (Complex.I * (Real.log 2 : ℝ) * x))
      (Complex.exp (Complex.I * (Real.log 3 : ℝ) * x)) = 0) : x.im = 0 :=
  ks_real_zeros PLY_leeYang (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num)) hx

/-! ## 6. The local dictionary (Corollary E.3) -/

/-- Local zeros of `1 - a p^{-s}` lie on `Re s = log‖a‖ / log p` (kernel). -/
theorem local_zero_re {p : ℝ} (hp : 1 < p) {a : ℂ} (ha : a ≠ 0) {s : ℂ}
    (hs : a * (p : ℂ) ^ (-s) = 1) : s.re = Real.log ‖a‖ / Real.log p := by
  have hp0 : 0 < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hn := congrArg norm hs
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp0, norm_one, Complex.neg_re] at hn
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hl := congrArg Real.log hn
  rw [Real.log_mul ha0.ne' (Real.rpow_pos_of_pos hp0 _).ne', Real.log_rpow hp0, Real.log_one] at hl
  field_simp
  linarith

/-- Every nonzero local root has a local zero (kernel). -/
theorem local_zero_exists {p : ℝ} (hp : 1 < p) {a : ℂ} (ha : a ≠ 0) :
    ∃ s : ℂ, a * (p : ℂ) ^ (-s) = 1 ∧ s.re = Real.log ‖a‖ / Real.log p := by
  have hp0 : 0 < p := by linarith
  have hlogp : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  have hlogpC : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hlogp
  refine ⟨Complex.log a / (Real.log p : ℂ), ?_, ?_⟩
  · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp0.ne'), ← Complex.ofReal_log hp0.le]
    have : (Real.log p : ℂ) * -(Complex.log a / (Real.log p : ℂ)) = -Complex.log a := by
      field_simp
    rw [this, Complex.exp_neg, Complex.exp_log ha]
    field_simp
  · rw [Complex.div_ofReal_re, Complex.log_re]

/-- `log‖a‖/log p = 1/2 ↔ ‖a‖ = √p` (kernel). -/
lemma half_iff_norm_eq_sqrt {p : ℝ} (hp : 1 < p) {a : ℂ} (ha : a ≠ 0) :
    Real.log ‖a‖ / Real.log p = 1 / 2 ↔ ‖a‖ = Real.sqrt p := by
  have hp0 : 0 < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  rw [div_eq_iff hlogp.ne']
  constructor
  · intro h
    have : Real.log ‖a‖ = Real.log (Real.sqrt p) := by
      rw [Real.log_sqrt hp0.le]; linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha0) (Set.mem_Ioi.mpr hs0) this
  · intro h
    rw [h, Real.log_sqrt hp0.le]
    ring

/-- **Corollary E.3, the local dictionary (kernel).** For a local factor `∏ (1 - a_j T)`, `T = p^{-s}`,
with all `a_j ≠ 0`: all local zeros lie on `Re s = 1/2` iff every `|a_j| = √p`, i.e. iff the rescaled
factor `∏ (1 - a_j p^{-1/2} z)` has all its roots `z = √p/a_j` on the unit circle (one-variable
Lee-Yang = local Ramanujan). -/
theorem local_dictionary {p : ℝ} (hp : 1 < p) (A : Multiset ℂ) (hA : ∀ a ∈ A, a ≠ 0) :
    (∀ s : ℂ, (A.map (fun a => 1 - a * (p : ℂ) ^ (-s))).prod = 0 → s.re = 1 / 2) ↔
      ∀ a ∈ A, ‖a‖ = Real.sqrt p := by
  constructor
  · intro h a ha
    obtain ⟨s, hs, hre⟩ := local_zero_exists hp (hA a ha)
    have hprod : (A.map (fun a => 1 - a * (p : ℂ) ^ (-s))).prod = 0 := by
      rw [Multiset.prod_eq_zero_iff]
      exact Multiset.mem_map.mpr ⟨a, ha, by rw [hs, sub_self]⟩
    have := h s hprod
    rw [hre] at this
    exact (half_iff_norm_eq_sqrt hp (hA a ha)).mp this
  · intro h s hs
    rw [Multiset.prod_eq_zero_iff] at hs
    obtain ⟨a, ha, has⟩ := Multiset.mem_map.mp hs
    have h1 : a * (p : ℂ) ^ (-s) = 1 := by linear_combination -has
    rw [local_zero_re hp (hA a ha) h1]
    exact (half_iff_norm_eq_sqrt hp (hA a ha)).mpr (h a ha)

/-- The quadratic family `z² + c z + 1` (the rescaled factor of `1 + c√p T + p T²`) has a root in
the open unit disc as soon as `c > 2` (Lee-Yang failure; kernel). -/
theorem quadratic_leeYang_fails {c : ℝ} (hc : 2 < c) :
    ∃ z : ℝ, -1 < z ∧ z < 0 ∧ z ^ 2 + c * z + 1 = 0 := by
  have hd : 0 < c ^ 2 - 4 := by nlinarith
  set r := Real.sqrt (c ^ 2 - 4) with hr
  have hr2 : r ^ 2 = c ^ 2 - 4 := Real.sq_sqrt hd.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  refine ⟨(-c + r) / 2, ?_, ?_, ?_⟩
  · -- r > c - 2
    have : c - 2 < r := by
      by_contra hcon
      push Not at hcon
      nlinarith
    linarith
  · have : r < c := by nlinarith
    linarith
  · nlinarith

/-- Zoo instances (kernel): the golden-fake numerator `1 + 5T + 5T²` (`c = √5`) and round 1's
`W1(29,11)` factor `1 + 11T + 29T²` (`c = 11/√29`) both have `c > 2`, hence a local root inside the
unit disc and local zeros off `Re s = 1/2`. -/
theorem zoo_local_factors_not_leeYang :
    2 < Real.sqrt 5 ∧ 2 < 11 / Real.sqrt 29 := by
  constructor
  · rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · have h29 : 0 < Real.sqrt 29 := Real.sqrt_pos.mpr (by norm_num)
    rw [lt_div_iff₀ h29]
    have hs : Real.sqrt 29 ^ 2 = 29 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 29]

/-! ## 7. Capstone -/

/-- **Capstone (kernel).** The rigidity seat's buildable core in one statement:
(1) Lemma M: positive Guinand partners with a common archimedean/pole functional cannot be nested
    (`μ₁ ≤ μ₂` forces `μ₁ = μ₂`), and their (locally finite) prime sides then coincide;
(2) circularity certificate Z1, both directions: zeta has a (test-)tempered positive real Guinand
    partner iff RH (the zero-side positivity clause IS RH; it is not a route to it);
(3) quantitative Theorem A: the self-duality defect on the single Fejer test bounds the mass off
    the integers;
(4) Corollary E.2: zeta's local Bragg sequence `-p^{-m/2}` is not a unimodular power sum;
(5) Corollary E.3: local zeros on `Re s = 1/2` iff every local root has modulus `√p`. -/
theorem rigidity_capstone :
    (∀ (E : (ℝ → ℂ) → ℂ) (μ₁ μ₂ P₁ P₂ : Measure ℝ) [IsLocallyFiniteMeasure P₁]
        [IsLocallyFiniteMeasure P₂],
      IsGuinandPartner E (measPr P₁) μ₁ → IsGuinandPartner E (measPr P₂) μ₂ → μ₁ ≤ μ₂ →
      Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ₂ → P₁ {0} = 0 →
      IntegrableOn (fun u : ℝ => |u|⁻¹) (Ioo (-1) 1) P₁ → μ₁ = μ₂ ∧ P₁ = P₂) ∧
    ((∃ μ : Measure ℝ, IsZetaPartner μ ∧ IsTestTempered μ) ↔ RiemannHypothesis) ∧
    (∀ (ν : Measure ℝ) [IsLocallyFiniteMeasure ν], Integrable fej ν →
      ν (Ioo (-1) 1 \ {0}) = 0 → ∀ R ε : ℝ, 0 < R → 0 < ε →
      ENNReal.ofReal (4 * ε ^ 2 / (Real.pi ^ 2 * R ^ 2)) *
          ν {x : ℝ | |x| ≤ R ∧ ∀ n : ℤ, ε ≤ |x - n|}
        ≤ ENNReal.ofReal (∫ x, fej x ∂ν - ∫ x, tri x ∂ν)) ∧
    (∀ p : ℝ, 1 < p → ∀ (S : Finset ℂ) (a : ℂ → ℂ), (∀ w ∈ S, ‖w‖ = 1) →
      ¬ ∀ m : ℕ, ∑ w ∈ S, a w * w ^ (m + 1) = -(((Real.sqrt p)⁻¹ ^ (m + 1) : ℝ) : ℂ)) ∧
    (∀ p : ℝ, 1 < p → ∀ A : Multiset ℂ, (∀ a ∈ A, a ≠ 0) →
      ((∀ s : ℂ, (A.map (fun a => 1 - a * (p : ℂ) ^ (-s))).prod = 0 → s.re = 1 / 2) ↔
        ∀ a ∈ A, ‖a‖ = Real.sqrt p)) :=
  ⟨fun _ _ _ _ _ _ _ h₁ h₂ hle ht h0 hi => guinand_antichain_le h₁ h₂ hle ht h0 hi,
    zeta_positive_partner_iff_rh,
    fun _ _ hint hgap _ _ hR hε => offInteger_mass_le hint hgap hR hε,
    fun _ hp S a hS => zeta_bragg_not_unimodular hp S id hS (Set.injOn_id _) a,
    fun _ hp A hA => local_dictionary hp A hA⟩

end CruxFQRigidity

#print axioms CruxFQRigidity.rigidity_capstone
#print axioms CruxFQRigidity.guinand_antichain
#print axioms CruxFQRigidity.guinand_antichain_measure
#print axioms CruxFQRigidity.guinand_antichain_le
#print axioms CruxFQRigidity.antichain_core
#print axioms CruxFQRigidity.zeta_partner_no_added_zeros
#print axioms CruxFQRigidity.zeta_partner_no_deleted_zeros
#print axioms CruxFQRigidity.zeta_partner_implies_rh
#print axioms CruxFQRigidity.zeta_positive_partner_iff_rh
#print axioms CruxFQRigidity.zetaZeroMeasure_extremal_of_rh
#print axioms CruxFQRigidity.zeta_partners_antichain
#print axioms CruxFQRigidity.antichain_negative_controls
#print axioms CruxFQRigidity.integral_gwHat_volume
#print axioms CruxFQRigidity.measure_eq_of_integral_test_eq
#print axioms CruxFQRigidity.fourier_decay
#print axioms CruxFQRigidity.gwHat_testFn
#print axioms CruxFQRigidity.window_partner_weil_positivity
#print axioms CruxFQRigidity.all_windows_implies_rh
#print axioms CruxFQRigidity.all_windows_iff_rh
#print axioms CruxFQRigidity.offInteger_mass_le
#print axioms CruxFQRigidity.poisson_defect_eq
#print axioms CruxFQRigidity.fejer_defect_identity
#print axioms CruxFQRigidity.fourier_tri
#print axioms CruxFQRigidity.bohr_mean
#print axioms CruxFQRigidity.unimodular_powerSum_coeff_eq_zero
#print axioms CruxFQRigidity.zeta_bragg_not_unimodular
#print axioms CruxFQRigidity.leeYang_powerSum_not_tendsto_zero
#print axioms CruxFQRigidity.unimodular_powerSum_frequently_large
#print axioms CruxFQRigidity.leeYang_powerSum_frequently_large
#print axioms CruxFQRigidity.ks_real_zeros
#print axioms CruxFQRigidity.PLY_leeYang
#print axioms CruxFQRigidity.PLY_real_zeros
#print axioms CruxFQRigidity.PLY_not_product
#print axioms CruxFQRigidity.local_zero_re
#print axioms CruxFQRigidity.local_zero_exists
#print axioms CruxFQRigidity.local_dictionary
#print axioms CruxFQRigidity.quadratic_leeYang_fails
#print axioms CruxFQRigidity.zoo_local_factors_not_leeYang
