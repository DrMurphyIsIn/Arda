/-
CruxFQ_PoissonRigidity.lean -- crux-fq workflow, KERNEL seat.
Round 1's Theorem A in crystalline-measure (Fourier-quasicrystal) form, complete in the kernel,
plus the fooling family showing that this rigidity is blind to zeros.

conjecture1_proved = False. Nothing here bears on where the zeros of `riemannZeta` lie.

Checked by: `cd telperion/examples/li_positivity/lean && lake env lean Crux/CruxFQ_PoissonRigidity.lean`
(Lean v4.34.0-rc1, Mathlib de5ce8a9). No `sorry`, `admit`, `native_decide`, new `axiom`, or `opaque`.
Every `#print axioms` line at the end reports exactly `[propext, Classical.choice, Quot.sound]`.

THE PREDICATE. `IsPoissonPair ν β` : for every continuous compactly supported `f : ℝ → ℂ` whose
Fourier transform is `ν`-integrable, `∫ 𝓕 f dν = ∫ f dν + β (f 0 - ∫ f)`; i.e. `ν̂ = ν + β(δ₀ - Leb)`
tested on `C_c` functions with integrable transform. `β = 0` is exact self-duality (a self-dual
crystalline measure). A nonzero `β` is the footprint of a pole normalization (the Lebesgue part).
CAVEAT (not formalized): for a translation-bounded positive measure, the Schwartz-tested
distributional identity implies this `C_c`-tested one by a standard approximation; we assume the
`C_c` form directly.

WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
 1. The Fejer Fourier pair `𝓕(max 0 (1-|x|)) = sinc(π·)²` and its translates (`fourier_tri`,
    `fourier_tri_sub`). This replaces round 1's unproved Cohn-Elkies pair; the Fejer pair is
    enough, and it is blind to the pole term because `tri 0 = ∫ tri = 1`.
 2. THEOREM A, CRYSTALLINE FORM (`poisson_rigidity`, `selfDual_rigidity`): a positive locally finite
    measure with no mass in `(-1,1) \ {0}`, `sinc²`-integrable, satisfying `IsPoissonPair ν β`, is
    carried by `ℤ`, has `ν{m} = ν{0} + β` for every `m ≠ 0`, and equals the sum of its atoms; for
    `β = 0` it is `ν{0} • Σ_{n∈ℤ} δ_n`. No discreteness or density hypothesis is assumed: positivity
    and the gap force the support onto `ℤ` (Step 3), translated Fejer certificates fix every mass
    (Step 4).
 3. Positive controls: the integer comb satisfies every hypothesis (`intComb_admissible`, via
    Mathlib's Poisson summation), and `r δ₀ + c Σ_{n≠0} δ_n` is a Poisson pair with `β = c - r`
    (`poissonPair_realizable`). So the characterization is sharp. The gap is also LP-sharp: a
    self-dual positive Poisson measure with a gap `(-a,a) \ {0}`, `a > 1`, is zero
    (`gap_gt_one_forces_zero`). Every Poisson pair is translation bounded, with an explicit window
    bound (`translation_bounded_of_poissonPair`): the kernel shadow of the local translation-boundedness
    lemma that makes every positive-measure FQ theorem inapplicable to zeta's zero measure, whose
    window counts grow like `(1/2π) log T`.
 4. The fooling family `ν_{p,c} = p^{-1/2} comb(1/p) + c comb(1) + p^{1/2} comb(p)` (`nup`):
    positive, locally finite, `sinc²`-integrable, exactly self-dual (`nup_isPoissonPair`, via Poisson
    summation for dilated lattices `comb_poisson`), a positive atom at `0`, but an atom at `1/p` inside
    the gap (`nup_gap_violated`), so not a multiple of the comb. Its positive half has Dirichlet
    transform `ζ(s) Q_{p,c}(s)`, `Q = p^{s-1/2} + c + p^{1/2-s}` (`nup_dirichlet`); the completion
    `Λ = Γ_ℝ ζ Q` satisfies ζ's exact FE (`LambdaP_one_sub`, `LambdaP_eq_Gammaℝ_mul`).
    Zeros of `Q`: all on `Re s = 1/2` for `0 ≤ c ≤ 2` (`Qp_zero_re_of_le_two`); for `c > 2` an explicit
    zero `s*` with `Re s* > 1/2` (`Qp_offline_zero`), inside the open strip when
    `c < √p + 1/√p` (`Qp_offline_zero_in_strip`). The crystalline data do not change across `c = 2`.
 5. Round 1's surgered witness `W1(29,11) = ζ(s)(1 + 11·29^{-s} + 29·29^{-2s})` is exactly
    `29^{1/2-s}` times the Dirichlet transform of `ν_{29, 11/√29}` (`Qp_euler_factor`,
    `W1_as_crystalline`), and round 1's golden fake completion `ξ·(2cosh((s-1/2)log 5) + √5)` is
    `s(s-1)/2` times the completed Mellin transform of `ν_{5,√5}` (`golden_as_crystalline`).
    Both negative controls ARE positive self-dual crystalline measures without the gap.
 6. The onset `c = 2` is local Ramanujan: the Satake parameters of `1 + c√p·T + p·T²` all have modulus
    `√p` iff `c ≤ 2` (`satake_ramanujan_iff`), the one-variable Lee-Yang condition. The crystalline
    data of `ν_{p,c}` are indifferent to it.
 7. Capstone `fq_rigidity_is_rh_blind` and Mathlib-vocabulary restatements `writer_*`.

WHAT THIS FILE DOES NOT ESTABLISH:
 - Step 2 of Theorem A: "ζ's FE for `∫ x^{-s} dN` implies `IsPoissonPair (δ₀ + N + N(-·)) β`"
   (Hamburger/Bochner modular relation; needs Mellin inversion, a contour shift with
   Phragmen-Lindelof, and density of Gaussians). It is the one remaining formalization target
   (round 1's NT4); its statement is `classP_collapse_beurling_q1` in RH_AXIOM_ISOLATION section 5.2.
 - Anything about the zeros of `riemannZeta`, RH, or any zero-side (Guinand-Weil) rigidity.
-/
import Mathlib

open MeasureTheory Real Complex Set
open scoped FourierTransform

noncomputable section

namespace CruxFQ

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

lemma hasCompactSupport_tri_sub (a : ℝ) :
    HasCompactSupport (fun x : ℝ => ((tri (x - a) : ℝ) : ℂ)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := a - 1) (b := a + 1)) ?_
  intro x hx
  have : 1 ≤ |x - a| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [tri_of_one_le_abs this]

/-- The Fourier integral at frequency `0` is the Lebesgue integral. -/
lemma fourier_at_zero (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp

lemma integral_tri : ∫ x, ((tri x : ℝ) : ℂ) = 1 := by
  rw [← fourier_at_zero, fourier_tri, fej_zero]; simp

/-- **Translated Fourier pair.** `𝓕 (tri (· - a)) ξ = e^{-2π i a ξ} · sinc(πξ)^2`. -/
theorem fourier_tri_sub (a ξ : ℝ) :
    𝓕 (fun x : ℝ => ((tri (x - a) : ℝ) : ℂ)) ξ
      = Complex.exp (↑(-2 * π * a * ξ) * Complex.I) * ((fej ξ : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← fourier_tri, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  rw [← integral_add_right_eq_self
    (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • ((tri (v - a) : ℝ) : ℂ)) a]
  congr 1
  funext v
  simp only [add_sub_cancel_right, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma integral_tri_sub (a : ℝ) : ∫ x, ((tri (x - a) : ℝ) : ℂ) = 1 := by
  rw [integral_sub_right_eq_self (fun x : ℝ => ((tri x : ℝ) : ℂ)) a, integral_tri]

lemma norm_fourier_tri_sub (a ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => ((tri (x - a) : ℝ) : ℂ)) ξ‖ = fej ξ := by
  rw [fourier_tri_sub, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (fej_nonneg ξ)]

/-! ## The Poisson-pair predicate -/

/-- `IsPoissonPair ν β` : the distributional Fourier transform of the (positive, locally finite)
measure `ν` is `ν + β (δ₀ - Lebesgue)`, tested against every continuous compactly supported `f`
whose Fourier transform is `ν`-integrable:
`∫ 𝓕 f dν = ∫ f dν + β (f 0 - ∫ f)`.
`β = 0` is exact self-duality `ν̂ = ν` (a self-dual crystalline measure); a nonzero `β` is the
footprint of a pole (a Lebesgue component in the Fourier transform). -/
def IsPoissonPair (ν : Measure ℝ) (β : ℂ) : Prop :=
  ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → Integrable (𝓕 f) ν →
    ∫ ξ, 𝓕 f ξ ∂ν = ∫ x, f x ∂ν + β * (f 0 - ∫ x, f x)

/-- The Poisson identity for the translated triangles, unpacked. -/
lemma poisson_tri_sub {ν : Measure ℝ} {β : ℂ} (hP : IsPoissonPair ν β)
    (hint : Integrable fej ν) (a : ℝ) :
    ∫ ξ, Complex.exp (↑(-2 * π * a * ξ) * Complex.I) * ((fej ξ : ℝ) : ℂ) ∂ν
      = ∫ x, ((tri (x - a) : ℝ) : ℂ) ∂ν + β * (((tri (0 - a) : ℝ) : ℂ) - 1) := by
  have hcont : Continuous (fun x : ℝ => ((tri (x - a) : ℝ) : ℂ)) := by
    have := continuous_tri; fun_prop
  have hFint : Integrable (𝓕 (fun x : ℝ => ((tri (x - a) : ℝ) : ℂ))) ν := by
    refine Integrable.mono' hint ?_ (ae_of_all _ fun ξ => (norm_fourier_tri_sub a ξ).le)
    have : 𝓕 (fun x : ℝ => ((tri (x - a) : ℝ) : ℂ))
        = fun ξ => Complex.exp (↑(-2 * π * a * ξ) * Complex.I) * ((fej ξ : ℝ) : ℂ) := by
      funext ξ; exact fourier_tri_sub a ξ
    rw [this]
    exact (Continuous.aestronglyMeasurable (by have := continuous_fej; fun_prop))
  have := hP _ hcont (hasCompactSupport_tri_sub a) hFint
  rw [integral_tri_sub] at this
  have e : 𝓕 (fun x : ℝ => ((tri (x - a) : ℝ) : ℂ))
      = fun ξ => Complex.exp (↑(-2 * π * a * ξ) * Complex.I) * ((fej ξ : ℝ) : ℂ) := by
    funext ξ; exact fourier_tri_sub a ξ
  rw [e] at this
  simpa using this


/-! ## Step 3: the Fejer certificate forces the support onto ℤ -/

lemma mass_singleton_lt_top (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (a : ℝ) : ν {a} < ⊤ :=
  isCompact_singleton.measure_lt_top

/-- **Support forcing (kernel).** Positivity, the gap `(-1,1) \ {0}`, and the Poisson identity for
the single Fejer pair `(tri, sinc²)` force `ν` onto the integers. The pole term is invisible to this
certificate because `tri 0 = ∫ tri = 1`. -/
theorem ae_int_of_poissonPair {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {β : ℂ}
    (hP : IsPoissonPair ν β) (hint : Integrable fej ν)
    (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    ∀ᵐ x ∂ν, ∃ n : ℤ, x = (n : ℝ) := by
  have h0 := poisson_tri_sub hP hint 0
  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul, sub_zero,
    tri_zero, Complex.ofReal_one, sub_self] at h0
  have hae_gap : ∀ᵐ x ∂ν, x ∉ Ioo (-1) 1 \ {0} := measure_eq_zero_iff_ae_notMem.mp hgap
  have htri : (fun x => tri x) =ᵐ[ν] ({0} : Set ℝ).indicator 1 := by
    filter_upwards [hae_gap] with x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [tri_zero]
    · have hx' : x ∉ Ioo (-1) 1 := fun h => hx ⟨h, hx0⟩
      have h1 : 1 ≤ |x| := by
        rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx'
        rcases hx' with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp [tri_of_one_le_abs h1, hx0]
  have hI_tri : ∫ x, tri x ∂ν = ν.real {0} := by
    rw [integral_congr_ae htri, integral_indicator_one (measurableSet_singleton 0)]
  have hI_fej : ∫ x, fej x ∂ν = ν.real {0} := by
    rw [integral_complex_ofReal, integral_complex_ofReal, add_zero] at h0
    rw [← hI_tri]; exact_mod_cast h0
  have hind_int : Integrable (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) ν := by
    refine (integrableOn_const (C := (1:ℝ)) ?_).integrable_indicator (measurableSet_singleton 0)
    exact (mass_singleton_lt_top ν 0).ne
  have hg_nonneg : ∀ x, 0 ≤ fej x - ({0} : Set ℝ).indicator (1 : ℝ → ℝ) x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [fej_zero]
    · simp [hx, fej_nonneg]
  have hzero : ∫ x, (fej x - ({0} : Set ℝ).indicator (1 : ℝ → ℝ) x) ∂ν = 0 := by
    rw [integral_sub hint hind_int, hI_fej, integral_indicator_one (measurableSet_singleton 0),
      sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hg_nonneg)
    (hint.sub hind_int)).mp hzero
  filter_upwards [hae] with x hx
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  · have : fej x = 0 := by simpa [hx0] using hx
    exact exists_int_of_fej_eq_zero this

/-! ## Step 4: translated certificates fix every atom -/

/-- **Atom formula (kernel).** Once `ν` lives on `ℤ`, the translated Fejer pair at `m ≠ 0` gives
`ν{m} = ν{0} + β`. -/
theorem mass_intCast_of_poissonPair {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {β : ℂ}
    (hP : IsPoissonPair ν β) (hint : Integrable fej ν)
    (hZ : ∀ᵐ x ∂ν, ∃ n : ℤ, x = (n : ℝ)) (m : ℤ) (hm : m ≠ 0) :
    ((ν.real {(m : ℝ)} : ℝ) : ℂ) = ((ν.real {0} : ℝ) : ℂ) + β := by
  have h := poisson_tri_sub hP hint m
  have hL : (fun ξ : ℝ => Complex.exp (↑(-2 * π * (m : ℝ) * ξ) * Complex.I) * ((fej ξ : ℝ) : ℂ))
      =ᵐ[ν] ({0} : Set ℝ).indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [hZ] with ξ hξ
    obtain ⟨n, rfl⟩ := hξ
    by_cases hn0 : n = 0
    · subst hn0; simp [fej_zero]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      simp [fej_intCast hn0, hn']
  have hR : (fun x : ℝ => ((tri (x - m) : ℝ) : ℂ))
      =ᵐ[ν] ({(m : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [hZ] with x hx
    obtain ⟨n, rfl⟩ := hx
    by_cases hnm : n = m
    · subst hnm; simp [tri_zero]
    · have e : (n : ℝ) - m = ((n - m : ℤ) : ℝ) := by push_cast; ring
      have hne : (n : ℝ) ≠ m := by exact_mod_cast hnm
      rw [e, tri_intCast (sub_ne_zero.mpr hnm)]
      simp [hne]
  rw [integral_congr_ae hL, integral_congr_ae hR,
    integral_indicator_const _ (measurableSet_singleton _),
    integral_indicator_const _ (measurableSet_singleton _)] at h
  have htm : tri (0 - (m : ℝ)) = 0 := by
    rw [zero_sub]
    have : -(m : ℝ) = ((-m : ℤ) : ℝ) := by push_cast; ring
    rw [this, tri_intCast (neg_ne_zero.mpr hm)]
  rw [htm] at h
  simp only [Complex.real_smul, mul_one, Complex.ofReal_zero, zero_sub, mul_neg] at h
  linear_combination -h

/-! ## Assembly -/

/-- A measure concentrated on `ℤ` is the sum of its atoms. -/
theorem eq_sum_dirac_of_ae_int {ν : Measure ℝ} (hZ : ∀ᵐ x ∂ν, ∃ n : ℤ, x = (n : ℝ)) :
    ν = Measure.sum (fun n : ℤ => ν {(n : ℝ)} • Measure.dirac (n : ℝ)) := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  have hmem : ∀ᵐ x ∂ν, x ∈ range (Int.cast : ℤ → ℝ) := by
    filter_upwards [hZ] with x hx
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n, rfl⟩
  rw [← Measure.measure_inter_eq_of_ae hmem]
  have hU : range (Int.cast : ℤ → ℝ) ∩ s = ⋃ n : ℤ, ({(n : ℝ)} ∩ s) := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_iUnion, mem_singleton_iff]
    constructor
    · rintro ⟨⟨n, rfl⟩, hx⟩; exact ⟨n, rfl, hx⟩
    · rintro ⟨n, rfl, hx⟩; exact ⟨⟨n, rfl⟩, hx⟩
  rw [hU, measure_iUnion]
  · congr 1
    funext n
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ hs]
    by_cases hn : (n : ℝ) ∈ s
    · have : ({(n : ℝ)} : Set ℝ) ∩ s = {(n : ℝ)} := by
        ext x; simp only [mem_inter_iff, mem_singleton_iff]
        constructor
        · rintro ⟨rfl, _⟩; rfl
        · rintro rfl; exact ⟨rfl, hn⟩
      simp [this, hn]
    · have : ({(n : ℝ)} : Set ℝ) ∩ s = ∅ := by
        ext x; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
        rintro ⟨rfl, hx⟩; exact hn hx
      simp [this, hn]
  · intro i j hij
    have hij' : (i : ℝ) ≠ j := by exact_mod_cast hij
    exact Disjoint.mono inter_subset_left inter_subset_left (disjoint_singleton.mpr hij')
  · intro n; exact (measurableSet_singleton _).inter hs

/-- The integer comb `Σ_{n ∈ ℤ} δ_n`. -/
def intComb : Measure ℝ := Measure.sum (fun n : ℤ => (1 : ENNReal) • Measure.dirac (n : ℝ))

/-- **Theorem A, crystalline-measure form (kernel; the Poisson-pair is a hypothesis).**
Let `ν` be a positive locally finite measure on `ℝ` with no mass in `(-1,1) \ {0}`, with
`sinc(π·)^2` integrable, whose Fourier transform is `ν + β (δ₀ - Leb)` on compactly supported
continuous tests. Then `ν` is carried by `ℤ`, every atom off the origin has mass `ν{0} + β`, and
`ν` is the sum of its atoms. No discreteness, uniform discreteness, or density hypothesis is
assumed: positivity plus the gap force discreteness. -/
theorem poisson_rigidity {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {β : ℂ}
    (hP : IsPoissonPair ν β) (hint : Integrable fej ν)
    (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    (∀ᵐ x ∂ν, ∃ n : ℤ, x = (n : ℝ)) ∧
    (∀ m : ℤ, m ≠ 0 → ((ν.real {(m : ℝ)} : ℝ) : ℂ) = ((ν.real {0} : ℝ) : ℂ) + β) ∧
    ν = Measure.sum (fun n : ℤ => ν {(n : ℝ)} • Measure.dirac (n : ℝ)) := by
  have hZ := ae_int_of_poissonPair hP hint hgap
  exact ⟨hZ, mass_intCast_of_poissonPair hP hint hZ, eq_sum_dirac_of_ae_int hZ⟩

/-- **Self-dual form.** If `ν̂ = ν` exactly (`β = 0`), then `ν = ν{0} • (Σ_{n∈ℤ} δ_n)`. -/
theorem selfDual_rigidity {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hP : IsPoissonPair ν 0) (hint : Integrable fej ν)
    (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    ν = ν {0} • intComb := by
  obtain ⟨_, hm, hsum⟩ := poisson_rigidity hP hint hgap
  have hall : ∀ n : ℤ, ν {(n : ℝ)} = ν {0} := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · have h := hm n hn
      simp only [add_zero, Complex.ofReal_inj] at h
      rw [Measure.real, Measure.real] at h
      exact (ENNReal.toReal_eq_toReal_iff' (mass_singleton_lt_top ν _).ne
        (mass_singleton_lt_top ν _).ne).mp h
  have key : Measure.sum (fun n : ℤ => ν {(n : ℝ)} • Measure.dirac (n : ℝ)) = ν {0} • intComb := by
    simp_rw [hall]
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.smul_apply, intComb, Measure.sum_apply _ hs, smul_eq_mul,
      ← ENNReal.tsum_mul_left]
    simp
  exact hsum.trans key


/-! ## Positive control: the integer comb satisfies every hypothesis -/

lemma intComb_apply {s : Set ℝ} (hs : MeasurableSet s) :
    intComb s = ∑' n : ℤ, s.indicator 1 (n : ℝ) := by
  rw [intComb, Measure.sum_apply _ hs]
  congr 1; funext n
  rw [Measure.smul_apply, one_smul, Measure.dirac_apply' _ hs]

lemma intComb_Icc_lt_top (R : ℝ) : intComb (Icc (-R) R) < ⊤ := by
  rw [intComb_apply measurableSet_Icc]
  have hfin : ∀ n : ℤ, n ∉ Finset.Icc (-⌈R⌉) ⌈R⌉ → (Icc (-R) R).indicator (1 : ℝ → ENNReal) (n : ℝ) = 0 := by
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    have : (n : ℝ) ∉ Icc (-R) R := by
      intro h
      rcases hn with hn | hn
      · have h1 : (n : ℝ) < -⌈R⌉ := by exact_mod_cast hn
        have h2 : -(⌈R⌉ : ℝ) ≤ -R := by have := Int.le_ceil R; linarith
        linarith [h.1]
      · have h1 : (⌈R⌉ : ℝ) < n := by exact_mod_cast hn
        have h2 : R ≤ ⌈R⌉ := Int.le_ceil R
        linarith [h.2]
    simp [this]
  rw [tsum_eq_sum hfin]
  exact ENNReal.sum_lt_top.mpr fun n _ => by
    by_cases h : (n : ℝ) ∈ Icc (-R) R <;> simp [h]

instance : IsFiniteMeasureOnCompacts intComb := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
  exact (measure_mono hR).trans_lt (intComb_Icc_lt_top R)

lemma intComb_gap : intComb (Ioo (-1) 1 \ {0}) = 0 := by
  rw [intComb_apply (measurableSet_Ioo.diff (measurableSet_singleton 0))]
  have : ∀ n : ℤ, (n : ℝ) ∉ Ioo (-1) 1 \ {0} := by
    rintro n ⟨⟨h1, h2⟩, h3⟩
    have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < 1 := by exact_mod_cast h2
    have : n = 0 := by omega
    exact h3 (by simp [this])
  simp [this]

lemma intComb_ae_int : ∀ᵐ x ∂intComb, ∃ n : ℤ, x = (n : ℝ) := by
  rw [ae_iff]
  have hms : MeasurableSet {a : ℝ | ¬∃ n : ℤ, a = (n : ℝ)} := by
    have : {a : ℝ | ¬∃ n : ℤ, a = (n : ℝ)} = (range (Int.cast : ℤ → ℝ))ᶜ := by
      ext a; simp [eq_comm]
    rw [this]
    exact (Set.countable_range _).measurableSet.compl
  rw [intComb_apply hms]
  simp

lemma integrable_fej_intComb : Integrable fej intComb := by
  have hc : ∀ n : ℤ, (1 : ENNReal) ≠ ⊤ := fun _ => ENNReal.one_ne_top
  rw [intComb, integrable_sum_dirac_iff hc]
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  have : n ≠ 0 := by simpa using hn
  simp [fej_intCast this]

lemma integral_intComb (g : ℝ → ℂ) : ∫ x, g x ∂intComb = ∑' n : ℤ, g n := by
  rw [intComb, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  simp

lemma isBigO_of_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    f =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  have hev : f =ᶠ[Filter.cocompact ℝ] fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem hf.isCompact.compl_mem_cocompact
      fun x hx => image_eq_zero_of_notMem_tsupport hx
  exact hev.isBigO.trans (Asymptotics.isBigO_zero _ _)

/-- **Positive control (kernel).** The integer comb is a Poisson pair with `β = 0`
(Poisson summation, Mathlib). -/
theorem intComb_isPoissonPair : IsPoissonPair intComb 0 := by
  intro f hc hcs hFint
  rw [integral_intComb, integral_intComb, zero_mul, add_zero]
  have hsum : Summable fun n : ℤ => 𝓕 f n := by
    have := (show Integrable (𝓕 f) (Measure.sum (fun n : ℤ => (1 : ENNReal) • Measure.dirac (n : ℝ)))
      from hFint).summable_of_dirac
    simp only [ENNReal.toReal_one, one_mul] at this
    exact this.of_norm
  have := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc one_lt_two
    (isBigO_of_hasCompactSupport hcs) hsum 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at this
  exact this.symm

instance : IsLocallyFiniteMeasure intComb := inferInstance

/-- The comb satisfies all hypotheses of `poisson_rigidity` / `selfDual_rigidity`, so the
characterization is not vacuous: the admissible measures are EXACTLY `c • intComb`. -/
theorem intComb_admissible :
    IsPoissonPair intComb 0 ∧ Integrable fej intComb ∧ intComb (Ioo (-1) 1 \ {0}) = 0 ∧
    intComb {0} = 1 :=
  ⟨intComb_isPoissonPair, integrable_fej_intComb, intComb_gap, by
    rw [intComb_apply (measurableSet_singleton 0)]
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      simp [this]⟩


/-! ## The LP bound is sharp, and Poisson pairs are translation bounded -/

/-- **The 1D LP gap bound (kernel).** A positive self-dual Poisson measure with a gap
`(-a,a) \ {0}` wider than the integer gap (`a > 1`) is zero. With `selfDual_rigidity`: the maximal gap
is `1` and it is attained only on the ray through the integer comb. -/
theorem gap_gt_one_forces_zero {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hP : IsPoissonPair ν 0) (hint : Integrable fej ν) {a : ℝ} (ha : 1 < a)
    (hgap : ν (Ioo (-a) a \ {0}) = 0) : ν = 0 := by
  have hsub : Ioo (-1 : ℝ) 1 \ {0} ⊆ Ioo (-a) a \ {0} := by
    intro x hx
    exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, hx.2⟩
  have hgap1 : ν (Ioo (-1) 1 \ {0}) = 0 := measure_mono_null hsub hgap
  have hν := selfDual_rigidity hP hint hgap1
  have h1mem : (1 : ℝ) ∈ Ioo (-a) a \ {0} := ⟨⟨by linarith, ha⟩, by norm_num⟩
  have hν1 : ν {1} = 0 := measure_mono_null (singleton_subset_iff.mpr h1mem) hgap
  have hc1 : intComb {1} = 1 := by
    rw [intComb_apply (measurableSet_singleton 1), tsum_eq_single 1]
    · simp
    · intro n hn
      have : (n : ℝ) ≠ 1 := by exact_mod_cast hn
      simp [this]
  have h0 : ν {0} = 0 := by
    have := congrArg (fun μ : Measure ℝ => μ {1}) hν
    simp only [Measure.smul_apply, hc1, smul_eq_mul, mul_one] at this
    rw [← this]; exact hν1
  rw [hν, h0, zero_smul]

/-- **Poisson pairs are translation bounded (kernel).** If `ν ≥ 0` is a Poisson pair with pole
footprint `β` and `sinc²` is `ν`-integrable, then every unit window carries mass at most
`2 (∫ sinc² dν + ‖β‖)`. (Kernel shadow of the local translation-boundedness lemma behind
Kurasov-Sarnak Thm 1, Olevskii-Ulanovskii Prop. 1 and Favorov-Deger Thm 1: a positive measure whose
Fourier transform is tame near `0` has bounded window counts. The zero measure of zeta, whose windows
grow like `(1/2π) log T`, can never be such a `ν`.) -/
theorem translation_bounded_of_poissonPair {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {β : ℂ}
    (hP : IsPoissonPair ν β) (hint : Integrable fej ν) (t : ℝ) :
    ν (Icc (t - 1 / 2) (t + 1 / 2)) ≤ ENNReal.ofReal (2 * ((∫ ξ, fej ξ ∂ν) + ‖β‖)) := by
  have h := poisson_tri_sub hP hint t
  have htri_int : Integrable (fun x : ℝ => tri (x - t)) ν := by
    have hc : Continuous (fun x : ℝ => tri (x - t)) := continuous_tri.comp (continuous_id.sub continuous_const)
    have hcs : HasCompactSupport (fun x : ℝ => tri (x - t)) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := t - 1) (b := t + 1)) ?_
      intro x hx
      have : 1 ≤ |x - t| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact tri_of_one_le_abs this
    exact hc.integrable_of_hasCompactSupport hcs
  -- upper bound on the real integral of the triangle
  have hupper : ∫ x, tri (x - t) ∂ν ≤ (∫ ξ, fej ξ ∂ν) + ‖β‖ := by
    rw [integral_complex_ofReal] at h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    have hL : (∫ ξ, Complex.exp (↑(-2 * π * t * ξ) * Complex.I) * ((fej ξ : ℝ) : ℂ) ∂ν).re
        ≤ ∫ ξ, fej ξ ∂ν := by
      refine (Complex.re_le_norm _).trans ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
      congr 1; funext ξ
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (fej_nonneg ξ)]
    have hB : -(β * (((tri (0 - t) : ℝ) : ℂ) - 1)).re ≤ ‖β‖ := by
      have hb : ‖((tri (0 - t) : ℝ) : ℂ) - 1‖ ≤ 1 := by
        rw [show ((tri (0 - t) : ℝ) : ℂ) - 1 = ((tri (0 - t) - 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_le]
        have h1 := tri_nonneg (0 - t)
        have h2 : tri (0 - t) ≤ 1 := by unfold tri; exact max_le (by norm_num) (by linarith [abs_nonneg (0 - t)])
        constructor <;> linarith
      calc -(β * (((tri (0 - t) : ℝ) : ℂ) - 1)).re ≤ ‖β * (((tri (0 - t) : ℝ) : ℂ) - 1)‖ :=
            (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ = ‖β‖ * ‖((tri (0 - t) : ℝ) : ℂ) - 1‖ := norm_mul _ _
        _ ≤ ‖β‖ * 1 := by gcongr
        _ = ‖β‖ := mul_one _
    linarith
  -- lower bound: tri(x - t) ≥ (1/2) on the window
  have hlower : (1 / 2) * ν.real (Icc (t - 1 / 2) (t + 1 / 2)) ≤ ∫ x, tri (x - t) ∂ν := by
    have hind : Integrable ((Icc (t - 1 / 2) (t + 1 / 2)).indicator (fun _ => (1 / 2 : ℝ))) ν := by
      refine (integrableOn_const (C := (1 / 2 : ℝ)) ?_).integrable_indicator measurableSet_Icc
      exact (isCompact_Icc.measure_lt_top).ne
    have heq : ∫ x, (Icc (t - 1 / 2) (t + 1 / 2)).indicator (fun _ => (1 / 2 : ℝ)) x ∂ν
        = ν.real (Icc (t - 1 / 2) (t + 1 / 2)) * (1 / 2) := by
      rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    calc (1 / 2) * ν.real (Icc (t - 1 / 2) (t + 1 / 2))
        = ∫ x, (Icc (t - 1 / 2) (t + 1 / 2)).indicator (fun _ => (1 / 2 : ℝ)) x ∂ν := by
          rw [heq]; ring
      _ ≤ ∫ x, tri (x - t) ∂ν := by
          refine integral_mono hind htri_int (fun x => ?_)
          by_cases hx : x ∈ Icc (t - 1 / 2) (t + 1 / 2)
          · rw [Set.indicator_of_mem hx]
            have habs : |x - t| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
            show (1 / 2 : ℝ) ≤ tri (x - t)
            rw [tri_of_abs_le (by linarith)]; linarith
          · rw [Set.indicator_of_notMem hx]; exact tri_nonneg _
  have hreal : ν.real (Icc (t - 1 / 2) (t + 1 / 2)) ≤ 2 * ((∫ ξ, fej ξ ∂ν) + ‖β‖) := by linarith
  have hfin : ν (Icc (t - 1 / 2) (t + 1 / 2)) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## K2: positive self-dual crystalline measures without the gap (the fooling family) -/

/-- The dilated comb `Σ_{n∈ℤ} δ_{a n}`. -/
def comb (a : ℝ) : Measure ℝ := Measure.sum (fun n : ℤ => (1 : ENNReal) • Measure.dirac (a * n))

lemma integral_comb (a : ℝ) (g : ℝ → ℂ) : ∫ x, g x ∂comb a = ∑' n : ℤ, g (a * n) := by
  rw [comb, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  simp

lemma fourier_comp_div (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun y => f (y / a)) ξ = (a : ℂ) * 𝓕 f (a * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_div
    (fun x => Complex.exp (↑(-2 * π * x * (a * ξ)) * Complex.I) • f x) a
  rw [abs_of_pos ha, Complex.real_smul] at h
  rw [← h]
  congr 1
  funext y
  congr 3
  field_simp

lemma summable_norm_comp_mul_of_hasCompactSupport {f : ℝ → ℂ} (hcs : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) : Summable fun n : ℤ => ‖f (a * n)‖ := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  set N : ℤ := ⌈R / a⌉ with hN
  apply summable_of_ne_finset_zero (s := Finset.Icc (-N) N)
  intro n hn
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  have hbig : R < |a * n| := by
    rw [abs_mul, abs_of_pos ha]
    have hRa : R / a ≤ N := Int.le_ceil _
    rcases hn with hn | hn
    · have h1 : (n : ℝ) < -N := by exact_mod_cast hn
      have : (N : ℝ) < |(n : ℝ)| := lt_of_lt_of_le (by linarith) (neg_le_abs _)
      calc R = a * (R / a) := by field_simp
        _ ≤ a * N := by gcongr
        _ < a * |(n : ℝ)| := by gcongr
    · have h1 : (N : ℝ) < n := by exact_mod_cast hn
      have : (N : ℝ) < |(n : ℝ)| := lt_of_lt_of_le h1 (le_abs_self _)
      calc R = a * (R / a) := by field_simp
        _ ≤ a * N := by gcongr
        _ < a * |(n : ℝ)| := by gcongr
  have hnot : a * (n : ℝ) ∉ tsupport f := by
    intro hmem
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  simp [image_eq_zero_of_notMem_tsupport hnot]

/-- **Poisson summation for a dilated comb (kernel).**
`∫ 𝓕 f d(comb a) = (1/a) ∫ f d(comb (1/a))`, i.e. `(comb a)^ = (1/a) comb (1/a)`. -/
theorem comb_poisson {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (hc : Continuous f)
    (hcs : HasCompactSupport f) (hint : Integrable (𝓕 f) (comb a)) :
    ∫ ξ, 𝓕 f ξ ∂comb a = ((1 / a : ℝ) : ℂ) * ∫ x, f x ∂comb (1 / a) := by
  rw [integral_comb, integral_comb]
  set g : ℝ → ℂ := fun y => f (y / a) with hg
  have hgc : Continuous g := hc.comp (continuous_id.div_const a)
  have hgcs : HasCompactSupport g := by
    have := hcs.comp_homeomorph (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne'))
    convert this using 1
    funext y
    simp [g, div_eq_mul_inv]
  have hsumF : Summable fun n : ℤ => 𝓕 f (a * n) := by
    have := (show Integrable (𝓕 f)
      (Measure.sum (fun n : ℤ => (1 : ENNReal) • Measure.dirac (a * (n : ℝ)))) from hint).summable_of_dirac
    simp only [ENNReal.toReal_one, one_mul] at this
    exact this.of_norm
  have hsumG : Summable fun n : ℤ => 𝓕 g n := by
    have e : (fun n : ℤ => 𝓕 g n) = fun n : ℤ => (a : ℂ) * 𝓕 f (a * n) := by
      funext n; exact fourier_comp_div f ha n
    rw [e]; exact hsumF.mul_left _
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hgc one_lt_two
    (isBigO_of_hasCompactSupport hgcs) hsumG 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  have e : (fun n : ℤ => 𝓕 g n) = fun n : ℤ => (a : ℂ) * 𝓕 f (a * n) := by
    funext n; exact fourier_comp_div f ha n
  rw [e, tsum_mul_left] at hP
  have e2 : ∀ n : ℤ, g n = f (1 / a * n) := by intro n; simp [g]; ring_nf
  simp_rw [e2] at hP
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [hP]
  push_cast
  field_simp

lemma integrable_comb_of_hasCompactSupport {f : ℝ → ℂ} (hcs : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) : Integrable f (comb a) := by
  rw [comb, integrable_sum_dirac_iff (fun _ => ENNReal.one_ne_top)]
  simpa using summable_norm_comp_mul_of_hasCompactSupport hcs ha

lemma comb_apply (a : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    comb a s = ∑' n : ℤ, s.indicator 1 (a * n) := by
  rw [comb, Measure.sum_apply _ hs]
  congr 1; funext n
  rw [Measure.smul_apply, one_smul, Measure.dirac_apply' _ hs]

lemma comb_Icc_lt_top {a : ℝ} (ha : 0 < a) (R : ℝ) : comb a (Icc (-R) R) < ⊤ := by
  rw [comb_apply a measurableSet_Icc]
  set N : ℤ := ⌈R / a⌉
  have hfin : ∀ n : ℤ, n ∉ Finset.Icc (-N) N →
      (Icc (-R) R).indicator (1 : ℝ → ENNReal) (a * n) = 0 := by
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    have hRa : R / a ≤ N := Int.le_ceil _
    have hRa' : R ≤ a * N := by
      have := mul_le_mul_of_nonneg_left hRa ha.le
      rwa [mul_div_cancel₀ R ha.ne'] at this
    have : a * (n : ℝ) ∉ Icc (-R) R := by
      intro h
      rcases hn with hn | hn
      · have h1 : (n : ℝ) < -N := by exact_mod_cast hn
        have : a * (n : ℝ) < -(a * N) := by nlinarith
        linarith [h.1]
      · have h1 : (N : ℝ) < n := by exact_mod_cast hn
        have : a * N < a * (n : ℝ) := by nlinarith
        linarith [h.2]
    simp [this]
  rw [tsum_eq_sum hfin]
  exact ENNReal.sum_lt_top.mpr fun n _ => by
    by_cases h : a * (n : ℝ) ∈ Icc (-R) R <;> simp [h]

lemma comb_compact_lt_top {a : ℝ} (ha : 0 < a) {K : Set ℝ} (hK : IsCompact K) :
    comb a K < ⊤ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
  exact (measure_mono hR).trans_lt (comb_Icc_lt_top ha R)

lemma abs_sinc_le_inv_abs {y : ℝ} (hy : y ≠ 0) : |Real.sinc y| ≤ |y|⁻¹ := by
  rw [Real.sinc_of_ne_zero hy, abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one y) (abs_nonneg y) |>.trans_eq (one_div _)

lemma fej_le_inv_sq {x : ℝ} (hx : x ≠ 0) : fej x ≤ 1 / x ^ 2 := by
  unfold fej
  have hpx : π * x ≠ 0 := mul_ne_zero pi_ne_zero hx
  have h1 := abs_sinc_le_inv_abs hpx
  have h2 : Real.sinc (π * x) ^ 2 ≤ (|π * x|⁻¹) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  refine h2.trans ?_
  rw [inv_pow, sq_abs, one_div, mul_pow]
  apply inv_anti₀ (by positivity)
  have : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg x, sq_pos_of_ne_zero hx]

lemma integrable_fej_comb {a : ℝ} (ha : 0 < a) : Integrable fej (comb a) := by
  rw [comb, integrable_sum_dirac_iff (fun _ => ENNReal.one_ne_top)]
  simp only [ENNReal.toReal_one, one_mul]
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left (1 / a ^ 2)) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hx : a * (n : ℝ) ≠ 0 := mul_ne_zero ha.ne' hn'
  rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (fej_nonneg _)]
  refine (fej_le_inv_sq hx).trans (le_of_eq ?_)
  rw [mul_pow]; field_simp


/-- The fooling family with base `p > 1`:
`ν_{p,c} = p^{-1/2} comb(1/p) + c comb(1) + p^{1/2} comb(p)`.
Its positive half has Dirichlet transform `ζ(s) (p^{s-1/2} + c + p^{1/2-s})`; for `p = 29`,
`c = 11/√29` this is `29^{s-1/2}` times round 1's surgered witness `W1(29,11)`. -/
def nup (p c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / Real.sqrt p) • comb (1 / p) + ENNReal.ofReal c • comb 1
    + ENNReal.ofReal (Real.sqrt p) • comb p

lemma integrable_of_smul_comb {g : ℝ → ℂ} {r : ℝ} (hr : 0 < r) {a : ℝ}
    (h : Integrable g (ENNReal.ofReal r • comb a)) : Integrable g (comb a) :=
  (integrable_smul_measure (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top).mp h

/-- **The fooling family is self-dual (kernel).** For every `p > 0` and `c > 0`, `ν_{p,c}` is a
positive measure with `ν̂ = ν` on compactly supported continuous tests. -/
theorem nup_isPoissonPair {p c : ℝ} (hp : 0 < p) (hc : 0 < c) : IsPoissonPair (nup p c) 0 := by
  intro f hcont hcs hint
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hspi : 0 < 1 / Real.sqrt p := by positivity
  have hpi : 0 < 1 / p := by positivity
  rw [nup, integrable_add_measure, integrable_add_measure] at hint
  obtain ⟨⟨h1, h2⟩, h3⟩ := hint
  have h1' := integrable_of_smul_comb hspi h1
  have h2' := integrable_of_smul_comb hc h2
  have h3' := integrable_of_smul_comb hsp h3
  have hf1 := integrable_comb_of_hasCompactSupport hcs hpi
  have hf2 := integrable_comb_of_hasCompactSupport hcs (a := 1) one_pos
  have hf3 := integrable_comb_of_hasCompactSupport hcs hp
  have hsm : ∀ {μ : Measure ℝ} {g : ℝ → ℂ} {r : ℝ}, Integrable g μ →
      Integrable g (ENNReal.ofReal r • μ) := fun h => h.smul_measure ENNReal.ofReal_ne_top
  rw [nup, integral_add_measure ((hsm h1').add_measure (hsm h2')) (hsm h3'),
    integral_add_measure (hsm h1') (hsm h2'),
    integral_add_measure ((hsm hf1).add_measure (hsm hf2)) (hsm hf3),
    integral_add_measure (hsm hf1) (hsm hf2)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hspi.le, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal hsp.le, zero_mul, add_zero]
  rw [comb_poisson hpi f hcont hcs h1', comb_poisson one_pos f hcont hcs h2',
    comb_poisson hp f hcont hcs h3']
  have e1 : (1 : ℝ) / (1 / p) = p := by field_simp
  have e2 : (1 : ℝ) / 1 = 1 := by norm_num
  rw [e1, e2]
  simp only [Complex.real_smul]
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have hsqC : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = p := by exact_mod_cast hsq
  have hspC : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsq2 : (Real.sqrt p : ℂ) ^ 2 = p := by rw [sq]; exact hsqC
  push_cast
  field_simp
  linear_combination (-(p : ℂ) * (∫ x, f x ∂comb p) + (∫ x, f x ∂comb (1 / p))) * hsq2

/-! ### The Mellin side: `Q_{p,c}(s) = p^{s-1/2} + c + p^{1/2-s}` -/

/-- `Q_{p,c}(s) = p^{s-1/2} + c + p^{1/2-s}` (written with `exp`). -/
def Qp (p c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 1 / 2) * (Real.log p : ℂ)) + c + Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ)))

lemma Qp_one_sub (p c : ℝ) (s : ℂ) : Qp p c (1 - s) = Qp p c s := by
  unfold Qp
  have e : (1 - s - 1 / 2) * (Real.log p : ℂ) = -((s - 1 / 2) * (Real.log p : ℂ)) := by ring
  rw [e, neg_neg]
  ring

/-- **On-line regime (kernel).** For `p > 1` and `0 ≤ c ≤ 2`, every zero of `Q_{p,c}` lies on
`Re s = 1/2`. -/
theorem Qp_zero_re_of_le_two {p c : ℝ} (hp : 1 < p) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) {s : ℂ}
    (h : Qp p c s = 0) : s.re = 1 / 2 := by
  set w : ℂ := (s - 1 / 2) * (Real.log p : ℂ) with hw
  set z : ℂ := Complex.exp w with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hinv : Complex.exp (-w) = z⁻¹ := by rw [Complex.exp_neg]
  have h' : z + c + z⁻¹ = 0 := by
    have := h; unfold Qp at this; rw [← hw, hinv] at this; exact this
  have hq : z ^ 2 + c * z + 1 = 0 := by
    have : z * (z + c + z⁻¹) = 0 := by rw [h', mul_zero]
    have e : z * (z + c + z⁻¹) = z ^ 2 + c * z + 1 := by field_simp
    rw [← e]; exact this
  have hre : z.re ^ 2 - z.im ^ 2 + c * z.re + 1 = 0 := by
    have := congrArg Complex.re hq
    simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.zero_re] at this
    linarith
  have him : z.im * (2 * z.re + c) = 0 := by
    have := congrArg Complex.im hq
    simp only [sq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, Complex.zero_im] at this
    linarith
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    rcases mul_eq_zero.mp him with hy | hx
    · rw [hy] at hre ⊢
      nlinarith [sq_nonneg (2 * z.re + c), mul_nonneg hc0 (sub_nonneg.mpr hc2)]
    · have hx' : z.re = -c / 2 := by linarith
      rw [hx'] at hre ⊢
      nlinarith
  have hnorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [hsq]
    have := norm_nonneg z
    nlinarith
  have hwre : w.re = 0 := by
    have := Complex.norm_exp w
    rw [← hz, hnorm] at this
    exact (Real.exp_eq_one_iff _).mp this.symm
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  have : (s.re - 1 / 2) * Real.log p = 0 := by
    have e : w.re = (s.re - 1 / 2) * Real.log p := by
      rw [hw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.sub_re]
      norm_num
    rw [← e]; exact hwre
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hlog

/-- The larger root `r = (c + √(c² - 4))/2` of `r² - c r + 1 = 0`. -/
def rootR (c : ℝ) : ℝ := (c + Real.sqrt (c ^ 2 - 4)) / 2

lemma rootR_gt_one {c : ℝ} (hc : 2 < c) : 1 < rootR c := by
  unfold rootR
  have : 0 < Real.sqrt (c ^ 2 - 4) := Real.sqrt_pos.mpr (by nlinarith)
  linarith

lemma rootR_add_inv {c : ℝ} (hc : 2 < c) : rootR c + (rootR c)⁻¹ = c := by
  have hr := rootR_gt_one hc
  have hr0 : rootR c ≠ 0 := by linarith
  have hsq : Real.sqrt (c ^ 2 - 4) ^ 2 = c ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  field_simp
  unfold rootR
  nlinarith [hsq]

/-- The explicit off-line zero `s* = 1/2 + (log r + iπ)/log p`. -/
def sStar (p c : ℝ) : ℂ := 1 / 2 + ((Real.log (rootR c) : ℂ) + π * Complex.I) / (Real.log p : ℂ)

lemma sStar_re {p c : ℝ} : (sStar p c).re = 1 / 2 + Real.log (rootR c) / Real.log p := by
  unfold sStar
  rw [Complex.add_re, Complex.div_ofReal_re]
  simp

/-- **Off-line regime (kernel).** For `p > 1` and `c > 2`, `Q_{p,c}(s*) = 0` with
`Re s* = 1/2 + log r / log p > 1/2`. -/
theorem Qp_offline_zero {p c : ℝ} (hp : 1 < p) (hc : 2 < c) :
    Qp p c (sStar p c) = 0 ∧ 1 / 2 < (sStar p c).re := by
  have hr := rootR_gt_one hc
  have hr0 : 0 < rootR c := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hlogpC : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hlogp.ne'
  refine ⟨?_, ?_⟩
  · unfold Qp sStar
    have hw : (1 / 2 + ((Real.log (rootR c) : ℂ) + π * Complex.I) / (Real.log p : ℂ) - 1 / 2)
        * (Real.log p : ℂ) = (Real.log (rootR c) : ℂ) + π * Complex.I := by
      field_simp; ring
    rw [hw, Complex.exp_neg, Complex.exp_add, Complex.exp_pi_mul_I,
      ← Complex.ofReal_exp, Real.exp_log hr0]
    have hsumC : (rootR c : ℂ) + (rootR c : ℂ)⁻¹ = c := by exact_mod_cast rootR_add_inv hc
    linear_combination -hsumC
  · rw [sStar_re]
    have : 0 < Real.log (rootR c) / Real.log p := div_pos (Real.log_pos hr) hlogp
    linarith

/-- **Off-line zero inside the open critical strip (kernel).** For `p > 1` and
`2 < c < √p + 1/√p`, the zero `s*` satisfies `1/2 < Re s* < 1`. -/
theorem Qp_offline_zero_in_strip {p c : ℝ} (hp : 1 < p) (hc : 2 < c)
    (hc' : c < Real.sqrt p + 1 / Real.sqrt p) :
    Qp p c (sStar p c) = 0 ∧ 1 / 2 < (sStar p c).re ∧ (sStar p c).re < 1 := by
  obtain ⟨h0, hgt⟩ := Qp_offline_zero hp hc
  refine ⟨h0, hgt, ?_⟩
  rw [sStar_re]
  have hr := rootR_gt_one hc
  have hp0 : 0 < p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsp1 : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hp
  have hlt : rootR c < Real.sqrt p := by
    by_contra hge
    rw [not_lt] at hge
    have hsum := rootR_add_inv hc
    have key : Real.sqrt p + (Real.sqrt p)⁻¹ ≤ rootR c + (rootR c)⁻¹ := by
      have hr0 : 0 < rootR c := by linarith
      rw [← sub_nonneg]
      have e : rootR c + (rootR c)⁻¹ - (Real.sqrt p + (Real.sqrt p)⁻¹)
          = (rootR c - Real.sqrt p) * (rootR c * Real.sqrt p - 1) / (rootR c * Real.sqrt p) := by
        field_simp; ring
      rw [e]
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (by linarith)
      nlinarith
    rw [one_div] at hc'
    linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hlog : Real.log (rootR c) < Real.log p / 2 := by
    have : Real.log (rootR c) < Real.log (Real.sqrt p) :=
      Real.log_lt_log (by linarith) hlt
    rwa [Real.log_sqrt hp0.le] at this
  have : Real.log (rootR c) / Real.log p < 1 / 2 := by
    rw [div_lt_iff₀ hlogp]; linarith
  linarith

/-- The completed Mellin transform of `ν_{p,c}`: `Λ_{p,c}(s) = Λ_ζ(s) · Q_{p,c}(s)`. -/
def LambdaP (p c : ℝ) (s : ℂ) : ℂ := completedRiemannZeta s * Qp p c s

/-- **ζ's exact functional equation (kernel).** -/
theorem LambdaP_one_sub (p c : ℝ) (s : ℂ) : LambdaP p c (1 - s) = LambdaP p c s := by
  unfold LambdaP
  rw [completedRiemannZeta_one_sub, Qp_one_sub]

/-- The completion identity: `Λ_{p,c}(s) = Γ_ℝ(s) · (ζ(s) Q_{p,c}(s))` for `s ≠ 0`, `Γ_ℝ(s) ≠ 0`. -/
theorem LambdaP_eq_Gammaℝ_mul (p c : ℝ) {s : ℂ} (hs : s ≠ 0) (hG : Complex.Gammaℝ s ≠ 0) :
    LambdaP p c s = Complex.Gammaℝ s * (riemannZeta s * Qp p c s) := by
  unfold LambdaP
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

/-! ### Every hypothesis of `selfDual_rigidity` except the gap -/

theorem nup_isFiniteMeasureOnCompacts {p : ℝ} (hp : 0 < p) (c : ℝ) :
    IsFiniteMeasureOnCompacts (nup p c) := by
  refine ⟨fun K hK => ?_⟩
  simp only [nup, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩ <;>
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (comb_compact_lt_top (by positivity) hK)

lemma integrable_fej_nup {p : ℝ} (hp : 0 < p) (c : ℝ) : Integrable fej (nup p c) := by
  unfold nup
  refine ((Integrable.add_measure ?_ ?_).add_measure ?_) <;>
    exact (integrable_fej_comb (by positivity)).smul_measure ENNReal.ofReal_ne_top

/-- **The fooling family violates the gap (kernel):** it has an atom at `1/p ∈ (0,1)`. -/
theorem nup_gap_violated {p : ℝ} (hp : 1 < p) (c : ℝ) : nup p c (Ioo (-1) 1 \ {0}) ≠ 0 := by
  have hp0 : 0 < p := by linarith
  have hS : MeasurableSet (Ioo (-1 : ℝ) 1 \ {0}) := measurableSet_Ioo.diff (measurableSet_singleton 0)
  have hmem : (1 / p : ℝ) * ((1 : ℤ) : ℝ) ∈ Ioo (-1 : ℝ) 1 \ {0} := by
    have h1 : 0 < 1 / p := by positivity
    have h2 : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
    refine ⟨⟨by push_cast; linarith, by push_cast; linarith⟩, ?_⟩
    push_cast; simp only [mul_one, mem_singleton_iff]; exact h1.ne'
  have hc1 : 1 ≤ comb (1 / p) (Ioo (-1) 1 \ {0}) := by
    rw [comb_apply _ hS]
    refine le_trans ?_ (ENNReal.le_tsum (1 : ℤ))
    rw [Set.indicator_of_mem hmem]
    simp
  have hpos : 0 < ENNReal.ofReal (1 / Real.sqrt p) :=
    ENNReal.ofReal_pos.mpr (by have := Real.sqrt_pos.mpr hp0; positivity)
  apply ne_of_gt
  calc (0 : ENNReal) < ENNReal.ofReal (1 / Real.sqrt p) * 1 := by simp only [mul_one]; exact hpos
    _ ≤ ENNReal.ofReal (1 / Real.sqrt p) * comb (1 / p) (Ioo (-1) 1 \ {0}) := by gcongr
    _ ≤ nup p c (Ioo (-1) 1 \ {0}) := by
      simp only [nup, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact le_add_right (le_add_right le_rfl)

theorem nup_ne_smul_intComb {p : ℝ} (hp : 1 < p) (c : ℝ) (r : ENNReal) : nup p c ≠ r • intComb := by
  intro h
  have := nup_gap_violated hp c
  rw [h, Measure.smul_apply, intComb_gap, smul_zero] at this
  exact this rfl

lemma nup_atom_zero_ne_zero {p : ℝ} (hp : 0 < p) (c : ℝ) : nup p c {0} ≠ 0 := by
  have hc1 : 1 ≤ comb p {0} := by
    rw [comb_apply _ (measurableSet_singleton 0)]
    refine le_trans ?_ (ENNReal.le_tsum (0 : ℤ))
    simp
  have hpos : 0 < ENNReal.ofReal (Real.sqrt p) :=
    ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hp)
  apply ne_of_gt
  calc (0 : ENNReal) < ENNReal.ofReal (Real.sqrt p) * 1 := by simp only [mul_one]; exact hpos
    _ ≤ ENNReal.ofReal (Real.sqrt p) * comb p {0} := by gcongr
    _ ≤ nup p c {0} := by
      simp only [nup, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact le_add_left le_rfl

/-! ### Mellin/Dirichlet link -/

lemma cpow_div_real {x p : ℝ} (hx : 0 < x) (hp : 0 < p) (s : ℂ) :
    ((x / p : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ (-s) * Complex.exp (s * (Real.log p : ℂ)) := by
  have hxp : (0 : ℝ) < x / p := by positivity
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hxp.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hxp.le, ← Complex.ofReal_log hx.le,
    Real.log_div hx.ne' hp.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cpow_mul_real {x p : ℝ} (hx : 0 < x) (hp : 0 < p) (s : ℂ) :
    ((p * x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ (-s) * Complex.exp (-(s * (Real.log p : ℂ))) := by
  have hxp : (0 : ℝ) < p * x := by positivity
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hxp.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hxp.le, ← Complex.ofReal_log hx.le,
    Real.log_mul hp.ne' hx.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma sqrt_eq_exp {p : ℝ} (hp : 0 < p) :
    ((Real.sqrt p : ℝ) : ℂ) = Complex.exp (1 / 2 * (Real.log p : ℂ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma inv_sqrt_eq_exp {p : ℝ} (hp : 0 < p) :
    ((1 / Real.sqrt p : ℝ) : ℂ) = Complex.exp (-(1 / 2 * (Real.log p : ℂ))) := by
  rw [Complex.exp_neg, ← sqrt_eq_exp hp]
  push_cast
  ring

/-- **Mellin/Dirichlet link (kernel).** For `Re s > 1`, the Dirichlet transform of the positive
half of `ν_{p,c}` (atoms `n/p`, `n`, `pn`, `n ≥ 1`, masses `p^{-1/2}`, `c`, `p^{1/2}`) is
`ζ(s) Q_{p,c}(s)`. -/
theorem nup_dirichlet {p : ℝ} (hp : 0 < p) (c : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ =>
        ((1 / Real.sqrt p : ℝ) : ℂ) * ((((n : ℝ) + 1) / p : ℝ) : ℂ) ^ (-s)
        + (c : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
        + ((Real.sqrt p : ℝ) : ℂ) * ((p * ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s))
      (riemannZeta s * Qp p c s) := by
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    have h2 := (summable_nat_add_iff 1).mpr this
    simpa [Nat.cast_add, Nat.cast_one] using h2
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hsum.hasSum
  have key : ∀ n : ℕ,
      ((1 / Real.sqrt p : ℝ) : ℂ) * ((((n : ℝ) + 1) / p : ℝ) : ℂ) ^ (-s)
        + (c : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
        + ((Real.sqrt p : ℝ) : ℂ) * ((p * ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s)
      = Qp p c s * (1 / ((n : ℂ) + 1) ^ s) := by
    intro n
    have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [cpow_div_real hx hp, cpow_mul_real hx hp, inv_sqrt_eq_exp hp, sqrt_eq_exp hp]
    have e : (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) = 1 / ((n : ℂ) + 1) ^ s := by
      rw [Complex.cpow_neg, one_div]; push_cast; rfl
    rw [e]
    unfold Qp
    have e1 : Complex.exp (-(1 / 2 * (Real.log p : ℂ))) * Complex.exp (s * (Real.log p : ℂ))
        = Complex.exp ((s - 1 / 2) * (Real.log p : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e2 : Complex.exp (1 / 2 * (Real.log p : ℂ)) * Complex.exp (-(s * (Real.log p : ℂ)))
        = Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination (1 / ((n : ℂ) + 1) ^ s) * e1 + (1 / ((n : ℂ) + 1) ^ s) * e2
  have := hz.mul_left (Qp p c s)
  rw [mul_comm (Qp p c s)] at this
  simpa only [key] using this

/-- **Round 1's surgered witness is a member (kernel).** `p^{1/2-s} · Q_{p,c}(s)` is the Euler factor
`1 + c√p·p^{-s} + p·p^{-2s}`; at `p = 29`, `c = 11/√29` this is `1 + 11·29^{-s} + 29·29^{-2s}`,
the factor of `W1(29,11) = ζ(s)(1 + 11·29^{-s} + 29·29^{-2s})`. -/
theorem Qp_euler_factor {p : ℝ} (hp : 0 < p) (c : ℝ) (s : ℂ) :
    Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ))) * Qp p c s
      = 1 + (c * Real.sqrt p : ℝ) * Complex.exp (-(s * (Real.log p : ℂ)))
        + (p : ℂ) * Complex.exp (-(2 * s * (Real.log p : ℂ))) := by
  unfold Qp
  rw [show ((c * Real.sqrt p : ℝ) : ℂ) = (c : ℂ) * ((Real.sqrt p : ℝ) : ℂ) by push_cast; ring,
    sqrt_eq_exp hp]
  have hpC : (p : ℂ) = Complex.exp (Real.log p : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hp]
  rw [hpC]
  have e1 : Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ))) * Complex.exp ((s - 1 / 2) * (Real.log p : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  have e2 : Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ))) = Complex.exp (1 / 2 * (Real.log p : ℂ)) * Complex.exp (-(s * (Real.log p : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e3 : Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ))) * Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ)))
      = Complex.exp (Real.log p : ℂ) * Complex.exp (-(2 * s * (Real.log p : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [mul_add, mul_add, e1, e3]
  rw [e2]
  ring

lemma W1_parameters : 2 < 11 / Real.sqrt 29 ∧ 11 / Real.sqrt 29 < Real.sqrt 29 + 1 / Real.sqrt 29 ∧
    11 / Real.sqrt 29 * Real.sqrt 29 = 11 := by
  have hs : 0 < Real.sqrt 29 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 29 * Real.sqrt 29 = 29 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 29 < 11 / 2 := by
    rw [show (11 / 2 : ℝ) = Real.sqrt ((11 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hs]; linarith
  · rw [div_lt_iff₀ hs, add_mul, div_mul_cancel₀ _ hs.ne', hsq]; norm_num
  · field_simp

/-! ### Sharpness of the pole term: every `β` allowed by positivity is realized -/

/-- `Σ_{n ≠ 0} δ_n`. -/
def combNZ : Measure ℝ :=
  Measure.sum (fun n : ℤ => (if n = 0 then (0 : ENNReal) else 1) • Measure.dirac (n : ℝ))

lemma integral_combNZ (g : ℝ → ℂ) : ∫ x, g x ∂combNZ = ∑' n : ℤ, ite (n = 0) 0 (g n) := by
  rw [combNZ, integral_sum_dirac (fun n => by split_ifs <;> simp)]
  congr 1; funext n; split_ifs <;> simp

/-- **Realizability of the pole footprint (kernel).** For `r ≥ 0`, `c > 0`, the positive measure
`r δ₀ + c Σ_{n≠0} δ_n` (Dirichlet transform `c ζ(s)`) is a Poisson pair with `β = c - r`. Together
with `poisson_rigidity`, the gap-admissible Poisson pairs are exactly these. -/
theorem poissonPair_realizable {r c : ℝ} (hr : 0 ≤ r) (hc : 0 < c) :
    IsPoissonPair (ENNReal.ofReal r • Measure.dirac 0 + ENNReal.ofReal c • combNZ)
      ((c : ℂ) - r) := by
  intro f hcont hcs hint
  rw [integrable_add_measure] at hint
  obtain ⟨h1, h2⟩ := hint
  have h2' : Integrable (𝓕 f) combNZ :=
    (integrable_smul_measure (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top).mp h2
  have hsumNZ : Summable (fun n : ℤ => ite (n = 0) 0 (𝓕 f n)) := by
    have := (show Integrable (𝓕 f) (Measure.sum (fun n : ℤ =>
      (if n = 0 then (0 : ENNReal) else 1) • Measure.dirac (n : ℝ))) from h2').summable_of_dirac
    refine Summable.of_norm (this.congr (fun n => ?_))
    split_ifs with h <;> simp [h]
  have hsum : Summable (fun n : ℤ => 𝓕 f n) := by
    have e : (fun n : ℤ => 𝓕 f (n : ℝ))
        = fun n : ℤ => ite (n = 0) 0 (𝓕 f (n : ℝ)) + ite (n = 0) (𝓕 f 0) 0 := by
      funext n; split_ifs with h <;> simp [h]
    rw [e]
    refine hsumNZ.add (summable_of_ne_finset_zero (s := {0}) (fun n hn => ?_))
    have : n ≠ 0 := by simpa using hn
    simp [this]
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont one_lt_two
    (isBigO_of_hasCompactSupport hcs) hsum 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  have hfs : Summable (fun n : ℤ => f n) := by
    have := summable_norm_comp_mul_of_hasCompactSupport hcs one_pos
    simp only [one_mul] at this
    exact this.of_norm
  have hf1 : Integrable f (ENNReal.ofReal r • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hf2 : Integrable f (ENNReal.ofReal c • combNZ) := by
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [combNZ, integrable_sum_dirac_iff (fun n => by split_ifs <;> simp)]
    have := summable_norm_comp_mul_of_hasCompactSupport hcs one_pos
    simp only [one_mul] at this
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) this
    split_ifs <;> simp
  rw [integral_add_measure h1 h2, integral_add_measure hf1 hf2, integral_smul_measure,
    integral_smul_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, integral_combNZ, integral_combNZ, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal hc.le, fourier_at_zero]
  have e1 := hsum.tsum_eq_add_tsum_ite 0
  have e2 := hfs.tsum_eq_add_tsum_ite 0
  simp only [Int.cast_zero] at e1 e2
  rw [fourier_at_zero] at e1
  simp only [Complex.real_smul]
  have key : ∑' n : ℤ, ite (n = 0) 0 (𝓕 f n) = ∑' n : ℤ, ite (n = 0) 0 (f n) + f 0 - ∫ x, f x := by
    have := hP
    rw [e1, e2] at this
    linear_combination -this
  rw [key]
  ring

/-! ### The onset `c = 2` is local Ramanujan (the one-variable Lee-Yang condition) -/

/-- A root of `z² + c z + 1` with `0 ≤ c ≤ 2` lies on the unit circle. -/
lemma norm_eq_one_of_quadratic {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2) {z : ℂ}
    (hq : z ^ 2 + c * z + 1 = 0) : ‖z‖ = 1 := by
  have hre : z.re ^ 2 - z.im ^ 2 + c * z.re + 1 = 0 := by
    have := congrArg Complex.re hq
    simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.zero_re] at this
    linarith
  have him : z.im * (2 * z.re + c) = 0 := by
    have := congrArg Complex.im hq
    simp only [sq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, Complex.zero_im] at this
    linarith
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    rcases mul_eq_zero.mp him with hy | hx
    · rw [hy] at hre ⊢
      nlinarith [sq_nonneg (2 * z.re + c), mul_nonneg hc0 (sub_nonneg.mpr hc2)]
    · have hx' : z.re = -c / 2 := by linarith
      rw [hx'] at hre ⊢
      nlinarith
  have h2 : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [hsq]
  have := norm_nonneg z
  nlinarith

/-- **The onset is local Ramanujan (kernel).** For `p > 0`, `c ≥ 0`, the Satake parameters of the
surgered local factor `1 + c√p·T + p·T² = (1 - αT)(1 - βT)`, i.e. the roots of
`α² + c√p·α + p`, all have `|α| = √p` iff `c ≤ 2`. By `Qp_zero_re_of_le_two` / `Qp_offline_zero`,
this is exactly the range in which every zero of `Q_{p,c}` lies on the critical line. -/
theorem satake_ramanujan_iff {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) :
    (∀ α : ℂ, α ^ 2 + ((c * Real.sqrt p : ℝ) : ℂ) * α + p = 0 → ‖α‖ = Real.sqrt p) ↔ c ≤ 2 := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hspC : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  have hsq : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hp.le]
  constructor
  · intro h
    by_contra hc2
    rw [not_le] at hc2
    -- the real root α = -√p · r with r = rootR c > 1 has norm √p · r ≠ √p
    set r := rootR c with hr
    have hr1 : 1 < r := rootR_gt_one hc2
    have hrr : r + r⁻¹ = c := rootR_add_inv hc2
    have hr0 : r ≠ 0 := by linarith
    have hroot : ((-(Real.sqrt p * r) : ℝ) : ℂ) ^ 2 + ((c * Real.sqrt p : ℝ) : ℂ)
        * ((-(Real.sqrt p * r) : ℝ) : ℂ) + p = 0 := by
      have hpsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
      have hreal : (-(Real.sqrt p * r)) ^ 2 + (c * Real.sqrt p) * (-(Real.sqrt p * r)) + p = 0 := by
        have hc' : c = r + r⁻¹ := hrr.symm
        rw [hc']
        field_simp
        nlinarith [hpsq]
      exact_mod_cast hreal
    have hn := h _ hroot
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)] at hn
    have : Real.sqrt p * r > Real.sqrt p * 1 := by gcongr
    linarith
  · intro hc2 α hα
    set z : ℂ := α / (Real.sqrt p : ℂ) with hz
    have hαz : α = (Real.sqrt p : ℂ) * z := by rw [hz]; field_simp
    have hq : z ^ 2 + c * z + 1 = 0 := by
      rw [hαz] at hα
      have e : ((Real.sqrt p : ℂ) * z) ^ 2 + ((c * Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℂ) * z) + p
          = (p : ℂ) * (z ^ 2 + c * z + 1) := by
        push_cast
        linear_combination (z ^ 2 + c * z) * hsq
      rw [e] at hα
      have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      exact (mul_eq_zero.mp hα).resolve_left hpC
    have hz1 := norm_eq_one_of_quadratic hc hc2 hq
    rw [hαz, norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]

/-! ## Capstone -/

/-- **CAPSTONE (kernel): crystalline-measure rigidity pins the integers and is blind to zeros.**

(1) [Theorem A, crystalline-measure form] every positive locally finite self-dual Poisson measure
    with the gap `(-1,1) \ {0}` and `sinc²` integrable is `ν{0} • Σ_{n∈ℤ} δ_n`; the comb is
    admissible, so the admissible class is exactly the ray through the comb.

(2) [fooling family] for every `p > 1` and every `c` with `2 < c < √p + 1/√p` the measure `ν_{p,c}`
    (three lattice combs; uniformly discrete support and spectrum) is positive, locally finite,
    `sinc²`-integrable, self-dual, with a positive atom at `0`, not a multiple of the comb; its
    positive half has Dirichlet transform `ζ(s) Q_{p,c}(s)` (`Re s > 1`); its completion
    `Λ_{p,c} = Γ_ℝ ζ Q_{p,c}` satisfies ζ's exact functional equation; and `Λ_{p,c}` vanishes at a
    point with `1/2 < Re s < 1`. The gap is the only hypothesis of (1) it fails. -/
theorem fq_rigidity_is_rh_blind :
    (∀ ν : Measure ℝ, IsLocallyFiniteMeasure ν → IsPoissonPair ν 0 → Integrable fej ν →
        ν (Ioo (-1) 1 \ {0}) = 0 → ν = ν {0} • intComb) ∧
    (IsPoissonPair intComb 0 ∧ Integrable fej intComb ∧ intComb (Ioo (-1) 1 \ {0}) = 0 ∧
        intComb {0} = 1) ∧
    (∀ p c : ℝ, 1 < p → 2 < c → c < Real.sqrt p + 1 / Real.sqrt p →
        IsPoissonPair (nup p c) 0 ∧ IsFiniteMeasureOnCompacts (nup p c) ∧
        Integrable fej (nup p c) ∧ nup p c {0} ≠ 0 ∧ nup p c (Ioo (-1) 1 \ {0}) ≠ 0 ∧
        (∀ r : ENNReal, nup p c ≠ r • intComb) ∧
        (∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ =>
            ((1 / Real.sqrt p : ℝ) : ℂ) * ((((n : ℝ) + 1) / p : ℝ) : ℂ) ^ (-s)
            + (c : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
            + ((Real.sqrt p : ℝ) : ℂ) * ((p * ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s))
          (riemannZeta s * Qp p c s)) ∧
        (∀ s : ℂ, 0 < s.re → LambdaP p c s = Complex.Gammaℝ s * (riemannZeta s * Qp p c s)) ∧
        (∀ s : ℂ, LambdaP p c (1 - s) = LambdaP p c s) ∧
        (LambdaP p c (sStar p c) = 0 ∧ 1 / 2 < (sStar p c).re ∧ (sStar p c).re < 1)) := by
  refine ⟨fun ν hν hP hint hgap => selfDual_rigidity hP hint hgap, intComb_admissible, ?_⟩
  intro p c hp hc hc'
  have hp0 : 0 < p := by linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨hs0, hgt, hlt⟩ := Qp_offline_zero_in_strip hp hc hc'
  refine ⟨nup_isPoissonPair hp0 hc0, nup_isFiniteMeasureOnCompacts hp0 c, integrable_fej_nup hp0 c,
    nup_atom_zero_ne_zero hp0 c, nup_gap_violated hp c, nup_ne_smul_intComb hp c,
    fun s hs => nup_dirichlet hp0 c hs, ?_, LambdaP_one_sub p c, ⟨?_, hgt, hlt⟩⟩
  · intro s hs
    exact LambdaP_eq_Gammaℝ_mul p c (fun h => by rw [h] at hs; simp at hs)
      (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  · unfold LambdaP; rw [hs0, mul_zero]

/-- **Onset control (kernel).** For `p > 1` and `0 < c ≤ 2` the same positive self-dual family has
every zero of its extra factor on the critical line. The crystalline data (positivity,
self-duality, supports) do not change across `c = 2`; the zero location does. -/
theorem fooling_onset {p c : ℝ} (hp : 1 < p) (hc0 : 0 < c) (hc2 : c ≤ 2) :
    IsPoissonPair (nup p c) 0 ∧ ∀ s : ℂ, Qp p c s = 0 → s.re = 1 / 2 :=
  ⟨nup_isPoissonPair (by linarith) hc0, fun _ hs => Qp_zero_re_of_le_two hp hc0.le hc2 hs⟩

/-- **Round 1's `W1(29,11)` is the Mellin transform of a positive self-dual crystalline measure
(kernel).** With `c = 11/√29`: `ν_{29,c}` is a positive self-dual Poisson measure, the Euler factor
of `W1(29,11)` is `29^{1/2-s} Q_{29,c}(s)`, and `Λ_{29,c}` has an off-line zero in the open strip
(numerically at `Re s ≈ 0.5612`, the witness of round 1). -/
theorem W1_as_crystalline :
    IsPoissonPair (nup 29 (11 / Real.sqrt 29)) 0 ∧
    (∀ s : ℂ, Complex.exp (-((s - 1 / 2) * (Real.log 29 : ℂ))) * Qp 29 (11 / Real.sqrt 29) s
      = 1 + 11 * Complex.exp (-(s * (Real.log 29 : ℂ)))
        + 29 * Complex.exp (-(2 * s * (Real.log 29 : ℂ)))) ∧
    (LambdaP 29 (11 / Real.sqrt 29) (sStar 29 (11 / Real.sqrt 29)) = 0 ∧
      1 / 2 < (sStar 29 (11 / Real.sqrt 29)).re ∧ (sStar 29 (11 / Real.sqrt 29)).re < 1) := by
  obtain ⟨h1, h2, h3⟩ := W1_parameters
  have h29 : (1 : ℝ) < 29 := by norm_num
  refine ⟨nup_isPoissonPair (by norm_num) (by linarith), fun s => ?_, ?_⟩
  · rw [Qp_euler_factor (by norm_num) _ s, h3]
    push_cast
    ring
  · obtain ⟨hs0, hgt, hlt⟩ := (fq_rigidity_is_rh_blind.2.2 29 _ h29 h1 h2).2.2.2.2.2.2.2.2.2
    exact ⟨hs0, hgt, hlt⟩

/-- **Round 1's golden fake is a member (kernel).** Its completion factor
`XiA(s) = 2 cosh((s-1/2) log 5) + √5` is `Q_{5,√5}`; so `ξ · XiA` is, up to the polynomial
`s(s-1)/2`, the completed Mellin transform of the positive self-dual crystalline measure
`ν_{5,√5}`, and its off-line zero sits at `Re s = 1/2 + log φ / log 5` with `φ = (1+√5)/2`. -/
theorem golden_as_crystalline :
    IsPoissonPair (nup 5 (Real.sqrt 5)) 0 ∧
    (∀ s : ℂ, Qp 5 (Real.sqrt 5) s
      = 2 * Complex.cosh ((s - 1 / 2) * (Real.log 5 : ℂ)) + (Real.sqrt 5 : ℂ)) ∧
    rootR (Real.sqrt 5) = (1 + Real.sqrt 5) / 2 ∧
    (LambdaP 5 (Real.sqrt 5) (sStar 5 (Real.sqrt 5)) = 0 ∧
      1 / 2 < (sStar 5 (Real.sqrt 5)).re ∧ (sStar 5 (Real.sqrt 5)).re < 1) ∧
    (sStar 5 (Real.sqrt 5)).re = 1 / 2 + Real.log ((1 + Real.sqrt 5) / 2) / Real.log 5 := by
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : 2 < Real.sqrt 5 := by nlinarith
  have hroot : rootR (Real.sqrt 5) = (1 + Real.sqrt 5) / 2 := by
    unfold rootR
    rw [hsq, show (5 : ℝ) - 4 = 1 by norm_num, Real.sqrt_one]
    ring
  have hlt : Real.sqrt 5 < Real.sqrt 5 + 1 / Real.sqrt 5 := by
    have : 0 < 1 / Real.sqrt 5 := by positivity
    linarith
  obtain ⟨hs0, hgt, hlt'⟩ :=
    (fq_rigidity_is_rh_blind.2.2 5 _ (by norm_num) h2 hlt).2.2.2.2.2.2.2.2.2
  refine ⟨nup_isPoissonPair (by norm_num) hs5, fun s => ?_, hroot, ⟨hs0, hgt, hlt'⟩, ?_⟩
  · unfold Qp
    rw [Complex.cosh, Complex.exp_neg]
    ring
  · rw [sStar_re, hroot]

/-! ## Restatements in Mathlib-only vocabulary (guards against rigged definitions) -/

theorem writer_thmA_fq (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hP : ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → Integrable (𝓕 f) ν →
      ∫ ξ, 𝓕 f ξ ∂ν = ∫ x, f x ∂ν)
    (hint : Integrable (fun x : ℝ => Real.sinc (π * x) ^ 2) ν)
    (hgap : ν (Set.Ioo (-1) 1 \ {0}) = 0) :
    ν = ν {0} • Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ)) := by
  have hP' : IsPoissonPair ν 0 := by
    intro f h1 h2 h3; rw [hP f h1 h2 h3]; ring
  have := selfDual_rigidity hP' hint hgap
  rw [this]
  congr 2
  · rw [intComb]; simp only [one_smul]

theorem writer_comb_admissible :
    (∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
      Integrable (𝓕 f) (Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ))) →
      ∫ ξ, 𝓕 f ξ ∂(Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ)))
        = ∫ x, f x ∂(Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ)))) := by
  intro f h1 h2 h3
  have e : Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ)) = intComb := by
    rw [intComb]; simp only [one_smul]
  rw [e] at h3 ⊢
  have := intComb_isPoissonPair f h1 h2 h3
  rw [this]; ring

theorem writer_fourier_triangle (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((max 0 (1 - |x|) : ℝ) : ℂ)) ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) :=
  fourier_tri ξ

theorem writer_selfdual_offline (p c : ℝ) (hp : 1 < p) (hc : 2 < c)
    (hc' : c < Real.sqrt p + 1 / Real.sqrt p) :
    (∀ s : ℂ, completedRiemannZeta (1 - s) *
        (Complex.exp ((1 - s - 1 / 2) * (Real.log p : ℂ)) + c
          + Complex.exp (-((1 - s - 1 / 2) * (Real.log p : ℂ))))
      = completedRiemannZeta s *
        (Complex.exp ((s - 1 / 2) * (Real.log p : ℂ)) + c
          + Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ))))) ∧
    ∃ s : ℂ, 1 / 2 < s.re ∧ s.re < 1 ∧
      completedRiemannZeta s * (Complex.exp ((s - 1 / 2) * (Real.log p : ℂ)) + c
          + Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ)))) = 0 := by
  refine ⟨fun s => LambdaP_one_sub p c s, ?_⟩
  obtain ⟨hs0, hgt, hlt⟩ := Qp_offline_zero_in_strip hp hc hc'
  refine ⟨sStar p c, hgt, hlt, ?_⟩
  have : Qp p c (sStar p c) = 0 := hs0
  unfold Qp at this
  rw [this, mul_zero]

end CruxFQ

#print axioms CruxFQ.fourier_tri
#print axioms CruxFQ.poisson_rigidity
#print axioms CruxFQ.selfDual_rigidity
#print axioms CruxFQ.gap_gt_one_forces_zero
#print axioms CruxFQ.translation_bounded_of_poissonPair
#print axioms CruxFQ.intComb_admissible
#print axioms CruxFQ.comb_poisson
#print axioms CruxFQ.nup_isPoissonPair
#print axioms CruxFQ.Qp_zero_re_of_le_two
#print axioms CruxFQ.Qp_offline_zero
#print axioms CruxFQ.Qp_offline_zero_in_strip
#print axioms CruxFQ.LambdaP_one_sub
#print axioms CruxFQ.LambdaP_eq_Gammaℝ_mul
#print axioms CruxFQ.integrable_fej_nup
#print axioms CruxFQ.nup_gap_violated
#print axioms CruxFQ.nup_ne_smul_intComb
#print axioms CruxFQ.nup_atom_zero_ne_zero
#print axioms CruxFQ.nup_dirichlet
#print axioms CruxFQ.Qp_euler_factor
#print axioms CruxFQ.W1_parameters
#print axioms CruxFQ.poissonPair_realizable
#print axioms CruxFQ.satake_ramanujan_iff
#print axioms CruxFQ.fq_rigidity_is_rh_blind
#print axioms CruxFQ.fooling_onset
#print axioms CruxFQ.W1_as_crystalline
#print axioms CruxFQ.golden_as_crystalline
#print axioms CruxFQ.writer_thmA_fq
#print axioms CruxFQ.writer_comb_admissible
#print axioms CruxFQ.writer_fourier_triangle
#print axioms CruxFQ.writer_selfdual_offline
