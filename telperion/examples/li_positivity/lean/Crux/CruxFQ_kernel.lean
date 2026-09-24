/-
CruxFQ_kernel.lean -- crux-fq workflow, KERNEL builder (round 2, "Theorem A as a crystalline-measure
rigidity, complete in the kernel, and a kernel proof that this rigidity cannot see zeros").

conjecture1_proved = False. Nothing here bears on where the zeros of `riemannZeta` lie, and nothing
here reduces RH to anything.

Checked by: `cd telperion/examples/li_positivity/lean && leanlock.sh lake env lean Crux/CruxFQ_kernel.lean`
(Lean v4.34.0-rc1, Mathlib de5ce8a9). Self-contained: imports only Mathlib. No `sorry`, `admit`,
`native_decide`, new `axiom`, or `opaque`. Every `#print axioms` line at the end reports exactly
`[propext, Classical.choice, Quot.sound]`.

PROVENANCE. Part 0 re-states, verbatim up to the namespace `CruxFQK`, the Theorem-A core of the seat file
`Crux/CruxFQ_PoissonRigidity.lean` (Fejer pair, `IsPoissonPair`, Steps 3-4, the comb, the fooling family
`ν_{p,c}` and its Mellin side); the islands build Crux files one at a time, so it cannot be imported.
Parts 1-10 are new.

WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
 1. EVEN-TEST REDUCTION (`isPoissonPair_of_even`): for a negation-invariant `ν`, the Poisson identity on
    even `C_c` tests implies it on all `C_c` tests.
 2. GAUSSIAN DETERMINATION (`isPoissonPair_of_theta`): for a positive, locally finite, even measure `ν`
    with every Gaussian integrable, the MODULAR RELATION
        `θ_ν(1/t) = √t θ_ν(t) + β(√t - 1)`  for all `t > 0`,   `θ_ν(t) = ∫ e^{-π t x²} dν(x)`,
    implies `IsPoissonPair ν β`, i.e. `ν̂ = ν + β(δ₀ - Leb)` on EVERY continuous compactly supported
    test with `ν`-integrable transform. This closes, in the kernel, the "Gaussian/Schwartz to `C_c`"
    substrate gap named by the seat and removes the seat file's CAVEAT (the `C_c` form was assumed).
    Proof: a Gaussian-regularized defect `T_s(h) = T(h * G_s)` vanishes on every Gaussian (the theta
    relation at `st/(s+t)`, `Tdef_gauss`), is bounded by `C·K_s` on `e^{-πx²}`-dominated tests
    (`norm_Tdef_le`), hence vanishes on every even `C_c` test by Weierstrass approximation in the
    variable `z = e^{-πx²}` (`exists_gauss_poly_approx`, `Tdef_even_eq_zero`); and `√s T_s(f) → T(f)`
    as `s → ∞` (approximate identity, `tendsto_sqrt_mul_Tdef`). Only real Gaussians are used.
 3. THEOREM A FROM THE MODULAR RELATION ALONE (`thmA_theta`, `thmA_theta_selfDual`): positive, locally
    finite, even, Gaussian-integrable, no mass in `(-1,1) \ {0}`, and the modular relation imply: `ν` is
    carried by `ℤ`, `ν{m} = ν{0} + β` for `m ≠ 0`, `ν` is the sum of its atoms; for `β = 0`,
    `ν = ν{0} • Σ_{n∈ℤ} δ_n`. `sinc²`-integrability is DERIVED (`integrable_fej_of_theta`, from the
    growth bound `θ_ν(4^{-i}) ≤ 2^i(θ_ν(1) + 2‖β‖)` the relation itself gives). Also in theta form: the
    LP-sharpness (`theta_gap_gt_one_forces_zero`) and translation boundedness
    (`translation_bounded_of_theta`).
 4. POSITIVE CONTROL (`intComb_theta_admissible`): the integer comb satisfies every hypothesis (Jacobi's
    identity via Mathlib's Gaussian Poisson summation); its `C_c` Poisson identity is RE-DERIVED from
    Jacobi by item 2.
 5. RH-BLINDNESS IN THETA FORM (`theta_rigidity_is_rh_blind`, `theta_fooling_onset`,
    `controls_in_theta_form`): the fooling family `ν_{p,c}` satisfies Jacobi's relation EXACTLY, is even,
    positive, locally finite, Gaussian-integrable, and (re-derived via item 2,
    `nup_isPoissonPair_via_theta`) self-dual on `C_c`; its completed Mellin transform `Λ_ζ · Q_{p,c}`
    has ζ's exact FE and, for `2 < c < √p + 1/√p`, a zero with `1/2 < Re s < 1`. Round 1's W1(29,11) and
    golden fake are members. The onset `c = 2` is local Ramanujan.
 6. ROUND 1's MILESTONE NT4 REDUCED TO THE CLASSICAL CONVERSE (`classP_collapse_beurling_q1_of_theta`,
    `classP_collapse_beurling_q1_of_hamburgerConverse`): with the registry definitions
    `BeurlingNormalized` and `ZetaShapeFE` copied verbatim from RH_AXIOM_ISOLATION_2026-09-22 §5.2, a
    normalized Beurling measure `N` whose even extension `δ₀ + N + N(-·)` satisfies the modular relation
    (any `β`) is `Σ_{n≥1} δ_n` (Gaussian integrability derived from the polynomial growth,
    `integrable_gauss_of_beurling`). Hence `classP_collapse_beurling_q1` follows from `HamburgerConverse`
    ("the FE gives the modular relation, or its anti-version when the root number is -1"), a `Prop`
    stated here and NOT proved; its content is Mellin inversion plus a contour shift, with no positivity.
 7. THE ROOT NUMBER IS FORCED (`no_antiTheta`, `step2_of_hamburgerConverse`): the registry's `ZetaShapeFE`
    quantifies the root number `ε` existentially, and Theorem A's Fejer mechanism says nothing about the
    `ε = -1` branch `θ_ν(t) + t^{-1/2}θ_ν(1/t) = c(1 + t^{-1/2})` (`ν̂ = -ν + c(δ₀ + Leb)`). It is excluded
    in the kernel for every positive locally finite measure with the gap and an atom at `1`: the
    self-dual LP test `K = 2G_1 - G_4 - G_{1/4}/2` has `K(0) = 1/2` and `K ≤ -G_4` on `|x| ≥ 1`, while two
    instances of the relation force `∫ K dν = θ_ν(1)/2 ≥ (ν{0} + e^{-π}ν{1})/2`.

WHAT THIS FILE DOES NOT ESTABLISH:
 - `HamburgerConverse` (Hamburger/Bochner, both root numbers): "`s(s-1)Γ_ℝ(s) ∫ x^{-s} dN` entire of
    finite order with the FE implies the modular relation (or its anti-version) for `δ₀ + N + N(-·)`". It
    is the ONLY unformalized step between the registry statement `classP_collapse_beurling_q1` and this
    file (Mellin inversion, vertical Gamma decay, Phragmen-Lindelof in the strip, a contour shift; applying
    `(t d/dt)(4 t d/dt + 2)` to the theta function first removes both poles, so no residue theorem is
    needed). The converse direction (modular relation implies FE) is Mathlib's `WeakFEPair` machinery and
    is not wired here.
 - The converse of item 2 (`IsPoissonPair` implies the modular relation) is not formalized.
 - Anything about the zeros of `riemannZeta`, RH, or any zero-side (Guinand-Weil) rigidity. Items 3 and 5
    together say the opposite: the rigidity pins the prime side and is zero-blind.
 - Novelty of Theorem A (theta form) as a published statement is NOT asserted (expert check pending).
-/
import Mathlib

open MeasureTheory Real Complex Set
open scoped FourierTransform

noncomputable section

namespace CruxFQK

/-! ## Part 0. Theorem A, crystalline form (seat core, re-stated from `CruxFQ_PoissonRigidity.lean`) -/

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

/-! ## Part 0b. The fooling family and its Mellin side (seat core, re-stated) -/

/-! ## K2: positive self-dual crystalline measures without the gap (the fooling family) -/

/-- The dilated comb `Σ_{n∈ℤ} δ_{a n}`. -/
def comb (a : ℝ) : Measure ℝ := Measure.sum (fun n : ℤ => (1 : ENNReal) • Measure.dirac (a * n))

lemma integral_comb (a : ℝ) (g : ℝ → ℂ) : ∫ x, g x ∂comb a = ∑' n : ℤ, g (a * n) := by
  rw [comb, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  simp
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
/-- The fooling family with base `p > 1`:
`ν_{p,c} = p^{-1/2} comb(1/p) + c comb(1) + p^{1/2} comb(p)`.
Its positive half has Dirichlet transform `ζ(s) (p^{s-1/2} + c + p^{1/2-s})`; for `p = 29`,
`c = 11/√29` this is `29^{s-1/2}` times round 1's surgered witness `W1(29,11)`. -/
def nup (p c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / Real.sqrt p) • comb (1 / p) + ENNReal.ofReal c • comb 1
    + ENNReal.ofReal (Real.sqrt p) • comb p
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

open Filter Topology

/-! ## Part 1. Gaussian toolkit and Fourier helpers -/

/-- The Gaussian `G_t(x) = e^{-π t x²}`. -/
def gauss (t x : ℝ) : ℝ := Real.exp (-π * t * x ^ 2)

lemma gauss_pos (t x : ℝ) : 0 < gauss t x := Real.exp_pos _

lemma gauss_nonneg (t x : ℝ) : 0 ≤ gauss t x := (gauss_pos t x).le

lemma gauss_zero (t : ℝ) : gauss t 0 = 1 := by simp [gauss]

lemma gauss_neg (t x : ℝ) : gauss t (-x) = gauss t x := by simp [gauss]

lemma gauss_le_one {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : gauss t x ≤ 1 := by
  unfold gauss
  rw [Real.exp_le_one_iff]
  have := mul_nonneg (mul_nonneg pi_pos.le ht) (sq_nonneg x)
  linarith

lemma gauss_anti {t t' : ℝ} (h : t ≤ t') (x : ℝ) : gauss t' x ≤ gauss t x := by
  unfold gauss
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h pi_pos.le) (sq_nonneg x)
  linarith

lemma gauss_mul (s t x : ℝ) : gauss s x * gauss t x = gauss (s + t) x := by
  unfold gauss; rw [← Real.exp_add]; ring_nf

lemma continuous_gauss (t : ℝ) : Continuous (gauss t) := by unfold gauss; fun_prop

lemma integrable_gauss {t : ℝ} (ht : 0 < t) : Integrable (gauss t) := by
  have := integrable_exp_neg_mul_sq (b := π * t) (by positivity)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [gauss]; ring_nf

lemma integral_gauss {t : ℝ} (ht : 0 < t) : ∫ x, gauss t x = (Real.sqrt t)⁻¹ := by
  have h := integral_gaussian (π * t)
  have e : (fun x : ℝ => gauss t x) = fun x : ℝ => Real.exp (-(π * t) * x ^ 2) := by
    funext x; simp only [gauss]; ring_nf
  rw [e, h, show π / (π * t) = t⁻¹ by field_simp, Real.sqrt_inv]

/-- Gaussian convolution: `∫ G_t(a) G_s(x - a) da = (s+t)^{-1/2} G_{st/(s+t)}(x)`. -/
lemma gauss_conv {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    ∫ a, gauss t a * gauss s (x - a) = (Real.sqrt (s + t))⁻¹ * gauss (s * t / (s + t)) x := by
  have hst : 0 < s + t := by linarith
  have key : ∀ a, gauss t a * gauss s (x - a)
      = gauss (s + t) (a - s * x / (s + t)) * gauss (s * t / (s + t)) x := by
    intro a
    unfold gauss
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [key]
  rw [integral_mul_const, integral_sub_right_eq_self (fun a => gauss (s + t) a),
    integral_gauss hst]

lemma sqrt_cpow_half {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt t : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht]
  norm_num

/-- Fourier transform of the Gaussian: `𝓕 G_t = t^{-1/2} G_{1/t}`. -/
lemma fourier_gauss {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((gauss t x : ℝ) : ℂ)) ξ = (((Real.sqrt t)⁻¹ * gauss (1 / t) ξ : ℝ) : ℂ) := by
  have h := congrFun (fourier_gaussian_pi (b := (t : ℂ)) (by simpa using ht)) ξ
  have e1 : (fun x : ℝ => ((gauss t x : ℝ) : ℂ)) = fun x : ℝ => cexp (-↑π * (t : ℂ) * ↑x ^ 2) := by
    funext x
    simp only [gauss, Complex.ofReal_exp]
    push_cast; ring_nf
  rw [e1, h, sqrt_cpow_half ht.le]
  simp only [gauss, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv]
  push_cast
  ring_nf

lemma integrable_exp_smul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • f v) := by
  have hn : ∀ v : ℝ, ‖Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • f v‖ = ‖f v‖ := by
    intro v; rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Integrable.mono' hf.norm ?_ (ae_of_all _ fun v => le_of_eq (hn v))
  exact (by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I)).aestronglyMeasurable.smul
    hf.aestronglyMeasurable

lemma fourier_add_of_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_add (integrable_exp_smul hf ξ)
      (integrable_exp_smul hg ξ)]
  congr 1; funext v; rw [smul_add]

lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  congr 1; funext v; simp only [smul_eq_mul]; ring

lemma norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext v; rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf



/-! ## Part 2. Even-test reduction -/

/-- The Poisson identity tested only on EVEN compactly supported continuous functions. -/
def IsPoissonPairEven (ν : Measure ℝ) (β : ℂ) : Prop :=
  ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → (∀ x, f (-x) = f x) → Integrable (𝓕 f) ν →
    ∫ ξ, 𝓕 f ξ ∂ν = ∫ x, f x ∂ν + β * (f 0 - ∫ x, f x)

lemma fourier_comp_neg (f : ℝ → ℂ) (ξ : ℝ) : 𝓕 (fun x => f (-x)) ξ = 𝓕 f (-ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_neg_eq_self (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • f (-v))]
  congr 1; funext v
  simp only [neg_neg]
  congr 3
  push_cast; ring


/-- **Even-test reduction (kernel).** For a negation-invariant measure `ν`, the Poisson identity on
even tests implies it on all tests. -/
theorem isPoissonPair_of_even {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant]
    {β : ℂ} (h : IsPoissonPairEven ν β) : IsPoissonPair ν β := by
  intro f hc hcs hF
  set fe : ℝ → ℂ := fun x => (1 / 2 : ℂ) * (f x + f (-x)) with hfe
  have hcn : Continuous fun x => f (-x) := hc.comp continuous_neg
  have hcsn : HasCompactSupport fun x => f (-x) := hcs.comp_homeomorph (Homeomorph.neg ℝ)
  have hfi : Integrable f := hc.integrable_of_hasCompactSupport hcs
  have hfni : Integrable fun x => f (-x) := hcn.integrable_of_hasCompactSupport hcsn
  have hfec : Continuous fe := by simp only [hfe]; fun_prop
  have hfecs : HasCompactSupport fe := by
    simp only [hfe]
    exact (hcs.add hcsn).mul_left
  have hfeven : ∀ x, fe (-x) = fe x := by intro x; simp only [hfe, neg_neg]; ring
  have hFe : ∀ ξ, 𝓕 fe ξ = (1 / 2 : ℂ) * (𝓕 f ξ + 𝓕 f (-ξ)) := by
    intro ξ
    rw [hfe, fourier_const_mul, fourier_add_of_integrable hfi hfni, fourier_comp_neg]
  have hFint : Integrable (𝓕 fe) ν := by
    have : 𝓕 fe = fun ξ => (1 / 2 : ℂ) * (𝓕 f ξ + 𝓕 f (-ξ)) := funext hFe
    rw [this]
    exact (hF.add hF.comp_neg).const_mul _
  have key := h fe hfec hfecs hfeven hFint
  have hfν : Integrable f ν := hc.integrable_of_hasCompactSupport hcs
  have e1 : ∫ ξ, 𝓕 fe ξ ∂ν = ∫ ξ, 𝓕 f ξ ∂ν := by
    simp_rw [hFe]
    rw [integral_const_mul, integral_add hF hF.comp_neg, integral_neg_eq_self (𝓕 f) ν]
    ring
  have e2 : ∫ x, fe x ∂ν = ∫ x, f x ∂ν := by
    simp only [hfe]
    rw [integral_const_mul, integral_add hfν hfν.comp_neg, integral_neg_eq_self f ν]
    ring
  have e3 : fe 0 = f 0 := by simp only [hfe, neg_zero]; ring
  have e4 : ∫ x, fe x = ∫ x, f x := by
    simp only [hfe]
    rw [integral_const_mul, integral_add hfi hfni, integral_neg_eq_self f volume]
    ring
  rw [e1, e2, e3, e4] at key
  exact key



/-! ## The modular (theta) relation and the regularized defect `T_s` -/

/-- `mθ ν t = ∫ e^{-π t x²} dν(x)`, the theta function of the measure `ν`. -/
def mθ (ν : Measure ℝ) (t : ℝ) : ℝ := ∫ x, gauss t x ∂ν

/-- Every Gaussian is `ν`-integrable. -/
def GaussIntegrable (ν : Measure ℝ) : Prop := ∀ t : ℝ, 0 < t → Integrable (gauss t) ν

/-- **The modular (theta) relation with pole footprint `β`:**
`θ_ν(1/t) = √t θ_ν(t) + β (√t - 1)` for all `t > 0`. This is the Poisson identity tested on the
centred Gaussians only. For the integer comb it is Jacobi's `θ(1/t) = √t θ(t)` (`β = 0`). -/
def ThetaRelation (ν : Measure ℝ) (β : ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → ((mθ ν (1 / t) : ℝ) : ℂ)
    = (Real.sqrt t : ℂ) * (mθ ν t : ℂ) + β * ((Real.sqrt t : ℂ) - 1)

/-- Gaussian smoothing `(h * G_s)(x) = ∫ h(a) e^{-π s (x - a)²} da`. -/
def gconv (s : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ := ∫ a, h a * (gauss s (x - a) : ℂ)

/-- The Gaussian-regularized Poisson defect `T_s(h) = T(h * G_s)`, written out:
`s^{-1/2} ∫ G_{1/s} 𝓕h dν - ∫ (h * G_s) dν - β ((h * G_s)(0) - s^{-1/2} ∫ h)`. -/
def Tdef (ν : Measure ℝ) (β : ℂ) (s : ℝ) (h : ℝ → ℂ) : ℂ :=
  (Real.sqrt s : ℂ)⁻¹ * (∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 h ξ ∂ν) - (∫ x, gconv s h x ∂ν)
    - β * (gconv s h 0 - (Real.sqrt s : ℂ)⁻¹ * ∫ a, h a)

/-- Gaussian domination `‖h x‖ ≤ C e^{-π x²}`, with continuity. -/
def GDom (C : ℝ) (h : ℝ → ℂ) : Prop := Continuous h ∧ ∀ x, ‖h x‖ ≤ C * gauss 1 x

namespace GDom

variable {C : ℝ} {h : ℝ → ℂ}

lemma nonneg (hh : GDom C h) : 0 ≤ C := by
  have h0 := hh.2 0
  rw [gauss_zero, mul_one] at h0
  exact (norm_nonneg _).trans h0

lemma integrable (hh : GDom C h) : Integrable h := by
  refine Integrable.mono' ((integrable_gauss one_pos).const_mul C) hh.1.aestronglyMeasurable
    (ae_of_all _ hh.2)

lemma integral_norm_le (hh : GDom C h) : ∫ x, ‖h x‖ ≤ C := by
  calc ∫ x, ‖h x‖ ≤ ∫ x, C * gauss 1 x :=
        integral_mono hh.integrable.norm ((integrable_gauss one_pos).const_mul C) hh.2
    _ = C := by rw [integral_const_mul, integral_gauss one_pos, Real.sqrt_one, inv_one, mul_one]

lemma norm_fourier_le' (hh : GDom C h) (ξ : ℝ) : ‖𝓕 h ξ‖ ≤ C :=
  (norm_fourier_le h ξ).trans hh.integral_norm_le

lemma integrable_conv (hh : GDom C h) (s x : ℝ) (hs : 0 ≤ s) :
    Integrable (fun a => h a * (gauss s (x - a) : ℂ)) := by
  refine Integrable.mono' ((integrable_gauss one_pos).const_mul C) ?_ (ae_of_all _ fun a => ?_)
  · exact (hh.1.mul (Complex.continuous_ofReal.comp
      ((continuous_gauss s).comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _)]
    calc ‖h a‖ * gauss s (x - a) ≤ (C * gauss 1 a) * 1 :=
          mul_le_mul (hh.2 a) (gauss_le_one hs _) (gauss_nonneg _ _)
            (mul_nonneg hh.nonneg (gauss_nonneg _ _))
      _ = C * gauss 1 a := mul_one _

lemma norm_gconv_le (hh : GDom C h) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ‖gconv s h x‖ ≤ C * ((Real.sqrt (s + 1))⁻¹ * gauss (s * 1 / (s + 1)) x) := by
  unfold gconv
  have hb : ∀ a, ‖h a * (gauss s (x - a) : ℂ)‖ ≤ C * (gauss 1 a * gauss s (x - a)) := by
    intro a
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hh.2 a) (gauss_nonneg _ _)
  have hint : Integrable (fun a => gauss 1 a * gauss s (x - a)) := by
    refine Integrable.mono' (integrable_gauss one_pos) ?_ (ae_of_all _ fun a => ?_)
    · exact ((continuous_gauss 1).mul
        ((continuous_gauss s).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (gauss_nonneg _ _) (gauss_nonneg _ _))]
      calc gauss 1 a * gauss s (x - a) ≤ gauss 1 a * 1 :=
            mul_le_mul_of_nonneg_left (gauss_le_one hs.le _) (gauss_nonneg _ _)
        _ = gauss 1 a := mul_one _
  refine (norm_integral_le_of_norm_le (hint.const_mul C) (ae_of_all _ hb)).trans (le_of_eq ?_)
  rw [integral_const_mul, gauss_conv hs one_pos]

lemma continuous_gconv (hh : GDom C h) {s : ℝ} (hs : 0 ≤ s) : Continuous (gconv s h) := by
  unfold gconv
  refine continuous_of_dominated (bound := fun a => C * gauss 1 a) (fun x => ?_) (fun x => ?_)
    ((integrable_gauss one_pos).const_mul C) (ae_of_all _ fun a => ?_)
  · exact (hh.integrable_conv s x hs).aestronglyMeasurable
  · refine ae_of_all _ fun a => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _)]
    calc ‖h a‖ * gauss s (x - a) ≤ (C * gauss 1 a) * 1 :=
          mul_le_mul (hh.2 a) (gauss_le_one hs _) (gauss_nonneg _ _)
            (mul_nonneg hh.nonneg (gauss_nonneg _ _))
      _ = C * gauss 1 a := mul_one _
  · exact continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_gauss s).comp (continuous_id.sub continuous_const)))

lemma integrable_gconv (hh : GDom C h) {ν : Measure ℝ} (hν : GaussIntegrable ν) {s : ℝ}
    (hs : 0 < s) : Integrable (gconv s h) ν := by
  refine Integrable.mono' ((hν (s * 1 / (s + 1)) (by positivity)).const_mul (C * (Real.sqrt (s + 1))⁻¹))
    (hh.continuous_gconv hs.le).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  refine (hh.norm_gconv_le hs x).trans (le_of_eq ?_)
  ring

lemma integrable_fourier_weight (hh : GDom C h) {ν : Measure ℝ} (hν : GaussIntegrable ν) {s : ℝ}
    (hs : 0 < s) : Integrable (fun ξ => (gauss (1 / s) ξ : ℂ) * 𝓕 h ξ) ν := by
  refine Integrable.mono' ((hν (1 / s) (by positivity)).mul_const C) ?_ (ae_of_all _ fun ξ => ?_)
  · exact ((Complex.continuous_ofReal.comp (continuous_gauss _)).mul
      (continuous_fourier_of_integrable hh.integrable)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (hh.norm_fourier_le' ξ) (gauss_nonneg _ _)

lemma add {C₁ C₂ : ℝ} {h₁ h₂ : ℝ → ℂ} (hh₁ : GDom C₁ h₁) (hh₂ : GDom C₂ h₂) :
    GDom (C₁ + C₂) (fun x => h₁ x + h₂ x) :=
  ⟨hh₁.1.add hh₂.1, fun x => (norm_add_le _ _).trans (by
    have := hh₁.2 x; have := hh₂.2 x; nlinarith)⟩

lemma const_mul (hh : GDom C h) (c : ℂ) : GDom (‖c‖ * C) (fun x => c * h x) :=
  ⟨continuous_const.mul hh.1, fun x => by
    rw [norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hh.2 x) (norm_nonneg _)⟩

end GDom

lemma gdom_gauss {t : ℝ} (ht : 1 ≤ t) : GDom 1 (fun x => (gauss t x : ℂ)) :=
  ⟨Complex.continuous_ofReal.comp (continuous_gauss t), fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _), one_mul]
    exact gauss_anti ht x⟩

/-! ### Linearity and the uniform bound -/

theorem Tdef_add {ν : Measure ℝ} {β : ℂ} (hν : GaussIntegrable ν) {s : ℝ} (hs : 0 < s)
    {C₁ C₂ : ℝ} {h₁ h₂ : ℝ → ℂ} (hh₁ : GDom C₁ h₁) (hh₂ : GDom C₂ h₂) :
    Tdef ν β s (fun x => h₁ x + h₂ x) = Tdef ν β s h₁ + Tdef ν β s h₂ := by
  have hF : ∀ ξ, 𝓕 (fun x => h₁ x + h₂ x) ξ = 𝓕 h₁ ξ + 𝓕 h₂ ξ :=
    fourier_add_of_integrable hh₁.integrable hh₂.integrable
  have hG : ∀ x, gconv s (fun x => h₁ x + h₂ x) x = gconv s h₁ x + gconv s h₂ x := by
    intro x; unfold gconv
    rw [← integral_add (hh₁.integrable_conv s x hs.le) (hh₂.integrable_conv s x hs.le)]
    congr 1; funext a; ring
  unfold Tdef
  simp_rw [hF, hG, mul_add]
  rw [integral_add (hh₁.integrable_fourier_weight hν hs) (hh₂.integrable_fourier_weight hν hs),
    integral_add (hh₁.integrable_gconv hν hs) (hh₂.integrable_gconv hν hs),
    integral_add hh₁.integrable hh₂.integrable]
  ring

theorem Tdef_const_mul {ν : Measure ℝ} {β : ℂ} {s : ℝ} (c : ℂ) (h : ℝ → ℂ) :
    Tdef ν β s (fun x => c * h x) = c * Tdef ν β s h := by
  have hF : ∀ ξ, 𝓕 (fun x => c * h x) ξ = c * 𝓕 h ξ := fourier_const_mul c h
  have hG : ∀ x, gconv s (fun x => c * h x) x = c * gconv s h x := by
    intro x; unfold gconv
    rw [← integral_const_mul]
    congr 1; funext a; ring
  unfold Tdef
  simp_rw [hF, hG]
  have e1 : ∫ ξ, (gauss (1 / s) ξ : ℂ) * (c * 𝓕 h ξ) ∂ν = c * ∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 h ξ ∂ν := by
    rw [← integral_const_mul]; congr 1; funext ξ; ring
  rw [e1, integral_const_mul, integral_const_mul]
  ring

/-- The constant in the uniform bound for `T_s`. -/
def Kconst (ν : Measure ℝ) (β : ℂ) (s : ℝ) : ℝ :=
  (Real.sqrt s)⁻¹ * mθ ν (1 / s) + (Real.sqrt (s + 1))⁻¹ * mθ ν (s * 1 / (s + 1))
    + ‖β‖ * (1 + (Real.sqrt s)⁻¹)

theorem norm_Tdef_le {ν : Measure ℝ} {β : ℂ} (hν : GaussIntegrable ν) {s : ℝ} (hs : 0 < s)
    {C : ℝ} {h : ℝ → ℂ} (hh : GDom C h) : ‖Tdef ν β s h‖ ≤ C * Kconst ν β s := by
  have hC := hh.nonneg
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq1 : 0 < Real.sqrt (s + 1) := Real.sqrt_pos.mpr (by linarith)
  have hsq1' : (Real.sqrt (s + 1))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hsq1]
    have : Real.sqrt 1 ≤ Real.sqrt (s + 1) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at this
  -- term 1
  have t1 : ‖(Real.sqrt s : ℂ)⁻¹ * ∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 h ξ ∂ν‖
      ≤ C * ((Real.sqrt s)⁻¹ * mθ ν (1 / s)) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hsq.le]
    have : ‖∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 h ξ ∂ν‖ ≤ ∫ ξ, gauss (1 / s) ξ * C ∂ν := by
      refine norm_integral_le_of_norm_le ((hν _ (by positivity)).mul_const C) (ae_of_all _ fun ξ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (hh.norm_fourier_le' ξ) (gauss_nonneg _ _)
    rw [integral_mul_const] at this
    unfold mθ
    calc (Real.sqrt s)⁻¹ * ‖∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 h ξ ∂ν‖
        ≤ (Real.sqrt s)⁻¹ * ((∫ ξ, gauss (1 / s) ξ ∂ν) * C) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hsq.le)
      _ = C * ((Real.sqrt s)⁻¹ * ∫ x, gauss (1 / s) x ∂ν) := by ring
  -- term 2
  have t2 : ‖∫ x, gconv s h x ∂ν‖ ≤ C * ((Real.sqrt (s + 1))⁻¹ * mθ ν (s * 1 / (s + 1))) := by
    have := norm_integral_le_of_norm_le
      (((hν (s * 1 / (s + 1)) (by positivity)).const_mul ((Real.sqrt (s + 1))⁻¹)).const_mul C)
      (ae_of_all ν (hh.norm_gconv_le hs))
    rw [integral_const_mul, integral_const_mul] at this
    exact this
  -- term 3
  have t3 : ‖β * (gconv s h 0 - (Real.sqrt s : ℂ)⁻¹ * ∫ a, h a)‖ ≤ C * (‖β‖ * (1 + (Real.sqrt s)⁻¹)) := by
    rw [norm_mul]
    have g0 : ‖gconv s h 0‖ ≤ C := by
      refine (hh.norm_gconv_le hs 0).trans ?_
      have := gauss_le_one (t := s * 1 / (s + 1)) (by positivity) 0
      calc C * ((Real.sqrt (s + 1))⁻¹ * gauss (s * 1 / (s + 1)) 0) ≤ C * 1 :=
            mul_le_mul_of_nonneg_left (mul_le_one₀ hsq1' (gauss_nonneg _ _) this) hC
      _ = C := mul_one C
    have g1 : ‖(Real.sqrt s : ℂ)⁻¹ * ∫ a, h a‖ ≤ (Real.sqrt s)⁻¹ * C := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hsq.le]
      exact mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hh.integral_norm_le)
        (inv_nonneg.mpr hsq.le)
    calc ‖β‖ * ‖gconv s h 0 - (Real.sqrt s : ℂ)⁻¹ * ∫ a, h a‖
        ≤ ‖β‖ * (C + (Real.sqrt s)⁻¹ * C) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add g0 g1)) (norm_nonneg _)
      _ = C * (‖β‖ * (1 + (Real.sqrt s)⁻¹)) := by ring
  unfold Tdef Kconst
  calc _ ≤ ‖(Real.sqrt s : ℂ)⁻¹ * ∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 h ξ ∂ν‖
        + ‖∫ x, gconv s h x ∂ν‖ + ‖β * (gconv s h 0 - (Real.sqrt s : ℂ)⁻¹ * ∫ a, h a)‖ := by
        refine (norm_sub_le _ _).trans ?_
        exact add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ C * ((Real.sqrt s)⁻¹ * mθ ν (1 / s)) + C * ((Real.sqrt (s + 1))⁻¹ * mθ ν (s * 1 / (s + 1)))
        + C * (‖β‖ * (1 + (Real.sqrt s)⁻¹)) := add_le_add (add_le_add t1 t2) t3
    _ = _ := by ring

/-! ### `T_s` vanishes on every Gaussian (this is where the theta relation enters) -/

theorem Tdef_gauss {ν : Measure ℝ} {β : ℂ} (hθ : ThetaRelation ν β)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : Tdef ν β s (fun x => (gauss t x : ℂ)) = 0 := by
  have hst : 0 < s + t := by linarith
  have hF : ∀ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 (fun x => (gauss t x : ℂ)) ξ
      = (((Real.sqrt t)⁻¹ * gauss (1 / s + 1 / t) ξ : ℝ) : ℂ) := by
    intro ξ
    rw [fourier_gauss ht, ← gauss_mul]
    push_cast; ring
  have h1 : ∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 (fun x => (gauss t x : ℂ)) ξ ∂ν
      = (((Real.sqrt t)⁻¹ * mθ ν (1 / s + 1 / t) : ℝ) : ℂ) := by
    simp_rw [hF]
    rw [integral_complex_ofReal, integral_const_mul]
    rfl
  have hg : ∀ x, gconv s (fun x => (gauss t x : ℂ)) x
      = (((Real.sqrt (s + t))⁻¹ * gauss (s * t / (s + t)) x : ℝ) : ℂ) := by
    intro x
    unfold gconv
    have e : (fun a => ((gauss t a : ℝ) : ℂ) * (gauss s (x - a) : ℂ))
        = fun a => ((gauss t a * gauss s (x - a) : ℝ) : ℂ) := by
      funext a; push_cast; ring
    rw [e, integral_complex_ofReal, gauss_conv hs ht]
  have h2 : ∫ x, gconv s (fun x => (gauss t x : ℂ)) x ∂ν
      = (((Real.sqrt (s + t))⁻¹ * mθ ν (s * t / (s + t)) : ℝ) : ℂ) := by
    simp_rw [hg]
    rw [integral_complex_ofReal, integral_const_mul]
    rfl
  have h3 : gconv s (fun x => (gauss t x : ℂ)) 0 = (((Real.sqrt (s + t))⁻¹ : ℝ) : ℂ) := by
    rw [hg, gauss_zero, mul_one]
  have h4 : ∫ a, ((gauss t a : ℝ) : ℂ) = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_gauss ht]
  set u := s * t / (s + t) with hu_def
  have hu : 0 < u := by positivity
  have hu' : 1 / u = 1 / s + 1 / t := by rw [hu_def]; field_simp; ring
  have hθu := hθ u hu
  rw [hu'] at hθu
  have hsqrt : Real.sqrt u = Real.sqrt s * Real.sqrt t / Real.sqrt (s + t) := by
    rw [hu_def, Real.sqrt_div' _ hst.le, Real.sqrt_mul hs.le]
  have hs0 : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  have ht0 : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hst0 : (Real.sqrt (s + t) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hst).ne'
  unfold Tdef
  rw [h1, h2, h3, h4]
  push_cast
  rw [hθu, hsqrt]
  push_cast
  field_simp
  ring


/-! ### Weierstrass in the variable `z = e^{-π x²}`: even `C_c` tests are Gaussian polynomials up to `ε G_1` -/

lemma mθ_nonneg (ν : Measure ℝ) (t : ℝ) : 0 ≤ mθ ν t :=
  integral_nonneg fun x => gauss_nonneg t x

lemma Kconst_nonneg (ν : Measure ℝ) (β : ℂ) {s : ℝ} (hs : 0 < s) : 0 ≤ Kconst ν β s := by
  unfold Kconst
  have h1 := mθ_nonneg ν (1 / s)
  have h2 := mθ_nonneg ν (s * 1 / (s + 1))
  have h3 : 0 ≤ (Real.sqrt s)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h4 : 0 ≤ (Real.sqrt (s + 1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  positivity

/-- Compactly supported continuous functions are dominated by any Gaussian. -/
lemma exists_gdom_of_hasCompactSupport {f : ℝ → ℂ} (hc : Continuous f) (hcs : HasCompactSupport f)
    {κ : ℝ} (hκ : 0 ≤ κ) : ∃ C, ∀ x, ‖f x‖ ≤ C * gauss κ x := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M * Real.exp (π * κ * R ^ 2), fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · have hxR : |x| ≤ R := by
      have := hR hx
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hx2 : x ^ 2 ≤ R ^ 2 := by
      have h0 : 0 ≤ |x| := abs_nonneg x
      have : |x| ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 hxR 2
      rwa [sq_abs] at this
    have h1 : 1 ≤ Real.exp (π * κ * R ^ 2) * gauss κ x := by
      unfold gauss
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hx2 (mul_nonneg pi_pos.le hκ)
      nlinarith
    calc ‖f x‖ ≤ M := hM x
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * (Real.exp (π * κ * R ^ 2) * gauss κ x) := mul_le_mul_of_nonneg_left h1 hM0
      _ = M * Real.exp (π * κ * R ^ 2) * gauss κ x := by ring
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    have := gauss_nonneg κ x
    positivity

/-- The inverse of `x ↦ e^{-π x²}` on `(0,1]`. -/
def Φz (z : ℝ) : ℝ := Real.sqrt (-Real.log z / π)

lemma Φz_gauss (x : ℝ) : Φz (gauss 1 x) = |x| := by
  unfold Φz gauss
  rw [Real.log_exp]
  have : -(-π * 1 * x ^ 2) / π = x ^ 2 := by field_simp
  rw [this, Real.sqrt_sq_eq_abs]

lemma even_abs {f : ℝ → ℂ} (hev : ∀ x, f (-x) = f x) (x : ℝ) : f |x| = f x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, hev]

/-- Continuity on `[0,1]` of `z ↦ g(f(Φ z))/z` for compactly supported `f` and `g 0 = 0`. -/
lemma continuousOn_transfer {f : ℝ → ℂ} (hc : Continuous f) (hcs : HasCompactSupport f)
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : g 0 = 0) :
    ContinuousOn (fun z => g (f (Φz z)) / z) (Icc 0 1) := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  set δ := Real.exp (-π * (R ^ 2 + 1)) with hδ
  have hδpos : 0 < δ := Real.exp_pos _
  have hvanish : ∀ z, 0 < z → z < δ → f (Φz z) = 0 := by
    intro z hz hzδ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hlog : Real.log z < -π * (R ^ 2 + 1) := by
      rw [← Real.log_exp (-π * (R ^ 2 + 1))]
      exact Real.log_lt_log hz hzδ
    have harg : R ^ 2 + 1 < -Real.log z / π := by
      rw [lt_div_iff₀ pi_pos]; nlinarith [pi_pos]
    have hΦ : R ^ 2 + 1 < Φz z ^ 2 := by
      unfold Φz
      rw [Real.sq_sqrt (by nlinarith [sq_nonneg R])]
      exact harg
    have hΦ0 : 0 ≤ Φz z := Real.sqrt_nonneg _
    rw [abs_of_nonneg hΦ0] at this
    have hR0 : 0 ≤ R := hΦ0.trans this
    nlinarith
  intro z hz
  rcases eq_or_lt_of_le hz.1 with h0 | hpos
  · -- at z = 0 the function vanishes on [0, δ)
    subst h0
    have hval : g (f (Φz 0)) / 0 = 0 := by simp
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ hval
    have : Icc (0 : ℝ) 1 ∩ Iio δ ∈ 𝓝[Icc 0 1] (0 : ℝ) :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds hδpos)
    filter_upwards [this] with w hw
    rcases eq_or_lt_of_le hw.1.1 with hw0 | hwpos
    · rw [← hw0]; simp
    · rw [hvanish w hwpos hw.2, hg0, zero_div]
  · -- for z > 0 the function is continuous at z
    apply ContinuousAt.continuousWithinAt
    have hΦc : ContinuousAt Φz z := by
      unfold Φz
      exact (((Real.continuousAt_log hpos.ne').neg).div_const π).sqrt
    exact ((hg.continuousAt.comp (hc.continuousAt.comp hΦc))).div continuousAt_id hpos.ne'

lemma gauss_succ_eq_pow (i : ℕ) (x : ℝ) : gauss ((i : ℝ) + 1) x = gauss 1 x ^ (i + 1) := by
  unfold gauss
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast; ring

/-- One real coordinate of the approximation. -/
lemma approx_coord {f : ℝ → ℂ} (hev : ∀ x, f (-x) = f x) {g : ℂ → ℝ} {p : Polynomial ℝ} {ε : ℝ}
    (hp : ∀ z ∈ Icc (0 : ℝ) 1, |p.eval z - g (f (Φz z)) / z| < ε) (x : ℝ) :
    |gauss 1 x * p.eval (gauss 1 x) - g (f x)| ≤ ε * gauss 1 x := by
  set z := gauss 1 x with hz
  have hz0 : 0 < z := gauss_pos 1 x
  have hz1 : z ≤ 1 := gauss_le_one zero_le_one x
  have h := hp z ⟨hz0.le, hz1⟩
  rw [hz, Φz_gauss, even_abs hev, ← hz] at h
  have e : z * p.eval z - g (f x) = z * (p.eval z - g (f x) / z) := by field_simp
  rw [e, abs_mul, abs_of_pos hz0, mul_comm ε]
  exact mul_le_mul_of_nonneg_left h.le hz0.le

/-- **Weierstrass step (kernel).** An even compactly supported continuous test is, up to
`ε e^{-π x²}`, a finite combination of the Gaussians `e^{-π (i+1) x²}`. -/
lemma exists_gauss_poly_approx {f : ℝ → ℂ} (hc : Continuous f) (hcs : HasCompactSupport f)
    (hev : ∀ x, f (-x) = f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ c : ℕ → ℂ, ∀ x,
      ‖f x - ∑ i ∈ Finset.range N, c i * (gauss ((i : ℝ) + 1) x : ℂ)‖ ≤ ε * gauss 1 x := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨pr, hpr⟩ := exists_polynomial_near_of_continuousOn 0 1 _
    (continuousOn_transfer hc hcs Complex.continuous_re Complex.zero_re) (ε / 2) hε2
  obtain ⟨pi', hpi⟩ := exists_polynomial_near_of_continuousOn 0 1 _
    (continuousOn_transfer hc hcs Complex.continuous_im Complex.zero_im) (ε / 2) hε2
  refine ⟨max pr.natDegree pi'.natDegree + 1,
    fun i => (pr.coeff i : ℂ) + Complex.I * (pi'.coeff i : ℂ), fun x => ?_⟩
  set N := max pr.natDegree pi'.natDegree + 1
  set z := gauss 1 x with hz
  have hr := approx_coord hev hpr x
  have hi := approx_coord hev hpi x
  rw [← hz] at hr hi
  have hsum : ∑ i ∈ Finset.range N, ((pr.coeff i : ℂ) + Complex.I * (pi'.coeff i : ℂ))
        * (gauss ((i : ℝ) + 1) x : ℂ)
      = ((z * pr.eval z : ℝ) : ℂ) + Complex.I * ((z * pi'.eval z : ℝ) : ℂ) := by
    rw [Polynomial.eval_eq_sum_range' (n := N) (by omega) z,
      Polynomial.eval_eq_sum_range' (n := N) (by omega) z]
    simp_rw [gauss_succ_eq_pow, ← hz]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (f x - (((z * pr.eval z : ℝ) : ℂ) + Complex.I * ((z * pi'.eval z : ℝ) : ℂ))).re
      = -(z * pr.eval z - (f x).re) := by simp
  have him : (f x - (((z * pr.eval z : ℝ) : ℂ) + Complex.I * ((z * pi'.eval z : ℝ) : ℂ))).im
      = -(z * pi'.eval z - (f x).im) := by simp
  rw [hre, him, abs_neg, abs_neg]
  have : ε / 2 * z + ε / 2 * z = ε * z := by ring
  linarith

/-- **`T_s` annihilates every even compactly supported continuous test (kernel).** -/
theorem Tdef_even_eq_zero {ν : Measure ℝ} {β : ℂ} (hν : GaussIntegrable ν) (hθ : ThetaRelation ν β)
    {s : ℝ} (hs : 0 < s) {f : ℝ → ℂ} (hc : Continuous f) (hcs : HasCompactSupport f)
    (hev : ∀ x, f (-x) = f x) : Tdef ν β s f = 0 := by
  have hsum : ∀ (c : ℕ → ℂ) (N : ℕ),
      GDom (∑ i ∈ Finset.range N, ‖c i‖ * 1)
        (fun x => ∑ i ∈ Finset.range N, c i * (gauss ((i : ℝ) + 1) x : ℂ)) ∧
      Tdef ν β s (fun x => ∑ i ∈ Finset.range N, c i * (gauss ((i : ℝ) + 1) x : ℂ)) = 0 := by
    intro c N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      refine ⟨⟨continuous_const, fun x => by simp⟩, ?_⟩
      have e : (fun _ : ℝ => (0 : ℂ)) = fun x => (0 : ℂ) * (gauss 1 x : ℂ) := by
        funext x; ring
      rw [e, Tdef_const_mul, zero_mul]
    | succ n ih =>
      have hg : GDom (‖c n‖ * 1) (fun x => c n * (gauss ((n : ℝ) + 1) x : ℂ)) :=
        (gdom_gauss (by have := n.cast_nonneg (α := ℝ); linarith)).const_mul (c n)
      have hadd := ih.1.add hg
      simp only [Finset.sum_range_succ]
      refine ⟨hadd, ?_⟩
      rw [Tdef_add hν hs ih.1 hg, ih.2, Tdef_const_mul, Tdef_gauss hθ hs (by positivity),
        mul_zero, add_zero]
  by_contra hne
  have hpos : 0 < ‖Tdef ν β s f‖ := norm_pos_iff.mpr hne
  have hK := Kconst_nonneg ν β hs
  set ε := ‖Tdef ν β s f‖ / (2 * (Kconst ν β s + 1)) with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨N, c, happrox⟩ := exists_gauss_poly_approx hc hcs hev hε
  set hp := fun x => ∑ i ∈ Finset.range N, c i * (gauss ((i : ℝ) + 1) x : ℂ) with hhp
  have hgd : GDom ε (fun x => f x - hp x) := ⟨hc.sub (hsum c N).1.1, happrox⟩
  have hdecomp : f = fun x => (f x - hp x) + hp x := by funext x; ring
  have hsplit : Tdef ν β s f = Tdef ν β s (fun x => f x - hp x) := by
    conv_lhs => rw [hdecomp]
    rw [Tdef_add hν hs hgd (hsum c N).1, (hsum c N).2, add_zero]
  have hb := norm_Tdef_le (β := β) hν hs hgd
  rw [← hsplit] at hb
  have hlt : ε * Kconst ν β s < ‖Tdef ν β s f‖ := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### The approximate identity: `√s · T_s(f) → T(f)` as `s → ∞` -/

lemma gconv_eq_sub (s : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    gconv s f x = ∫ a, f (x - a) * (gauss s a : ℂ) := by
  unfold gconv
  have e : (fun a => f a * (gauss s (x - a) : ℂ))
      = fun a => (fun b => f (x - b) * (gauss s b : ℂ)) (x - a) := by
    funext a; simp only [sub_sub_cancel]
  rw [e, integral_sub_left_eq_self (fun b => f (x - b) * (gauss s b : ℂ)) volume x]

lemma sqrt_mul_gconv {s : ℝ} (hs : 0 < s) (f : ℝ → ℂ) (x : ℝ) :
    (Real.sqrt s : ℂ) * gconv s f x = ∫ u, f (x - u / Real.sqrt s) * (gauss 1 u : ℂ) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h := Measure.integral_comp_div (fun a => f (x - a) * (gauss s a : ℂ)) (Real.sqrt s)
  rw [abs_of_pos hsq] at h
  have e : ∀ u, gauss s (u / Real.sqrt s) = gauss 1 u := by
    intro u; unfold gauss
    congr 1
    rw [div_pow, Real.sq_sqrt hs.le]
    field_simp
  simp_rw [e] at h
  rw [h, gconv_eq_sub, Complex.real_smul]

lemma tendsto_sqrt_mul_gconv {f : ℝ → ℂ} (hc : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (x : ℝ) : Tendsto (fun s => (Real.sqrt s : ℂ) * gconv s f x) atTop (𝓝 (f x)) := by
  have heq : ∀ᶠ s in atTop, ∫ u, f (x - u / Real.sqrt s) * (gauss 1 u : ℂ)
      = (Real.sqrt s : ℂ) * gconv s f x :=
    (eventually_gt_atTop 0).mono fun s hs => (sqrt_mul_gconv hs f x).symm
  have hlim : Tendsto (fun s => ∫ u, f (x - u / Real.sqrt s) * (gauss 1 u : ℂ)) atTop
      (𝓝 (∫ u, f x * (gauss 1 u : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => M * gauss 1 u) ?_ ?_
      ((integrable_gauss one_pos).const_mul M) (ae_of_all _ fun u => ?_)
    · refine Eventually.of_forall fun s => ?_
      exact ((hc.comp (continuous_const.sub (continuous_id.div_const _))).mul
        (Complex.continuous_ofReal.comp (continuous_gauss 1))).aestronglyMeasurable
    · refine Eventually.of_forall fun s => ae_of_all _ fun u => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _)]
      exact mul_le_mul_of_nonneg_right (hM _) (gauss_nonneg _ _)
    · have h1 : Tendsto (fun s : ℝ => u / Real.sqrt s) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
      have h2 : Tendsto (fun s : ℝ => x - u / Real.sqrt s) atTop (𝓝 x) := by
        simpa using (tendsto_const_nhds (x := x)).sub h1
      exact ((hc.tendsto x).comp h2).mul_const _
  have hval : ∫ u, f x * (gauss 1 u : ℂ) = f x := by
    rw [integral_const_mul, integral_complex_ofReal, integral_gauss one_pos, Real.sqrt_one,
      inv_one, Complex.ofReal_one, mul_one]
  rw [hval] at hlim
  exact hlim.congr' heq

lemma norm_sqrt_mul_gconv_le {f : ℝ → ℂ} {C : ℝ}
    (hC : ∀ a, ‖f a‖ ≤ C * gauss (1 / 2) a) {s : ℝ} (hs : 1 ≤ s) (x : ℝ) :
    ‖(Real.sqrt s : ℂ) * gconv s f x‖ ≤ C * gauss (1 / 3) x := by
  have hs0 : 0 < s := by linarith
  have hC0 : 0 ≤ C := by
    have h0 := hC 0; rw [gauss_zero, mul_one] at h0; exact (norm_nonneg _).trans h0
  have hint : Integrable (fun a => gauss (1 / 2) a * gauss s (x - a)) := by
    refine Integrable.mono' (integrable_gauss (t := 1 / 2) (by norm_num)) ?_ (ae_of_all _ fun a => ?_)
    · exact ((continuous_gauss _).mul
        ((continuous_gauss s).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (gauss_nonneg _ _) (gauss_nonneg _ _))]
      calc gauss (1 / 2) a * gauss s (x - a) ≤ gauss (1 / 2) a * 1 :=
            mul_le_mul_of_nonneg_left (gauss_le_one hs0.le _) (gauss_nonneg _ _)
        _ = gauss (1 / 2) a := mul_one _
  have hconv : ‖gconv s f x‖ ≤ C * ((Real.sqrt (s + 1 / 2))⁻¹ * gauss (s * (1 / 2) / (s + 1 / 2)) x) := by
    unfold gconv
    have hb : ∀ a, ‖f a * (gauss s (x - a) : ℂ)‖ ≤ C * (gauss (1 / 2) a * gauss s (x - a)) := by
      intro a
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hC a) (gauss_nonneg _ _)
    refine (norm_integral_le_of_norm_le (hint.const_mul C) (ae_of_all _ hb)).trans (le_of_eq ?_)
    rw [integral_const_mul, gauss_conv hs0 (by norm_num)]
  have hsq : Real.sqrt s * (Real.sqrt (s + 1 / 2))⁻¹ ≤ 1 := by
    have hp : 0 < Real.sqrt (s + 1 / 2) := Real.sqrt_pos.mpr (by linarith)
    rw [mul_inv_le_iff₀ hp, one_mul]
    exact Real.sqrt_le_sqrt (by linarith)
  have hg : gauss (s * (1 / 2) / (s + 1 / 2)) x ≤ gauss (1 / 3) x := by
    apply gauss_anti
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt s * ‖gconv s f x‖
      ≤ Real.sqrt s * (C * ((Real.sqrt (s + 1 / 2))⁻¹ * gauss (s * (1 / 2) / (s + 1 / 2)) x)) :=
        mul_le_mul_of_nonneg_left hconv (Real.sqrt_nonneg _)
    _ = C * ((Real.sqrt s * (Real.sqrt (s + 1 / 2))⁻¹) * gauss (s * (1 / 2) / (s + 1 / 2)) x) := by
        ring
    _ ≤ C * (1 * gauss (1 / 3) x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsq hg (gauss_nonneg _ _) zero_le_one) hC0
    _ = C * gauss (1 / 3) x := by ring

/-- **Approximate identity (kernel).** For a compactly supported continuous test `f` with
`ν`-integrable Fourier transform, `√s · T_s(f)` converges to the Poisson defect
`∫ 𝓕 f dν - ∫ f dν - β (f 0 - ∫ f)` as `s → ∞`. -/
theorem tendsto_sqrt_mul_Tdef {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {β : ℂ}
    (hν : GaussIntegrable ν) {f : ℝ → ℂ} (hc : Continuous f) (hcs : HasCompactSupport f)
    (hF : Integrable (𝓕 f) ν) :
    Tendsto (fun s => (Real.sqrt s : ℂ) * Tdef ν β s f) atTop
      (𝓝 ((∫ ξ, 𝓕 f ξ ∂ν) - (∫ x, f x ∂ν) - β * (f 0 - ∫ x, f x))) := by
  obtain ⟨C₁, hC₁⟩ := exists_gdom_of_hasCompactSupport hc hcs zero_le_one
  have hG : GDom C₁ f := ⟨hc, hC₁⟩
  obtain ⟨C₂, hC₂⟩ := exists_gdom_of_hasCompactSupport hc hcs (κ := 1 / 2) (by norm_num)
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  -- (a) the Fourier term
  have hA : Tendsto (fun s => ∫ ξ, (gauss (1 / s) ξ : ℂ) * 𝓕 f ξ ∂ν) atTop (𝓝 (∫ ξ, 𝓕 f ξ ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖𝓕 f ξ‖) ?_ ?_ hF.norm
      (ae_of_all _ fun ξ => ?_)
    · refine Eventually.of_forall fun s => ?_
      exact ((Complex.continuous_ofReal.comp (continuous_gauss _)).mul
        (continuous_fourier_of_integrable hG.integrable)).aestronglyMeasurable
    · refine (eventually_gt_atTop 0).mono fun s hs => ae_of_all _ fun ξ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gauss_nonneg _ _)]
      calc gauss (1 / s) ξ * ‖𝓕 f ξ‖ ≤ 1 * ‖𝓕 f ξ‖ :=
            mul_le_mul_of_nonneg_right (gauss_le_one (by positivity) _) (norm_nonneg _)
        _ = ‖𝓕 f ξ‖ := one_mul _
    · have h1 : Tendsto (fun s : ℝ => -π * (1 / s) * ξ ^ 2) atTop (𝓝 (-π * 0 * ξ ^ 2)) :=
        ((tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop tendsto_id)).mul tendsto_const_nhds)
      have h2 : Tendsto (fun s : ℝ => gauss (1 / s) ξ) atTop (𝓝 1) := by
        have h3 := (Real.continuous_exp.tendsto _).comp h1
        have e : (fun s : ℝ => gauss (1 / s) ξ) = Real.exp ∘ (fun s : ℝ => -π * (1 / s) * ξ ^ 2) := by
          funext s; rfl
        rw [e]
        convert h3 using 2
        simp
      have h3 := ((Complex.continuous_ofReal.tendsto _).comp h2).mul (tendsto_const_nhds (x := 𝓕 f ξ))
      simpa using h3
  -- (b) the smoothed-test term
  have hB : Tendsto (fun s => ∫ x, (Real.sqrt s : ℂ) * gconv s f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => C₂ * gauss (1 / 3) x) ?_ ?_
      ((hν (1 / 3) (by norm_num)).const_mul C₂) (ae_of_all _ fun x => ?_)
    · refine (eventually_gt_atTop 0).mono fun s hs => ?_
      exact (continuous_const.mul (hG.continuous_gconv hs.le)).aestronglyMeasurable
    · refine (eventually_ge_atTop 1).mono fun s hs => ae_of_all _ fun x => ?_
      exact norm_sqrt_mul_gconv_le hC₂ hs x
    · exact tendsto_sqrt_mul_gconv hc hM x
  -- (c) the value at the origin
  have hC : Tendsto (fun s => (Real.sqrt s : ℂ) * gconv s f 0) atTop (𝓝 (f 0)) :=
    tendsto_sqrt_mul_gconv hc hM 0
  have hlim := (hA.sub hB).sub ((hC.sub (tendsto_const_nhds (x := ∫ x, f x))).const_mul β)
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  have hsq : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  unfold Tdef
  rw [integral_const_mul]
  field_simp

/-! ### Main theorem: the theta relation implies the Poisson-pair identity -/

/-- **Gaussian determination (kernel).** For a locally finite positive measure `ν` with all
Gaussians integrable, the modular relation `θ_ν(1/t) = √t θ_ν(t) + β(√t - 1)` implies the Poisson
identity on every EVEN continuous compactly supported test with `ν`-integrable transform. -/
theorem isPoissonPairEven_of_theta {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {β : ℂ}
    (hν : GaussIntegrable ν) (hθ : ThetaRelation ν β) : IsPoissonPairEven ν β := by
  intro f hc hcs hev hF
  have hT := tendsto_sqrt_mul_Tdef (β := β) hν hc hcs hF
  have h0 : Tendsto (fun s => (Real.sqrt s : ℂ) * Tdef ν β s f) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
    show (0 : ℂ) = (Real.sqrt s : ℂ) * Tdef ν β s f
    rw [Tdef_even_eq_zero hν hθ hs hc hcs hev, mul_zero]
  have := tendsto_nhds_unique hT h0
  linear_combination this

/-- **Gaussian determination, full form (kernel).** For an EVEN (negation-invariant) locally
finite positive measure with all Gaussians integrable, the modular relation alone implies
`IsPoissonPair ν β`: `ν̂ = ν + β(δ₀ - Leb)` on all continuous compactly supported tests with
`ν`-integrable transform. No Schwartz-to-`C_c` approximation is assumed. -/
theorem isPoissonPair_of_theta {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant]
    {β : ℂ} (hν : GaussIntegrable ν) (hθ : ThetaRelation ν β) : IsPoissonPair ν β :=
  isPoissonPair_of_even (isPoissonPairEven_of_theta hν hθ)


/-! ## Part 5. Theorem A from the modular relation alone

The only analytic input left is the theta relation. Local finiteness of `ν` and the Gaussian
integrability are the standing tameness hypotheses; `sinc²`-integrability is DERIVED (dyadic
Gaussian majorant + the growth bound the theta relation itself gives). -/

lemma fej_le_one (x : ℝ) : fej x ≤ 1 := by
  unfold fej
  have h := Real.abs_sinc_le_one (π * x)
  rw [← sq_abs]
  calc |Real.sinc (π * x)| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = 1 := one_pow 2

lemma mθ_anti {ν : Measure ℝ} (hν : GaussIntegrable ν) {t t' : ℝ} (ht : 0 < t) (h : t ≤ t') :
    mθ ν t' ≤ mθ ν t :=
  integral_mono (hν t' (by linarith)) (hν t ht) (fun x => gauss_anti h x)

lemma sqrt_four_pow (i : ℕ) : Real.sqrt ((4 : ℝ) ^ i) = 2 ^ i := by
  rw [show (4 : ℝ) ^ i = (2 ^ i) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-- **Growth from the modular relation (kernel):** `θ_ν(4^{-i}) ≤ 2^i (θ_ν(1) + 2‖β‖)`, i.e.
`ν[-R,R] = O(R)`. -/
lemma mθ_dyadic_le {ν : Measure ℝ} {β : ℂ} (hν : GaussIntegrable ν) (hθ : ThetaRelation ν β)
    (i : ℕ) : mθ ν (1 / 4 ^ i) ≤ 2 ^ i * (mθ ν 1 + 2 * ‖β‖) := by
  have h4 : (0 : ℝ) < 4 ^ i := by positivity
  have h := hθ (4 ^ i) h4
  rw [sqrt_four_pow] at h
  have hm : mθ ν (4 ^ i) ≤ mθ ν 1 := mθ_anti hν one_pos (one_le_pow₀ (by norm_num))
  have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hnorm := congrArg norm h
  rw [Complex.norm_real, Real.norm_of_nonneg (mθ_nonneg _ _)] at hnorm
  have hb : ‖(((2 : ℝ) ^ i : ℝ) : ℂ) * (mθ ν (4 ^ i) : ℂ) + β * ((((2 : ℝ) ^ i : ℝ) : ℂ) - 1)‖
      ≤ 2 ^ i * mθ ν (4 ^ i) + ‖β‖ * (2 ^ i + 1) := by
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (mθ_nonneg _ _)]
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (le_of_eq ?_)) (norm_nonneg _)
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_one]
  rw [← hnorm] at hb
  have hmn := mθ_nonneg ν (4 ^ i)
  have hβ := norm_nonneg β
  nlinarith

/-- Pointwise dyadic Gaussian majorant of the Fejer kernel. -/
lemma fej_le_dyadic (x : ℝ) :
    ∃ j : ℕ, fej x ≤ 4 * Real.exp π * ((1 / 4 ^ j) * gauss (1 / 4 ^ j) x) := by
  have hex : ∃ n : ℕ, x ^ 2 ≤ 4 ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x ^ 2) (by norm_num : (1 : ℝ) < 4)
    exact ⟨n, hn.le⟩
  classical
  refine ⟨Nat.find hex, ?_⟩
  have hxj : x ^ 2 ≤ 4 ^ Nat.find hex := Nat.find_spec hex
  have h4j : (0 : ℝ) < 4 ^ Nat.find hex := by positivity
  have hg : Real.exp (-π) ≤ gauss (1 / 4 ^ Nat.find hex) x := by
    unfold gauss
    apply Real.exp_le_exp.mpr
    have : x ^ 2 / 4 ^ Nat.find hex ≤ 1 := (div_le_one h4j).mpr hxj
    have e : -π * (1 / 4 ^ Nat.find hex) * x ^ 2 = -π * (x ^ 2 / 4 ^ Nat.find hex) := by ring
    rw [e]; nlinarith [pi_pos]
  have hRHS : 4 * (1 / 4 ^ Nat.find hex)
      ≤ 4 * Real.exp π * ((1 / 4 ^ Nat.find hex) * gauss (1 / 4 ^ Nat.find hex) x) := by
    have h1 : 1 ≤ Real.exp π * gauss (1 / 4 ^ Nat.find hex) x := by
      calc (1 : ℝ) = Real.exp π * Real.exp (-π) := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp π * gauss (1 / 4 ^ Nat.find hex) x :=
          mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
    have h14 : 0 ≤ 4 * (1 / (4 : ℝ) ^ Nat.find hex) := by positivity
    calc 4 * (1 / 4 ^ Nat.find hex) = (4 * (1 / 4 ^ Nat.find hex)) * 1 := (mul_one _).symm
      _ ≤ (4 * (1 / 4 ^ Nat.find hex)) * (Real.exp π * gauss (1 / 4 ^ Nat.find hex) x) :=
          mul_le_mul_of_nonneg_left h1 h14
      _ = _ := by ring
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0] at hRHS ⊢
    refine (fej_le_one x).trans (le_trans ?_ hRHS)
    norm_num
  · have hlt : 4 ^ (Nat.find hex - 1) < x ^ 2 := not_le.mp (Nat.find_min hex (by omega))
    have hpos' : (0 : ℝ) < 4 ^ (Nat.find hex - 1) := by positivity
    have hx0 : x ≠ 0 := by
      intro h
      have hx2 : x ^ 2 = 0 := by rw [h]; ring
      linarith
    have e : (4 : ℝ) ^ Nat.find hex = 4 * 4 ^ (Nat.find hex - 1) := by
      rw [← pow_succ']; congr 1; omega
    calc fej x ≤ 1 / x ^ 2 := fej_le_inv_sq hx0
      _ ≤ 1 / 4 ^ (Nat.find hex - 1) := one_div_le_one_div_of_le hpos' hlt.le
      _ = 4 * (1 / 4 ^ Nat.find hex) := by rw [e]; field_simp
      _ ≤ _ := hRHS

/-- **`sinc²`-integrability is forced by the modular relation (kernel).** -/
theorem integrable_fej_of_theta {ν : Measure ℝ} {β : ℂ} (hν : GaussIntegrable ν)
    (hθ : ThetaRelation ν β) : Integrable fej ν := by
  refine ⟨continuous_fej.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fej_nonneg)]
  set C := 4 * Real.exp π * (mθ ν 1 + 2 * ‖β‖) with hC
  have hpt : ∀ x, ENNReal.ofReal (fej x)
      ≤ ∑' i : ℕ, ENNReal.ofReal (4 * Real.exp π * ((1 / 4 ^ i) * gauss (1 / 4 ^ i) x)) := by
    intro x
    obtain ⟨j, hj⟩ := fej_le_dyadic x
    exact (ENNReal.ofReal_le_ofReal hj).trans
      (ENNReal.le_tsum (f := fun i : ℕ =>
        ENNReal.ofReal (4 * Real.exp π * ((1 / 4 ^ i) * gauss (1 / 4 ^ i) x))) j)
  have hterm : ∀ i : ℕ, ∫⁻ x, ENNReal.ofReal (4 * Real.exp π * ((1 / 4 ^ i) * gauss (1 / 4 ^ i) x)) ∂ν
      ≤ ENNReal.ofReal (C * (1 / 2) ^ i) := by
    intro i
    have hint : Integrable (fun x => 4 * Real.exp π * ((1 / 4 ^ i) * gauss (1 / 4 ^ i) x)) ν :=
      ((hν _ (by positivity)).const_mul _).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by
      have := gauss_nonneg (1 / 4 ^ i) x; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_const_mul, integral_const_mul]
    have hd := mθ_dyadic_le hν hθ i
    unfold mθ at hd
    have e : (1 / (4 : ℝ) ^ i) * 2 ^ i = (1 / 2) ^ i := by
      rw [show (4 : ℝ) ^ i = 2 ^ i * 2 ^ i by rw [← mul_pow]; norm_num]
      field_simp
      rw [one_div_pow]
      field_simp
    have hA : 0 ≤ 4 * Real.exp π := by positivity
    have hB : (0 : ℝ) ≤ 1 / 4 ^ i := by positivity
    calc 4 * Real.exp π * (1 / 4 ^ i * ∫ x, gauss (1 / 4 ^ i) x ∂ν)
        ≤ 4 * Real.exp π * (1 / 4 ^ i * (2 ^ i * (mθ ν 1 + 2 * ‖β‖))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hB) hA
      _ = 4 * Real.exp π * (mθ ν 1 + 2 * ‖β‖) * ((1 / (4 : ℝ) ^ i) * 2 ^ i) := by ring
      _ = C * (1 / 2) ^ i := by rw [e]
  have hC0 : 0 ≤ C := by
    have := mθ_nonneg ν 1
    have := norm_nonneg β
    positivity
  calc ∫⁻ x, ENNReal.ofReal (fej x) ∂ν
      ≤ ∫⁻ x, ∑' i : ℕ, ENNReal.ofReal (4 * Real.exp π * ((1 / 4 ^ i) * gauss (1 / 4 ^ i) x)) ∂ν :=
        lintegral_mono hpt
    _ = ∑' i : ℕ, ∫⁻ x, ENNReal.ofReal (4 * Real.exp π * ((1 / 4 ^ i) * gauss (1 / 4 ^ i) x)) ∂ν :=
        lintegral_tsum fun i => (ENNReal.measurable_ofReal.comp
          (by have := continuous_gauss (1 / 4 ^ i); fun_prop : Continuous fun x =>
            4 * Real.exp π * ((1 / 4 ^ i) * gauss (1 / 4 ^ i) x)).measurable).aemeasurable
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (C * (1 / 2) ^ i) := ENNReal.tsum_le_tsum hterm
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          (summable_geometric_two.mul_left C)]
        exact ENNReal.ofReal_lt_top

/-- **THEOREM A FROM THE MODULAR RELATION (kernel).** Let `ν` be a positive, locally finite,
even measure on `ℝ` with every Gaussian integrable, with no mass in `(-1,1) \ {0}`, satisfying
`θ_ν(1/t) = √t θ_ν(t) + β(√t - 1)` for all `t > 0`. Then `ν` is carried by `ℤ`, every atom off the
origin has mass `ν{0} + β`, and `ν` is the sum of its atoms. No discreteness, density,
`sinc²`-integrability, Schwartz or `C_c` Poisson hypothesis is assumed. -/
theorem thmA_theta {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant] {β : ℂ}
    (hν : GaussIntegrable ν) (hθ : ThetaRelation ν β) (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    (∀ᵐ x ∂ν, ∃ n : ℤ, x = (n : ℝ)) ∧
    (∀ m : ℤ, m ≠ 0 → ((ν.real {(m : ℝ)} : ℝ) : ℂ) = ((ν.real {0} : ℝ) : ℂ) + β) ∧
    ν = Measure.sum (fun n : ℤ => ν {(n : ℝ)} • Measure.dirac (n : ℝ)) :=
  poisson_rigidity (isPoissonPair_of_theta hν hθ) (integrable_fej_of_theta hν hθ) hgap

/-- **Self-dual form (kernel).** With `β = 0` (Jacobi's relation `θ(1/t) = √t θ(t)`), the
admissible measures are exactly the multiples of the integer comb. -/
theorem thmA_theta_selfDual {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant]
    (hν : GaussIntegrable ν) (hθ : ThetaRelation ν 0) (hgap : ν (Ioo (-1) 1 \ {0}) = 0) :
    ν = ν {0} • intComb :=
  selfDual_rigidity (isPoissonPair_of_theta hν hθ) (integrable_fej_of_theta hν hθ) hgap

/-- **LP sharpness in theta form (kernel):** a wider gap forces `ν = 0`. -/
theorem theta_gap_gt_one_forces_zero {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant]
    (hν : GaussIntegrable ν) (hθ : ThetaRelation ν 0) {a : ℝ} (ha : 1 < a)
    (hgap : ν (Ioo (-a) a \ {0}) = 0) : ν = 0 :=
  gap_gt_one_forces_zero (isPoissonPair_of_theta hν hθ) (integrable_fej_of_theta hν hθ) ha hgap

/-- **Translation boundedness from the modular relation (kernel).** Every measure satisfying the
theta relation has uniformly bounded unit windows. (The zero-ordinate measure of `ζ`, whose windows
grow like `(1/2π) log T`, can therefore satisfy NO relation of this shape.) -/
theorem translation_bounded_of_theta {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant]
    {β : ℂ} (hν : GaussIntegrable ν) (hθ : ThetaRelation ν β) (t : ℝ) :
    ν (Icc (t - 1 / 2) (t + 1 / 2)) ≤ ENNReal.ofReal (2 * ((∫ ξ, fej ξ ∂ν) + ‖β‖)) :=
  translation_bounded_of_poissonPair (isPoissonPair_of_theta hν hθ) (integrable_fej_of_theta hν hθ) t

/-! ## Part 6. Positive control: the integer comb, via Jacobi's theta identity -/

lemma isNegInvariant_of_preimage {μ : Measure ℝ}
    (h : ∀ s, MeasurableSet s → μ (Neg.neg ⁻¹' s) = μ s) : μ.IsNegInvariant :=
  ⟨by ext s hs; rw [Measure.neg_def, Measure.map_apply measurable_neg hs]; exact h s hs⟩

lemma intComb_isNegInvariant : intComb.IsNegInvariant := by
  refine isNegInvariant_of_preimage fun s hs => ?_
  rw [intComb_apply (measurable_neg hs), intComb_apply hs]
  have e : ∀ n : ℤ, (Neg.neg ⁻¹' s).indicator (1 : ℝ → ENNReal) (n : ℝ)
      = s.indicator (1 : ℝ → ENNReal) (((-n : ℤ) : ℝ)) := by
    intro n
    by_cases h : -(n : ℝ) ∈ s
    · rw [Set.indicator_of_mem (show (n : ℝ) ∈ Neg.neg ⁻¹' s from h),
        Set.indicator_of_mem (show (((-n : ℤ) : ℝ)) ∈ s by push_cast; exact h)]
      rfl
    · rw [Set.indicator_of_notMem (show (n : ℝ) ∉ Neg.neg ⁻¹' s from h),
        Set.indicator_of_notMem (show (((-n : ℤ) : ℝ)) ∉ s by push_cast; exact h)]
  simp_rw [e]
  exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => s.indicator (1 : ℝ → ENNReal) (n : ℝ))

instance : intComb.IsNegInvariant := intComb_isNegInvariant

/-- Jacobi's `θ(u) = Σ_{n∈ℤ} e^{-π u n²}`. -/
def jθ (u : ℝ) : ℝ := ∑' n : ℤ, gauss u n

lemma summable_gauss_int {u : ℝ} (hu : 0 < u) : Summable (fun n : ℤ => gauss u n) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left (1 / (π * u))) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (gauss_nonneg _ _)]
  unfold gauss
  have hy : 0 < π * u * (n : ℝ) ^ 2 := by positivity
  have h1 : π * u * (n : ℝ) ^ 2 ≤ Real.exp (π * u * (n : ℝ) ^ 2) := by
    have := Real.add_one_le_exp (π * u * (n : ℝ) ^ 2); linarith
  have e : Real.exp (-π * u * (n : ℝ) ^ 2) = (Real.exp (π * u * (n : ℝ) ^ 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e]
  calc (Real.exp (π * u * (n : ℝ) ^ 2))⁻¹ ≤ (π * u * (n : ℝ) ^ 2)⁻¹ := inv_anti₀ hy h1
    _ = 1 / (π * u) * (1 / (n : ℝ) ^ 2) := by field_simp

/-- **Jacobi (Mathlib's Gaussian Poisson summation):** `θ(1/u) = √u θ(u)`. -/
lemma jθ_inv {u : ℝ} (hu : 0 < u) : jθ (1 / u) = Real.sqrt u * jθ u := by
  have h := Real.tsum_exp_neg_mul_int_sq (a := 1 / u) (by positivity)
  unfold jθ gauss
  rw [h]
  have e1 : 1 / (1 / u) ^ (1 / 2 : ℝ) = Real.sqrt u := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow zero_le_one hu.le, Real.one_rpow, one_div_one_div]
  rw [e1]
  congr 1
  refine tsum_congr fun n => ?_
  congr 1
  field_simp

lemma integral_gauss_intComb (t : ℝ) : ∫ x, gauss t x ∂intComb = jθ t := by
  rw [intComb, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  simp [jθ]

lemma intComb_gaussIntegrable : GaussIntegrable intComb := by
  intro t ht
  have hc : ∀ n : ℤ, (1 : ENNReal) ≠ ⊤ := fun _ => ENNReal.one_ne_top
  rw [intComb, integrable_sum_dirac_iff hc]
  simpa [Real.norm_of_nonneg (gauss_nonneg _ _)] using summable_gauss_int ht

/-- **The integer comb satisfies the modular relation with `β = 0` (kernel).** -/
theorem intComb_theta : ThetaRelation intComb 0 := by
  intro t ht
  simp only [mθ, integral_gauss_intComb, zero_mul, add_zero]
  rw [jθ_inv ht]
  push_cast; ring

/-- **The theta-form characterization is sharp and not vacuous (kernel).** The integer comb
satisfies every hypothesis of `thmA_theta_selfDual`, and (as a consequence of the Gaussian
determination theorem) its `C_c` Poisson identity is RE-DERIVED here from Jacobi's identity. -/
theorem intComb_theta_admissible :
    intComb.IsNegInvariant ∧ GaussIntegrable intComb ∧ ThetaRelation intComb 0 ∧
    intComb (Ioo (-1) 1 \ {0}) = 0 ∧ intComb {0} = 1 ∧ IsPoissonPair intComb 0 :=
  ⟨intComb_isNegInvariant, intComb_gaussIntegrable, intComb_theta, intComb_gap,
    (intComb_admissible).2.2.2, isPoissonPair_of_theta intComb_gaussIntegrable intComb_theta⟩

/-! ## Part 7. The theta form is RH-blind: the fooling family `ν_{p,c}` -/

lemma comb_isNegInvariant (a : ℝ) : (comb a).IsNegInvariant := by
  refine isNegInvariant_of_preimage fun s hs => ?_
  rw [comb_apply a (measurable_neg hs), comb_apply a hs]
  have e : ∀ n : ℤ, (Neg.neg ⁻¹' s).indicator (1 : ℝ → ENNReal) (a * (n : ℝ))
      = s.indicator (1 : ℝ → ENNReal) (a * ((-n : ℤ) : ℝ)) := by
    intro n
    by_cases h : -(a * (n : ℝ)) ∈ s
    · rw [Set.indicator_of_mem (show a * (n : ℝ) ∈ Neg.neg ⁻¹' s from h),
        Set.indicator_of_mem (show a * (((-n : ℤ) : ℝ)) ∈ s by push_cast; rw [mul_neg]; exact h)]
      rfl
    · rw [Set.indicator_of_notMem (show a * (n : ℝ) ∉ Neg.neg ⁻¹' s from h),
        Set.indicator_of_notMem (show a * (((-n : ℤ) : ℝ)) ∉ s by push_cast; rw [mul_neg]; exact h)]
  simp_rw [e]
  exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => s.indicator (1 : ℝ → ENNReal) (a * (n : ℝ)))

lemma gauss_mul_arg (t a y : ℝ) : gauss t (a * y) = gauss (t * a ^ 2) y := by
  unfold gauss; congr 1; ring

lemma integral_gauss_comb (a t : ℝ) : ∫ x, gauss t x ∂comb a = jθ (t * a ^ 2) := by
  rw [comb, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  simp only [ENNReal.toReal_one, one_smul, jθ]
  simp_rw [gauss_mul_arg]

lemma comb_gaussIntegrable {a : ℝ} (ha : a ≠ 0) : GaussIntegrable (comb a) := by
  intro t ht
  have hc : ∀ n : ℤ, (1 : ENNReal) ≠ ⊤ := fun _ => ENNReal.one_ne_top
  rw [comb, integrable_sum_dirac_iff hc]
  have := summable_gauss_int (u := t * a ^ 2) (by positivity)
  simpa [Real.norm_of_nonneg (gauss_nonneg _ _), gauss_mul_arg] using this

lemma isNegInvariant_add {μ₁ μ₂ : Measure ℝ} (h₁ : μ₁.IsNegInvariant) (h₂ : μ₂.IsNegInvariant) :
    (μ₁ + μ₂).IsNegInvariant := by
  refine isNegInvariant_of_preimage fun s hs => ?_
  have e₁ : μ₁ (Neg.neg ⁻¹' s) = μ₁ s := by
    rw [← Measure.map_apply measurable_neg hs, ← Measure.neg_def, Measure.neg_eq_self]
  have e₂ : μ₂ (Neg.neg ⁻¹' s) = μ₂ s := by
    rw [← Measure.map_apply measurable_neg hs, ← Measure.neg_def, Measure.neg_eq_self]
  rw [Measure.add_apply, Measure.add_apply, e₁, e₂]

lemma isNegInvariant_smul {μ : Measure ℝ} (h : μ.IsNegInvariant) (r : ENNReal) :
    (r • μ).IsNegInvariant := by
  refine isNegInvariant_of_preimage fun s hs => ?_
  have e : μ (Neg.neg ⁻¹' s) = μ s := by
    rw [← Measure.map_apply measurable_neg hs, ← Measure.neg_def, Measure.neg_eq_self]
  rw [Measure.smul_apply, Measure.smul_apply, e]

lemma nup_isNegInvariant (p c : ℝ) : (nup p c).IsNegInvariant := by
  unfold nup
  exact isNegInvariant_add (isNegInvariant_add (isNegInvariant_smul (comb_isNegInvariant _) _)
    (isNegInvariant_smul (comb_isNegInvariant _) _)) (isNegInvariant_smul (comb_isNegInvariant _) _)

lemma nup_gaussIntegrable {p : ℝ} (hp : 0 < p) (c : ℝ) : GaussIntegrable (nup p c) := by
  intro t ht
  unfold nup
  refine ((Integrable.add_measure ?_ ?_).add_measure ?_) <;>
    exact (comb_gaussIntegrable (by positivity) t ht).smul_measure ENNReal.ofReal_ne_top

lemma mθ_nup {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) (t : ℝ) (ht : 0 < t) :
    mθ (nup p c) t = 1 / Real.sqrt p * jθ (t * (1 / p) ^ 2) + c * jθ (t * 1 ^ 2)
      + Real.sqrt p * jθ (t * p ^ 2) := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have i1 := (comb_gaussIntegrable (a := 1 / p) (by positivity) t ht).smul_measure
    (ENNReal.ofReal_ne_top (r := 1 / Real.sqrt p))
  have i2 := (comb_gaussIntegrable (a := 1) one_ne_zero t ht).smul_measure
    (ENNReal.ofReal_ne_top (r := c))
  have i3 := (comb_gaussIntegrable (a := p) hp.ne' t ht).smul_measure
    (ENNReal.ofReal_ne_top (r := Real.sqrt p))
  unfold mθ nup
  rw [integral_add_measure (i1.add_measure i2) i3, integral_add_measure i1 i2]
  simp only [integral_smul_measure, integral_gauss_comb, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hc,
    ENNReal.toReal_ofReal hsp.le]

lemma alg_nup {q t A B D c : ℝ} (hq : 0 < q) :
    1 / q * (t * (q * q) * A) + c * (t * B) + q * (t / (q * q) * D)
      = t * (1 / q * D + c * B + q * A) := by
  field_simp
  ring

/-- **The fooling family satisfies the modular relation with `β = 0` (kernel).** -/
theorem nup_theta {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) : ThetaRelation (nup p c) 0 := by
  intro t ht
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [mθ_nup hp hc t ht, mθ_nup hp hc (1 / t) (by positivity)]
  have a1 : jθ (1 / t * (1 / p) ^ 2) = Real.sqrt t * p * jθ (t * p ^ 2) := by
    have h := jθ_inv (u := t * p ^ 2) (by positivity)
    rw [show 1 / t * (1 / p) ^ 2 = 1 / (t * p ^ 2) by field_simp, h,
      Real.sqrt_mul ht.le, Real.sqrt_sq hp.le]
  have a2 : jθ (1 / t * 1 ^ 2) = Real.sqrt t * jθ (t * 1 ^ 2) := by
    rw [one_pow, mul_one, mul_one, jθ_inv ht]
  have a3 : jθ (1 / t * p ^ 2) = Real.sqrt t / p * jθ (t * (1 / p) ^ 2) := by
    have h := jθ_inv (u := t * (1 / p) ^ 2) (by positivity)
    rw [show 1 / t * p ^ 2 = 1 / (t * (1 / p) ^ 2) by field_simp, h,
      Real.sqrt_mul ht.le, Real.sqrt_sq (by positivity)]
    field_simp
  rw [a1, a2, a3]
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have key := alg_nup (q := Real.sqrt p) (t := Real.sqrt t) (A := jθ (t * p ^ 2))
    (B := jθ (t * 1 ^ 2)) (D := jθ (t * (1 / p) ^ 2)) (c := c) hsp
  rw [hsq] at key
  rw [key]
  push_cast
  ring

/-- The fooling family's `C_c` self-duality, RE-DERIVED from its theta relation by the Gaussian
determination theorem (an independent check of round 2's `nup_isPoissonPair`, which used
Poisson summation for dilated lattices). -/
theorem nup_isPoissonPair_via_theta {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) :
    IsPoissonPair (nup p c) 0 := by
  have : IsFiniteMeasureOnCompacts (nup p c) := nup_isFiniteMeasureOnCompacts hp c
  have := nup_isNegInvariant p c
  exact isPoissonPair_of_theta (nup_gaussIntegrable hp c) (nup_theta hp hc)

/-- **CAPSTONE (kernel): Theorem A in modular-relation form pins the integers, and is blind to
zeros.**

(1) Every positive, locally finite, even, Gaussian-integrable measure with the gap and Jacobi's
    relation `θ(1/t) = √t θ(t)` is `ν{0} • Σ_{n∈ℤ} δ_n`; the comb is admissible.
(2) For `p > 1` and `2 < c < √p + 1/√p`, the measure `ν_{p,c}` is positive, locally finite, even,
    Gaussian-integrable, satisfies Jacobi's relation EXACTLY, has an atom at `0`, violates only the
    gap, and the completed Mellin transform `Λ_{p,c} = Λ_ζ · Q_{p,c}` of its positive half has ζ's
    exact functional equation and a zero with `1/2 < Re s < 1`. -/
theorem theta_rigidity_is_rh_blind :
    (∀ ν : Measure ℝ, ∀ _ : IsLocallyFiniteMeasure ν, ∀ _ : ν.IsNegInvariant,
        GaussIntegrable ν → ThetaRelation ν 0 → ν (Ioo (-1) 1 \ {0}) = 0 → ν = ν {0} • intComb) ∧
    (intComb.IsNegInvariant ∧ GaussIntegrable intComb ∧ ThetaRelation intComb 0 ∧
        intComb (Ioo (-1) 1 \ {0}) = 0 ∧ intComb {0} = 1) ∧
    (∀ p c : ℝ, 1 < p → 2 < c → c < Real.sqrt p + 1 / Real.sqrt p →
        IsFiniteMeasureOnCompacts (nup p c) ∧ (nup p c).IsNegInvariant ∧
        GaussIntegrable (nup p c) ∧ ThetaRelation (nup p c) 0 ∧ IsPoissonPair (nup p c) 0 ∧
        nup p c {0} ≠ 0 ∧ nup p c (Ioo (-1) 1 \ {0}) ≠ 0 ∧ (∀ r : ENNReal, nup p c ≠ r • intComb) ∧
        (∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ =>
            ((1 / Real.sqrt p : ℝ) : ℂ) * ((((n : ℝ) + 1) / p : ℝ) : ℂ) ^ (-s)
            + (c : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
            + ((Real.sqrt p : ℝ) : ℂ) * ((p * ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s))
          (riemannZeta s * Qp p c s)) ∧
        (∀ s : ℂ, LambdaP p c (1 - s) = LambdaP p c s) ∧
        (LambdaP p c (sStar p c) = 0 ∧ 1 / 2 < (sStar p c).re ∧ (sStar p c).re < 1)) := by
  refine ⟨fun ν _ _ hν hθ hgap => thmA_theta_selfDual hν hθ hgap,
    ⟨intComb_isNegInvariant, intComb_gaussIntegrable, intComb_theta, intComb_gap,
      (intComb_admissible).2.2.2⟩, ?_⟩
  intro p c hp hc hc'
  have hp0 : 0 < p := by linarith
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨hs0, hgt, hlt⟩ := Qp_offline_zero_in_strip hp hc hc'
  refine ⟨nup_isFiniteMeasureOnCompacts hp0 c, nup_isNegInvariant p c, nup_gaussIntegrable hp0 c,
    nup_theta hp0 hc0, nup_isPoissonPair_via_theta hp0 hc0, nup_atom_zero_ne_zero hp0 c,
    nup_gap_violated hp c, nup_ne_smul_intComb hp c, fun s hs => nup_dirichlet hp0 c hs,
    LambdaP_one_sub p c, ⟨?_, hgt, hlt⟩⟩
  unfold LambdaP; rw [hs0, mul_zero]

/-- **Onset control (kernel).** For `0 ≤ c ≤ 2` the same family satisfies the same theta relation,
and every zero of its extra factor `Q_{p,c}` is on the critical line. The theta data do not change
across `c = 2`; the zero location does, exactly at local Ramanujan (`satake_ramanujan_iff`). -/
theorem theta_fooling_onset {p c : ℝ} (hp : 1 < p) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    ThetaRelation (nup p c) 0 ∧ (∀ s : ℂ, Qp p c s = 0 → s.re = 1 / 2) ∧
    ((∀ α : ℂ, α ^ 2 + ((c * Real.sqrt p : ℝ) : ℂ) * α + p = 0 → ‖α‖ = Real.sqrt p) ↔ c ≤ 2) :=
  ⟨nup_theta (by linarith) hc0, fun _ hs => Qp_zero_re_of_le_two hp hc0 hc2 hs,
    satake_ramanujan_iff (by linarith) hc0⟩

/-- **Round 1's `W1(29,11)` and golden fake satisfy Jacobi's relation exactly (kernel).** -/
theorem controls_in_theta_form :
    ThetaRelation (nup 29 (11 / Real.sqrt 29)) 0 ∧ ThetaRelation (nup 5 (Real.sqrt 5)) 0 ∧
    (∀ s : ℂ, Complex.exp (-((s - 1 / 2) * (Real.log 29 : ℂ))) * Qp 29 (11 / Real.sqrt 29) s
      = 1 + 11 * Complex.exp (-(s * (Real.log 29 : ℂ)))
        + 29 * Complex.exp (-(2 * s * (Real.log 29 : ℂ)))) := by
  obtain ⟨h1, _, h3⟩ := W1_parameters
  refine ⟨nup_theta (by norm_num) (by linarith), nup_theta (by norm_num) (Real.sqrt_nonneg _),
    fun s => ?_⟩
  rw [Qp_euler_factor (by norm_num) _ s, h3]
  push_cast
  ring

/-! ## Part 8. Restatements in Mathlib-only vocabulary (guards against rigged definitions) -/

/-- Theorem A, theta form, stated with raw Mathlib objects only: Jacobi's relation for the Gaussian
integrals of a positive even locally finite measure with the unit gap forces it onto `ℤ`. -/
theorem writer_thmA_theta (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant]
    (hint : ∀ t : ℝ, 0 < t → Integrable (fun x : ℝ => Real.exp (-π * t * x ^ 2)) ν)
    (hθ : ∀ t : ℝ, 0 < t → ∫ x, Real.exp (-π * (1 / t) * x ^ 2) ∂ν
      = Real.sqrt t * ∫ x, Real.exp (-π * t * x ^ 2) ∂ν)
    (hgap : ν (Set.Ioo (-1) 1 \ {0}) = 0) :
    ν = ν {0} • Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ)) := by
  have hν : GaussIntegrable ν := hint
  have hθ' : ThetaRelation ν 0 := by
    intro t ht
    simp only [mθ, gauss, zero_mul, add_zero]
    rw [hθ t ht]
    push_cast; ring
  have h1 := thmA_theta_selfDual hν hθ' hgap
  have h2 : intComb = Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ)) := by
    rw [intComb]; simp only [one_smul]
  calc ν = ν {0} • intComb := h1
    _ = ν {0} • Measure.sum (fun n : ℤ => Measure.dirac (n : ℝ)) := by rw [h2]

/-- The Gaussian determination theorem, stated with raw Mathlib objects only (`β = 0`). -/
theorem writer_gaussian_determination (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] [ν.IsNegInvariant]
    (hint : ∀ t : ℝ, 0 < t → Integrable (fun x : ℝ => Real.exp (-π * t * x ^ 2)) ν)
    (hθ : ∀ t : ℝ, 0 < t → ∫ x, Real.exp (-π * (1 / t) * x ^ 2) ∂ν
      = Real.sqrt t * ∫ x, Real.exp (-π * t * x ^ 2) ∂ν) :
    ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → Integrable (𝓕 f) ν →
      ∫ ξ, 𝓕 f ξ ∂ν = ∫ x, f x ∂ν := by
  have hν : GaussIntegrable ν := hint
  have hθ' : ThetaRelation ν 0 := by
    intro t ht
    simp only [mθ, gauss, zero_mul, add_zero]
    rw [hθ t ht]
    push_cast; ring
  intro f h1 h2 h3
  have := isPoissonPair_of_theta hν hθ' f h1 h2 h3
  rw [this]; ring

/-! ## Part 9. Round 1's milestone `RH_classP_collapse_beurling_q1` reduced to the Mellin step

The registry draft (RH_AXIOM_ISOLATION_2026-09-22 §5.2) states NT4 with `BeurlingNormalized` and
`ZetaShapeFE`, copied verbatim below. We prove: the conclusion of NT4 follows from the modular
relation for the even extension `δ₀ + N + N(-·)`, so NT4 is kernel-equivalent to the single classical
step "`ZetaShapeFE 1 N` implies the modular relation" (`Step2MellinHalf`, NOT proved here). -/

/-- Round 1's normalization of a Beurling-type measure (registry draft, verbatim). -/
def BeurlingNormalized (N : Measure ℝ) : Prop :=
  N (Set.Iio 1) = 0 ∧ N {1} = 1 ∧
    ∃ C k : ℝ, ∀ X : ℝ, 1 ≤ X → N (Set.Icc 1 X) ≤ ENNReal.ofReal (C * X ^ k)

/-- Round 1's zeta-shape functional equation with conductor `q` (registry draft, verbatim). -/
def ZetaShapeFE (q : ℝ) (N : Measure ℝ) : Prop :=
  ∃ (ε : ℂ) (ξ : ℂ → ℂ) (σ₀ : ℝ), Differentiable ℂ ξ ∧
    (∃ C c : ℝ, ∀ s : ℂ, ‖ξ s‖ ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖))) ∧
    (∀ s : ℂ, σ₀ < s.re →
      Integrable (fun x : ℝ => (x : ℂ) ^ (-s)) N ∧
      ξ s = s * (s - 1) * ((q : ℂ) / (Real.pi : ℂ)) ^ (s / 2) * Complex.Gamma (s / 2) *
        ∫ x, (x : ℂ) ^ (-s) ∂N) ∧
    ∀ s : ℂ, ξ s = ε * (starRingEnd ℂ) (ξ (1 - (starRingEnd ℂ) s))

/-- The even extension `δ₀ + N + N(-·)` of a measure on `[1,∞)`. -/
def symmExt (N : Measure ℝ) : Measure ℝ := Measure.dirac 0 + N + N.map Neg.neg

/-- **The one remaining step of Theorem A (a `Prop`, NOT proved here).** Hamburger/Bochner: the
zeta-shape FE with conductor 1 of a normalized Beurling measure implies the modular relation of its
even extension. Mathlib has the converse direction (`WeakFEPair`); this direction needs Mellin
inversion, a contour shift across the two poles, and Phragmen-Lindelof in the strip. -/
def Step2MellinHalf : Prop :=
  ∀ N : Measure ℝ, BeurlingNormalized N → ZetaShapeFE 1 N → ∃ β : ℂ, ThetaRelation (symmExt N) β

lemma measure_Icc_lt_top_of_beurling {N : Measure ℝ} (hN : BeurlingNormalized N) (R : ℝ) :
    N (Icc (-R) R) < ⊤ := by
  obtain ⟨h0, -, C, k, hCk⟩ := hN
  have hsub : Icc (-R) R ⊆ Iio 1 ∪ Icc 1 (max R 1) := by
    intro x hx
    by_cases h : x < 1
    · exact Or.inl h
    · exact Or.inr ⟨not_lt.mp h, le_trans hx.2 (le_max_left _ _)⟩
  calc N (Icc (-R) R) ≤ N (Iio 1 ∪ Icc 1 (max R 1)) := measure_mono hsub
    _ ≤ N (Iio 1) + N (Icc 1 (max R 1)) := measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (C * (max R 1) ^ k) := by
        rw [h0]; exact add_le_add le_rfl (hCk _ (le_max_right _ _))
    _ < ⊤ := by rw [zero_add]; exact ENNReal.ofReal_lt_top

lemma symmExt_apply (N : Measure ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    symmExt N s = Measure.dirac (0 : ℝ) s + N s + N (Neg.neg ⁻¹' s) := by
  unfold symmExt
  rw [Measure.add_apply, Measure.add_apply, Measure.map_apply measurable_neg hs]

lemma symmExt_finiteOnCompacts {N : Measure ℝ} (hN : BeurlingNormalized N) :
    IsFiniteMeasureOnCompacts (symmExt N) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
  refine (measure_mono hR).trans_lt ?_
  rw [symmExt_apply N measurableSet_Icc]
  have h1 := measure_Icc_lt_top_of_beurling hN R
  have h2 : N (Neg.neg ⁻¹' Icc (-R) R) < ⊤ := by
    have : Neg.neg ⁻¹' Icc (-R) R = Icc (-R) R := by
      ext x; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro h <;>
        constructor <;> linarith [h.1, h.2]
    rw [this]; exact h1
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, h1⟩, h2⟩

lemma symmExt_isNegInvariant (N : Measure ℝ) : (symmExt N).IsNegInvariant := by
  refine isNegInvariant_of_preimage fun s hs => ?_
  rw [symmExt_apply N (measurable_neg hs), symmExt_apply N hs]
  have e : Neg.neg ⁻¹' (Neg.neg ⁻¹' s) = s := by ext x; simp
  have ed : Measure.dirac (0 : ℝ) (Neg.neg ⁻¹' s) = Measure.dirac (0 : ℝ) s := by
    rw [Measure.dirac_apply' _ (measurable_neg hs), Measure.dirac_apply' _ hs]
    by_cases h : (0 : ℝ) ∈ s
    · rw [Set.indicator_of_mem (show (0 : ℝ) ∈ Neg.neg ⁻¹' s by simpa using h),
        Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show (0 : ℝ) ∉ Neg.neg ⁻¹' s by simpa using h),
        Set.indicator_of_notMem h]
  rw [e, ed, add_assoc, add_assoc, add_comm (N (Neg.neg ⁻¹' s)) (N s)]

/-- Polynomial growth on `[1,∞)` gives every Gaussian moment. -/
lemma integrable_gauss_of_beurling {N : Measure ℝ} (hN : BeurlingNormalized N) {t : ℝ}
    (ht : 0 < t) : Integrable (gauss t) N := by
  obtain ⟨h0, -, C, k, hCk⟩ := hN
  refine ⟨(continuous_gauss t).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gauss_nonneg t))]
  set C' := max C 0 with hC'
  -- pointwise majorant on `[1,∞)`, which carries `N`
  have hae : ∀ᵐ x ∂N, 1 ≤ x := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 1 ≤ a} = Iio 1 := by ext a; simp
    rw [this, h0]
  have hpt : ∀ᵐ x ∂N, ENNReal.ofReal (gauss t x)
      ≤ ∑' j : ℕ, ENNReal.ofReal (gauss t (2 ^ j)) * (Icc 1 ((2 : ℝ) ^ (j + 1))).indicator 1 x := by
    filter_upwards [hae] with x hx
    have hex : ∃ j : ℕ, x ≤ 2 ^ (j + 1) := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, hn.le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))⟩
    classical
    set j := Nat.find hex with hj
    have hxj : x ≤ 2 ^ (j + 1) := Nat.find_spec hex
    have hlow : (2 : ℝ) ^ j ≤ x := by
      rcases Nat.eq_zero_or_pos j with h0' | hpos
      · rw [h0', pow_zero]; exact hx
      · have := Nat.find_min hex (show j - 1 < j by omega)
        rw [not_le] at this
        have e : j - 1 + 1 = j := by omega
        rw [e] at this
        exact this.le
    have hmem : x ∈ Icc (1 : ℝ) (2 ^ (j + 1)) := ⟨hx, hxj⟩
    have hg : gauss t x ≤ gauss t (2 ^ j) := by
      unfold gauss
      apply Real.exp_le_exp.mpr
      have h2 : (0 : ℝ) ≤ 2 ^ j := by positivity
      have h3 : ((2 : ℝ) ^ j) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ h2 hlow 2
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ π * t)
      linarith
    calc ENNReal.ofReal (gauss t x) ≤ ENNReal.ofReal (gauss t (2 ^ j)) :=
          ENNReal.ofReal_le_ofReal hg
      _ = ENNReal.ofReal (gauss t (2 ^ j)) * (Icc 1 ((2 : ℝ) ^ (j + 1))).indicator 1 x := by
          rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (gauss t (2 ^ j)) * (Icc 1 ((2 : ℝ) ^ (j + 1))).indicator 1 x :=
          ENNReal.le_tsum (f := fun j : ℕ =>
            ENNReal.ofReal (gauss t (2 ^ j)) * (Icc 1 ((2 : ℝ) ^ (j + 1))).indicator 1 x) j
  -- summability of the dyadic weights, by the ratio test
  set a : ℕ → ℝ := fun j => gauss t (2 ^ j) * (C' * ((2 : ℝ) ^ (j + 1)) ^ k) with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => mul_nonneg (gauss_nonneg _ _)
    (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))
  have hsum : Summable a := by
    by_cases hC0 : C' = 0
    · have : a = fun _ => 0 := by funext j; simp [ha, hC0]
      rw [this]; exact summable_zero
    have hCpos : 0 < C' := lt_of_le_of_ne (le_max_right _ _) (Ne.symm hC0)
    have hapos : ∀ j, 0 < a j := fun j => mul_pos (gauss_pos _ _)
      (mul_pos hCpos (Real.rpow_pos_of_pos (by positivity) _))
    refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
      (Eventually.of_forall fun j => (hapos j).ne') ?_
    have hratio : ∀ j : ℕ, ‖a (j + 1)‖ / ‖a j‖
        = Real.exp (-(3 * π * t) * 4 ^ j) * (2 : ℝ) ^ k := by
      intro j
      rw [Real.norm_of_nonneg (ha0 _), Real.norm_of_nonneg (ha0 _)]
      simp only [ha, gauss]
      have e1 : ((2 : ℝ) ^ (j + 1 + 1)) ^ k = (2 : ℝ) ^ k * ((2 : ℝ) ^ (j + 1)) ^ k := by
        rw [← Real.mul_rpow (by norm_num) (by positivity), pow_succ, mul_comm]
      have e2 : Real.exp (-π * t * ((2 : ℝ) ^ (j + 1)) ^ 2)
          = Real.exp (-(3 * π * t) * 4 ^ j) * Real.exp (-π * t * ((2 : ℝ) ^ j) ^ 2) := by
        rw [← Real.exp_add]; congr 1
        rw [show (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring
      rw [e1, e2]
      have hx1 : 0 < Real.exp (-π * t * ((2 : ℝ) ^ j) ^ 2) := Real.exp_pos _
      have hx2 : 0 < ((2 : ℝ) ^ (j + 1)) ^ k := Real.rpow_pos_of_pos (by positivity) _
      field_simp
    simp_rw [hratio]
    have h4 : Tendsto (fun j : ℕ => (4 : ℝ) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hexp : Tendsto (fun j : ℕ => Real.exp (-(3 * π * t) * 4 ^ j)) atTop (𝓝 0) := by
      have hc : 0 < 3 * π * t := by positivity
      have := (Real.tendsto_exp_neg_atTop_nhds_zero).comp (h4.const_mul_atTop hc)
      refine this.congr fun j => ?_
      simp only [Function.comp_apply]; ring_nf
    simpa using hexp.mul_const ((2 : ℝ) ^ k)
  calc ∫⁻ x, ENNReal.ofReal (gauss t x) ∂N
      ≤ ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal (gauss t (2 ^ j))
          * (Icc 1 ((2 : ℝ) ^ (j + 1))).indicator 1 x ∂N := lintegral_mono_ae hpt
    _ = ∑' j : ℕ, ∫⁻ x, ENNReal.ofReal (gauss t (2 ^ j))
          * (Icc 1 ((2 : ℝ) ^ (j + 1))).indicator 1 x ∂N :=
        lintegral_tsum fun j => (measurable_const.mul
          ((measurable_one.indicator measurableSet_Icc))).aemeasurable
    _ = ∑' j : ℕ, ENNReal.ofReal (gauss t (2 ^ j)) * N (Icc 1 ((2 : ℝ) ^ (j + 1))) := by
        congr 1; funext j
        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Icc),
          lintegral_indicator_one measurableSet_Icc]
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (a j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        simp only [ha]
        rw [ENNReal.ofReal_mul (gauss_nonneg _ _)]
        gcongr
        refine (hCk _ (one_le_pow₀ (by norm_num))).trans ?_
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (by positivity) _)
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum]
        exact ENNReal.ofReal_lt_top

lemma symmExt_gaussIntegrable {N : Measure ℝ} (hN : BeurlingNormalized N) :
    GaussIntegrable (symmExt N) := by
  intro t ht
  have hN' := integrable_gauss_of_beurling hN ht
  unfold symmExt
  have hd : Integrable (gauss t) (Measure.dirac (0 : ℝ)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (continuous_gauss t).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (gauss_nonneg _ _)]
    exact gauss_le_one ht.le x
  have hm : Integrable (gauss t) (N.map Neg.neg) := by
    have h' : Integrable (fun x => gauss t (-x)) N :=
      hN'.congr (ae_of_all _ fun x => (gauss_neg t x).symm)
    exact (integrable_map_measure (continuous_gauss t).aestronglyMeasurable
      measurable_neg.aemeasurable).mpr h'
  exact (hd.add_measure hN').add_measure hm

/-- **NT4 from the modular relation (kernel).** A normalized Beurling measure whose even extension
satisfies the modular relation (with any footprint `β`) is `Σ_{n≥1} δ_n`. -/
theorem classP_collapse_beurling_q1_of_theta (N : Measure ℝ) (hN : BeurlingNormalized N) {β : ℂ}
    (hθ : ThetaRelation (symmExt N) β) :
    N = Measure.sum (fun n : ℕ => Measure.dirac ((n : ℝ) + 1)) := by
  have hfin := symmExt_finiteOnCompacts hN
  have hneg := symmExt_isNegInvariant N
  have hG := symmExt_gaussIntegrable hN
  obtain ⟨h0, h1, -⟩ := hN
  have hN0 : N {0} = 0 := measure_mono_null (by intro x hx; simp at hx; simp [hx]) h0
  have hNm1 : N {-1} = 0 := measure_mono_null (by intro x hx; simp at hx; simp [hx]) h0
  have hν0 : symmExt N {0} = 1 := by
    rw [symmExt_apply N (measurableSet_singleton 0), hN0]
    have hd0 : Measure.dirac (0 : ℝ) {0} = 1 := by
      rw [Measure.dirac_apply' _ (measurableSet_singleton 0)]; simp
    have : Neg.neg ⁻¹' ({0} : Set ℝ) = {0} := by ext x; simp
    rw [this, hN0, hd0]; simp
  have hν1 : symmExt N {1} = 1 := by
    rw [symmExt_apply N (measurableSet_singleton 1), h1]
    have hd : Measure.dirac (0 : ℝ) {1} = 0 := by
      rw [Measure.dirac_apply' _ (measurableSet_singleton 1)]; simp
    have : Neg.neg ⁻¹' ({1} : Set ℝ) = {-1} := by ext x; simp
    rw [this, hNm1, hd]; simp
  have hgap : symmExt N (Ioo (-1) 1 \ {0}) = 0 := by
    have hS : MeasurableSet (Ioo (-1 : ℝ) 1 \ {0}) := measurableSet_Ioo.diff (measurableSet_singleton 0)
    rw [symmExt_apply N hS]
    have hd : Measure.dirac (0 : ℝ) (Ioo (-1) 1 \ {0}) = 0 := by
      rw [Measure.dirac_apply' _ hS]; simp
    have hA : N (Ioo (-1) 1 \ {0}) = 0 := measure_mono_null (fun x hx => hx.1.2) h0
    have hB : N (Neg.neg ⁻¹' (Ioo (-1) 1 \ {0})) = 0 :=
      measure_mono_null (fun x hx => by
        simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_Ioo] at hx
        show x < 1
        linarith [hx.1.1]) h0
    rw [hd, hA, hB]; simp
  -- Theorem A: masses, then β = 0
  obtain ⟨-, hm, -⟩ := thmA_theta hG hθ hgap
  have hβ : β = 0 := by
    have h := hm 1 one_ne_zero
    have e1 : (symmExt N).real {((1 : ℤ) : ℝ)} = 1 := by
      rw [Measure.real, Int.cast_one, hν1]; simp
    have e0 : (symmExt N).real {0} = 1 := by rw [Measure.real, hν0]; simp
    rw [e1, e0] at h
    linear_combination -h
  subst hβ
  have hcomb : symmExt N = intComb := by
    rw [thmA_theta_selfDual hG hθ hgap, hν0, one_smul]
  -- read off `N` on `[1,∞)`
  ext s hs
  have hNs : N s = N (s ∩ Ici 1) := by
    rw [← measure_inter_add_sdiff s (measurableSet_Ici (a := (1 : ℝ)))]
    have : N (s \ Ici 1) = 0 := measure_mono_null (fun x hx => by
      have := hx.2; simp only [Set.mem_Ici, not_le] at this; exact this) h0
    rw [this, add_zero]
  have hsym : symmExt N (s ∩ Ici 1) = N (s ∩ Ici 1) := by
    rw [symmExt_apply N (hs.inter measurableSet_Ici)]
    have hd : Measure.dirac (0 : ℝ) (s ∩ Ici 1) = 0 := by
      rw [Measure.dirac_apply' _ (hs.inter measurableSet_Ici)]
      rw [Set.indicator_of_notMem (by simp)]
    have hB : N (Neg.neg ⁻¹' (s ∩ Ici 1)) = 0 :=
      measure_mono_null (fun x hx => by
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ici] at hx
        show x < 1
        linarith [hx.2]) h0
    rw [hd, hB, zero_add, add_zero]
  rw [hNs, ← hsym, hcomb, intComb_apply (hs.inter measurableSet_Ici),
    Measure.sum_apply _ hs]
  have hinj : Function.Injective (fun n : ℕ => ((n : ℤ) + 1)) := by
    intro a b h; simpa using h
  have hsupp : Function.support (fun z : ℤ => (s ∩ Ici 1).indicator (1 : ℝ → ENNReal) (z : ℝ))
      ⊆ Set.range (fun n : ℕ => ((n : ℤ) + 1)) := by
    intro z hz
    have hz' : (z : ℝ) ∈ s ∩ Ici 1 := by
      by_contra hc
      exact hz (Set.indicator_of_notMem hc _)
    have h1z' : (1 : ℝ) ≤ (z : ℝ) := Set.mem_Ici.mp hz'.2
    have h1z : (1 : ℤ) ≤ z := by exact_mod_cast h1z'
    refine ⟨(z - 1).toNat, ?_⟩
    simp only
    omega
  rw [← hinj.tsum_eq hsupp]
  congr 1; funext n
  rw [Measure.dirac_apply' _ hs]
  have hn1 : ((((n : ℤ) + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hn1]
  have hmemI : (n : ℝ) + 1 ∈ Ici (1 : ℝ) := by
    simp only [Set.mem_Ici]; have := n.cast_nonneg (α := ℝ); linarith
  by_cases hsn : (n : ℝ) + 1 ∈ s
  · rw [Set.indicator_of_mem (show (n : ℝ) + 1 ∈ s ∩ Ici 1 from ⟨hsn, hmemI⟩),
      Set.indicator_of_mem hsn]
  · rw [Set.indicator_of_notMem (fun h => hsn h.1), Set.indicator_of_notMem hsn]

/-- **NT4 is kernel-reduced to the Mellin step (kernel).** If the classical converse
`Step2MellinHalf` holds, round 1's milestone `classP_collapse_beurling_q1` follows. -/
theorem classP_collapse_beurling_q1_of_step2 (h2 : Step2MellinHalf) :
    ∀ N : Measure ℝ, BeurlingNormalized N → ZetaShapeFE 1 N →
      N = Measure.sum (fun n : ℕ => Measure.dirac ((n : ℝ) + 1)) := by
  intro N hN hFE
  obtain ⟨β, hθ⟩ := h2 N hN hFE
  exact classP_collapse_beurling_q1_of_theta N hN hθ

/-! ## Part 10. The root number: the anti-modular relation is impossible (kernel)

`ZetaShapeFE` quantifies the root number `ε` existentially. For a real measure `ε = ±1`, and for
`ε = -1` the classical converse yields the ANTI-modular relation
`θ_ν(t) + t^{-1/2} θ_ν(1/t) = c (1 + t^{-1/2})`, i.e. `ν̂ = -ν + c(δ₀ + Leb)` on Gaussians. Theorem A's
Fejer mechanism does not apply to it. It is nevertheless impossible for a positive measure with the gap
and an atom at `1`: the self-dual test `K = 2 G_1 - G_4 - G_{1/4}/2` has `K(0) = 1/2 > 0` and
`K ≤ -G_4 < 0` on `|x| ≥ 1`, and two instances of the relation (`t = 1`, `t = 4`) give
`∫ K dν = c/2 = θ_ν(1)/2`, which positivity contradicts. -/

/-- The anti-modular relation (root number `-1`). -/
def AntiThetaRelation (ν : Measure ℝ) (c : ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → ((mθ ν t : ℝ) : ℂ) + ((Real.sqrt t)⁻¹ : ℝ) * ((mθ ν (1 / t) : ℝ) : ℂ)
    = c * (1 + ((Real.sqrt t)⁻¹ : ℝ))

/-- The LP test `K = 2 G_1 - G_4 - (1/2) G_{1/4}` (self-dual: `K = f + 𝓕 f` with `f = G_1 - G_4`). -/
def Kanti (x : ℝ) : ℝ := 2 * gauss 1 x - gauss 4 x - (1 / 2) * gauss (1 / 4) x

lemma Kanti_zero : Kanti 0 = 1 / 2 := by
  simp only [Kanti, gauss_zero]; norm_num

lemma four_le_exp : (4 : ℝ) ≤ Real.exp (3 * π / 4) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
  have h5 : Real.exp 2 ≤ Real.exp (3 * π / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  linarith

lemma Kanti_le {x : ℝ} (hx : 1 ≤ |x|) : Kanti x ≤ -gauss 4 x := by
  unfold Kanti
  have hx2 : 1 ≤ x ^ 2 := by
    have := mul_le_mul hx hx zero_le_one (abs_nonneg x)
    rwa [one_mul, ← sq, sq_abs] at this
  have hmono : Real.exp (3 * π / 4) ≤ Real.exp (3 * π / 4 * x ^ 2) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 3 * π / 4)
    linarith
  have key : 2 * gauss 1 x ≤ (1 / 2) * gauss (1 / 4) x := by
    unfold gauss
    have e : Real.exp (-π * (1 / 4) * x ^ 2)
        = Real.exp (-π * 1 * x ^ 2) * Real.exp (3 * π / 4 * x ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    have hp := Real.exp_pos (-π * 1 * x ^ 2)
    have h4 := four_le_exp
    nlinarith
  linarith

lemma Kanti_one_neg : Kanti 1 < 0 :=
  lt_of_le_of_lt (Kanti_le (by simp)) (neg_neg_of_pos (gauss_pos 4 1))

lemma continuous_Kanti : Continuous Kanti := by
  unfold Kanti
  have := continuous_gauss 1; have := continuous_gauss 4; have := continuous_gauss (1 / 4)
  fun_prop

/-- **No anti-modular relation (kernel).** A positive locally finite Gaussian-integrable measure with
the gap `(-1,1) \ {0}` and a positive atom at `1` satisfies no anti-modular relation. -/
theorem no_antiTheta {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hν : GaussIntegrable ν) {c : ℂ}
    (hanti : AntiThetaRelation ν c) (hgap : ν (Ioo (-1) 1 \ {0}) = 0) (h1 : 0 < ν.real {1}) :
    False := by
  have hA := hanti 1 one_pos
  have hB := hanti 4 (by norm_num)
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs4] at hB
  rw [Real.sqrt_one, inv_one, div_one] at hA
  have hc : c = (mθ ν 1 : ℂ) := by
    push_cast at hA
    linear_combination -hA / 2
  rw [hc] at hB
  have hBr : mθ ν 4 + (1 / 2) * mθ ν (1 / 4) = mθ ν 1 * (1 + 1 / 2) := by
    have h := hB
    push_cast at h
    have h' : ((mθ ν 4 + 2⁻¹ * mθ ν (1 / 4) : ℝ) : ℂ) = ((mθ ν 1 * (1 + 2⁻¹) : ℝ) : ℂ) := by
      push_cast; linear_combination h
    have := Complex.ofReal_injective h'
    linarith
  have hi1 := hν 1 one_pos
  have hi4 := hν 4 (by norm_num)
  have hi14 := hν (1 / 4) (by norm_num)
  have i2 : Integrable (fun x => 2 * gauss 1 x) ν := hi1.const_mul 2
  have i3 : Integrable (fun x => 2 * gauss 1 x - gauss 4 x) ν := i2.sub hi4
  have i4 : Integrable (fun x => 1 / 2 * gauss (1 / 4) x) ν := hi14.const_mul (1 / 2)
  have hKint : Integrable Kanti ν := i3.sub i4
  have hK : ∫ x, Kanti x ∂ν = mθ ν 1 / 2 := by
    have e : (fun x => Kanti x) = fun x => (2 * gauss 1 x - gauss 4 x) - 1 / 2 * gauss (1 / 4) x := rfl
    rw [e, integral_sub i3 i4, integral_sub i2 hi4, integral_const_mul, integral_const_mul]
    unfold mθ at hBr ⊢
    linarith
  -- the two atoms
  have hfin0 : ν {0} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  have hfin1 : ν {1} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  have hind0 : Integrable (({0} : Set ℝ).indicator (fun _ => (1 : ℝ))) ν :=
    (integrableOn_const (C := (1 : ℝ)) hfin0).integrable_indicator (measurableSet_singleton 0)
  have hind1 : Integrable (({1} : Set ℝ).indicator (fun _ => (1 : ℝ))) ν :=
    (integrableOn_const (C := (1 : ℝ)) hfin1).integrable_indicator (measurableSet_singleton 1)
  -- upper bound: `K ≤ K(0) 1_{0} + K(1) 1_{1}` off the gap
  have hae_gap : ∀ᵐ x ∂ν, x ∉ Ioo (-1) 1 \ {0} := measure_eq_zero_iff_ae_notMem.mp hgap
  have hupper : ∫ x, Kanti x ∂ν
      ≤ Kanti 0 * ν.real {0} + Kanti 1 * ν.real {1} := by
    have hle : ∀ᵐ x ∂ν, Kanti x ≤ Kanti 0 * ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x
        + Kanti 1 * ({1} : Set ℝ).indicator (fun _ => (1 : ℝ)) x := by
      filter_upwards [hae_gap] with x hx
      by_cases h0 : x = 0
      · subst h0; simp
      by_cases h1' : x = 1
      · subst h1'; simp
      have hx1 : 1 ≤ |x| := by
        by_contra hlt
        exact hx ⟨abs_lt.mp (not_le.mp hlt), h0⟩
      rw [Set.indicator_of_notMem (by simpa using h0), Set.indicator_of_notMem (by simpa using h1')]
      simp only [mul_zero, add_zero]
      exact (Kanti_le hx1).trans (neg_nonpos.mpr (gauss_nonneg 4 x))
    calc ∫ x, Kanti x ∂ν
        ≤ ∫ x, (Kanti 0 * ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x
            + Kanti 1 * ({1} : Set ℝ).indicator (fun _ => (1 : ℝ)) x) ∂ν :=
          integral_mono_ae hKint ((hind0.const_mul _).add (hind1.const_mul _)) hle
      _ = Kanti 0 * ν.real {0} + Kanti 1 * ν.real {1} := by
          rw [integral_add (hind0.const_mul _) (hind1.const_mul _), integral_const_mul,
            integral_const_mul, integral_indicator_const _ (measurableSet_singleton 0),
            integral_indicator_const _ (measurableSet_singleton 1)]
          simp
  -- lower bound: `θ(1) ≥ ν{0} + e^{-π} ν{1}`
  have hlower : ν.real {0} + gauss 1 1 * ν.real {1} ≤ mθ ν 1 := by
    have hle : ∀ x, ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x
        + gauss 1 1 * ({1} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ≤ gauss 1 x := by
      intro x
      by_cases h0 : x = 0
      · subst h0; simp [gauss_zero]
      by_cases h1' : x = 1
      · subst h1'; simp
      rw [Set.indicator_of_notMem (by simpa using h0), Set.indicator_of_notMem (by simpa using h1')]
      simp only [mul_zero, add_zero]
      exact gauss_nonneg 1 x
    have i5 : Integrable (fun x => ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x
        + gauss 1 1 * ({1} : Set ℝ).indicator (fun _ => (1 : ℝ)) x) ν := hind0.add (hind1.const_mul _)
    have := integral_mono i5 hi1 hle
    rw [integral_add hind0 (hind1.const_mul _), integral_const_mul,
      integral_indicator_const _ (measurableSet_singleton 0),
      integral_indicator_const _ (measurableSet_singleton 1)] at this
    unfold mθ
    simpa using this
  have hK1 := Kanti_one_neg
  have hg1 := gauss_pos 1 1
  rw [Kanti_zero] at hupper
  have h0nn : 0 ≤ ν.real {0} := measureReal_nonneg
  nlinarith

/-! ### The remaining step, with the root number resolved -/

/-- Hamburger/Bochner's converse with BOTH root numbers: the classical complex-analytic content of
Step 2 (NOT formalized). Its proof is Mellin inversion plus a contour shift; it uses no positivity. -/
def HamburgerConverse : Prop :=
  ∀ N : Measure ℝ, BeurlingNormalized N → ZetaShapeFE 1 N →
    (∃ β : ℂ, ThetaRelation (symmExt N) β) ∨ (∃ c : ℂ, AntiThetaRelation (symmExt N) c)

lemma symmExt_gap {N : Measure ℝ} (hN : BeurlingNormalized N) :
    symmExt N (Ioo (-1) 1 \ {0}) = 0 := by
  obtain ⟨h0, -, -⟩ := hN
  have hS : MeasurableSet (Ioo (-1 : ℝ) 1 \ {0}) := measurableSet_Ioo.diff (measurableSet_singleton 0)
  rw [symmExt_apply N hS]
  have hd : Measure.dirac (0 : ℝ) (Ioo (-1) 1 \ {0}) = 0 := by
    rw [Measure.dirac_apply' _ hS]; simp
  have hA : N (Ioo (-1) 1 \ {0}) = 0 := measure_mono_null (fun x hx => hx.1.2) h0
  have hB : N (Neg.neg ⁻¹' (Ioo (-1) 1 \ {0})) = 0 :=
    measure_mono_null (fun x hx => by
      simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_Ioo] at hx
      show x < 1
      linarith [hx.1.1]) h0
  rw [hd, hA, hB]; simp

lemma symmExt_one {N : Measure ℝ} (hN : BeurlingNormalized N) : symmExt N {1} = 1 := by
  obtain ⟨h0, h1, -⟩ := hN
  have hNm1 : N {-1} = 0 := measure_mono_null (by intro x hx; simp at hx; simp [hx]) h0
  rw [symmExt_apply N (measurableSet_singleton 1), h1]
  have hd : Measure.dirac (0 : ℝ) {1} = 0 := by
    rw [Measure.dirac_apply' _ (measurableSet_singleton 1)]; simp
  have : Neg.neg ⁻¹' ({1} : Set ℝ) = {-1} := by ext x; simp
  rw [this, hNm1, hd]; simp

/-- **The root number is forced (kernel).** The classical converse with both root numbers implies
`Step2MellinHalf`: the `ε = -1` branch is impossible for a normalized positive Beurling measure. -/
theorem step2_of_hamburgerConverse (h : HamburgerConverse) : Step2MellinHalf := by
  intro N hN hFE
  rcases h N hN hFE with hθ | ⟨c, hanti⟩
  · exact hθ
  · exfalso
    have hfin := symmExt_finiteOnCompacts hN
    have hpos : 0 < (symmExt N).real {1} := by
      rw [Measure.real, symmExt_one hN]; simp
    exact no_antiTheta (symmExt_gaussIntegrable hN) hanti (symmExt_gap hN) hpos

/-- **Round 1's milestone NT4 from the classical converse alone (kernel).** -/
theorem classP_collapse_beurling_q1_of_hamburgerConverse (h : HamburgerConverse) :
    ∀ N : Measure ℝ, BeurlingNormalized N → ZetaShapeFE 1 N →
      N = Measure.sum (fun n : ℕ => Measure.dirac ((n : ℝ) + 1)) :=
  classP_collapse_beurling_q1_of_step2 (step2_of_hamburgerConverse h)

end CruxFQK

#print axioms CruxFQK.fourier_tri
#print axioms CruxFQK.poisson_rigidity
#print axioms CruxFQK.selfDual_rigidity
#print axioms CruxFQK.isPoissonPair_of_even
#print axioms CruxFQK.fourier_gauss
#print axioms CruxFQK.gauss_conv
#print axioms CruxFQK.Tdef_gauss
#print axioms CruxFQK.Tdef_add
#print axioms CruxFQK.norm_Tdef_le
#print axioms CruxFQK.exists_gauss_poly_approx
#print axioms CruxFQK.Tdef_even_eq_zero
#print axioms CruxFQK.tendsto_sqrt_mul_Tdef
#print axioms CruxFQK.isPoissonPairEven_of_theta
#print axioms CruxFQK.isPoissonPair_of_theta
#print axioms CruxFQK.mθ_dyadic_le
#print axioms CruxFQK.integrable_fej_of_theta
#print axioms CruxFQK.thmA_theta
#print axioms CruxFQK.thmA_theta_selfDual
#print axioms CruxFQK.theta_gap_gt_one_forces_zero
#print axioms CruxFQK.translation_bounded_of_theta
#print axioms CruxFQK.jθ_inv
#print axioms CruxFQK.intComb_theta
#print axioms CruxFQK.intComb_theta_admissible
#print axioms CruxFQK.nup_theta
#print axioms CruxFQK.nup_isPoissonPair_via_theta
#print axioms CruxFQK.theta_rigidity_is_rh_blind
#print axioms CruxFQK.theta_fooling_onset
#print axioms CruxFQK.controls_in_theta_form
#print axioms CruxFQK.writer_thmA_theta
#print axioms CruxFQK.writer_gaussian_determination
#print axioms CruxFQK.integrable_gauss_of_beurling
#print axioms CruxFQK.symmExt_isNegInvariant
#print axioms CruxFQK.classP_collapse_beurling_q1_of_theta
#print axioms CruxFQK.classP_collapse_beurling_q1_of_step2
#print axioms CruxFQK.no_antiTheta
#print axioms CruxFQK.step2_of_hamburgerConverse
#print axioms CruxFQK.classP_collapse_beurling_q1_of_hamburgerConverse
