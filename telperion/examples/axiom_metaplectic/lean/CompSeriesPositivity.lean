import AxiomProbe
import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexHarmonicEigenvaluesAndSmoothness
import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLComplex.BruhatHopfCoordinates

/-!
# Complementary-series positivity for PGL2(ℂ), all ν ∈ (0, 1)

The AxiomMath library proves that the standard intertwiner on the complex principal series at the
single parameter `s = 1/6` (that is, `ν = 1/3`) acts on the ℓ-th K-type by
`(3‖β‖/2) · ∏_{j=1}^{ℓ} (j − 1/3)/(j + 1/3)`. This file generalises that computation to every real
parameter `s ∈ (0, 1/2)`, i.e. every `ν = 2s ∈ (0, 1)`.

## Parameter convention

The library's `PrincipalSeries s` consists of smooth `f` with
`f (upperTriangular a d b * g) = |a/d|_ℂ ^ (1/2 + s) * f g`, where `|z|_ℂ = ‖z‖²`. This is unitary
induction of `|a/d|_ℂ ^ s`, so the complementary series is `0 < s < 1/2`, and the library's
eigenvalue parameter is `ν = 2s` (its `positiveParameter = 1/6` gives `ν = 1/3`). Core lemmas are
stated in `s`; the headline theorem `compSeries_Ktype_eigenvalues` is stated in `ν`.

## Results

* `compSeriesEigenvalue ν β ℓ = (‖β‖ / (2ν)) · ∏_{j=1}^{ℓ} (j − ν)/(j + ν)` and its positivity for
  `0 < ν < 1` (`compSeriesEigenvalue_pos`);
* the intertwiner `compSeriesIntertwiner s : PrincipalSeries s →ₗ[ℂ] PrincipalSeries (-s)` for every
  `s > 0`, its equivariance, and agreement with the library's `standardIntertwiner` at `s = 1/6`;
* `compSeries_Ktype_eigenvalues`: on the ℓ-th K-type the intertwiner is the scalar
  `compSeriesEigenvalue ν β ℓ > 0`;
* `compSeries_form_Ktype_nonneg`: the intertwining form `∫ (M f) · conj f` against any measure on
  SU(2) is real and nonnegative on each K-type.

Not included: continuity of the intertwiner for general `s` (the library proves it at `s = 1/6`), and
strict positive definiteness of the L²(K) form across K-types.

conjecture1_proved = False. This is not progress on RH; it is the first step of a speculative lead.

## Provenance

Several lemmas below are adapted from the AxiomMath library `DedekindZetaZeroFree`
(https://github.com/AxiomMath/DedekindZetaZeroFree, commit 284348a4, Apache-2.0). Each adapted
lemma names its source file. The adaptations replace the numerals `1/6`, `1/3`, `4/3`, `8/3`, `3π`
by expressions in the parameter `s`; otherwise the proofs follow the originals.
-/

namespace Arda.AxiomMetaplectic

open DedekindZetaZeroFree.KPCplxCharacterHaar DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts
open DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open MeasureTheory
open scoped BigOperators

/-! ### The closed-form eigenvalue -/

section Eigenvalue

/-- The K-type eigenvalue of the standard intertwiner at complementary-series parameter `ν`:
`(‖β‖ / (2ν)) · ∏_{j=1}^{ℓ} (j − ν)/(j + ν)`. At `ν = 1/3` this is the library's `eigenvalue`. -/
noncomputable def compSeriesEigenvalue (ν : ℝ) (β : ℂˣ) (ℓ : ℕ) : ℝ :=
  (characterScale β / (2 * ν)) *
    ∏ j ∈ Finset.Icc 1 ℓ, (((j : ℝ) - ν) / ((j : ℝ) + ν))

/-- Every K-type eigenvalue is strictly positive throughout the complementary series `0 < ν < 1`.
Adapted from the private `eigenvalue_pos` in
`RepresentationTheory/PrincipalSeries/Complex/ComplexHarmonicEigenvaluesAndSmoothness.lean`. -/
theorem compSeriesEigenvalue_pos {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (β : ℂˣ) (ℓ : ℕ) :
    0 < compSeriesEigenvalue ν β ℓ := by
  have hc := characterScale_pos β
  unfold compSeriesEigenvalue
  apply mul_pos
  · exact div_pos hc (by linarith)
  · apply Finset.prod_pos
    intro j hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    apply div_pos <;> linarith

/-- At `ν = 1/3` the closed form is exactly the library's eigenvalue. -/
theorem compSeriesEigenvalue_one_third (β : ℂˣ) (ℓ : ℕ) :
    compSeriesEigenvalue (1 / 3) β ℓ =
      DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues.eigenvalue β ℓ := by
  unfold compSeriesEigenvalue DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues.eigenvalue
  congr 1
  ring

/-- The range `ν < 1` is sharp for the closed form: for `ν > 1` the ℓ = 1 value is negative.
This is arithmetic on `compSeriesEigenvalue` only; the operator identity below is proved for
`ν < 1`, since the library's beta integral assumes that. -/
theorem compSeriesEigenvalue_one_neg {ν : ℝ} (hν1 : 1 < ν) (β : ℂˣ) :
    compSeriesEigenvalue ν β 1 < 0 := by
  have hc := characterScale_pos β
  unfold compSeriesEigenvalue
  rw [Finset.Icc_self, Finset.prod_singleton]
  push_cast
  apply mul_neg_of_pos_of_neg
  · exact div_pos hc (by linarith)
  · apply div_neg_of_neg_of_pos <;> linarith

end Eigenvalue

/-! ### Transport of the intertwining integral to the sphere -/

section Transport

open DedekindZetaZeroFree.ComplexFractionalInverse.RawSphereProjection
open DedekindZetaZeroFree.ComplexLocal.StereographicTransport
open scoped RealInnerProductSpace

/-- Hopf coordinates of an SU(2) element lie on the unit sphere.
Copied verbatim from the private `coords_norm` in
`RepresentationTheory/PrincipalSeries/Complex/IntertwinerSphericalKernelTransport.lean`. -/
private theorem coords_norm (k : ComplexSU2) :
    ‖(WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re) : rawAmbient)‖ = 1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.mul_re] at h
  have hs : ‖(WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re) : rawAmbient)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [compactSphereCoordinate, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re ^ 2 +
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im ^ 2 +
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ^ 2 +
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im ^ 2 - 1)]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re) : rawAmbient)]

/-- Iwasawa factor of the open Bruhat cell at parameter `s`:
`f (w u_z k) = (1 + ‖z‖²)^(−(1 + 2s)) · f (κ_z k)`.
Adapted from `normalized_bruhat_factorization` (exponent `−4/3` there) in
`RepresentationTheory/RankOne/PGLComplex/BruhatHopfCoordinates.lean`; the matrix identity is reused. -/
theorem compSeries_bruhat_section (s : ℝ) (z : ℂ) (f : PrincipalSeries s) (k : ComplexSU2) :
    f (weyl * upperUnipotent z * complexSU2Embedding k) =
      ((denominator z ^ (-(1 + 2 * s)) : ℝ) : ℂ) * f (complexSU2Embedding (kappa z * k)) := by
  rw [(normalized_bruhat_factorization z).1, mul_assoc, ← map_mul]
  have hc := f.property.1
  dsimp [HasCovariance] at hc
  rw [unsignedUpper, hc]
  change _ * _ = _ * _
  congr 1
  congr 1
  dsimp [inductionWeight, complexAbs]
  have hn : ‖(-1 / (radius z : ℂ)) / (radius z : ℂ)‖ ^ 2 =
      denominator z ^ (-2 : ℝ) := by
    simp only [norm_div, norm_neg, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (radius_pos z)]
    rw [div_div, ← sq, div_pow, radius_sq, one_pow, Real.rpow_neg (by
      unfold denominator; positivity), Real.rpow_two]
    ring
  rw [hn, ← Real.rpow_mul (by unfold denominator; positivity)]
  congr 1
  ring

/-- The section-to-sphere transport at parameter `s`, with density constant `π/(2s) = π/ν` and
latitude weight `ν · u^(ν − 1)`.
Adapted from `positive_section_stereographic` (constant `3π`, weight `(1/3) u^(−2/3)`) in
`RepresentationTheory/RankOne/PGLComplex/BruhatHopfCoordinates.lean`. -/
theorem compSeries_section_stereographic (s : ℝ) (hs : 0 < s) (H : ComplexSU2 → rawSphere)
    (hH : HasRawHopfCoordinates H) (f : PrincipalSeries s)
    (F : rawSphere → ℂ)
    (hf : ∀ k, f (complexSU2Embedding k) = F (H k))
    (k : ComplexSU2) :
    MeasurePreserving (fun z => H (kappa z * k)) planeProbability rawSphereArea ∧
      (∀ z : ℂ, f (weyl * upperUnipotent z * complexSU2Embedding k) =
        ((Real.pi / (2 * s) : ℝ) : ℂ) *
          (denominator z ^ (-2 : ℝ) / Real.pi : ℝ) *
          ((((2 * s) *
            ((1 - inner ℝ (H k : rawAmbient)
              (H (kappa z * k) : rawAmbient)) / 2) ^ (2 * s - 1 : ℝ)) : ℝ) : ℂ) *
          F (H (kappa z * k))) := by
  obtain ⟨hσ, hg⟩ := hopf_rotation_geometry H hH
  obtain ⟨R, hR, ht⟩ := hg k
  constructor
  · have he : (fun z => H (kappa z * k)) = rotation R ∘ sigma := by
      funext z
      rw [hR, hσ]
      rfl
    rw [he]
    have hmp : MeasurePreserving (rotation R) rawSphereArea rawSphereArea := by
      refine ⟨(rotation_continuous R).measurable, ?_⟩
      rw [rawSphereArea, Measure.map_smul, (rotation_preserving R).map_eq]
      exact (rotation_continuous R).measurable.aemeasurable
    exact hmp.comp stereographic_measure_transport.1
  · intro z
    rw [compSeries_bruhat_section s z f k, hf, ht]
    have hD : 0 < denominator z := by unfold denominator; positivity
    have hs0 : (2 * s) ≠ 0 := by positivity
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hs' : denominator z ^ (-(1 + 2 * s)) =
        Real.pi / (2 * s) * (denominator z ^ (-2 : ℝ) / Real.pi) *
        ((2 * s) * (1 / denominator z) ^ (2 * s - 1 : ℝ)) := by
      rw [show (1 / denominator z) = (denominator z)⁻¹ by simp,
        ← Real.rpow_neg_eq_inv_rpow]
      have he : -(1 + 2 * s) = -2 + -(2 * s - 1) := by ring
      rw [he, Real.rpow_add hD]
      field_simp
    rw [show ((Real.pi / (2 * s) : ℝ) : ℂ) *
        (↑(denominator z ^ (-2 : ℝ) / Real.pi) : ℂ) *
        (↑((2 * s) * (1 / denominator z) ^ (2 * s - 1 : ℝ)) : ℂ) =
        ↑(denominator z ^ (-(1 + 2 * s))) by
      exact_mod_cast hs'.symm]

/-- Pushing the Haar integral against `characterHaar β` to the sphere, for an arbitrary density
constant `c`. Adapted from `positive_haar_integral_of_transport` (constant `3π`) in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerHarmonicIntegrals.lean`. -/
theorem compSeries_haar_integral_of_transport (c : ℝ) (β : ℂˣ)
    (q : ℂ → rawSphere)
    (hq : MeasurePreserving q planeProbability rawSphereArea)
    (K : rawSphere → ℂ) (hK : AEStronglyMeasurable K rawSphereArea)
    (g : ℂ → ℂ)
    (hg : ∀ z, g z = ((c : ℝ) : ℂ) * (denominator z ^ (-2 : ℝ) / Real.pi : ℝ) * K (q z)) :
    (∫ z, g z ∂characterHaar β) =
      ((c * characterScale β / (2 * Real.pi) : ℝ) : ℂ) * ∫ y, K y ∂rawSphereArea := by
  let d : ℂ → ℝ := fun z => denominator z ^ (-2 : ℝ) / Real.pi
  have hd : Measurable (fun z => ENNReal.ofReal (d z)) := by
    dsimp [d, denominator]
    fun_prop
  have hdpos (z : ℂ) : 0 ≤ d z := by
    dsimp [d]
    exact div_nonneg (Real.rpow_nonneg (by unfold denominator; positivity) _) Real.pi_pos.le
  have hm := integral_map hq.measurable.aemeasurable (hq.map_eq ▸ hK)
  rw [hq.map_eq] at hm
  have he : (∫ z, (d z : ℂ) * K (q z) ∂euclideanArea) = ∫ y, K y ∂rawSphereArea := by
    change _ = _ at hm
    rw [planeProbability,
      integral_withDensity_eq_integral_toReal_smul hd
        (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))] at hm
    simpa only [ENNReal.toReal_ofReal (hdpos _), Complex.real_smul] using hm.symm
  have hc : 0 ≤ characterScale β / (2 * Real.pi) :=
    div_nonneg (characterScale_pos β).le (mul_pos (by norm_num) Real.pi_pos).le
  rw [characterHaar, integral_smul_measure, ENNReal.toReal_ofReal hc, Complex.real_smul]
  simp_rw [hg]
  change ((characterScale β / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ z, ((c : ℝ) : ℂ) * (d z : ℂ) * K (q z) ∂euclideanArea) = _
  simp_rw [show ∀ z, ((c : ℝ) : ℂ) * (d z : ℂ) * K (q z) =
    ((c : ℝ) : ℂ) * ((d z : ℂ) * K (q z)) from fun z => mul_assoc _ _ _]
  rw [integral_const_mul, he]
  push_cast
  ring

/-- **The K-type integral at parameter `s ∈ (0, 1/2)`.** If `f ∈ PrincipalSeries s` restricts on
SU(2) to a degree-ℓ harmonic polynomial `p`, then
`∫ f (w u_x k) d(characterHaar β)(x) = compSeriesEigenvalue (2s) β ℓ · p(k)`.
Adapted from `positive_intertwiner_harmonic_integral` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerHarmonicIntegrals.lean`. -/
theorem compSeries_harmonic_integral (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1 / 2)
    (β : ℂˣ) (ℓ : ℕ)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ)
    (f : PrincipalSeries s)
    (hf : ∀ k : ComplexSU2,
      f (complexSU2Embedding k) = MvPolynomial.eval (compactSphereCoordinate k) p)
    (k : ComplexSU2) :
    (∫ x : ℂ, f (weyl * upperUnipotent x * complexSU2Embedding k) ∂characterHaar β) =
      (compSeriesEigenvalue (2 * s) β ℓ : ℂ) *
        MvPolynomial.eval (compactSphereCoordinate k) p := by
  let H : ComplexSU2 → rawSphere := fun h =>
    ⟨WithLp.toLp 2 (fun i => (compactSphereCoordinate h i).re),
      mem_sphere_zero_iff_norm.mpr (coords_norm h)⟩
  have hH : HasRawHopfCoordinates H := fun _ => rfl
  have hc (h : ComplexSU2) (i : Fin 3) :
      ((H h : rawAmbient) i : ℂ) = compactSphereCoordinate h i := by
    fin_cases i <;> simp [H, compactSphereCoordinate, -Complex.ofReal_pow]
  have hfH : ∀ h, f (complexSU2Embedding h) = HarmonicIntegral.rawPolynomialSphere p (H h) := by
    intro h
    rw [hf]
    unfold HarmonicIntegral.rawPolynomialSphere
    rw [show (fun i => ((H h : rawAmbient) i : ℂ)) = compactSphereCoordinate h from
      funext (hc h)]
  obtain ⟨hq, hsec⟩ := compSeries_section_stereographic s hs0 H hH f _ hfH k
  let w : ℝ → ℝ := fun u => (2 * s) * u ^ (2 * s - 1 : ℝ)
  have hw : Integrable w (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity.powerWeight_integrable
      (2 * s) (by linarith)
  have hK := HarmonicIntegral.raw_polynomial_latitude_integrable p w hw (H k)
  rw [compSeries_haar_integral_of_transport (Real.pi / (2 * s)) β (fun z => H (kappa z * k)) hq
    (HarmonicIntegral.rawLatitudeKernel w (H k) p) hK.aestronglyMeasurable
    (fun z => f (weyl * upperUnipotent z * complexSU2Embedding k))
    (fun z => by simpa only [HarmonicIntegral.rawLatitudeKernel, w, mul_assoc] using hsec z)]
  rw [HarmonicIntegral.raw_polynomial_funkHecke ℓ p hp w hw (H k)]
  have hbeta := DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity.shiftedLegendre_beta
    ℓ (2 * s) (by linarith) (by linarith)
  change (∫ u : ℝ in Set.Icc 0 1,
    w u * (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u) = _ at hbeta
  rw [hbeta]
  have hpoint : HarmonicIntegral.rawPolynomialSphere p (H k) =
      MvPolynomial.eval (compactSphereCoordinate k) p := by
    unfold HarmonicIntegral.rawPolynomialSphere
    rw [show (fun i => ((H k : rawAmbient) i : ℂ)) = compactSphereCoordinate k from
      funext (hc k)]
  have hconst : Real.pi / (2 * s) * characterScale β / (2 * Real.pi) =
      characterScale β / (2 * (2 * s)) := by
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hs : s ≠ 0 := hs0.ne'
    field_simp
  rw [hpoint, hconst, compSeriesEigenvalue]
  push_cast
  ring

end Transport

/-! ### Convergence of the intertwining integral for every `s > 0` -/

section Convergence

open Filter Asymptotics

/-- Chart transition at parameter `s`. Adapted from the private `transition_norm` (exponent `8/3`)
in `RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerConvergence.lean`. -/
private lemma transition_norm (s : ℝ) (f : PrincipalSeries s) (x : ℂ) (hx : 1 ≤ ‖x‖) :
    ‖openCoordinate f x‖ =
      ‖x‖ ^ (-(2 * (1 + 2 * s))) * ‖infinityCoordinate f x⁻¹‖ := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; norm_num at hx
  have h := coordinate_transition s f x⁻¹ (inv_ne_zero hx0)
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hw : transitionWeight s x⁻¹ = ‖x‖ ^ (2 * (1 + 2 * s)) := by
    simp only [transitionWeight, norm_inv, Real.rpow_eq_pow]
    rw [Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    congr 1
    ring
  rw [inv_inv, hw] at h
  have hn := congrArg norm h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hxp _)] at hn
  have hr : ‖x‖ ^ (-(2 * (1 + 2 * s))) * ‖x‖ ^ (2 * (1 + 2 * s)) = 1 := by
    rw [← Real.rpow_add hxp]; simp
  rw [hn, ← mul_assoc, hr, one_mul]

/-- Decay of the open-chart coordinate at parameter `s`. Adapted from the private `tail_bigO` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerConvergence.lean`. -/
private lemma tail_bigO (s : ℝ) (hs : 0 < s) (f : PrincipalSeries s) :
    openCoordinate f =O[cocompact ℂ] (fun x : ℂ => (1 + ‖x‖) ^ (-(2 * (1 + 2 * s)))) := by
  have he : -(2 * (1 + 2 * s)) ≤ 0 := by linarith
  have hcont : Continuous (infinityCoordinate f) := f.property.2.2.continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont.continuousOn
  refine isBigO_iff.mpr ⟨max C 0 * (2 : ℝ) ^ (2 * (1 + 2 * s)), ?_⟩
  have hev : ∀ᶠ x : ℂ in cocompact ℂ, 1 ≤ ‖x‖ := by
    filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with x hx
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le
  filter_upwards [hev] with x hx
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; norm_num at hx
  have hxi : x⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have hi := (hC x⁻¹ hxi).trans (le_max_left C 0)
  have hp : ‖x‖ ^ (-(2 * (1 + 2 * s))) ≤
      (2 : ℝ) ^ (2 * (1 + 2 * s)) * (1 + ‖x‖) ^ (-(2 * (1 + 2 * s))) := by
    have ht : (1 + ‖x‖) / 2 ≤ ‖x‖ := by linarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖x‖) / 2) ht he
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at h
    simpa only [mul_comm] using h
  rw [transition_norm s f x hx]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    _ ≤ ‖x‖ ^ (-(2 * (1 + 2 * s))) * max C 0 :=
      mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (norm_nonneg _) _)
    _ ≤ ((2 : ℝ) ^ (2 * (1 + 2 * s)) * (1 + ‖x‖) ^ (-(2 * (1 + 2 * s)))) * max C 0 :=
      mul_le_mul_of_nonneg_right hp (le_max_right C 0)
    _ = _ := by ring

/-- The intertwining integral converges absolutely for every `f ∈ PrincipalSeries s`, `s > 0`.
Adapted from `positive_intertwiner_integrable` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerConvergence.lean`. -/
theorem compSeries_integrable (s : ℝ) (hs : 0 < s) (β : ℂˣ)
    (f : PrincipalSeries s) (g : ComplexGL2) :
    Integrable (fun x : ℂ => f (weyl * upperUnipotent x * g)) (characterHaar β) := by
  have := characterHaar_isAddHaarMeasure β
  let F := rightTranslate s g f
  change Integrable (openCoordinate F) (characterHaar β)
  have hcont : Continuous (openCoordinate F) := F.property.2.1.continuous
  apply hcont.locallyIntegrable.integrable_of_isBigO_cocompact (tail_bigO s hs F)
  apply (integrable_iff_integrableAtFilter_cocompact.mp ?_).1
  exact integrable_one_add_norm (by rw [Complex.finrank_real_complex]; push_cast; linarith)

end Convergence

/-! ### The image lies in `PrincipalSeries (-s)` -/

section Covariance

open scoped Matrix

/-- Adapted from the private `positive_intertwiner_triangular_identity` in
`RepresentationTheory/PrincipalSeries/Complex/ComplexHarmonicEigenvaluesAndSmoothness.lean`
(parameter free; copied because it is private). -/
private lemma triangular_identity (a d : ℂˣ) (b x : ℂ) :
    weyl * upperUnipotent x * upperTriangular a d b =
      upperTriangular d a 0 * (weyl * upperUnipotent ((b + x * (d : ℂ)) / (a : ℂ))) := by
  apply Units.ext
  have h1 : (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  have h2 : (upperTriangular d a 0 : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(d : ℂ), 0; 0, (a : ℂ)] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, h1, h2,
      mul_assoc, mul_comm]
  all_goals field_simp

/-- `|d/a|_ℂ^(1/2 + s) · |d/a|_ℂ^(−1) = |a/d|_ℂ^(1/2 − s)`. Adapted from the private
`positive_intertwiner_weight` in
`RepresentationTheory/PrincipalSeries/Complex/ComplexHarmonicEigenvaluesAndSmoothness.lean`. -/
private lemma intertwiner_weight (s : ℝ) (a d : ℂˣ) :
    inductionWeight s d a * (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ = inductionWeight (-s) a d := by
  have hpos : 0 < ‖(d : ℂ) / (a : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (div_ne_zero d.ne_zero a.ne_zero)) 2
  have hinv : ‖(a : ℂ) / (d : ℂ)‖ ^ 2 = (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ := by
    rw [← inv_div, norm_inv, inv_pow]
  simp only [inductionWeight, complexAbs, hinv]
  simp only [Real.rpow_eq_pow]
  have hneg : (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ =
      (‖(d : ℂ) / (a : ℂ)‖ ^ 2) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_one]
  rw [← Real.rpow_neg_eq_inv_rpow]
  conv_lhs => arg 2; rw [hneg]
  rw [← Real.rpow_add hpos]
  congr 1
  ring

/-- The intertwining integral is `(-s)`-covariant. Adapted from `positive_intertwiner_covariance`
in `RepresentationTheory/PrincipalSeries/Complex/ComplexHarmonicEigenvaluesAndSmoothness.lean`. -/
theorem compSeries_covariance (s : ℝ) (β : ℂˣ) (f : PrincipalSeries s) :
    HasCovariance (-s) (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) := by
  intro a d b g
  have : (characterHaar β).IsAddHaarMeasure := characterHaar_isAddHaarMeasure β
  have hf := f.property.1
  change HasCovariance s (f : ComplexGL2 → ℂ) at hf
  simp_rw [← mul_assoc, triangular_identity, mul_assoc, hf d a 0]
  rw [integral_const_mul]
  have heq (x : ℂ) : (b + x * (d : ℂ)) / (a : ℂ) =
      (d : ℂ) / (a : ℂ) * x + b / (a : ℂ) := by ring
  simp_rw [heq, ← mul_assoc]
  rw [character_integral_mul β (fun x => f (weyl * upperUnipotent (x + b / (a : ℂ)) * g))
    ((d : ℂ) / (a : ℂ)) (div_ne_zero d.ne_zero a.ne_zero)]
  rw [integral_add_right_eq_self (fun x => f (weyl * upperUnipotent x * g)) (b / (a : ℂ)),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, intertwiner_weight]

end Covariance

section Smoothness

open Filter
open scoped Matrix.Norms.Elementwise ContDiff Topology

/-- Adapted from `positive_open_integrand_joint_contDiff` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerSmoothness.lean`
(proof unchanged; only the parameter is generalised). -/
lemma open_integrand_joint_contDiff (s : ℝ) (f : PrincipalSeries s) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ =>
      f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent p.2))) := by
  have hf := ((principalSeries_mem_iff s f).mp f.property).2
  let g : ℂ × ℂ → ComplexGL2 := fun p => weyl * upperUnipotent p.1 * (weyl * upperUnipotent p.2)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ =>
      (g p : Matrix (Fin 2) (Fin 2) ℂ)) := by
    dsimp [g]
    unfold upperUnipotent
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ =>
      (weyl : Matrix (Fin 2) (Fin 2) ℂ) * !![1, p.1; 0, 1] *
        ((weyl : Matrix (Fin 2) (Fin 2) ℂ) * !![1, p.2; 0, 1]))
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have h := hf.comp (s := Set.univ) hg.contDiffOn
    (fun p _ => Matrix.GeneralLinearGroup.det_ne_zero (g p))
  rw [contDiffOn_univ] at h
  convert h using 1
  funext p
  dsimp [matrixFunction]
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (g p))]
  apply congrArg (f : ComplexGL2 → ℂ)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- Adapted from `positive_open_integrand_jets_contDiff` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerSmoothness.lean`. -/
lemma open_integrand_jets_contDiff (s : ℝ) (f : PrincipalSeries s) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => iteratedFDeriv ℝ n
      (fun z => f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent z))) p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  induction n generalizing p with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p
        (open_integrand_joint_contDiff s f).contDiffAt
  | succ n ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => fderiv ℝ
        (iteratedFDeriv ℝ n (fun z => f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent z)))) p.2) p := by
      exact ((ih (p.1,p.2)).comp (p,p.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
        (m := (⊤ : ℕ∞)) contDiffAt_snd (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => ℂ) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p hd

/-- Adapted from `positive_open_integrand_jets_measurable` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerSmoothness.lean`. -/
lemma open_integrand_jets_measurable (s : ℝ) (β : ℂˣ) (f : PrincipalSeries s)
    (n : ℕ) (z : ℂ) : AEStronglyMeasurable (fun x : ℂ => iteratedFDeriv ℝ n
      (fun z => f (weyl * upperUnipotent x * (weyl * upperUnipotent z))) z) (characterHaar β) := by
  exact ((open_integrand_jets_contDiff s f n).continuous.comp
    (continuous_id.prodMk continuous_const)).aestronglyMeasurable

set_option backward.isDefEq.respectTransparency false in
/-- Adapted from `positive_open_contDiff_of_jet_bounds` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerSmoothness.lean`. -/
lemma open_contDiff_of_jet_bounds (s : ℝ) (β : ℂˣ) (f : PrincipalSeries s)
    (hbound : ∀ n : ℕ, ∀ z : ℂ, ∃ (t : Set ℂ) (b : ℂ → ℝ),
      t ∈ nhds z ∧ Integrable b (characterHaar β) ∧
        ∀ᵐ x ∂characterHaar β, ∀ w ∈ t,
          ‖iteratedFDeriv ℝ n (fun v =>
            f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) w‖ ≤ b x) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)) := by
  have hs (x : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      f (weyl * upperUnipotent x * (weyl * upperUnipotent z))) := by
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (x, z)) :=
      contDiff_const.prodMk contDiff_id
    have hh := (open_integrand_joint_contDiff s f).comp he
    exact hh
  exact (integral_contDiff_of_locally_dominated_jets (characterHaar β)
    (fun z x => f (weyl * upperUnipotent x * (weyl * upperUnipotent z))) hs
    (open_integrand_jets_measurable s β f) hbound).1

/-- Adapted from `intertwiner_tail_weight_integrable` (exponent `8/3`) in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerSmoothness.lean`. -/
lemma tail_weight_integrable (s : ℝ) (hs : 0 < s) (β : ℂˣ) :
    IntegrableOn (fun x : ℂ => ‖x‖ ^ (-(2 * (1 + 2 * s))))
      (Metric.closedBall (0 : ℂ) 1)ᶜ (characterHaar β) := by
  have := characterHaar_isAddHaarMeasure β
  have he : -(2 * (1 + 2 * s)) ≤ 0 := by linarith
  have hi : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-(2 * (1 + 2 * s)))) (characterHaar β) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  apply (hi.mul_const ((2 : ℝ) ^ (2 * (1 + 2 * s)))).integrableOn.mono'
  · exact (by fun_prop : Measurable (fun x : ℂ => ‖x‖ ^ (-(2 * (1 + 2 * s))))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (Metric.isClosed_closedBall.measurableSet.compl)] with x hx
    have hx : 1 ≤ ‖x‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using
        (le_of_lt (show 1 < ‖x‖ by simpa using hx))
    have ht : (1 + ‖x‖) / 2 ≤ ‖x‖ := by linarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖x‖) / 2) ht he
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)] using h

/-- The open-chart coordinate of the image is smooth. Adapted from
`positive_intertwiner_openCoordinate_contDiff` in
`RepresentationTheory/PrincipalSeries/Complex/PositiveIntertwinerSmoothness.lean`. -/
theorem compSeries_openCoordinate_contDiff (s : ℝ) (hs : 0 < s) (β : ℂˣ)
    (f : PrincipalSeries s) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)) := by
  apply open_contDiff_of_jet_bounds s β f
  intro n z
  let G : ℂ × ℂ → ℂ := fun p =>
    f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent p.2))
  obtain ⟨C₀, hC₀, hcompact⟩ :=
    OpenSmoothness.compact_family_spatial_jets_bounded G
      (open_integrand_joint_contDiff s f) n z
  obtain ⟨C₁, hC₁, htranslate⟩ :=
    OpenSmoothness.weighted_inverse_translate_spatial_jets_bounded
      (openCoordinate f) f.property.2.1 (-(2 * (1 + 2 * s))) n z
  have htail : ∀ x ∈ (Metric.closedBall (0 : ℂ) 1)ᶜ,
      ∀ w ∈ Metric.closedBall z 1,
        ‖iteratedFDeriv ℝ n (fun v =>
          f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) w‖ ≤
            C₁ * ‖x‖ ^ (-(2 * (1 + 2 * s))) := by
    intro x hx w hw
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      simp at hx
    have he : (fun v => f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) =
        (fun v => ((‖x‖ ^ (-(2 * (1 + 2 * s))) : ℝ) : ℂ) *
          openCoordinate f (v + x⁻¹)) := by
      funext v
      have ha : -2 * (1 + 2 * s) = -(2 * (1 + 2 * s)) := by ring
      simpa only [ha] using intertwiner_open_integrand_eq s f x v hx0
    rw [he]
    exact htranslate x hx w hw
  have := characterHaar_isAddHaarMeasure β
  exact OpenSmoothness.local_majorant_of_finite_piece_and_integrable_tail
    (characterHaar β) (Metric.closedBall (0 : ℂ) 1)
    Metric.isClosed_closedBall.measurableSet
    ((isCompact_closedBall (0 : ℂ) 1).measure_lt_top)
    (fun w x => iteratedFDeriv ℝ n (fun v =>
      f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) w)
    (fun x => ‖x‖ ^ (-(2 * (1 + 2 * s)))) (tail_weight_integrable s hs β)
    z C₀ C₁ hcompact htail

/-- The infinity-chart coordinate of the image is smooth. Adapted from
`positive_intertwiner_infinityCoordinate_contDiff` in
`RepresentationTheory/PrincipalSeries/Complex/ComplexHarmonicEigenvaluesAndSmoothness.lean`. -/
theorem compSeries_infinityCoordinate_contDiff (s : ℝ) (hs : 0 < s) (β : ℂˣ)
    (f : PrincipalSeries s) :
    ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)) := by
  have hweyl (y : ℂ) : weyl * upperUnipotent y * weyl = lowerUnipotent y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  have hchart :
      infinityCoordinate (fun g : ComplexGL2 =>
        ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) =
      openCoordinate (fun g : ComplexGL2 =>
        ∫ x : ℂ, rightTranslate s weyl f
          (weyl * upperUnipotent x * g) ∂characterHaar β) := by
    funext y
    change (∫ x : ℂ, f (weyl * upperUnipotent x * lowerUnipotent y)
        ∂characterHaar β) =
      ∫ x : ℂ, f ((weyl * upperUnipotent x * (weyl * upperUnipotent y)) * weyl)
        ∂characterHaar β
    simp only [mul_assoc, hweyl]
  rw [hchart]
  exact compSeries_openCoordinate_contDiff s hs β (rightTranslate s weyl f)

end Smoothness

/-! ### The intertwiner and its K-type eigenvalues -/

section Intertwiner

/-- The intertwining integral lands in `PrincipalSeries (-s)`. -/
theorem compSeries_section (s : ℝ) (hs : 0 < s) (β : ℂˣ) (f : PrincipalSeries s) :
    (fun g : ComplexGL2 => ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) ∈
      principalSeriesSubmodule (-s) :=
  ⟨compSeries_covariance s β f, compSeries_openCoordinate_contDiff s hs β f,
    compSeries_infinityCoordinate_contDiff s hs β f⟩

/-- The standard intertwiner `M(s) : PrincipalSeries s → PrincipalSeries (-s)`,
`(M f)(g) = ∫ f (w u_x g) d(characterHaar β)(x)`, for every `s > 0`.
(Continuity in the Fréchet topology is not proved here for general `s`.) -/
noncomputable def compSeriesIntertwiner (s : ℝ) (hs : 0 < s) (β : ℂˣ) :
    PrincipalSeries s →ₗ[ℂ] PrincipalSeries (-s) where
  toFun f := ⟨fun g => ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β,
    compSeries_section s hs β f⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    exact integral_add (compSeries_integrable s hs β f g) (compSeries_integrable s hs β h g)
  map_smul' c f := by
    apply Subtype.ext
    funext g
    exact integral_smul c (fun x : ℂ => f (weyl * upperUnipotent x * g))

theorem compSeriesIntertwiner_apply (s : ℝ) (hs : 0 < s) (β : ℂˣ) (f : PrincipalSeries s)
    (g : ComplexGL2) :
    compSeriesIntertwiner s hs β f g =
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β := rfl

/-- At `s = 1/6` our intertwiner is pointwise the library's `standardIntertwiner`. -/
theorem compSeriesIntertwiner_positiveParameter (β : ℂˣ) (f : PrincipalSeries positiveParameter)
    (g : ComplexGL2) :
    compSeriesIntertwiner positiveParameter (by norm_num [positiveParameter]) β f g =
      DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues.standardIntertwiner β f g :=
  (DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues.standardIntertwiner_apply β f g).symm

/-- `M(s)` intertwines the right-regular actions of PGL2(ℂ). Adapted from
`standardIntertwiner_equivariant` in
`RepresentationTheory/PrincipalSeries/Complex/ComplexHarmonicEigenvaluesAndSmoothness.lean`. -/
theorem compSeriesIntertwiner_equivariant (s : ℝ) (hs : 0 < s) (β : ℂˣ) (g : ComplexPGL2)
    (f : PrincipalSeries s) :
    compSeriesIntertwiner s hs β (pi s g f) = pi (-s) g (compSeriesIntertwiner s hs β f) := by
  induction g using Quotient.inductionOn with
  | h g =>
    change compSeriesIntertwiner s hs β (pi s (Matrix.ProjGenLinGroup.mk g) f) =
      pi (-s) (Matrix.ProjGenLinGroup.mk g) (compSeriesIntertwiner s hs β f)
    rw [pi_mk, pi_mk]
    apply Subtype.ext
    funext h
    change (∫ x : ℂ, f ((weyl * upperUnipotent x * h) * g) ∂characterHaar β) =
      ∫ x : ℂ, f (weyl * upperUnipotent x * (h * g)) ∂characterHaar β
    simp only [mul_assoc]

/-- On the ℓ-th K-type, `M(s)` acts (in the compact picture) by `compSeriesEigenvalue (2s) β ℓ`,
for `0 < s < 1/2`. Adapted from `standardIntertwiner_harmonic_eigenvalue` in
`RepresentationTheory/PrincipalSeries/Complex/ComplexHarmonicEigenvaluesAndSmoothness.lean`. -/
theorem compSeriesIntertwiner_harmonic_eigenvalue (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1 / 2)
    (β : ℂˣ) (ℓ : ℕ) (f : PrincipalSeries s) (hf : f ∈ harmonicKType s ℓ) :
    compSeriesIntertwiner s hs0 β f ∈ harmonicKType (-s) ℓ ∧
    compactRestriction (-s) (compSeriesIntertwiner s hs0 β f) =
      (compSeriesEigenvalue (2 * s) β ℓ : ℂ) • compactRestriction s f := by
  have hcompact : compactRestriction s f ∈
      (harmonicPolynomials ℓ).map polynomialCompactRestriction := hf
  obtain ⟨p, hp, hpf⟩ := hcompact
  have hscalar : compactRestriction (-s) (compSeriesIntertwiner s hs0 β f) =
      (compSeriesEigenvalue (2 * s) β ℓ : ℂ) • compactRestriction s f := by
    ext k
    change (∫ x : ℂ, f (weyl * upperUnipotent x * complexSU2Embedding k) ∂characterHaar β) =
      (compSeriesEigenvalue (2 * s) β ℓ : ℂ) * f (complexSU2Embedding k)
    have hfk : ∀ k : ComplexSU2, f (complexSU2Embedding k) =
        MvPolynomial.eval (compactSphereCoordinate k) p :=
      fun k => (congrFun hpf k).symm
    rw [hfk k]
    exact compSeries_harmonic_integral s hs0 hs1 β ℓ p hp f hfk k
  refine ⟨?_, hscalar⟩
  change compactRestriction (-s) (compSeriesIntertwiner s hs0 β f) ∈
    (harmonicPolynomials ℓ).map polynomialCompactRestriction
  rw [hscalar]
  exact Submodule.smul_mem _ _ hf

/-- **Complementary-series positivity, all ν ∈ (0, 1).** For `0 < ν < 1`, with the library's
principal series at parameter `s = ν/2`, the standard intertwiner `M(ν/2)` maps the ℓ-th K-type to
the ℓ-th K-type, acts there by the scalar `(‖β‖/(2ν)) · ∏_{j=1}^{ℓ} (j − ν)/(j + ν)`, and that
scalar is strictly positive. At `ν = 1/3` this is the library's `standardIntertwiner_harmonic_eigenvalue`
together with `eigenvalue_pos`. -/
theorem compSeries_Ktype_eigenvalues (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1) (β : ℂˣ) (ℓ : ℕ)
    (f : PrincipalSeries (ν / 2)) (hf : f ∈ harmonicKType (ν / 2) ℓ) :
    compSeriesIntertwiner (ν / 2) (by linarith) β f ∈ harmonicKType (-(ν / 2)) ℓ ∧
    compactRestriction (-(ν / 2)) (compSeriesIntertwiner (ν / 2) (by linarith) β f) =
      (compSeriesEigenvalue ν β ℓ : ℂ) • compactRestriction (ν / 2) f ∧
    0 < compSeriesEigenvalue ν β ℓ := by
  have h := compSeriesIntertwiner_harmonic_eigenvalue (ν / 2) (by linarith) (by linarith)
    β ℓ f hf
  rw [show 2 * (ν / 2) = ν by ring] at h
  exact ⟨h.1, h.2, compSeriesEigenvalue_pos hν0 hν1 β ℓ⟩

/-- The intertwining form on a K-type, against any measure `μ` on SU(2):
`∫ (M f)(k) · conj (f k) dμ = λ_ℓ · ∫ ‖f k‖² dμ`. -/
theorem compSeries_form_Ktype (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1) (β : ℂˣ) (ℓ : ℕ)
    (μ : Measure ComplexSU2)
    (f : PrincipalSeries (ν / 2)) (hf : f ∈ harmonicKType (ν / 2) ℓ) :
    (∫ k, compactRestriction (-(ν / 2)) (compSeriesIntertwiner (ν / 2) (by linarith) β f) k *
        starRingEnd ℂ (compactRestriction (ν / 2) f k) ∂μ) =
      (compSeriesEigenvalue ν β ℓ : ℂ) *
        ((∫ k, ‖compactRestriction (ν / 2) f k‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  obtain ⟨-, h2, -⟩ := compSeries_Ktype_eigenvalues ν hν0 hν1 β ℓ f hf
  rw [h2]
  have hpt : (fun k => ((compSeriesEigenvalue ν β ℓ : ℂ) • compactRestriction (ν / 2) f) k *
        starRingEnd ℂ (compactRestriction (ν / 2) f k)) =
      fun k => (compSeriesEigenvalue ν β ℓ : ℂ) *
        ((‖compactRestriction (ν / 2) f k‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc, Complex.mul_conj', Complex.ofReal_pow]
  rw [hpt, integral_const_mul, integral_complex_ofReal]

/-- Positivity of the intertwining form on each K-type: real and nonnegative against any
measure on SU(2). -/
theorem compSeries_form_Ktype_nonneg (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1) (β : ℂˣ) (ℓ : ℕ)
    (μ : Measure ComplexSU2)
    (f : PrincipalSeries (ν / 2)) (hf : f ∈ harmonicKType (ν / 2) ℓ) :
    0 ≤ (∫ k, compactRestriction (-(ν / 2)) (compSeriesIntertwiner (ν / 2) (by linarith) β f) k *
        starRingEnd ℂ (compactRestriction (ν / 2) f k) ∂μ).re ∧
    (∫ k, compactRestriction (-(ν / 2)) (compSeriesIntertwiner (ν / 2) (by linarith) β f) k *
        starRingEnd ℂ (compactRestriction (ν / 2) f k) ∂μ).im = 0 := by
  rw [compSeries_form_Ktype ν hν0 hν1 β ℓ μ f hf, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_im]
  exact ⟨mul_nonneg (compSeriesEigenvalue_pos hν0 hν1 β ℓ).le
    (integral_nonneg fun k => by positivity), rfl⟩

end Intertwiner

end Arda.AxiomMetaplectic
