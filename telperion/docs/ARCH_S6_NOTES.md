# Stage S6 notes: the Sonin/prolate structure theorem (2026-10-11)

Branch `mm/arch-s6`, island `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2, Mathlib 51e6992e).
conjecture1_proved = False. Nothing here is RH progress.

S6 formalises Connes–Consani (arXiv:2006.13771, "CC") §4: the pair of projections P₁, P̂₁ on
L²(ℝ)_ev, the prolate eigenbasis, CC Prop 4.5 and the spectral decomposition (81). It follows bypass B2
of the blueprint: there is no Halmos two-subspace theory, no angle operator, no simplicity of the
spectrum and no prolate ODE. The only spectral input is an orthonormal eigenbasis of a compact
self-adjoint operator.

## Status

* 16 Lean files plus the guard, 3,865 lines in total, all built with `lake build`. The branch
  includes a merge of `mm/archimedean-rung` (S5's HS files, S8, S9).
* `ArchS6_Guard.lean` prints `#print axioms` for 337 declarations: every top-level theorem plus the
  `prolateData` instance. Every line is exactly `[propext, Classical.choice, Quot.sound]`. There is
  no `sorry` and no `axiom`.
* The L² Fourier link that the brief allowed to stay open is **proved** (`fourier_ae_eq`).
* **S8's `ProlateData` is instantiated with no extra hypotheses** (`ArchS6_ProlateData`). That
  includes S8's "one substantive analytic obligation", the sup bound `M n`. It is proved by
  pointwise Bessel plus a Sobolev inequality, with no prolate ODE (see "How M n is obtained").
* **Trace class.** Σ\|λ_n\| ≤ 2cosh 2π (`tsum_abs_mu_le`), hence S7's hypothesis
  Σ\|τ_n\| < ∞ (`summable_abs_tau`).

```
cd telperion/examples/rvm_bridge/lean
lake build ArchS6_Trace ArchS6_Bridge       # builds the whole chain
lake env lean ArchS6_Guard.lean             # 337 lines, all [propext, Classical.choice, Quot.sound]
```

| file | lines | thms | content |
|---|---|---|---|
| ArchS6_Abstract | 570 | 69 | CC Prop 4.5 and (81) for an abstract pair (P₁, F) and eigenbasis |
| ArchS6_Fourier | 235 | 29 | 𝓕 on L² equals the Fourier integral on L¹ ∩ L²; reflection; L²(ℝ)_ev |
| ArchS6_Proj | 255 | 27 | P₁, extension/restriction to [a, b], the concrete pair `evenPair`, S(1,1) |
| ArchS6_Kernel | 269 | 26 | R𝓕E = T_{e^{-2πixy}}, kernel composition, P₁P̂₁P₁ = E ∘ T_sinc ∘ R |
| ArchS6_Eigen | 167 | 10 | orthonormal eigenbasis of a compact self-adjoint operator (any RCLike) |
| ArchS6_Even | 245 | 24 | J : L²[0,1] → L²(ℝ)_ev and P₁𝓕J = J C, with C = S9's 2cos(2πxω) |
| ArchS6_Strict | 199 | 11 | f and 𝓕f both vanishing off [-1, 1] force f = 0; so 0 < \|λ\| < 1 |
| ArchS6_Prolate | 175 | 13 | concrete `ProlateBasis`, **`sonin_prolate_structure`**, sinc eigenvectors |
| ArchS6_Real | 212 | 22 | real-valued prolates via the real operator C_ℝ, real φ_n |
| ArchS6_Bridge | 122 | 11 | S9 interface: continuous orthonormal eigenfamily with Parseval |
| ArchS6_Functions | 171 | 14 | ξ_n, η_n, ψ_n, ζ_n as explicit functions; φ_n is C^∞ |
| ArchS6_Enum | 130 | 10 | the eigenbasis index type is countable and infinite, so ≃ ℕ |
| ArchS6_Sobolev | 75 | 1 | f(x)² ≤ (∫f²)/(b−a) + 2∫(f² + f'²) on [a, b] |
| ArchS6_Bounds | 354 | 41 | φ', φ'' under the integral; pointwise Bessel; sup bounds Q_n; Σλ²S < ∞ |
| ArchS6_ProlateData | 108 | 9 | **S8's `ProlateData` instance**, `exists_prolateData` |
| ArchS6_Trace | 204 | 19 | Σ\|λ_n\| ≤ 2cosh 2π; Σ\|τ_n\| < ∞ (S7's `hτ`) |
| ArchS6_Guard | 374 | – | `#print axioms` for every theorem and the instance |

Import graph: `Abstract`, `Fourier` and `Eigen` import only Mathlib.
`Proj` imports `ArchS5_Spectral`, `Abstract` and `Fourier`. The rest is a chain:
`Kernel → Even`, `Kernel → Strict`, `Even + Eigen + Strict → Prolate → Real → {Bridge, Functions}`.
`Sobolev` imports only Mathlib. `Bridge + Functions + Sobolev → Bounds`, then
`Bounds + Enum + ArchS5_HS + ArchS8_ProlateData → ProlateData → Trace`.

## Conventions (fixed once)

* **Scalars and spaces.** `L2R = Lp ℂ 2 (volume : Measure ℝ)`, with Mathlib's inner product
  ⟪f, g⟫ = ∫_ℝ conj(f) g. L²([a, b]) is S5's `Lp ℂ 2 (volI a b)` (`L2I a b`), and the real
  version is `L2IR a b`.
* **Even subspace.** `evenL2 : Submodule ℂ L2R` is the kernel of (reflection − 1). It is closed and
  complete.
* **Fourier transform.** `𝓕` is Mathlib's `Lp.fourierTransformₗᵢ`. Its kernel is e^{-2πixy}, which is
  CC's F_{e_ℝ}. `𝓕⁻` has kernel e^{2πixy}.
* **Projections.** P₁ = multiplication by 1_{[-1,1]} (closed interval). CC's P̂₁ = F⁻¹P₁F is
  `hatP1 = 𝓕⁻ ∘ P1 ∘ 𝓕` on L²(ℝ). On L²(ℝ)_ev it equals F P₁ F (`evenPair_hatP₁`).
* **Eigenvalues.** λ_n is CC's **signed** λ(n), the eigenvalue of P₁FP₁ and of S9's T. The operator
  P₁P̂₁P₁ has eigenvalue λ_n².
* **Normalisation.** CC's inner product on L²(ℝ)_ev is ∫₀^∞ (CC (16)), which is half of Mathlib's
  ∫_ℝ. The map U ξ = ξ/√2 is unitary from CC's space to `evenL2`, so every inner-product identity
  transfers verbatim. Concretely `ξ_n(S6) = ξ_n(CC)/√2`, and `c2 = 1/√2` appears in the function forms.
  S9's unit eigenfunction e_n (∫₀¹ e_n² = 1) maps to ξ_n = J e_n with Mathlib norm 1, matching CC's
  norm 1.

## Statements

### Abstract layer (`ArchS6_Abstract`, namespace `ArchS6`)

```lean
structure ProjPair (H) where            -- P₁ orthogonal projection, F self-adjoint involution
  P₁ F : H →L[ℂ] H
  P₁_P₁ : ∀ x, P₁ (P₁ x) = P₁ x;  inner_P₁ : ∀ x y, ⟪P₁ x, y⟫ = ⟪x, P₁ y⟫
  F_F : ∀ x, F (F x) = x;          inner_F : ∀ x y, ⟪F x, y⟫ = ⟪x, F y⟫
-- derived: hatP₁ = F P₁ F, P = 1 - P₁, hatP = 1 - hatP₁, PhatPP = P hatP P,
--          sonin = {x | P₁ x = 0 ∧ P₁ (F x) = 0}  (CC Def 4.4)
structure ProlateBasis (S : ProjPair H) (ι) where
  ξ : ι → H;  lam : ι → ℝ;  orthonormal : Orthonormal ℂ ξ
  P₁_ξ : ∀ i, S.P₁ (ξ i) = ξ i
  eigen : ∀ i, S.P₁ (S.F (ξ i)) = (lam i : ℂ) • ξ i              -- CC (69)
  complete : ∀ x, S.P₁ x = x → (∀ i, ⟪ξ i, x⟫ = 0) → x = 0
  abs_lam_lt_one : ∀ i, |lam i| < 1
-- derived: η i = F ξ i, ψ i = P η i, s i = √(1 - λ²), ζ i = s⁻¹ • ψ i, τ i = λ / s
```

* **Prop 4.5 (i).** `P₁_η`: P₁ η = λ ξ (CC (74)).
* **Prop 4.5 (iii).** `inner_ψ_ψ` says ⟪ψ_i, ψ_j⟫ = δ_ij(1 − λ_i²). `norm_ψ` gives ‖ψ‖ = √(1 − λ²), and
  `orthonormal_ζ` says the ζ_n are orthonormal.
* **(78), (80), (70).** `hatP₁_ξ` gives P̂₁ξ = λη. `hatP₁_ξ'` gives P̂₁ξ = λ²ξ + λψ. `P₁hatP₁P₁_ξ`
  gives P₁P̂₁P₁ξ = λ²ξ.
* **ζ_n are eigenvectors.** `PhatPP_ψ` and `PhatPP_ζ` give P P̂ P ζ = λ² ζ.
* **Expansions.** `hasSum_P₁` says P₁ = Σ|ξ⟩⟨ξ|. `hasSum_hatP₁_P₁` is CC (79), and
  `hasSum_hatP₁_P₁'` is CC (80).
* **Sonin space as an eigenspace.** `mem_sonin_iff_fixed`: S(1,1) is the eigenspace of P P̂ P for the
  eigenvalue 1. This is the step CC use for (90).
* **(81).** `hasSum_PhatPP`: P P̂ P x = Σ λ²⟨ζ|x⟩ζ + S x as a `HasSum`, where
  S = `ProlateBasis.soninProj` is the orthogonal projection on Sonin's space.
* **(76) with exact remainder.** `hasSum_inner_PhatPP`: Re⟨x, P P̂ P x⟩ = Σ λ²|⟨ζ|x⟩|² + ‖Sx‖².
  `tsum_le_inner_PhatPP` is CC's inequality.
* **(77).** `inner_ξ_A_ξ`: for any operator A with ⟨η|Aη⟩ = ⟨ξ|Aξ⟩,
  ⟨ξ|Aξ⟩ = ⟨ζ|Aζ⟩ + τ(⟨ξ|Aζ⟩ + ⟨ζ|Aξ⟩). S7 supplies the hypothesis for A = ϑ(ρ⁻¹), using
  ϑ(ρ) = Fϑ(ρ⁻¹)F and real ξ_n.

How (81) is proved without Halmos: a vector x ∈ ker P₁ orthogonal to every ζ_n lies in Sonin's space
(`mem_sonin_of_orthogonal`). The reason is that ⟨ξ_i, P₁Fx⟩ = ⟨η_i, x⟩ = ⟨ψ_i, x⟩ + λ⟨ξ_i, x⟩ = 0,
and the ξ_i are complete in ran P₁. The rest is Bessel and Riesz–Fischer.

### L² Fourier link (`ArchS6_Fourier`)

Mathlib defines 𝓕 on L² only as the isometric extension from Schwartz space. These lemmas fill the gap:

```lean
theorem fourier_ae_eq (f : L2R) (hf : Integrable (f : ℝ → ℂ)) : (𝓕 f : L2R) =ᵐ[volume] 𝓕 (f : ℝ → ℂ)
theorem fourierInv_ae_eq (f : L2R) (hf : Integrable (f : ℝ → ℂ)) : (𝓕⁻ f : L2R) =ᵐ[volume] 𝓕⁻ (f : ℝ → ℂ)
theorem fourierInv_eq_reflect_fourier (f) : 𝓕⁻ f = reflect (𝓕 f)
theorem fourier_reflect (f) : 𝓕 (reflect f) = reflect (𝓕 f)
theorem fourier_fourier_of_even (hf : f ∈ evenL2) : 𝓕 (𝓕 f) = f
theorem inner_fourier_of_even (f) (hg : g ∈ evenL2) : ⟪𝓕 f, g⟫ = ⟪f, 𝓕 g⟫
def fourierEven : evenL2 →L[ℂ] evenL2
```

The proof of `fourier_ae_eq` goes through the tempered-distribution embedding
(`Lp.fourier_toTemperedDistribution_eq`). It then uses the multiplication formula
(`VectorFourier.integral_fourierIntegral_smul_eq_flip`) and the fundamental lemma
(`ae_eq_of_integral_contDiff_smul_eq`). The reflection identities follow by density of Schwartz
functions (`L2R_eq_of_integrable`).

### Concrete pair, sinc kernel (`ArchS6_Proj`, `ArchS6_Kernel`)

* **Extension and restriction.** `extendIcc a b : L2I a b →ₗᵢ L2R` and
  `restrictIcc a b : L2R →L L2I a b`, with `restrictIcc_extendIcc` and `inner_extendIcc_left`
  (⟪E h, f⟫ = ⟪h, R f⟫).
* **P₁ and the concrete pair.** `P1`, `isOrthProj_P1`, `P1_reflect`. `evenPair : ProjPair evenL2` is
  CC's pair. `mem_sonin_evenPair` says ξ ∈ S(1,1) iff ξ = 0 and 𝓕ξ = 0 a.e. on [-1, 1].
* **Fourier as an integral operator.** `restrict_fourier_extend`: R𝓕E =
  `intOp (kernelOfContinuous a b fourierK _)`, with fourierK(x, y) = e^{-2πixy}.
  `restrict_fourierInv_extend` is the same with e^{+2πixy}.
* **Kernel composition.** `intOp_kernelOfContinuous_comp`: T_{k₁} T_{k₂} = T_{k₁⋆k₂} for continuous
  kernels on [a, b], with (k₁⋆k₂)(x, z) = ∫ k₁(x, y)k₂(y, z) dy.
* **The sinc kernel.** `sincK_eq` gives sincK(x, y) = ∫_{-1}^{1} e^{2πi(x−y)ω} dω = 2 sinc(2π(x − y)).
  **`P1_hatP1_P1_eq`** states `P1 ∘L hatP1 ∘L P1 = E ∘L sincOp ∘L R` on L²(ℝ).
* **Properties.** `sincOp_compact_selfAdjoint` (via S5). `re_inner_sincOp` gives
  ⟨T_sinc h, h⟩ = ‖B h‖² with B = R𝓕E, and `re_inner_sincOp_le` gives 0 ≤ T_sinc ≤ 1.

### Eigenbasis, even picture, strictness, structure theorem

* **`ArchS6_Eigen`.** `EigenBasis T ι` is an orthonormal, complete family of eigenvectors with real
  eigenvalues. `exists_eigenBasis` gives one for any compact symmetric T on a Hilbert space over any
  RCLike field. Also: `hasSum`, `hasSum_inner_mul_inner` (Parseval), `toHilbertBasis`.
* **`ArchS6_Even`.** J h = (E₊h + R E₊h)/√2 is a linear isometry. `J_mem_evenL2` and `P1_J` place
  its image in L²(ℝ)_ev ∩ ran P₁, and `J_restrict` shows the range is all of that space.
  `Cop` = T_{2cos(2πxy)} on L²[0,1] is S9's operator. **`P1_fourier_J`** gives P₁𝓕J = J C.
* **`ArchS6_Strict`.** `eq_zero_of_fourier_ae_zero_Ioo`: if P₁f = f and 𝓕f vanishes a.e. on some
  (a, b), then f = 0. The proof extends 𝓕f to the entire function
  z ↦ ∫_{-1}^{1} e^{-2πizv} f(v) dv, differentiates under the integral sign, and applies the
  identity theorem. Corollaries:
  * `eq_zero_of_P1_fourier`: no nonzero f has both f and 𝓕f supported in [-1, 1];
  * `abs_lt_one_of_eigen`: \|λ\| < 1;
  * `ne_zero_of_eigen`: λ ≠ 0.
* **`ArchS6_Prolate`.**
  * `prolateBasisOf (b : EigenBasis Cop ι) : ProlateBasis evenPair ι` sets ξ_i = J e_i and
    λ_i = μ_i.
  * **`sonin_prolate_structure`** is the S6 capstone. There is a prolate basis with
    0 < \|λ_n\| < 1, each ξ_n = J e_n for a unit eigenvector of C, P₁ = Σ\|ξ⟩⟨ξ\|,
    (81) as a `HasSum`, and S(1,1) = Fix(P P̂ P).
  * `sincOp_restrict_ξ`: R ξ_n is an eigenvector of T_sinc with eigenvalue λ_n² (CC (70)).
  * `phi b i = λ⁻¹ · cosTrans (e i)` is the analytic continuation. `ae_eq_phi` says it equals e_i on
    [0,1], `fourier_ξ_ae` says 𝓕ξ_i = c2·λ_i·φ_i, and `continuous_phi`.
* **`ArchS6_Real`.**
  * `CopR` is the real operator. `complexify` turns a real eigenbasis into a complex one, and
    `realProlateBasis bR` is the resulting prolate basis.
  * `sonin_prolate_structure_real` is the capstone with real prolates.
  * `phiR` is the real φ_n. `phi_complexify` gives φ = ↑φ_R; also `ae_eq_phiR`, `continuous_phiR`,
    `fourier_ξ_ae_real`.
* **`ArchS6_Functions`.**
  * `coeFn_ξ`: ξ_n = c2·1_{[-1,1]}·φ_n.
  * `coeFn_η`: η_n = c2·λ_n·φ_n.
  * `coeFn_ψ`: ψ_n = c2·λ_n·1_{ℝ∖[-1,1]}·φ_n.
  * `coeFn_ζ`: ζ_n = c2·(λ_n/√(1−λ_n²))·1_{ℝ∖[-1,1]}·φ_n.
  * Real versions: `coeFn_ξ_real`, `coeFn_ζ_real`, `phiR_neg`.
  * **`contDiff_phiR`**: φ_n is C^N for every N ≤ ∞, via `Real.contDiff_fourier`, because E₊e_n has
    compact support and so finite moments.

### Enumeration, sup bounds, `ProlateData`, trace class

* **`ArchS6_Enum`.** `countable_of_orthonormal` uses disjoint balls of radius 1/2 in the separable
  space L²([0,1]; ℝ). `infinite_of_complete` uses the indicators of (1/(n+2), 1/(n+1)), which are
  infinitely many orthogonal nonzero vectors. Together these give **`exists_equiv_nat`**: every
  real eigenbasis of C_ℝ has an enumeration σ : ℕ ≃ ι.
* **`ArchS6_Sobolev`.** `sq_le_sobolev`: for f with continuous derivative and x ∈ [a, b],
  f(x)² ≤ (∫_a^b f²)/(b − a) + 2∫_a^b (f² + f'²).
* **`ArchS6_Bounds`.**
  * `hasDerivAt_kInt` differentiates ∫₀¹ g(x, y) e(y) dy under the integral sign.
  * `hasDerivAt_phiR` and `hasDerivAt_dphiR` give φ' = μ⁻¹F₁ and φ'' = μ⁻¹F₂, with
    F_k = ∫₀¹ ∂ₓᵏ 2cos(2πxy) e(y) dy.
  * `sum_sq_kInt_le` is pointwise Bessel. `abs_phiR_le_Q` and `abs_deriv_phiR_le_Q` give the sup
    bounds on [1/3, 3]. `summable_mu_sq_mul_S` gives Σ μ²S < ∞.
* **`ArchS6_ProlateData`.** `prolateData bR σ : ArchS8.ProlateData` and **`exists_prolateData`**.
* **`ArchS6_Trace`.** `hasSum_mu`: λ_i = Σ_j a_j c_ij², with a_j the coefficients of 2cos(2πt) in
  t² and c_ij = ∫₀¹ x^{2j} e_i. Then `sum_abs_mu_le`, `summable_abs_mu`,
  **`tsum_abs_mu_le`** (Σ\|λ_i\| ≤ 2cosh 2π), and **`summable_abs_tau`**.

### How `M n` is obtained (S8 obligation 5)

S8 needs sup bounds M_n on \|φ_n\| and \|φ_n'\| over [e^{−T}, 1], and N_n over [1, e^T], with
Σ λ_n²/(1 − λ_n²)·M_n·N_n < ∞. The eigen-relation alone gives only M_n ~ 1/\|λ_n\|, which is too
weak. The proof here works in three steps and does not use the prolate ODE.

1. **Pointwise Bessel.** λ_n φ_n(x) = ∫₀¹ 2cos(2πxy) e_n(y) dy = ⟨e_n, k_x⟩ for every real x. The
   same holds for λ_n φ_n' and λ_n φ_n'' with ∂ₓk_x and ∂ₓ²k_x. These kernels are bounded by 2, 4π
   and 8π² on y ∈ [0, 1]. Bessel over the orthonormal e_n gives, for every x,
   Σ_n λ_n²(φ_n² + φ_n'² + φ_n''²)(x) ≤ 4 + 16π² + 64π⁴.
2. **Sobolev on [a, b] = [1/3, 3] = [e^{−T}, e^T] with T = log 3.** Put
   S_n = ∫_a^b (φ_n² + φ_n'² + φ_n''²) and Q_n = √(C·S_n), where C = 1/(b − a) + 2. Then
   \|φ_n(x)\| ≤ Q_n and \|φ_n'(x)\| ≤ Q_n on all of [a, b].
3. **Summability.** Integrating step 1 over [a, b] gives Σ_n λ_n² S_n ≤ (b − a)(4 + 16π² + 64π⁴).
   With M_n = N_n = Q_n, each summand λ²/(1−λ²)·Q² = C·λ²S/(1−λ²) is at most 2C·λ²S once λ² ≤ 1/2.
   That holds for all large n because Σλ² < ∞ (S5's `tsum_real_eigenvalue_sq_le`).

Polynomial bounds in n, as in CC (100)/(166), are not needed and not proved. The bound Q_n is not
explicit per n; only its square-summability against λ_n² is.

## Correspondence with S8 and S9

| CC (§4) | S6 (Lean) | S8 (`ArchS8_ProlateData`) | S9 (`ArchS9_*`) |
|---|---|---|---|
| L²(ℝ)_ev, ⟨·\|·⟩ = ∫₀^∞ | `evenL2`, ⟪·,·⟫ = ∫_ℝ (U ξ = ξ/√2) | – | – |
| F_{e_ℝ} | `fourierEven` / `𝓕` | – | – |
| P₁, P̂₁, P, P̂ | `evenPair.P₁`, `.hatP₁`, `.P`, `.hatP` | – | – |
| S(1,1), S | `evenPair.sonin`, `ProlateBasis.soninProj` | – | – |
| P₁F P₁ on ran P₁ ∩ even | J C J⁻¹ (`P1_fourier_J`) | – | `T` with kernel `K ω x = 2cos(2πxω)` |
| λ(n) | `b.lam i = bR.μ i` | `lam n` | `thR n` (certified, n ≤ 12) |
| ξ_n on [0,1], ∫₀¹ξ_n² = 1 | `bR.e i` (`L2IR 0 1`), ξ_n = J e_n | `phi n` on [0,1] | `psiS n` (ip ψ ψ ≈ 1) |
| ξ_n^an = λ⁻¹ F ξ_n | `phiR bR i = λ⁻¹ cosTransR e_i` | `phi n` | `T ξ / λ` (`continuous_representative`) |
| ζ_n = λ/√(1−λ²) ξ_n^an on \|x\|>1 | `coeFn_ζ_real` (× c2) | `cc84_term` | – |

**S9.** S9 reports that its only remaining input is "Parseval for ψ_n against a complete
orthonormal family of continuous eigenfunctions of T". `ArchS6_Bridge.exists_S9_family` supplies that
family in S9's own terms. `ipS9` and `TS9` reproduce S9's `ip` and `T` verbatim, so no cross-branch
import is needed. It gives an orthonormal family e_k, continuous on ℝ, with
`TS9 (e k) ω = lam k * e k ω` for every ω, `lam k ≠ 0 ∧ |lam k| < 1`, and Parseval for every
continuous ψ. Fed to `ArchS9_Bridge.prolate_spectrum_complete`, it gives that S9's 13 certified
windows each contain exactly one eigenvalue of the complete spectrum. At merge, unfold `ipS9`/`TS9`
against `ip`/`T` (both are `rfl` after unfolding `K`). S9 states `horth` with `[DecidableEq ι]`; use
`classical`.

**S8.** `prolateData bR σ` fills every `ProlateData` field:
* `lam n = μ_{σ n}` with `lam_sq_lt_one`;
* `phi n = phiR bR (σ n)`, which is C^∞ (`contDiff_phiR`);
* `T = log 3`;
* `M n = N n = Q_{σ n}` with `bound_inner` and `bound_outer`;
* `summable_wMN`.

**Normalisation: `phi n = phiR`, not √2·phiR.** e_n is a unit vector of L²([0,1]), so
∫₀¹ phiR² = 1, which is CC's normalisation (16). The 1/√2 appears only in the L²(ℝ) vectors
ξ_n = J e_n.

**S7.** `exists_prolateData` provides (ι, bR, σ, D) with `D.lam n = bR.μ (σ n)` and
`D.phi n = phiR bR (σ n)`, which are the hypotheses `hDlam` and `hDphi` of S7's `thm47_concrete`.
`summable_abs_tau bR` is its `hτ`. S7 itself proved that S6's ξ_n and ζ_n are a.e. equal to
`xiRep (phiR bR n)` and `zetaRep τ_n (phiR bR n)` (`ArchS7_Concrete.xi_ae`, `zeta_ae`, using
`fourier_ξ_ae_real`). `coeFn_ξ_real` and `coeFn_ζ_real` here state the same facts with indicators.
So S7's obligation O4 is fully discharged by S6, and the abstract API in `ArchS6_Abstract` is
unchanged.

## Open items

1. **Ordering by S9's windows.** σ is an arbitrary enumeration. Indexing n ≤ 12 by S9's certified
   windows is a one-line composition after merge with S9: `exists_S9_family` feeds
   `prolate_spectrum_complete`, see arch-s9's note. Nothing in S7 or S8 needs it.
2. **Per-index decay.** The per-index decay of λ_n (|λ_n| ≤ 2(2π)^n/n! for the n-th largest) is
   not proved. Only the unordered Σ|λ| ≤ 2cosh 2π is proved, and that is all S7 and S8 use.
3. **Not needed, not done.** Simplicity of the spectrum, identification with Slepian's
   PS_{2n,0}(2π,·), explicit polynomial bounds on ξ_n(1), and the odd part of ran P₁.
4. **Thm 4.7 and ϑ.** These are S7's (its O1-O3). S6 gives S7 the abstract (77), the function
   forms of ξ_n and ζ_n, (81), `exists_prolateData` and `summable_abs_tau`.

## Lean footguns met on this pin

* **𝓕 on L² is extension-only.** There is no lemma identifying it with the Fourier integral on
  L¹ ∩ L²; use `fourier_ae_eq` from here. Note that `𝓕 f` for `f : L2R` and for `f : ℝ → ℂ` print
  identically.
* **Two `ofReal` coercions.** `RCLike.ofReal` and `Complex.ofReal` print identically and are `rfl`
  equal (`RCLike.ofReal_eq_complex_ofReal`), but `rw` does not see through them. An `EigenBasis` over
  ℂ states `eigen` with the RCLike cast, so use `show Cop e = (μ : ℂ) • e from b.eigen i` before
  rewriting. Likewise `integral_ofReal` (RCLike) does not rewrite Complex casts; use
  `integral_complex_ofReal`.
* **`exact_mod_cast` and complex norms.** `exact_mod_cast` can fail to strip `(↑a : ℂ) = ↑b` when
  the casts come from `inner_self_eq_norm_sq_to_K`. Use `congrArg RCLike.re` and
  `inner_self_eq_norm_sq` (real form) instead.
* **`convert … using 1` on `HasDerivAt`** leaves instance goals. Use `HasDerivAt.congr_deriv`.
* **`Submodule.coe_norm`** is `‖x‖ = ‖(x : E)‖`, so rewrite forward.
* **`Measure.eqOn_open_of_ae_eq`** needs `(μ := volume)` explicitly, otherwise the
  `IsOpenPosMeasure` instance is stuck.
* **Universes.** For `∃ ι : Type u, EigenBasis T ι` the scalar field must be `{𝕜 : Type}`, not
  `Type*`.
* **`open Classical in`** must come before the docstring.
* **Anonymous constructors inside `rw [indicator_of_mem ⟨…, …⟩]`** fail ("expected type could not
  be determined"). Use `(show x ∈ Icc a b from ⟨…, …⟩)`.
* **ContDiff smoothness.** `ContDiff ℝ ∞` needs `open scoped ContDiff`. `Set.setOf_eq_eq_singleton`
  is deprecated; use `Set.ofPred_eq_eq_singleton`.
* **Convenient tools.** `Integrable.bdd_mul` takes an a.e. bound, which is convenient on `volI`.
  `ae_eq_restrict_iff_indicator_ae_eq` converts between a.e. on `volI a b` and a.e. indicator
  equality on ℝ.
* **More footguns.** `Fact ((2 : ℝ≥0∞) ≠ ⊤)` is not an instance at this pin. Add it with
  `have` before `infer_instance` for `SeparableSpace (Lp ℝ 2 (volI 0 1))` (`Lp.SecondCountableTopology`).
* **`norm_tsum_le_tsum_norm` speaks of `‖·‖`.** For real `|·|`, rewrite with `← Real.norm_eq_abs`
  first.
* **`(hf.pow 2).intervalIntegrable`** has the function `f ^ 2` (Pi form), which does not match
  `fun t ↦ f t ^ 2` in `integral_add`. Use a `have` with the lambda type.
* **`intervalIntegral.integral_finset_sum`** is deprecated; use `integral_finsetSum` with explicit
  `(f := fun i t ↦ …)`.
* **Build times.** Each `lake build ArchS6_*` step takes about 30-45 s at the current load.
