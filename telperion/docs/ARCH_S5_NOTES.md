# Stage S5 notes: integral operators with L² kernels (2026-10-11)

Branch `mm/arch-s5`, island `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2, Mathlib 51e6992e).
conjecture1_proved = False. Nothing here is RH progress. This is reusable infrastructure for S6, S7 and S11.

## What this stage gives you

Everything lives in `namespace ArchS5`. Scalars are any `𝕜` with `[RCLike 𝕜]`, so ℝ and ℂ both work.

The setting is a pair of measure spaces `(α, μ)` and `(β, ν)`. Boundedness and adjoints only need
`SFinite`. Compactness needs `IsFiniteMeasure`. A kernel is an element `K : Lp 𝕜 2 (μ.prod ν)`, and its
operator is `intOp K : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ`.

All five Lean files plus the guard build. The guard prints exactly `[propext, Classical.choice, Quot.sound]`
for all 105 top-level theorems. There is no `sorry` and no `axiom`.

| file | lines | content |
|---|---|---|
| ArchS5_KernelOp.lean | 297 | pointwise transform, Hilbert-Schmidt bound, `intOpL`, `intOp`, kernel perturbation |
| ArchS5_Adjoint.lean | 143 | sesquilinear form, adjoint kernel, Hermitian kernels give self-adjoint operators |
| ArchS5_Compact.lean | 174 | compactness: rectangles are rank one, then a pi-lambda argument, then `Lp.induction` |
| ArchS5_Rayleigh.lean | 296 | `topEig`, variational bounds, Weyl k = 1, attainment for compact symmetric operators |
| ArchS5_MinMax.lean | 185 | `minmaxEig`, Weyl for every k, the two Courant-Fischer bounds, `minmaxEig T 1 = topEig T` |
| ArchS5_Spectral.lean | 193 | spectral package for `intOp`, continuous kernels on `[a, b]` |
| ArchS5_Guard.lean | 117 | `#print axioms` for every theorem |

Build and check:

```
cd telperion/examples/rvm_bridge/lean
lake build ArchS5_Spectral      # builds the whole chain
lake env lean ArchS5_Guard.lean # 105 lines, all [propext, Classical.choice, Quot.sound]
```

Import graph: `KernelOp → Adjoint → Compact`, `Rayleigh → MinMax`, and `Compact + MinMax → Spectral`.
`Rayleigh` and `MinMax` only import Mathlib. They work for any operator on any real or complex inner
product space.

## API with exact signatures

### Operator construction (ArchS5_KernelOp)

```lean
def kernelApply (ν : Measure β) (K : α × β → 𝕜) (f : β → 𝕜) (x : α) : 𝕜 := ∫ y, K (x, y) * f y ∂ν

theorem eLpNorm_two_sq (g : γ → E) : eLpNorm g 2 m ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂m
theorem enorm_kernelApply_le (hK : StronglyMeasurable K) (hf : AEStronglyMeasurable f ν) (x : α) :
    ‖kernelApply ν K f x‖ₑ ≤ eLpNorm (fun y ↦ K (x, y)) 2 ν * eLpNorm f 2 ν
theorem lintegral_eLpNorm_section_sq [SFinite ν] (hK : AEStronglyMeasurable K (μ.prod ν)) :
    ∫⁻ x, eLpNorm (fun y ↦ K (x, y)) 2 ν ^ 2 ∂μ = eLpNorm K 2 (μ.prod ν) ^ 2
theorem eLpNorm_kernelApply_le [SFinite ν] (hK : StronglyMeasurable K) (hf : MemLp f 2 ν) :
    eLpNorm (kernelApply ν K f) 2 μ ≤ eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν
theorem memLp_kernelApply [SFinite ν] (hK : StronglyMeasurable K) (hK2 : MemLp K 2 (μ.prod ν))
    (hfs : StronglyMeasurable f) (hf : MemLp f 2 ν) : MemLp (kernelApply ν K f) 2 μ
theorem ae_memLp_section [SFinite ν] (hK : StronglyMeasurable K) (hK2 : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ K (x, y)) 2 ν
theorem kernelApply_congr_right (h : f =ᵐ[ν] g) : kernelApply ν K f = kernelApply ν K g
theorem kernelApply_congr_left [SFinite ν] (h : K =ᵐ[μ.prod ν] K') :
    kernelApply ν K f =ᵐ[μ] kernelApply ν K' f

def intOpL : Lp 𝕜 2 (μ.prod ν) →L[𝕜] Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ      -- explicit args 𝕜 μ ν
def intOp (K : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ := intOpL 𝕜 μ ν K

theorem intOp_ae_eq (K) (f : Lp 𝕜 2 ν) : intOp K f =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν
theorem intOp_apply_eq_iff (K) (f) (g : Lp 𝕜 2 μ) :
    intOp K f = g ↔ g =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν
theorem norm_intOp_apply_le (K) (f) : ‖intOp K f‖ ≤ ‖K‖ * ‖f‖
theorem norm_intOp_le (K) : ‖intOp K‖ ≤ ‖K‖                          -- (1) Hilbert-Schmidt bound
theorem norm_intOpL_le : ‖intOpL 𝕜 μ ν‖ ≤ 1
theorem norm_intOp_sub_le (K K') : ‖intOp K - intOp K'‖ ≤ ‖K - K'‖   -- (6)
theorem lipschitzWith_intOp : LipschitzWith 1 (fun K : Lp 𝕜 2 (μ.prod ν) ↦ intOp K)
theorem continuous_intOp : Continuous (fun K : Lp 𝕜 2 (μ.prod ν) ↦ intOp K)
theorem intOp_zero / intOp_add / intOp_sub / intOp_neg / intOp_smul
```

All theorems from `intOp_ae_eq` on assume `[SFinite ν]`.

### Adjoint and self-adjointness (ArchS5_Adjoint), assuming `[SFinite μ] [SFinite ν]`

```lean
theorem eLpNorm_two_tensor (hg : AEStronglyMeasurable g μ) (hf : AEStronglyMeasurable f ν) :
    eLpNorm (fun p : α × β ↦ g p.1 * f p.2) 2 (μ.prod ν) = eLpNorm g 2 μ * eLpNorm f 2 ν
theorem memLp_two_tensor (hg : MemLp g 2 μ) (hf : MemLp f 2 ν) :
    MemLp (fun p : α × β ↦ g p.1 * f p.2) 2 (μ.prod ν)
theorem inner_intOp_eq_integral (K) (f : Lp 𝕜 2 ν) (g : Lp 𝕜 2 μ) :
    ⟪g, intOp K f⟫_𝕜 = ∫ p, conj (g p.1) * K p * f p.2 ∂(μ.prod ν)
theorem inner_intOp_left_eq_integral (K) (f) (g) :
    ⟪intOp K f, g⟫_𝕜 = ∫ p, g p.1 * conj (K p) * conj (f p.2) ∂(μ.prod ν)
def kernelAdjoint (K : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 (ν.prod μ)     -- (y, x) ↦ conj K(x, y)
theorem kernelAdjoint_ae_eq (K) : kernelAdjoint K =ᵐ[ν.prod μ] fun q ↦ conj (K q.swap)
theorem kernelAdjoint_kernelAdjoint (K) : kernelAdjoint (kernelAdjoint K) = K
theorem inner_intOp_kernelAdjoint (K) (f) (g) :
    ⟪intOp K f, g⟫_𝕜 = ⟪f, intOp (kernelAdjoint K) g⟫_𝕜
theorem adjoint_intOp (K) : ContinuousLinearMap.adjoint (intOp K) = intOp (kernelAdjoint K)
def IsHermitianKernel (K : Lp 𝕜 2 (μ.prod μ)) : Prop := ∀ᵐ p ∂(μ.prod μ), K p.swap = conj (K p)
theorem kernelAdjoint_eq_self (hK : IsHermitianKernel K) : kernelAdjoint K = K
theorem isSelfAdjoint_intOp (hK : IsHermitianKernel K) : IsSelfAdjoint (intOp K)      -- (3)
theorem isSymmetric_intOp (hK : IsHermitianKernel K) :
    (intOp K : Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ).IsSymmetric
```

### Compactness (ArchS5_Compact), assuming `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`

```lean
theorem intOp_indicator_rect (hA : MeasurableSet A) (hB : MeasurableSet B) (c : 𝕜) (f : Lp 𝕜 2 ν) :
    intOp (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c) f =
      (∫ y in B, f y ∂ν) • indicatorConstLp 2 hA (measure_ne_top μ A) c
theorem isCompactOperator_rankOne (φ : E →L[𝕜] 𝕜) (v : F) : IsCompactOperator (fun f ↦ φ f • v)
theorem isCompactOperator_intOp_indicator (c : 𝕜) :
    ∀ (S : Set (α × β)) (hS : MeasurableSet S),
      IsCompactOperator (intOp (indicatorConstLp 2 hS (measure_ne_top (μ.prod ν) S) c))
theorem isCompactOperator_intOp (K : Lp 𝕜 2 (μ.prod ν)) : IsCompactOperator (intOp K)   -- (2)
```

### Top eigenvalue (ArchS5_Rayleigh), for any `T : E →L[𝕜] E` on an inner product space

```lean
def topEig (T : E →L[𝕜] E) : ℝ := ⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x
theorem topEig_eq_iSup_sphere (T) : topEig T = ⨆ x : sphere (0 : E) 1, re ⟪T x, x⟫
theorem rayleighQuotient_le_topEig (T) (hx : x ≠ 0) : T.rayleighQuotient x ≤ topEig T
theorem re_inner_le_topEig_mul (T) (x) : re ⟪T x, x⟫ ≤ topEig T * ‖x‖ ^ 2
theorem le_topEig_of (T) (hx : x ≠ 0) (h : c * ‖x‖ ^ 2 ≤ re ⟪T x, x⟫) : c ≤ topEig T
theorem topEig_le_of_forall [Nontrivial E] (T) (h : ∀ x, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) : topEig T ≤ c
theorem topEig_le_of_forall' (T) (hc : 0 ≤ c) (h : ∀ x, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) : topEig T ≤ c
theorem abs_topEig_le_norm (T) : |topEig T| ≤ ‖T‖
theorem topEig_mono (h : ∀ x, re ⟪A x, x⟫ ≤ re ⟪B x, x⟫) : topEig A ≤ topEig B
theorem abs_topEig_sub_le (A B) : |topEig A - topEig B| ≤ ‖A - B‖                     -- (5), k = 1
theorem topEig_le_add_norm_sub (A B) : topEig A ≤ topEig B + ‖A - B‖
theorem norm_sq_apply_le_of_nonneg (S) (hS : (S : E →ₗ[𝕜] E).IsSymmetric)
    (hpos : ∀ x, 0 ≤ re ⟪S x, x⟫) (x) : ‖S x‖ ^ 2 ≤ ‖S‖ * re ⟪S x, x⟫
theorem exists_eigenvector_topEig (T) (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hpos : 0 < topEig T) : ∃ v : E, ‖v‖ = 1 ∧ T v = (topEig T : 𝕜) • v               -- (4)
theorem hasEigenvalue_topEig (T) (hT) (hK) (hpos) :
    Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) (topEig T : 𝕜)
theorem exists_isMaxOn_sphere (T) (hT) (hK) (hpos) : ∃ v : E, ‖v‖ = 1 ∧ re ⟪T v, v⟫ = topEig T
theorem eigenvalue_le_topEig (T) (hv : v ≠ 0) (h : T v = (c : 𝕜) • v) : c ≤ topEig T
theorem abs_iSup_sub_iSup_le / abs_iInf_sub_iInf_le      -- order lemmas, empty index allowed
```

`topEig T` uses the same expression as Mathlib's `IsSelfAdjoint.hasEigenvector_of_isMaxOn`, so the two
are interchangeable.

### Variational eigenvalues (ArchS5_MinMax)

```lean
def rayleighInf (T) (V : Submodule 𝕜 E) : ℝ := ⨅ x : { x : V // x ≠ 0 }, T.rayleighQuotient (x : E)
def minmaxEig (T : E →L[𝕜] E) (k : ℕ) : ℝ :=
  ⨆ V : { V : Submodule 𝕜 E // finrank 𝕜 V = k }, rayleighInf T V
theorem abs_minmaxEig_sub_le (A B) (k) : |minmaxEig A k - minmaxEig B k| ≤ ‖A - B‖        -- (5), all k
theorem minmaxEig_le_add_norm_sub (A B) (k) : minmaxEig A k ≤ minmaxEig B k + ‖A - B‖
theorem abs_minmaxEig_le_norm (T) (k) : |minmaxEig T k| ≤ ‖T‖
theorem minmaxEig_one (T) : minmaxEig T 1 = topEig T
theorem le_minmaxEig (T) (hk : 0 < k) (W) (hW : finrank 𝕜 W = k)
    (h : ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ re ⟪T x, x⟫) : c ≤ minmaxEig T k
theorem minmaxEig_le (T) (U) [FiniteDimensional 𝕜 U] [U.HasOrthogonalProjection]
    (hU : finrank 𝕜 U + 1 = k) (hc : 0 ≤ c) (h : ∀ x ∈ Uᗮ, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) :
    minmaxEig T k ≤ c
theorem minmaxEig_eq_of_bounds (T) (hk : 0 < k) (W U) [..] (hW) (hU) (hc) (hlo) (hhi) :
    minmaxEig T k = c
theorem exists_mem_orthogonal_of_finrank_lt [FiniteDimensional 𝕜 U] [U.HasOrthogonalProjection]
    (h : finrank 𝕜 U < finrank 𝕜 V) : ∃ x : E, x ∈ V ∧ x ∈ Uᗮ ∧ x ≠ 0
```

### Spectral package and interval kernels (ArchS5_Spectral)

```lean
theorem abs_topEig_intOp_sub_le [SFinite μ] (K K' : Lp 𝕜 2 (μ.prod μ)) :
    |topEig (intOp K) - topEig (intOp K')| ≤ ‖K - K'‖
theorem abs_minmaxEig_intOp_sub_le [SFinite μ] (K K') (k : ℕ) :
    |minmaxEig (intOp K) k - minmaxEig (intOp K') k| ≤ ‖K - K'‖
-- below: [IsFiniteMeasure μ]
theorem intOp_orthogonalComplement_iSup_eigenspaces_eq_bot (hK : IsHermitianKernel K) :
    (⨆ c, Module.End.eigenspace (intOp K : Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ) c)ᗮ = ⊥
theorem finiteDimensional_eigenspace_intOp (K) (hc : c ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace (intOp K : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ).toLinearMap c)
theorem exists_eigenvector_topEig_intOp (hK : IsHermitianKernel K) (hpos : 0 < topEig (intOp K)) :
    ∃ v : Lp 𝕜 2 μ, ‖v‖ = 1 ∧ intOp K v = (topEig (intOp K) : 𝕜) • v

abbrev volI (a b : ℝ) : Measure ℝ := volume.restrict (Icc a b)
def kernelOfContinuous (a b : ℝ) (k : ℝ × ℝ → 𝕜) (hk : Continuous k) :
    Lp 𝕜 2 ((volI a b).prod (volI a b))
theorem kernelOfContinuous_ae_eq (hk) : kernelOfContinuous a b k hk =ᵐ[(volI a b).prod (volI a b)] k
theorem intOp_kernelOfContinuous_ae_eq (hk) (f : Lp 𝕜 2 (volI a b)) :
    intOp (kernelOfContinuous a b k hk) f =ᵐ[volI a b] fun x ↦ ∫ y in Icc a b, k (x, y) * f y
theorem kernelOfContinuous_sub (hk) (hk') :
    kernelOfContinuous a b k hk - kernelOfContinuous a b k' hk' =
      kernelOfContinuous a b (k - k') (hk.sub hk')
theorem norm_kernelOfContinuous_le (hab : a ≤ b) (hk) (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖k (x, y)‖ ≤ C) : ‖kernelOfContinuous a b k hk‖ ≤ C * (b - a)
theorem abs_topEig_kernelOfContinuous_sub_le (hab) (hk) (hk') (hC0)
    (hC : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖k (x, y) - k' (x, y)‖ ≤ C) :
    |topEig (intOp (kernelOfContinuous a b k hk)) - topEig (intOp (kernelOfContinuous a b k' hk'))|
      ≤ C * (b - a)
theorem abs_minmaxEig_kernelOfContinuous_sub_le (hab) (hk) (hk') (hC0) (hC) (n : ℕ) : ... ≤ C * (b - a)
theorem isHermitianKernel_kernelOfContinuous (hk) (hsymm : ∀ x y, k (y, x) = starRingEnd 𝕜 (k (x, y))) :
    IsHermitianKernel (kernelOfContinuous a b k hk)
theorem intOp_kernelOfContinuous_compact_selfAdjoint (hk) (hsymm) :
    IsCompactOperator (intOp (kernelOfContinuous a b k hk)) ∧
      IsSelfAdjoint (intOp (kernelOfContinuous a b k hk))
```

## How the later stages consume this

* **S6 and bypass B2.** The prolate operator P₁FP₁ restricted to L²([-1, 1]) has the continuous
  kernel e^{2πixy}, or its even part. `kernelOfContinuous` with
  `intOp_kernelOfContinuous_compact_selfAdjoint` gives compact and self-adjoint. Then
  `intOp_orthogonalComplement_iSup_eigenspaces_eq_bot` gives the complete eigenbasis that B2 needs.
* **B3.** Taylor truncation of the kernel controls the spectrum through
  `abs_minmaxEig_kernelOfContinuous_sub_le`, which bounds the change by sup |k − T_n| · |I|.
  The Hilbert-Schmidt tail Σ_{k≥n} λ_k² ≤ ‖k − T_n‖²_{L²} is a different statement and is not here.
  See the open items.
* **S11 and bypass B4.** A Galerkin certificate for K_I uses three facts. Weyl gives
  `abs_topEig_sub_le` for the operator-norm tail. `topEig_le_of_forall'` turns a quadratic-form bound
  into λ_max ≤ c. `minmaxEig_le` with U the span of the computed top vector bounds λ₂ ≤ 0.78. For the
  overlap ⟨ζ|ξ₀⟩, `exists_eigenvector_topEig_intOp` supplies the true eigenvector.

## Open items (deliberately not done)

1. **Full Courant-Fischer identification.** It is not proved that, for compact self-adjoint T,
   `minmaxEig T k` equals the k-th largest positive eigenvalue counted with multiplicity. That needs an
   ordered enumeration of the spectrum, which Mathlib lacks. `le_minmaxEig` and `minmaxEig_le` give both
   directions whenever explicit eigenvectors or explicit complements are at hand, and that is what a
   certificate uses. Estimated cost: 300-500 lines on top of `orthogonalComplement_iSup_eigenspaces_eq_bot`.
2. **Hilbert-Schmidt identity.** It is not proved that Σ_n ‖T_K e_n‖² = ‖K‖²_{L²} for an orthonormal
   basis, nor that Σ λ_n² ≤ ‖K‖². B3's tail bound for the prolate series needs this second inequality.
   Route: Parseval on the sections K(x, ·), then monotone convergence. It needs a `HilbertBasis` of
   L²(ν), which exists via separability, and the island has `Lp.SecondCountableTopology`. Estimated
   cost: 250-400 lines.
3. **Compactness beyond finite measures.** `isCompactOperator_intOp` assumes `IsFiniteMeasure` on both
   factors. The σ-finite case follows by truncating K to E_n × F_n, using `norm_intOp_sub_le` and dominated
   convergence. This is not done because every planned use is on a bounded interval.
4. **Negative top of spectrum.** `exists_eigenvector_topEig` needs `0 < topEig T`, and this is sharp. For
   T = −diag(1/n) the supremum 0 is not attained. Apply the result to −T to get the bottom of the
   spectrum.

## Lean footguns met on this pin

* `eLpNorm_nnreal_eq_lintegral (p := 2)` does not fire on `eLpNorm g 2 μ`, because the `2` is an
  `ℝ≥0∞` literal. Use `eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top`.
  The helper `eLpNorm_two_sq` packages the squared form.
* `pow_le_pow_left₀` and `pow_le_pow_iff_left₀` fail on `ℝ≥0∞` with a missing `PosMulStrictMono`. Use
  `ENNReal.pow_le_pow_left` and `ENNReal.pow_le_pow_left_iff`.
* `zero_le` takes no explicit arguments at this pin, so `zero_le _` is an error.
* `isClosed_setOfPred_isCompactOperator.preimage continuous_intOp` fails to unify. The topology
  instances differ syntactically. State the closed set with an explicit type first, then call `.preimage`.
* `simpa [← Subtype.coe_ne_coe] using hx` hits maximum recursion. Use the terms
  `fun h ↦ hx (Subtype.ext h)` or `fun h ↦ hx (congrArg Subtype.val h)`.
* `convert h using 1` on an equality of coercions of continuous linear maps produces
  `(Lp 𝕜 2 ν).zero = ...` instance goals. Prove the function equality by `funext`, then `rw` and `exact`.
* The symmetric-difference notation `∆` needs `open scoped symmDiff`.
* `measure_diff` is deprecated. Use `measure_sdiff`. `orthogonalProjection` is deprecated. Use
  `Submodule.orthogonalProjectionOnto` and `orthogonalProjectionOnto_eq_zero_iff`.
* `LinearMap.mk₂` wants the scalar argument first, `∀ c m n, f m (c • n) = c • f m n`, in both smul
  fields.
* Each `lake env lean` on a single file takes about 45 s at load 6, mostly loading `import Mathlib`.
