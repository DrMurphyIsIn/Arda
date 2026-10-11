# Stage S7 notes: CC Thm 4.7, SoninTr = W∞ + E (2026-10-11)

Branch `mm/arch-s7`, island `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2).
Base: S6 at 6c42817ec merged with `mm/archimedean-rung` (S1-S5, S8).
Plan: `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`, section 1 row 10 and section 4 row S7.
Source: Connes-Consani arXiv:2006.13771 ("CC"), §4, Lemma 4.1, Prop 4.5, Thm 4.7 and its proof (85)-(90),
read from the PDF text.
`conjecture1_proved = False`.  Nothing here is RH progress.  No registry nodes were touched.

## 1. CC's proof of Thm 4.7, as a chain

CC prove (83), Tr(ϑ(f)S) = W∞(f) + ∫ f(ρ⁻¹)ε(ρ)d*ρ, from four inputs.

1. **(85)**, the local trace formula (43) of §2: W∞(f) + D(f) = Tr(ϑ(f) P P̂ P), with D(f) = ∫ f(ρ⁻¹)δ(ρ)d*ρ.
   This is CC Prop 2.2(iii) / Cor 2.3, i.e. S3's milestone M2, which S3 stopped (not in Lean).
2. **Lemma 4.1 / (63) / (75)**: δ(ρ) = Tr(ϑ(ρ⁻¹)P̂₁P₁) = Σ λ(n)⟨ξ_n|ϑ(ρ⁻¹)η_n⟩ for ρ ≥ 1, where δ is (48).
   The second equality is (79) (S6 `hasSum_hatP₁_P₁`).  The first is a trace computation.
3. **(77) and (82)**: Prop 4.5(iv) (S6 `inner_ξ_A_ξ`) and the support fact ⟨ζ_n|ϑ(ρ⁻¹)ξ_n⟩ = 0 for ρ ≥ 1.
   With CC's footnote λ√(1−λ²) + λ²τ = τ these give (89): δ(ρ) = Σ λ²⟨ζ_n|ϑ(ρ⁻¹)ζ_n⟩ + ε(ρ).
4. **(90)** from the spectral decomposition (81) (S6 `hasSum_PhatPP`, `hasSum_inner_PhatPP`):
   Tr(ϑ(f) P P̂ P) = Tr(ϑ(f) S) + Σ λ²⟨ζ_n|ϑ(f)ζ_n⟩.

## 2. Bypass B1: every trace is a Hilbert-Schmidt sum

For f = g∗g* one has ϑ(f) = V V† with V = ϑ(g).  So
* Tr(ϑ(f) S) = ‖S V‖²_HS = Σ_i ‖S V e_i‖² for any Hilbert basis (e_i) of L²(ℝ)_ev;
* Tr(ϑ(f) P P̂ P) = ‖P̂ P V‖²_HS = Σ_i ‖P̂ P V e_i‖²;
* ⟨ζ|ϑ(f)ζ⟩ = ‖V† ζ‖².

No trace class is used.  The HS sums are taken in `ℝ≥0∞`, so no summability is assumed for (90).
Basis independence is `tsum_norm_sq_swap` (Σ_i ‖V e_i‖² = Σ_j ‖V† f_j‖² for any two Hilbert bases).

Normalisation.  S6 uses L²(ℝ) with the full-line inner product, CC use ∫₀^∞ (16).  Every quantity in (84)
is a matrix coefficient between unit vectors, so it is the same in both conventions, provided
ξ_n = phi_n(|v|)/√2 on [−1, 1], where phi_n = ξ_n^an is S8's function, normalised by ∫₀¹ phi_n² = 1.

## 3. Statements

### M1 (done): CC (84) termwise = S8 (`ArchS7_Term.lean`)  -- closes S8 open item 1

```lean
def xiRep (phi : ℝ → ℝ) (v : ℝ) : ℂ := if |v| ≤ 1 then ((phi |v| / √2 : ℝ) : ℂ) else 0
def zetaRep (c : ℝ) (phi : ℝ → ℝ) (v : ℝ) : ℂ := if 1 ≤ |v| then ((c * phi |v| / √2 : ℝ) : ℂ) else 0
def dil (t : ℝ) (z : ℝ → ℂ) (v : ℝ) : ℂ := (exp (t/2) : ℂ) * z (exp t * v)      -- ϑ(e^{-t}) pointwise

theorem integral_coeff (phi) (c) (ht : 0 ≤ t) :
    ∫ v, conj (xiRep phi v) * dil t (zetaRep c phi) v = (kM phi (fun x => c * phi x) t : ℂ)
theorem cc84_coeff (D : ProlateData) (n) (ht : 0 ≤ t) :
    (τ_n : ℂ) * ∫ v, conj (xiRep (D.phi n) v) * dil t (zetaRep τ_n (D.phi n)) v = ((D.w n * D.kn n t : ℝ) : ℂ)
theorem eps_eq_tsum (D) (ht : 0 ≤ t) :
    ((D.eps t : ℝ) : ℂ) = ∑' n, (τ_n : ℂ) * ∫ v, conj (xiRep (D.phi n) v) * dil t (zetaRep τ_n (D.phi n)) v
theorem eps_abs_eq_tsum (D) (v) : the same at t = |v|      -- the form Eplus uses
```
Here τ_n = `D.lam n / √(1 − D.lam n ^ 2)`.  `zetaRep` is CC's ζ_n: it vanishes on (−1, 1) because
ζ_n = ψ_n/√(1−λ²) and ψ_n = P η_n, and on |v| ≥ 1 it is η_n/√(1−λ²) = τ_n phi_n/√2 because
phi_n = λ_n⁻¹ F ξ_n there (S8 note, item 2).  No hypothesis on phi is needed: the integrand is
exactly the indicator of {e^{−t} ≤ |v| ≤ 1} times an even function, for every v.

So **S8 open item 1 is reduced to an identification of representatives**: once S6's concrete ξ_n and ζ_n
are a.e. equal to `xiRep (phi n)` and `zetaRep τ_n (phi n)`, CC's ε of Thm 4.7 is `D.eps` and
E(f) = ∫ f(ρ⁻¹)ε(ρ)d*ρ is `D.Eplus f` (t = log ρ, ε(ρ⁻¹) = ε(ρ)).

### M2 (done): Thm 4.7 abstract (`ArchS7_HS.lean`, `ArchS7_Abstract.lean`)

Over S6's abstract `ProjPair S` and `ProlateBasis S ι` (`[Countable ι]`), with:

```lean
structure Scaling (S : ProjPair H) where          -- θ t = ϑ(e^t)
  θ : ℝ → H →L[ℂ] H
  norm_θ : ∀ t x, ‖θ t x‖ = ‖x‖
  F_θ_F : ∀ t x, S.F (θ t (S.F x)) = θ (-t) x      -- ϑ(ρ) = F⁻¹ ϑ(ρ⁻¹) F
  P₁_θ : ∀ t, 0 ≤ t → ∀ x, S.P₁ x = x → S.P₁ (θ (-t) x) = θ (-t) x   -- ϑ(ρ⁻¹) shrinks supports
  cont : ∀ x y, Continuous fun t => ⟪x, θ t y⟫
def δS t := ∑' n, (λ n : ℂ) * ⟪ξ n, θ (-t) (η n)⟫      -- CC (75)
def εS t := ∑' n, (τ n : ℂ) * ⟪ξ n, θ (-t) (ζ n)⟫      -- CC (84)
```

Hypotheses of the theorem:
* `hreal : ∀ n t, ⟪ξ n, θ t (ξ n)⟫ = ⟪ξ n, θ (-t) (ξ n)⟫` (ξ_n real valued);
* `hτ : Summable fun n => |τ n|` (B3 decay of λ_n);
* `V : H →L[ℂ] H` (ϑ(g)), `f : ℝ → ℂ` integrable (g∗g*), and the coefficient formula
  `hcoef : ∀ v, ((‖V† v‖ ^ 2 : ℝ) : ℂ) = ∫ x, f x * ⟪v, θ x v⟫`;
* `h85 : HasSum (fun i => ‖S.hatP (S.P (V (e i)))‖ ^ 2) (W + (∫ x, f x * δS |x|).re)` (CC (85)).

Conclusion: `HasSum (fun i => ‖soninProj (V (e i))‖ ^ 2) (W + (∫ x, f x * εS |x|).re)`, i.e.
Tr(ϑ(f)S) = W∞(f) + E(f), for every Hilbert basis e.

Proved (namespace `ArchS7` / `ArchS7.ProlateBasis`), all with exactly the standard axioms:

| theorem | content |
|---|---|
| `hasSum_norm_inner_sq`, `tsum_ofReal_norm_inner_sq` | Parseval for a Hilbert basis |
| `tsum_norm_sq_swap`, `hsSq_indep`, `hsSq_adjoint` | Σ‖V e_i‖² = Σ‖V† f_j‖²; HS norm basis independent |
| `hasSum_norm_hatP_P`, `ofReal_norm_hatP_P` | ‖P̂Px‖² = Σλ²\|⟨ζ_n,x⟩\|² + ‖Sx‖² (S6's (81)/(76)) |
| `tsum_PhatPP` | **CC (90)**: ‖P̂PV‖²_HS = ‖SV‖²_HS + Σ λ²‖V†ζ_n‖², in ℝ≥0∞, no hypotheses |
| `inner_ζ_θ_ξ` | **CC (82)** |
| `τ_eq` | CC footnote 8, τ = λ√(1−λ²) + λ²τ |
| `delta_term` | **CC (86)-(89) termwise** (uses S6 `inner_ξ_A_ξ` = (77)) |
| `inner_ψ_θ_ψ`, `inner_ξ_θ_η`, `inner_η_θ_ξ`, `cζ_neg` | ⟨ζ|ϑ(ρ)ζ⟩ = ⟨ζ|ϑ(ρ⁻¹)ζ⟩ from F ϑ F = ϑ⁻¹ and reality of ξ_n |
| `δS_eq`, `δS_abs_eq` | **CC (89)** as series, and its even form |
| `summable_lam_sq`, `summable_ε_terms`, `continuous_εS`, `norm_εS_le` | convergence from Σ\|τ_n\| < ∞ |
| `integral_δS` | integrated (89): ∫fδ = Σλ²‖V†ζ_n‖² + ∫fε (dominated termwise integration) |
| `thm47` | **CC Thm 4.7** (HS form) |
| `thm47_nonneg` | **CC (83)**: W + Re∫fε ≥ 0 |

Remarks.
* `Scaling` has no group law and no adjoint field: only isometry, F θ(t) F = θ(−t), the support property and
  weak continuity are used.
* `hcoef` encodes ϑ(f) = ϑ(g)ϑ(g)† and ⟨v|ϑ(f)v⟩ = ∫ f(x)⟨v|ϑ(e^x)v⟩dx.  It is the only place where
  integration over the group enters.
* Summability Σ|τ_n| < ∞ implies Σλ_n² < ∞ (`lam_sq_le_abs_τ`), so a single B3-type hypothesis suffices.

### M3 (done, modulo O1-O4): specialisation to S6's concrete basis (`ArchS7_Concrete.lean`)

Merged S6 through b765d5bbd (concrete `realProlateBasis bR`, `phiR`, `fourier_ξ_ae_real`).

| theorem | content |
|---|---|
| `ae_ne_real`, `ae_comp_mul` | null points; a.e. equality survives v ↦ cv |
| `cosTransR_neg`, `phiR_neg`, `phiR_abs`, `c2_eq` | phiR is even |
| `xi_ae` | S6's ξ_n =ᵐ `xiRep (phiR bR n)` |
| `zeta_ae` | CC's ζ_n =ᵐ `zetaRep τ_n (phiR bR n)` (from ζ = s⁻¹(Fξ − P₁Fξ) and S6's Fξ = c2·λ·phiR) |
| `inner_evenL2`, `inner_dil` | for a pointwise scaling, ⟨a|ϑ(e^{-t})b⟩ = ∫ conj A · dil t B |
| `εS_term`, `εS_eq_eps`, `integral_εS_eq_Eplus` | **CC's ε = S8's `D.eps`; E(f) = `D.Eplus f`** (S8 open item 1 closed for the concrete basis) |
| `xiRep_conj`, `hreal_of_pointwise` | the reality hypothesis `hreal`, by the substitution v = e^t w |
| `thm47_concrete` | **CC Thm 4.7**: ‖S ϑ(g)‖²_HS = `ArchS3.archW g` + Re `D.Eplus (autocorr g)` |
| `thm47_concrete_nonneg` | **CC (83)**: archW g + Re D.Eplus(autocorr g) ≥ 0 |

```lean
def IsPointwise (T : Scaling evenPair) : Prop :=
  ∀ t (f : evenL2), (T.θ t f : ℝ → ℂ) =ᵐ fun v ↦ (exp (-t/2) : ℂ) * (f : ℝ → ℂ) (exp (-t) * v)

theorem thm47_concrete {ι} (bR : EigenBasis CopR ι) (T : Scaling evenPair) (hT : IsPointwise T)
    (D : ProlateData) (σ : ℕ ≃ ι) (hDlam : ∀ n, D.lam n = bR.μ (σ n))
    (hDphi : ∀ n, D.phi n = phiR bR (σ n)) (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|)
    (g : ℝ → ℂ) (hf : Integrable (autocorr g)) (V : evenL2 →L[ℂ] evenL2)
    (hcoef : ∀ v, ((‖V† v‖ ^ 2 : ℝ) : ℂ) = ∫ x, autocorr g x * ⟪v, T.θ x v⟫)
    (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖P̂ (P (V (e k)))‖ ^ 2) (archW g + (∫ x, autocorr g x * δS b T |x|).re)) :
    HasSum (fun k ↦ ‖soninProj (V (e k))‖ ^ 2) (archW g + (D.Eplus (autocorr g)).re)
```

### O3 discharged: the concrete ϑ and ϑ(g) (`ArchS7_Dilation.lean`, `ArchS7_Theta.lean`)

| theorem / def | content |
|---|---|
| `thF`, `thL t : L²(ℝ) →ₗᵢ L²(ℝ)`, `coeFn_thL` | (θ t f)(v) = e^{−t/2} f(e^{−t}v), CC (61) with λ = e^t; isometry by `integral_comp_mul_left` |
| `thL_add`, `thL_zero`, `thL_neg_thL`, `inner_thL_left` | group law; θ(t)† = θ(−t) |
| `reflect_thL`, `thL_mem_evenL2` | θ preserves L²(ℝ)_ev |
| `P1_thL_neg` | CC (82): θ(−t) maps ran P₁ into itself for t ≥ 0 |
| `fourier_thF`, `fourier_thL`, `fourier_thL_fourier` | 𝓕 θ(t) = θ(−t) 𝓕 on L²(ℝ) (pointwise on L¹ ∩ L², then S6's density lemma); F θ(t) F = θ(−t) on evens |
| `norm_sq_eq_integral`, `continuous_thL_of_compact`, `continuous_thL` | strong continuity: dominated convergence on C_c, then uniform approximation |
| `thE`, `scalingEven`, `isPointwise_scalingEven` | **the `Scaling evenPair` exists and acts pointwise** |
| `thm47_even` | `thm47_concrete` with T = `scalingEven` |
| `theta g hg` (`= ∫ g(x) θ(x) dx`, Bochner), `adjoint_theta`, `inner_adjoint_theta` | ϑ(g) on L²(ℝ)_ev, ‖ϑ(g)‖ ≤ ‖g‖₁, ϑ(g)† w = ∫ conj g(x) θ(−x) w |
| `hcoef_theta` | **the coefficient formula**: ‖ϑ(g)† w‖² = ∫ autocorr g (u) ⟨w, θ(u) w⟩ du (Fubini + translation) |
| `thm47_theta`, `thm47_theta_nonneg` | Thm 4.7 and (83) with the concrete ϑ(g), g continuous and integrable |
| `thm47_weil` | Thm 4.7 for `IsWeilTest g` |

```lean
theorem thm47_weil {ι} (bR : EigenBasis CopR ι) (D : ProlateData) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hτ : Summable fun i ↦ |(realProlateBasis bR).τ i|) {g} (hW : IsWeilTest g) (e : HilbertBasis κ ℂ evenL2)
    (h85 : HasSum (fun k ↦ ‖P̂ (P (theta g _ (e k)))‖ ^ 2)
      (archW g + (∫ x, autocorr g x * δS (realProlateBasis bR) scalingEven |x|).re)) :
    HasSum (fun k ↦ ‖soninProj (theta g _ (e k))‖ ^ 2) (archW g + (D.Eplus (autocorr g)).re)
```

Totals: 7 files, about 1610 lines, 103 guarded theorems, all `[propext, Classical.choice, Quot.sound]`.

### O2 discharged: CC Lemma 4.1 + (75) without trace class (`ArchS7_Lemma41.lean`)

| theorem | content |
|---|---|
| `integral_cos_mul`, `integral_square_cos` | ∫₀¹cos(ay) = sinc a; ∫₀¹∫₀¹ cos(cxy) = S3's `sincInt c` |
| `hasSum_inner_intOp` | Σ_i ⟨T_{K₁} b_i, T_{K₂} b_i⟩ = ⟨K₁, K₂⟩ for a Hilbert basis (polarised S5 `hasSum_norm_intOp_sq`) |
| `ktK`, `K0`, `Kt`, `coeFn_intOp_Kt` | C_t has kernel e^{t/2}·2cos(2πe^t xy) on [0,1]²; C = S9's/S6's `Cop` |
| `hbOf`, `inner_reflect_left`, `inner_J_even` | Hilbert basis from S6's complete eigenbasis; ⟨J e, X⟩ = √2⟨e, X|_{[0,1]}⟩ for even X |
| `term_eq` | λ_n⟨ξ_n|ϑ(e^{-t})η_n⟩ = ⟨C e_n, C_t e_n⟩ |
| `conj_cosK_mul_ktK`, `integral_kprod`, `inner_K0_Kt` | ⟨K, K_t⟩ = ∫∫ 4e^{t/2}cos(2πxy)cos(2πe^t xy) = `ArchS3.deltaK t` (t ≥ 0) |
| `hasSum_δS`, `δS_eq_deltaK`, `δS_abs_eq_deltaK` | **CC (75) = CC (48)/(49)**: Σ λ_n⟨ξ_n|ϑ(e^{-t})η_n⟩ = deltaK t, i.e. δ(ρ) = Tr(ϑ(ρ⁻¹)P̂₁P₁) in HS form |
| `thm47_weil'`, `thm47_weil'_nonneg` | Thm 4.7 and (83) with `h85` in S3's own terms: ‖P̂ P ϑ(g)‖²_HS = `archW g + Dfun g` |

The −log t of CC (48) never appears: ∫∫_{[0,1]²}cos(cxy) is integrated in y first, giving sinc, which is
S3's (49) form directly.

Totals: 8 files, about 1960 lines, 121 guarded theorems, all `[propext, Classical.choice, Quot.sound]`.

## 4. Interface obligations still open (hypotheses of `thm47_weil'`)

* **O1 (S3 M2, CC (85) = Prop 2.2(iii)/Cor 2.3).**  `h85 : HasSum (k ↦ ‖P̂ (P (ϑ(g) e_k))‖²) (archW g + Dfun g)`,
  i.e. Tr(ϑ(g∗g*) P P̂ P) = W∞ + D.  This is exactly the identity S3 stopped on (Mellin transform of cos on
  the critical line, oscillatory limits).  Everything else in Thm 4.7 is now kernel-checked.
* **O4 (S6/S8/S9 data).**
  * an enumeration σ : ℕ ≃ ι of S6's eigenbasis (ι is countable because L²[0,1] is separable and the
    eigenvalues are nonzero; not proved here);
  * a `ProlateData D` with `D.lam = μ ∘ σ`, `D.phi = phiR ∘ σ` (S8's obligation 5: the sup bounds M_n);
  * Σ|τ_n| < ∞ (B3 decay; S5's `card_le_of_eigen_gt_tensor` gives the per-index bound).
* **O2 and O3 are closed.**

## 5. Lean footguns

* Dot notation `b.foo` for a lemma `ArchS7.ProlateBasis.foo` about `b : ArchS6.ProlateBasis S ι` fails:
  the projection looks in `ArchS6.ProlateBasis`.  Call `foo b` inside `namespace ArchS7.ProlateBasis`.
* `RCLike.inner_apply` is `⟪x, y⟫ = y * conj x` at this pin; `RCLike.inner_apply'` is `conj x * y`.
* `ENNReal.top_add` does not exist; use the root `top_add`.
* `integral_comp_mul_left` lives in `MeasureTheory.Measure`.
* On `↥evenL2` (a `Submodule` of `Lp`), `rw [inner_smul_right]`, `rw [inner_conj_symm]` and
  `rw [inner_self_eq_norm_sq_to_K]` fail to find the pattern (instance path mismatch), and `simp only` makes no
  progress; the term-mode lemma works.  Fix: restate them for `evenL2` (`inner_smul_right_E`, `inner_conj_symm_E`,
  `inner_self_E`) and rewrite with those.
* `integral_add_right_eq_self` needs `(μ := volume)` explicitly, otherwise `IsAddRightInvariant ?m` is stuck.
* `first | ring | tac` on a function-equality goal: `ring` "succeeds" via `ring_nf` fallback without closing it;
  put the other alternative first.
* After `rw [h] at e` with `e : ofReal (∑' a) = ∑' ofReal a`, `e` is already oriented `ofReal (∑' a) = ofReal c`.
* Lake: the S6 merge conflicted only in `lakefile.toml` (both stages append stanzas); resolve as the union and
  keep the S7 stanzas last.
