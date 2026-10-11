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

### M3 (planned): specialisation

W = `ArchS3.archW g` (W∞(g∗g*) in the island's conventions, = Re weilForm on the pole-free window),
f = `WeilExplicit.autocorr g`, εS|x| = `D.eps |x|` via M1, so ∫ f εS|x| = `D.Eplus (autocorr g)`.

## 4. Interface obligations (hypotheses of S7's theorems, not proved here)

* **O1 (S3 M2, CC (85)).**  ‖P̂ P ϑ(g)‖²_HS = archW g + D(g∗g*).  S3 stopped before M2.
* **O2 (Lemma 4.1 + (79), CC (75)).**  The kernel of D is the prolate series:
  δ(e^t) = Σ λ_n ⟨ξ_n|ϑ(e^{-t})η_n⟩ for t ≥ 0, where δ(e^{|u|}) = `ArchS3.deltaK u`.
  (79) is S6's; the trace identity (63) is not in Lean.
* **O3 (S6).**  The concrete scaling θ on `evenL2` with the `Scaling` fields, ϑ(g) as an operator and the
  coefficient formula `hcoef`.
* **O4 (S6).**  The concrete `ProlateBasis evenPair ℕ`, with ξ_n =ᵐ `xiRep (phi n)` and
  ζ_n =ᵐ `zetaRep τ_n (phi n)` for S8's `ProlateData` phi, and Σ|τ_n| < ∞ (B3).
