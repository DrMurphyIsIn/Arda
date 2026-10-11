# Stage S7b notes: CC Lemma 4.1 / (75), the prolate series of δ (S7 obligation O2) (2026-10-11)

Branch `mm/arch-s7b` (S7 at 0f1ce9a6a merged with `mm/archimedean-rung`), island
`telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2).  Module `ArchS7b_Lemma41.lean`, guard `ArchS7b_Guard.lean`.
Source: Connes-Consani arXiv:2006.13771 ("CC"), §4, Lemma 4.1 (60), its L²(ℝ)_ev form (63), (75), (79), and (48)/(49).
`conjecture1_proved = False`.  Nothing here is RH progress.  No registry nodes touched.  No ArchS7_* file edited.

## 1. Statement (O2 exactly as S7 states it)

S7 (`ARCH_S7_NOTES.md` §4): O2 is `δS(t) = ArchS3.deltaK t` for `t ≥ 0`, where
`δS b T t = Σ' i, λ_i ⟪ξ_i, θ(-t) η_i⟫` is CC's (75) and `deltaK t = ccDelta (e^{|t|})` is CC's (48).

```lean
theorem ArchS7b.δS_eq_deltaK {ι} (bR : EigenBasis CopR ι) (T : Scaling evenPair) [Countable ι]
    (hT : IsPointwise T) {t : ℝ} (ht : 0 ≤ t) :
    ProlateBasis.δS (realProlateBasis bR) T t = ((deltaK t : ℝ) : ℂ)
theorem ArchS7b.δS_abs_eq_deltaK ... (x : ℝ) : ProlateBasis.δS (realProlateBasis bR) T |x| = deltaK x
```

Hypotheses: only `IsPointwise T` (already a hypothesis of `thm47_concrete`) and `Countable ι` (derived from σ there).
**No eigenvalue decay (B3, hτ) is used.**

## 2. Proof (CC's trace argument replaced by Parseval along the eigenbasis)

CC prove (60) by a trace manipulation and then expand with (79).  We bypass the trace: write ρ = e^t, C the
operator with kernel 2cos(2πvy) on L²([0,1]; ℝ) (S9's operator, S6 `CopR`), e_n its real eigenbasis, so
λ_n ξ_n^an = C e_n (S6 `phiR`).

1. **Term** (`term_eq`).  With S7's representatives `xi_ae` (ξ_n = ξ_n^an(|v|)/√2 on [−1,1]) and S6's
   `fourier_ξ_ae_real` (η_n = Fξ_n = λ_n ξ_n^an/√2 on ℝ), `inner_dil` and evenness of ξ_n^an:
   λ_n⟨ξ_n|ϑ(ρ⁻¹)η_n⟩ = λ_n² ρ^{1/2} ∫₀¹ ξ_n^an(v) ξ_n^an(ρv) dv = ρ^{1/2} ∫₀¹ (Ce_n)(v)(Ce_n)(ρv) dv.
2. **Parseval** (`hasSum_cosTransR_mul`).  (Ce_n)(w) = ⟪k_w, e_n⟫ with k_w(y) = 2cos(2πwy) ∈ L²[0,1] (`kRow`),
   so Σ_n (Ce_n)(v)(Ce_n)(w) = ⟪k_v, k_w⟫ = ∫₀¹ 2cos(2πvy)2cos(2πwy) dy (completeness of e_n).
3. **Termwise integration** (`tsum_integral_cosTransR`).  |ab| ≤ (a²+b²)/2 and Bessel give
   Σ_n |(Ce_n)(v)(Ce_n)(ρv)| ≤ (‖k_v‖² + ‖k_ρv‖²)/2 ≤ 4 pointwise; Tonelli (`lintegral_tsum`) then
   `integral_tsum`.
4. **Closed form** (`deltaK_eq_double`).  4cos A cos B = 2(cos(A+B) + cos(B−A)) and ∫₀¹cos(cy)dy = sinc c give
   ∫₀¹∫₀¹ 2cos(2πvy)2cos(2πρvy) = 2(sincInt(2π(ρ+1)) + sincInt(2π(ρ−1))), which is S3's `deltaK` (CC (49)).

So δS(t) = e^{t/2}∫₀¹∫₀¹ 4cos(2πvy)cos(2πe^t vy) dy dv = deltaK t.  (The −log t of (48) is the Fubini shadow of
this double integral; we never need it, since S3 already proved (48) ⇔ (49).)

Normalisation check: the statement needed **no change of normalisation**.  S6's full-line L²(ℝ) with ξ = ξ^an/√2
and CC's (16) give the same matrix coefficients (S7 §2), and the factor 2 from evenness cancels the two 1/√2.

## 3. Numerical check (before formalising)

`telperion/research/arch_rung/s7b_o2check.py` [N-here, float64, NOT certified]: Nyström discretisation of C
(120 Gauss-Legendre nodes), eigenvalues 0.9999714, −0.9794847, 0.5240859, −0.0589766, ... agree with S9's certified
θ_0..θ_3 (ARCH_S9_NOTES).  Σ_n λ_n² e^{t/2}∫₀¹φ_n(v)φ_n(e^t v)dv against deltaK t (mpmath sincInt):

| t | series (75) | deltaK t |
|---|---|---|
| 0 | 2.237484834941829 | 2.2374848349418275 |
| 0.3 | 2.036086258431641 | 2.036086258431639 |
| 1 | 0.710872128362979 | 0.7108721283629807 |
| 2 | 0.37874818481214356 | 0.3787481848121471 |

## 4. How it plugs into `thm47_concrete`

`integral_δS_eq_Dfun`: Re ∫ autocorr g · δS(|x|) = `ArchS3.Dfun g`.  Hence

```lean
theorem ArchS7b.thm47_concrete_O1 ... (same hypotheses as ArchS7.thm47_concrete except h85)
    (h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (V (e k)))‖ ^ 2) (archW g + Dfun g)) :
    HasSum (fun k ↦ ‖soninProj (V (e k))‖ ^ 2) (archW g + (D.Eplus (autocorr g)).re)
theorem ArchS7b.thm47_concrete_O1_nonneg ... : 0 ≤ archW g + (D.Eplus (autocorr g)).re
```

`h85` is now exactly O1 in S3's own terms (CC (85): ‖P̂Pϑ(g)‖²_HS = W∞ + D with D = S3's `Dfun`).
Remaining obligations of Thm 4.7: O1, O3, O4 (S7 §4).  O2 is closed.

## 5. Results

`lake build ArchS7b_Lemma41` (8796 jobs, ~47 s for the module) and `lake env lean ArchS7b_Guard.lean`:
26 theorems, every one `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no `axiom`.
Files: `ArchS7b_Lemma41.lean` (≈350 lines), `ArchS7b_Guard.lean`.  Lakefile: two stanzas at the end.

## 6. Lean footguns

* `(hc : Continuous f).intervalIntegrable` is `∀ a b, …`: apply it to `0 1` before `integral_add`.
* After `unfold dil`, the representative `(fun w ↦ …) (e^t v)` stays un-beta-reduced; `beta_reduce` before `rw`.
* `volI` lives in `ArchS5`: `open ArchS5`.
* `Real.enorm_eq_ofReal_abs` + `ENNReal.ofReal_tsum_of_nonneg` turn a real tsum bound into the `integral_tsum`
  side condition.
* `prolateBasisOf_lam_ne_zero (complexify bR) i` gives `bR.μ i ≠ 0` (defeq), needed for μ·phiR = C e.
