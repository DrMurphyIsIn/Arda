# Stage S10 notes: the certified kernel χ on [0, log 2] (2026-10-11)

Branch `mm/arch-s10` (from `mm/archimedean-rung` a30da7cb9), island `telperion/examples/rvm_bridge/lean`.
Plan: `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`, section 4 row S10 and bypass B5.
`conjecture1_proved = False`.  Nothing here is RH progress.  No registry nodes were touched.

## 1. What is certified

Every theorem below is kernel-checked.  `lake env lean ArchS10_Guard.lean` prints exactly
`[propext, Classical.choice, Quot.sound]` for 113 declarations.  The 114th, `NH_eq`, depends on no axioms.
There is no `sorry` and no `axiom`.

The input is S8's abstract `D : ArchS8.ProlateData` plus one hypothesis bundle, `ArchS10.CertBasis D`:

```lean
structure CertBasis (D : ArchS8.ProlateData) : Prop where
  eig : ∀ n ω, T (D.phi n) ω = D.lam n * D.phi n ω            -- S9's T, on all of ℝ
  orth : ∀ n m, ip (D.phi n) (D.phi m) = if n = m then 1 else 0   -- orthonormal on [0,1]
  window : ∀ n ≤ Data.NCw, |D.lam n - thR n| ≤ (Data.w0q n : ℝ)  -- n ≤ 12 in S9's windows
  T_gt : Real.log 2 < D.T
```

No bound on the eigenfunctions of index n > 12 is assumed.  Their eigenvalues are at most d0Q ≈ 9.70e-22 (`CertBasis.tail_small`).  This follows from S9's localization, S9's simplicity, and orthogonality to the 13 window functions.

| theorem | statement | constant |
|---|---|---|
| `eps1_enclosure` | \|ε'(1⁺) − EQ\| ≤ deltaE | EQ = 22.99647568387053…, deltaE = 1.19e-22 |
| `eps1_pos`, `eps1_ne_zero` | ε'(1⁺) > 0, the hypothesis of S8's `prop55_KI` | |
| `Qeps_expsum` | \|(Qε)(e^t) − Σ_{l<40} d_l (e^{(2l+½)t} − e^{−(2l+½)t})\| ≤ dQtot on t ∈ [0, log 2] | dQtot = 6.45e-6 |
| `Qeps_poly` | \|(Qε)(e^t) − P(t)\| ≤ dQtot + deltaP | deltaP = 1.87e-8 |
| **`chi_enclosure`** | **\|χ(v) − chiPoly v\| ≤ deltaChi for \|v\| ≤ log 2** | **deltaChi = 1.41e-7** |
| `chi_L1` | ∫_0^{log 2} \|χ − chiPoly\| ≤ deltaChi · log 2 | about 9.8e-8 |
| `chi_neg` | χ(−v) = χ(v) | |
| `chiPoly_zero`, `chi_zero_consistent` | chiPoly 0 = 0 = χ(0), CC Rem 5.6 | |

* χ is S8's `D.chi v = D.Qeps |v| / (2 * D.eps1 0)`, the kernel of K_I (CC (104)).
* `chiPoly v = Σ_{i<67} chiCo i · |v|^i`.  The `ArchS10.Data.chiCo i` are explicit rationals equal to pco i/(2·EQ).
* Only the 33 odd coefficients are nonzero, and the top degree is 65.

**Against the targets.**
* χ is certified to 1.4e-7 sup and 1e-7 L¹ on [0, log 2].  The blueprint target was 1e-5 L¹.
* ε'(1⁺) is certified to 1.2e-22.  The target was an interval around 22.9965, to about 1e-6.
* The certified polynomial gives χ ∈ [−1.69625, 3.3290] on [0, log 2] (minimum at v ≈ 0.473, maximum at v ≈ 0.171).  This matches CC Fig. 10 and the blueprint's [−1.70, 3.33].
* Sample values:

  | v | 0.1 | 0.2 | 0.3 | 0.4 | 0.5 | log 2 |
  |---|---|---|---|---|---|---|
  | χ(v) | 2.65790 | 3.20792 | 1.35314 | −1.03041 | −1.60223 | 0.92722 |

* ∫_0^{log 2} \|χ\| ≈ 1.0616 [N-here, not certified].

## 2. How

### 2.1 The head collapses to a finite sinh series (`ArchS10_Exact.CC_psi`)

* `CC f f' t` is CC (99) with an arbitrary pair (f, f') in place of (ξ_n^an, ξ_n^an').
  So `D.Cn n t = CC (D.phi n) (deriv (D.phi n)) t` holds by `rfl`.
* CC is quadratic, so `w_n C_n = C(Tφ_n, Tdφ_n)/(1 − λ_n²)` (`CertBasis.wC_eq`).  Here λφ = Tφ, and λφ' = Tdφ holds even when λ = 0.
* For an even polynomial ψ = Σ_k B_k x^{2k}, which is S9's `psi J B n`:

      C(ψ, ψ')(e^t) = Σ_l hh_l (e^{(2l+½)t} − e^{−(2l+½)t}),
      hh_l = Σ_k 4kl B_k B_l/(2k+2l+1) − ψ(1)·2l·B_l.

  * The polynomial integral ∫_{e^{-t}}^1 x^{2k+2l} gives one term at the upper limit and one at the lower limit.
  * After a k ↔ l swap, the lower-limit half and the upper-limit half combine with CC's two boundary terms of (99).
  * Only 39 exponentials e^{±(2l+½)t} survive, and the sum is odd in t, which is CC Rem 5.6.
* With S9's ψ_n and θ_n (n ≤ 12), the head of Qε is Σ_l d_l (e^{(2l+½)t} − e^{−(2l+½)t}).
  * The coefficients are d_l = Σ_{n≤12} θ_n²/(1−θ_n²)·hh_{n,l}.  They are exact in the kernel (integers over DB²·Lc, like S9's Gram check) and rounded to 1e-60.
  * The coefficients alternate and reach |d_l|·2^{2l+½} ≈ 8.6e6 at l = 5.  So the sum cancels by about 1e7, which is harmless in exact rationals.
* The replacement λφ → ±θψ uses S9's `prolate_window`: \|λφ − sθψ\| ≤ Vq and \|λφ' − sθψ'\| ≤ Vdq on [0, 2].
  * `abs_CC_sub_le` shows that C(·)(e^t) for t ∈ [0, log 2] only evaluates its arguments on [1/2, 2].
  * `div_perturb` handles 1/(1 − λ²) against 1/(1 − θ²).
  * The total head error is 3.3e-20 per term.

### 2.2 The tail n > 12, unconditionally (`ArchS10_Tail`)

* Through S9's rank-40 frame, for any continuous f and every ω:
  * T f(ω) = Σ_m θ_m ⟨f, ψ_m⟩ψ_m(ω) + ⟨f, E_ω⟩, where E_ω(x) = K(ω, x) − Σ_m θ_m ψ_m(ω)ψ_m(x) (`errF_eq_ip`).
  * ‖E_ω‖² = errF(E_ω)(ω) ≤ ζ‖E_ω‖₁ ≤ ζ‖E_ω‖, so ‖E_ω‖ ≤ ζ (`ip_le_sq_of`).  ζ comes from S9's `errF_le_one/two`.
* For a tail eigenfunction e and m ≤ 12, (λ − θ_m)⟨e, ψ_m⟩ = ⟨e, Tψ_m − θ_mψ_m⟩ (`ip_res_eig`).
  * This uses symmetry of T and S9's residual ‖Tψ_m − θ_mψ_m‖ ≤ rhoQ = 6.7e-43.
  * The gap |λ − θ_m| ≥ |θ_m| − d0Q > 0 then makes the coefficient small.
* So λ_k e_k(ω) is a sum of 41 pieces, each a fixed vector paired with e_k.
  * A weighted Cauchy–Schwarz (Titu/Sedrakyan, weights ≈ √(piece bound)) bounds the square of the sum.
  * Bessel's inequality for each fixed vector bounds the sum over k:

  | quantity (finite S of tail indices) | bound | constant |
  |---|---|---|
  | Σ_{k∈S} (λ_k e_k(ω))², ω ∈ [0, 2] | AQ | 5.8e-9 |
  | Σ_{k∈S} (λ_k e_k'(ω))², ω ∈ [0, 2] | AdQ | 9.9e-7 |
  | Σ_{k∈S} (λ_k e_k(ω))², ω ∈ [0, 1] | A1Q | 1.2e-22 |

* The m = 13 piece dominates, with \|θ_13\|·sup\|ψ_13\| ≈ 7e-5 from the crude coefficient-sum bound.
* AM-GM on the products in C(·), and swapping the finite sum with the integral, then give:
  * `tail_CC_sum_le`: Σ_{k∈S} \|w C\| ≤ tauQ = 6.44e-6;
  * `tail_eps_sum_le`: Σ_{k∈S} w e_k(1)² ≤ tauE = 1.2e-22.
* The tail is what limits χ to 1.4e-7.  See open item 2 for how to improve it.
* **This does NOT use S8's open item 5 (a sup bound M_n beating 1/|λ_n|).**  The numerical tail needs only orthonormality and the eigen-relation.

### 2.3 The polynomial

* P(t) = Σ_{l<25} d_l (T_67(b_l t) − T_67(−b_l t)), with b_l = 2l + ½ and T_N the exp Taylor polynomial of degree < N.
* Remainder for l < 25: Mathlib's `Complex.exp_bound'` gives \|e^x − T_N(x)\| ≤ 2\|x\|^N/N! when \|x\| ≤ (N+1)/2.  The kernel checks b_l·0.6931471808 ≤ 34 = (67+1)/2.
* Dropped terms l ≥ 25: \|d_l\|(2^{2l+1} + 1), since e^{b_l t} ≤ 2^{2l+1} on [0, log 2].
* log 2 < 0.6931471808 is Mathlib's `Real.log_two_lt_d9`.
* The generator chooses (L0, N) = (25, 67) as the smallest N with deltaP ≤ 2e-8.

## 3. Interface for S11 (and S12)

* **The kernel.**  For x, y ∈ I with |I| ≤ log 2, χ(y − x) = chiPoly(y − x) + r(y − x), with |r| ≤ deltaChi = 1.41e-7 (`chi_enclosure`, `chi_neg`).
  * chiPoly is an odd polynomial in |v| of degree 65 with explicit rational coefficients `ArchS10.Data.chiCo i`, i < 67.
  * For Galerkin matrices, expand |y − x|^i separately on y ≥ x and y ≤ x.  All entries are then exact rationals.
  * By Schur/Young (CC Lemma 6.3), the perturbation from r has operator norm at most 2·deltaChi·|I| < 2e-7.
  * That is far below S11's slack (ε₂ − ε₁ ≈ 3e-3 for CC's Thm 1 route, or λ_max ≤ 0.96 for the one-condition route).
* **Lower degree.**  If S11 prefers a lower-degree kernel, Chebyshev economisation on [0, log 2] should give degree about 45 at 1e-8 [C, estimated from the coefficient decay, not computed].  Certifying it would need a piecewise Taylor-shift check of chiPoly − p, which is not done.  Alternatively, `Qeps_expsum` gives the finite sinh series directly.
* **ε'(1⁺).**  `eps1_pos` / `eps1_ne_zero` discharge `prop55_KI`'s hypothesis ε'(1⁺) ≠ 0.  `eps1_enclosure` gives the value 22.99647568387053 ± 1.2e-22, so S12 can unfold N_I = −2ε'(1⁺)(Id − K_I) numerically.
* **Hypothesis bundle.**  Every result takes `hB : CertBasis D`.

## 4. What S6 must supply, and S8's `summable_wMN` (module `ArchS10_Summable`)

**`summable_wMN` is a theorem, not an obligation.**
* `ArchS10.EigenFamily.toProlateData` builds a full S8 `ProlateData` from this weaker structure:

```lean
structure EigenFamily where
  lam : ℕ → ℝ
  phi : ℕ → ℝ → ℝ
  cont : ∀ n, Continuous (phi n)
  eig : ∀ n ω, T (phi n) ω = lam n * phi n ω                  -- S9's T, every ω ∈ ℝ
  ne : ∀ n, lam n ≠ 0
  orth : ∀ n m, ip (phi n) (phi m) = if n = m then 1 else 0   -- orthonormal in L²(0,1)
  c : ℝ
  c_lt : c < 1
  lam_sq_le : ∀ n, lam n ^ 2 ≤ c
-- def EigenFamily.toProlateData (F : EigenFamily) (T0 : ℝ) (hT : 0 < T0) : ArchS8.ProlateData
--   lam := F.lam, phi := F.phi, T := T0, M = N := s_X(φ_n)/|λ_n| with X = e^{T0}
```

* The construction needs any T0 > 0, so CC's T0 = log 3 is covered.
* `phi_contDiff` comes from the eigen-relation, `bound_inner/outer` from `abs_T_le_s` / `abs_Td_le_s`, and `summable_wMN` from `sum_wMN_le`.

**The mathematics.**
1. **An ω-free bound** (`abs_T_le_s`, `abs_Td_le_s`).  Expand 2cos(2πxω) in ω, using S9's `T_sub_le`/`Td_sub_le` with J → ∞.  For 0 ≤ ω ≤ X, X ≥ 1 and continuous f:

       |T f(ω)|, |Td f(ω)| ≤ s_X(f) := Σ'_j γ_j |⟨x^{2j}, f⟩|,     γ_j = 4(4πX)^{2j}/(2j)!.

2. **Bessel in every moment** (`sum_sq_s_le`).  Apply Bessel to each x^{2j}, which has ‖x^{2j}‖ ≤ 1, then Cauchy–Schwarz in j.  For every orthonormal family and every finite S:

       Σ_{n∈S} s_X(e_n)² ≤ (Σ'_j γ_j)² ≤ 16 cosh(4πX)².

3. **The weighted sum** (`EigenFamily.sum_wMN_le`).  With λ_nξ_n = Tξ_n, λ_nξ_n' = Tdξ_n and M_n = N_n = s_X(ξ_n)/|λ_n|:

       Σ_{n∈S} λ_n²/(1−λ_n²)·M_n·N_n = Σ_{n∈S} s_X(ξ_n)²/(1−λ_n²) ≤ (Σ'γ)²/(1 − c).

* So the trick is not to bound sup|ξ_n| better than 1/|λ_n|.
* Instead it bounds sup|λ_nξ_n| = sup_ω|⟨K_ω, ξ_n⟩| by an ω-free quantity, and that quantity is square-summable in n by Bessel.
* S8's own `abs_kn_le` and `summable_wB` then give, uniformly on |t| < T:

      Σ_n w_n·sup|kn|, sup|kn1|, sup|kn2| ≤ (2+T)·2e^{T/2}(1+e^T)·(Σ'γ)²/(1−c),

  and the same for Σ_n w_n sup|C_n| = Σ_n w_n sup|−kn2 + kn/4|.
* This is a convergence statement only.  The certified numerics of sections 1-2 use the sharper S9-frame tail of `ArchS10_Tail`.

**Recommendation for the S8 refactor.**
* Option A, no refactor: keep `ProlateData` as is, and S6 calls `EigenFamily.toProlateData`.
* Option B: replace the five fields M, N, `bound_inner`, `bound_outer`, `summable_wMN` with `orth`, `eig`, `ne`, and `c < 1`, `lam n ^ 2 ≤ c`.  Then derive the old fields inside S8 by this module.
* Either way, **S6's obligation becomes exactly `EigenFamily`**, plus `CertBasis.window` (n ≤ 12 in S9's windows) for S10's numbers.
  * `c` is free in the S9 setting.  For n ≤ 12, |λ_n| ≤ |θ_n| + w2q < 1 (S9's `lam_ok`).  For n > 12, |λ_n| ≤ d0Q (`CertBasis.tail_small`).
  * So c = max((|θ_0| + w2q 0)², d0Q²) ≈ 0.99994.  This one-line lemma is not yet written in Lean.
* **`ne : λ_n ≠ 0`.**  It is needed for `phi_contDiff`, since a kernel vector of T need not be C¹.
  * T on L²(0,1) is injective: Tf ≡ 0 makes the Fourier transform of the even extension vanish.  So an eigenbasis has no zero eigenvalues.
  * That injectivity is not proved here.  If S6 enumerates only eigenvectors of nonzero eigenvalues, nothing is lost for S8: w_n = 0 there.  S7's Sonin trace may need completeness separately.
* Completeness of the family is NOT needed by S8 or S10.

## 5. Open items

1. **`summable_wMN`** (S8 item 5) is now derived from `EigenFamily` (section 4).  What remains open is the one-line c-bound lemma for the S9 enumeration, and injectivity of T (or S6 restricting to λ ≠ 0).
2. **Tail precision.**  The tail dominates the error budget: tauQ = 6.4e-6 on Qε, versus 3.3e-20 for the head.
   * It comes from the coefficient-sum bound |θ_13|·Σ_k|B_{13,k}|4^k ≈ 7e-5 for |θ_13 ψ_13| on [0, 2].  A rough estimate of the true sup is 1e-7 [C, not computed].
   * Splitting the integral's inner factor to [0, 1] would need an errdF bound on [0, 1], which S9 does not export.  It would bring χ to about 1e-15.
   * Not needed for any current target.
3. **Low-degree / piecewise version** of chiPoly (section 3) is not certified.
4. **Wiring.**  `defaultTargets` and `AxiomGuardRvMBridge.lean` are untouched.  The seven `[[lean_lib]]` stanzas are at the end of `lakefile.toml`: ArchS10_Exact, _Data, _Cert, _Tail, _Chi, _Summable, _Guard.

## 6. Files, sizes, build times (shared machine, load ~20)

| module | lines | content | `lake build` |
|---|---|---|---|
| ArchS10_Exact | 379 | CC, `CC_smul`, `CC_psi`, exp Taylor bound, CC perturbation | 31 s |
| ArchS10_Data | 124 (31 KB) | generated by `gen_s10.py` | 29 s |
| ArchS10_Cert | 25 | 6 `decide +kernel` checks, about 30 s of kernel time | 41 s |
| ArchS10_Tail | 517 | Bessel tail through S9's frame | 38 s |
| ArchS10_Chi | 643 | head, assembly, main theorems | 44 s |
| ArchS10_Summable | 335 | `summable_wMN` from the eigen-relation; `EigenFamily.toProlateData` | 49 s |
| ArchS10_Guard | 122 | 114 `#print axioms` | 43 s (`lake env lean`) |

* The generator `telperion/research/arch_rung/s10/gen_s10.py` (319 lines) runs in 1.6 s.
* It reads S9's rational data directly from `ArchS9_Data.lean` and `ArchS9_CertRes.lean`.
* Usage: `~/hodge-engine/venv/bin/python gen_s10.py ArchS10_Data.lean`.  It pins *_NUM_THREADS=1.

## 7. Lean footguns met

* **One-step `calc` inside a nested tactic block.**  It swallows the following less-indented tactic lines as term-mode `have`s.  The symptom is "unexpected token 'have'; expected ':='" plus "unknown identifier `rw`" far below.  Use `exact` for single steps.
* **`rw [intervalIntegral.integral_sub (ii h1) (ii h2)]` with pre-elaborated integrability terms fails.**  It fixes the function shape as `(fun x => c) * (f * g)`, which does not match `fun x => c * (f x * g x)`.  Rewrite without arguments and discharge the side goals with `all_goals first | …`.
* **`intervalIntegral.integral_mono_on` needs `(μ := volume)`.**  Without it, `IsLocallyFiniteMeasure ?m` gets stuck when the integrability argument is a `by` block.
* **`abs_mul` rewrites greedily inside products.**  Give it the explicit argument, as in `abs_mul (x * y)`.
* **There is no `Rat.cast_ite`.**  To cast a `decide`d sum with an `if`, prove the cast lemma by `split_ifs <;> push_cast <;> rfl` (`Abnd_cast`).
* **`omit hB in` breaks field notation `hB.cont`.**  Field notation needs the explicit `CertBasis` argument.  Use `set_option linter.unusedSectionVars false in` instead.
* **`intervalIntegral.integral_finset_sum` is deprecated.**  Use `integral_finsetSum`.
* **`Summable.sum_add_tsum_nat_add`** is the `to_additive` form of `Multipliable.prod_mul_tprod_nat_add`.  A plain grep for the name finds only the NNReal version.
* **System-wide "Too many open files" errors** appeared once under load from other sessions.  A retry after a pause succeeded.
