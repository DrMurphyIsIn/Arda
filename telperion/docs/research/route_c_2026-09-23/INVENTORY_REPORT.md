# Route C synthesis, inventory report (workflow wf_0568fe15-630, 2026-09-23)

Raw input to ROUTE_C_SYNTHESIS_2026-09-23.md, committed so that its unanchored estimates are traceable. conjecture1_proved = False.

# Route C (de Bruijn-Newman) island: inventory as of `b524f7e7d`

conjecture1_proved = False. All four Route C registry nodes are proved. Route C does not prove RH. It turns RH into the open claim "every zero of H_0 is real" (Λ ≤ 0), and the island proves only the known half, de Bruijn's Λ ≤ 1/2.

**Worktree:** `/Users/peterwmurphy/arda-routec-syn`, HEAD `b524f7e7d` ("grant(rh): RH_dbn_debruijn_real_zeros -> PROVED"). Its parent is `2f9e83ba2`, the merge of #604 on top of #608 (`dd6ed74c6`, the Hadamard work). The island sources are byte-identical to `/Users/peterwmurphy/arda-grant-c3` (`diff -rq` clean).

**One side effect:** to run the build check I reflink-copied `.lake` from arda-grant-c3 into `telperion/examples/dbn/lean/.lake`. `.lake` is a gitignored build cache. I made no git writes and no registry edits.

## 1. Modules (`telperion/examples/dbn/lean/`, 21 files, 6140 lines)

The toolchain is `leanprover/lean4:v4.34.0-rc1`. The island depends on `LiCriterion`, pinned at `nicholasbulka/li-criterion-rh-equivalence-lean@35df682f`, which brings Mathlib `de5ce8a9` (`lakefile.toml`). All 21 modules are `defaultTargets`.

| Module | Lines | Imports | Purpose / key results |
|---|---|---|---|
| DBNDefs | 569 | Mathlib, Lc.LiCriterion.Basic | Polymath15 definitions: `thetaMoment` (:40), `Φ` (:211), `HIntegrand` (:408), `H t z := ∫_{Ioi 0} e^{tu²}Φ(u)cos(zu)` (:413). `Φ_neg` Φ(−u)=Φ(u) (:261); `abs_Φ_le` decay (:300); `integrableOn_HIntegrand` (:421); `H_neg` (:442); `H_ofReal_im` (:460); `riemannXi_eq_completedRiemannZeta` for s≠0,1 (:468); `hasDerivAt_H`/`differentiable_H`, H_t entire (:520, :566). Λ is deliberately not defined (header :11-13). |
| DBNXiRiemann (C2 module A) | 264 | DBNDefs | `psi` (:48); `evenKernel_zero_eq_thetaMoment` (:100); `weakFEPair_Λ₀_eq`, P.Λ₀ as two `Ioi 1` integrals for any `WeakFEPair` (:156); `completedRiemannZeta₀_eq_integral_psi`: Λ₀ s = ∫_1^∞ ψ(x)(x^{s/2−1}+x^{(1−s)/2−1}) for every s (:245). |
| DBNGKernel (module C) | 684 | DBNDefs | Kernel g = e^u(θ₀−1)/2 (:135) with g′ and g″ (:138, :143); `hasDerivAt_g`/`g'` (:161, :173); `g''_sub_g_eq`: g″−g = 8Φ (:214); `g'_zero`: g′(0) = −1/2 (:221); decay bounds (:244-297); `tendsto_exp_quad_mul_exp_neg_exp` (:351); generic integrability and boundary-limit lemmas (:395, :418). 66 theorems. |
| DBNXiCos (module B) | 134 | DBNXiRiemann, DBNGKernel | `integral_Ioi_one_eq_integral_exp_four_mul`, the substitution x = e^{4u} (:76); `xiCos_integrand` (:98); `completedRiemannZeta₀_half_add_eq`: Λ₀(1/2+iz/2) = 8∫_0^∞ g cos(zu) (:127). |
| DBNXiIBP (module D) | 88 | DBNGKernel | `integral_g_cos_ibp` (:39); `integral_g_cos_eq`: (z²+1)∫g cos = 1/2 − 8H_0(z) (:81). |
| DBNXi (module E) | 64 | DBNXiCos, DBNXiIBP | **`dbn_H0_eq_xi`** (:41); `H_zero_I`: H 0 i = 1/16 (:55). |
| DBNRealZerosIff (C4, conditional) | 141 | DBNDefs | `H0EqXi` Prop (:48); `xiArg_re`/`_eq_half_iff`/`_surj`/`xiArgInv_im` (:54-70); `riemannXi_eq_zero_iff_strip_zero`, which uses the upstream `LiCriterion.xi_zeros_are_nontrivial_zeros` (:80); `dbn_rh_iff_H0_real_zeros_of_H0_eq_xi` (hC2) (:116). |
| DBNRealZerosIffFinal (C4) | 36 | DBNXi, DBNRealZerosIff | `DBN.H0EqXi_holds` (:26); **`dbn_rh_iff_H0_real_zeros`** (:33). |
| DBNStrip | 501 | DBNDefs | Whole-line Gamma integral `integral_cexp_mul_exp_neg_exp` (:71); `H_zero_eq_half_integral` (:210); `H_conj` (:232); `integral_expTerm` (:293); `summable_integral_norm_expTerm` (:381); `H_zero_eq_of_im_lt`: H_0 = (1/16)s(s−1)π^{−s/2}Γ(s/2)ζ(s) for Im z < −1 (:448); `H0_zero_strip` (:482); `H0_ne_zero` (:489); **`dbn_H0_zero_strip`** (:499). |
| DBNStep (L4) | 480 | Mathlib | `shiftAvg δ f z = (f(z+iδ)+f(z−iδ))/2` (:51); `structure EvenHadamardData` {c, m, τ, tendsto_prod} (:119); `ofHasProd`/`ofMultipliable` (:182, :194); `shiftAvg_zero_im_sq_le` (:401): if f is real, has even Hadamard data and its zeros satisfy Im² ≤ Δ2, then zeros of T_δ f satisfy Im² ≤ max(Δ2−δ²,0). `shiftAvg_real_zeros` (:447); `zero_im_sq_le_of_shiftAvg_iterate` gives max(Δ2−Nδ²,0) (:459). |
| DBNStepControls | 155 | DBNStep | Positive control 1+z²: `step_bound_attained` shows the bound is sharp (:72). Negative control z²−2i: `step_needs_reality` shows the reality hypothesis is load-bearing (:132). |
| DBNHurwitz (L2e) | 124 | Mathlib | `hurwitz_ne_zero` via maximum modulus (:36); `hurwitz_ne_zero_of_entire` (:116). |
| DBNHeatApprox (L2a-d) | 633 | DBNDefs, DBNStep, DBNHurwitz | `Gδ δ N z := ∫cosh(δu)^N Φ cos(zu)` (:123); `G t N := Gδ (√(2t/N)) N` (:127); `Gδ_succ`: Gδ(N+1) = T_δ(Gδ N) (:187); `Gδ_eq_iterate` (:202); `differentiable_Gδ`/`Gδ_neg`/`Gδ_conj` (:208-219); `norm_Gδ_le_exp_rpow_norm`, order ≤ 3/2 (:355); `tendstoUniformlyOn_G` on strips (:485); `tendstoLocallyUniformly_G` (:494); `Φ_pos` (:551); `H_zero_ne_zero` (:583); `Gδ_zero_re_pos` (:590); `H_ne_zero_of_approx_on` (:616). |
| DBNDeBruijnReduction (L5) | 114 | DBNHeatApprox | Props `H0ZeroFreeOffStrip` (:41) and `ApproxHadamard` (:45); `G_zero_im_sq_le_of_obligations` (:57); `H_zero_im_sq_le_of_obligations` (:94); `H_ne_zero_of_obligations` (:107). |
| DBNHadamardCount (L3a) | 300 | Mathlib | `zeroCount` (:58); `summable_zero_multiplicity_rpow`: Σ ord_s(f)‖s‖^{−p} < ∞ for p > ρ (:220). |
| DBNHadamardProduct (L3b) | 364 | Mathlib | `evenProduct τ z := ∏'(1−z²τ_k²)` (:117); `hasProd_`/`differentiable_evenProduct` (:121, :125); `norm_evenProduct_le` (:196); `evenProduct_eq_zero_iff` (:235); `analyticOrderNatAt_evenProduct` (:330). |
| DBNHadamardMean (L3c/d) | 235 | Mathlib | `exists_exp_eq_of_ne_zero`: a zero-free entire g equals exp∘H (:37); `circleAverage_abs_re_le`, Jensen in the mean (:121). |
| DBNHadamardLinear (L3e) | 238 | Mathlib | `eq_linear_of_circleAverage_abs_re_le`: with p < 2, H = a + bz (:152), via Poisson, Borel-Carathéodory and Cauchy. |
| DBNHadamard (L3) | 452 | DBNStep, Count, Product, Mean, Linear | `IsRep`/`RepZero`/`ZeroIdx`/`repSeq` (:114-173); **`evenHadamardData_of_order_lt_two`**: f entire, even, not ≡ 0, ‖f‖ ≤ A e^{B‖z‖^ρ} with 0 < ρ < 2 implies `Nonempty (EvenHadamardData f)` (:321). |
| DBNHadamardApprox | 99 | DBNHadamard, DBNDeBruijnReduction, DBNStrip | `norm_Gδ_le_growth` (:39); `approxHadamard` (:70); `H0ZeroFreeOffStrip_holds` (:77); `H_zero_im_sq_le`: for all t ≥ 0, zeros of H_t satisfy Im² ≤ max(1−2t,0) (:83); `H_ne_zero_of_half_le` (:88); **`dbn_debruijn_real_zeros`** (:97). |
| AxiomGuardDBN | 465 | all 20 modules | 325 `#print axioms` lines. |

**Dependency DAG:**
- Defs → {RealZerosIff, XiRiemann, GKernel, Strip}
- {XiRiemann, GKernel} → XiCos
- GKernel → XiIBP
- {XiCos, XiIBP} → Xi
- {Xi, RealZerosIff} → RealZerosIffFinal
- {Defs, Step, Hurwitz} → HeatApprox → DeBruijnReduction
- {Step, Count, Product, Mean, Linear} → Hadamard
- {Hadamard, DeBruijnReduction, Strip} → HadamardApprox

The C2/C4 chain and the C3 chain share only DBNDefs. C3 does not import DBNXi.

**Provenance:**
- DBNDefs: `d51532c99`, 2026-09-17.
- C2 modules A-E and RealZerosIffFinal: `fd4385923`.
- RealZerosIff: `720bb16b0`.
- Strip: `df0220ee4`.
- Step, Controls, Hurwitz, HeatApprox, Reduction: `201824e6c`.
- Hadamard\* and HadamardApprox: 2026-09-23, PR #608.

## 2. The four registry nodes

Statements are in `telperion/missions/rh/lean/Statements/*.lean`, line 4 onward. All four `.toml` files record `status="proved"`, `closure_clean=true`, `via="direct"`.

| Slug | Statement (verbatim) | Artifact / theorem | depends_on | Granted | Kind |
|---|---|---|---|---|---|
| RH_dbn_H0_eq_xi | `theorem dbn_H0_eq_xi (z : ℂ) : DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)` | `DBNXi.lean` `dbn_H0_eq_xi` (:41) | `[]` | 2026-09-22 | lemma |
| RH_dbn_H0_zero_strip | `theorem dbn_H0_zero_strip : ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1` | `DBNStrip.lean` `dbn_H0_zero_strip` (:499) | `[]` | 2026-09-22 | lemma |
| RH_dbn_rh_iff_H0_real_zeros | `theorem dbn_rh_iff_H0_real_zeros : (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2) ↔ ∀ z : ℂ, DBN.H 0 z = 0 → z.im = 0` | `DBNRealZerosIffFinal.lean` (:33) | `["RH_dbn_H0_eq_xi"]` | 2026-09-22 | milestone |
| RH_dbn_debruijn_real_zeros | `theorem dbn_debruijn_real_zeros : ∀ t : ℝ, 1 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0` | `DBNHadamardApprox.lean` (:97) | `["RH_dbn_H0_zero_strip"]` | 2026-09-23 (`b524f7e7d`) | milestone |

`attempts.jsonl` lines 64-68 record the history, including one earlier "Stalled" entry for C4 at line 64.

**Audit testimony** (`telperion/docs/AUDIT_TESTIMONY_RH_dbn_<node>_<date>_{A1,A2}.md`). Every one of the eight files records `pass: true`, `axioms_clean: true` and `statement_byte_identical: true` (whitespace-normalised).

- **H0_eq_xi, A1 (202 lines):** mpmath at 30 digits. Λ₀ computed two ways: (M) Mathlib's Mellin form, (C) Γζ + 1/s + 1/(1−s).
  - Points z = i, 2+i, 10−0.7i, 3.5+0.25i, 28.2694.
  - Absolute difference ≤ 5.3e-28 for (M) and ≤ 6.5e-33 for (C) (:158-164). H_0(i) − 1/16 = 0 to 30 digits.
- **H0_eq_xi, A2 (180 lines):** mpmath at 25 digits. z = i gives 0; 0.7+0.4i gives 3.2e-28; 5−1.2i gives 1.8e-27 (:144-146). riemannXi = s(s−1)Λ/2 at 0.3+0.9i to 7e-27 (:152).
- **H0_zero_strip, A1 (181 lines):** half-plane identity at z = −2i, 3−1.5i, −7.25−3.1i. Relative difference 0 / 7.7e-32 / 2.2e-31 (:142-144). H_0(i) = 1/16.
- **H0_zero_strip, A2 (179 lines):**
  - Same identity at −2i, 3−1.5i, −7.25−3i: absolute difference 0 / 4.6e-33 / 1.5e-32.
  - Φ(u) − Φ(−u) ≈ 1e-41 (:90).
  - Import and constant walk: no C2 constant and nothing from LiCriterion in the closure.
  - The hardened gate rejected two mutations.
- **rh_iff, A1 (124) and A2 (184):** no numerics. They check the convention against Titchmarsh's Φ_T, the assembly algebra s(s−1) = −(z²+1)/4 (A1 :61-69), and elaboration with `pp.fullNames`. As a sanity probe, A2 derives the strip form from Mathlib's `RiemannHypothesis` in one direction only (:136, :181).
- **debruijn, A1 (77 lines):** mpmath at dps 40 (:57-66).
  - H_0 matches ξ/8 to 12 digits at 4 points.
  - Winding number for H_{1/2} is 0 on both off-axis boxes; minimum |H| on the boundary is 8.7e-10.
  - Planted zero at 30+0.5i gives winding 1.
  - Thin axis box gives winding 3 for both t = 0 and t = 1/2.
  - H_0 zeros equal 2γ_k (k = 1..3) to 1e-36. The grant commit message says 1e-34; the testimony says 1e-36.
- **debruijn, A2 (85 lines):** 1536-node Gauss-Legendre quadrature (:59-73).
  - ξ/8 relative error ≤ 1e-35.
  - H_0 zeros in [0,62] equal 2γ_1..2γ_4 to 7e-34.
  - H_{1/2} real zeros: 27.980, 41.668, 49.728, 60.379.
  - Winding 0 on [0,60]×[0.1,1], [0,60]×[−1,−0.1] and [0,60]×[0.02,3].
  - Controls give 1, 3 and 3.

## 3. How each node is proved

**C2, `dbn_H0_eq_xi`** (`DBNXi.lean:41-51`; the assembly is a single `linear_combination`):
- **A** (`DBNXiRiemann:156, 245`): Mathlib's Mellin convergence of `f_modif` via `isStrongFEPair_toStrongFEPair`. `f_modif` is split into an `Ioi 1` piece and an `Ioo 0 1` piece. The `Ioo 0 1` piece is inverted at the Mellin level (`mellin_comp_inv`, `mellin_cpow_smul`) using the functional equation. Result: Λ₀(s) = ∫_1^∞ ψ(x)(x^{s/2−1} + x^{(1−s)/2−1}) for every s.
- **B** (`DBNXiCos:76-127`): substitute x = e^{4u} using `integral_image_eq_integral_abs_deriv_smul`. Pointwise, 4e^{4u}ψ(x^{…}+x^{…}) = 8g(u)cos(zu). Result: Λ₀(1/2+iz/2) = 8J(z).
- **C** (`DBNGKernel:161-221`): g = e^u ψ(e^{4u}) with closed-form g′ and g″ from the termwise `hasDerivAt_thetaMoment`, so no tsum is ever swapped with an integral. g″ − g = 8Φ; g′(0) = −1/2 from the twice-differentiated theta functional equation.
- **D** (`DBNXiIBP:39-84`): two applications of `integral_Ioi_mul_deriv_eq_deriv_mul` give (z²+1)J = −g′(0) − ∫(g″−g)cos = 1/2 − 8H_0(z).
- **E:** at s = 1/2+iz/2, s(s−1) = −(z²+1)/4, so ξ = −(z²+1)J + 1/2 = 8H_0.

**Strip, `dbn_H0_zero_strip`** (`DBNStrip`). It does not use C2: its import closure is {DBNDefs, Mathlib, Lc Basic}.
- L1a: evenness of Φ folds H_0 into (1/2)∫_ℝ Φ e^{izu} (:210).
- L1b: termwise whole-line Gamma integral, ∫a_n e^{izu} = (1/8)s(s−1)π^{−s/2}Γ(s/2)n^{−s} for Im z < −1 (:71, :293).
- L1c: Tonelli bound O(n^{(Im z−1)/2}), then `hasSum_integral_of_summable_integral_norm`, giving H_0 = (1/16)s(s−1)π^{−s/2}Γ(s/2)ζ(s) on Im z < −1, i.e. Re s > 1 (:381-448).
- L1d: no factor vanishes there (`riemannZeta_ne_zero_of_one_lt_re`, the Euler product, and Γ ≠ 0). `H_neg` reflects the result to Im z > 1 (:459-482).

**C4, `dbn_rh_iff_H0_real_zeros`** (`DBNRealZerosIff:54-138`, `Final:33-36`):
- Re(1/2+iz/2) = 1/2 − Im z/2. Under this map the real axis corresponds exactly to Re s = 1/2, and the inverse is s ↦ −2i(s−1/2).
- ξ(s) = 0 ⇔ ζ(s) = 0 ∧ 0 < Re s < 1, from upstream `LiCriterion.xi_zeros_are_nontrivial_zeros`.
- Given C2, H_0 z = 0 ⇔ ξ(1/2+iz/2) = 0, since the factor 1/8 is nonzero.
- `Final` specialises the conditional bridge at `dbn_H0_eq_xi`. The theorem is an equivalence and proves neither side.

**C3, `dbn_debruijn_real_zeros`:**
- **Approximants** (`DBNHeatApprox`): Gδ with the factor cosh(δu)^N. On the kernel side T_δ is multiplication by cosh(δu), so `Gδ_succ` gives G t N = T_δ^N H_0 with δ² = 2t/N.
- **Step lemma** (`DBNStep:305-459`): for real f with `EvenHadamardData`, each factor ‖1−z²τ²‖·‖1−z²τ̄²‖ strictly increases from w−iδ to w+iδ when y² + δ² > Δ2. So ‖f(w+iδ)‖ > ‖f(w−iδ)‖, and T_δ f(w) ≠ 0. Iterating contracts Im² by Nδ² = 2t.
- **Base case:** the strip Im² ≤ 1 for H_0 (`H0ZeroFreeOffStrip_holds`, `DBNHadamardApprox:77`).
- **Hadamard** (`DBNHadamard:321`), genus 0 in the variable z²:
  - Count: Jensen plus dyadic summation.
  - Product: the even canonical product.
  - Mean: the zero-free quotient is exp∘H, and Jensen in the mean bounds circleAverage|Re H|.
  - Linear: Poisson, Borel-Carathéodory and Cauchy show H is affine; evenness removes the linear term.
  - Applied to Gδ using order 3/2 < 2 (`norm_Gδ_le_growth`), Gδ even, and Gδ(0) > 0 from `Φ_pos`.
- **Closure:** `tendstoLocallyUniformly_G` plus Hurwitz on the open set {max(1−2t,0) < Im²} give Im² ≤ max(1−2t,0) for H_t, t ≥ 0 (`:83`). At t ≥ 1/2 this forces Im z = 0 (`DBNDeBruijnReduction:107`, `DBNHadamardApprox:97`).

## 4. Trust boundary

**Build:** `leanlock.sh lake build --no-build` reports "All targets up-to-date (8759 jobs)".

**Axioms:** `leanlock.sh lake env lean AxiomGuardDBN.lean` exits 0 and prints 325 lines. All 325 say "depends on axioms: [propext, Classical.choice, Quot.sound]". None says "does not depend", and there is no `sorryAx`.

**Coverage:** a script check finds 321 distinct top-level `theorem`/`lemma` names across the DBN\*.lean files, with 0 missing from the guard. There are no `private` declarations.

**Incompleteness markers:** grepping the island for `sorry|admit|axiom|opaque|native_decide|implemented_by|extern|unsafe` as declarations or tactics finds nothing.

**Registry anchors:** `telperion/scripts/guard_anchors.py --island dbn` run with python3.12 prints "OK: all 4 proved registry anchors on `dbn` are printed … within [propext, Classical.choice, Quot.sound]". The system python3 lacks `tomllib`.

**Hypotheses:** none remain in any of the four registry theorems. Every named Prop obligation on the island is discharged:
- `H0EqXi` by `H0EqXi_holds` (`Final:26`)
- `H0ZeroFreeOffStrip` by `DBNHadamardApprox:77`
- `ApproxHadamard` by `approxHadamard` (`DBNHadamardApprox:70`)

The conditional `*_of_obligations` / `_of_H0_eq_xi` theorems remain as intermediate lemmas.

**What the trust rests on:**
1. **Registry vs island definitions.** Registry `DBN.H` is a textual copy in `Statements/RHDefs.lean:97-116`, citing DBNDefs :40-41, :211-214, :408-409, :413. It is not a shared import, so the link is the statement gate plus the auditors' line-for-line diff.
2. **Upstream code.** `LiCriterion.riemannXi` and `xi_zeros_are_nontrivial_zeros` come from the pinned external repo. Their axioms are inside the 3-axiom closure, but the code is not Arda-audited, apart from the rh_iff testimonies re-deriving the ξ normalisation.
3. **Lean 4 kernel and Mathlib `de5ce8a9`.**

**CI:** job `dbn-compiles` (`.github/workflows/telperion-lean-e2e.yml:2465-2525`) runs:
- a no-`sorry` grep
- `lake build`
- the axiom guard with a floor of ≥ 30 lines, a `sorryAx` check and a 3-axiom subset check
- `guard_anchors.py --island dbn`

`dbn-compiles` is in `required_status_checks` for main. However, branch protection `enforce_admins.enabled = false`, so admins can bypass it.

**Stale items (factual; I did not fix them):**
- The CI comment "32 `#print axioms` anchors … as of 2026-09-22" (:2501) and the floor of 30 are far below the actual 325.
- `AxiomGuardDBN.lean:19-21` still calls de Bruijn "a registry STATEMENT, not an island theorem".
- `DBNStep.lean:5` says "DBNHadamard.lean, NOT on this island yet".
- `DBNDeBruijnReduction.lean:7` says "Neither is proved on this island". Line 16 says "order 1"; the proved bound is order ≤ 3/2 (`DBNHeatApprox:355`).

## 5. Reusable assets and upstream candidates

**For later Route C work (Λ, Newman, monotonicity):**
- **Quantitative strip bound** `H_zero_im_sq_le`: for all t ≥ 0, Im² ≤ max(1−2t,0) (`DBNHadamardApprox:83`). This is stronger than the registry node.
- **Heat machinery:** `EvenHadamardData` with `shiftAvg_zero_im_sq_le` and `zero_im_sq_le_of_shiftAvg_iterate`, which is generic in F (`DBNStep:119, :401, :459`); `evenHadamardData_of_order_lt_two` for any even order-<2 entire function. Together these are the natural route to real-zero monotonicity in t, i.e. the up-set property. That lemma is not built.
- **Approximants and convergence:** `Gδ`/`G` with `Gδ_eq_iterate`, `tendstoLocallyUniformly_G`, `Φ_pos`, `H_zero_ne_zero` (every t), `H_conj`, `differentiable_H`, `hasDerivAt_H`.
- **Half-plane and representation identities:** the half-plane identity `H_zero_eq_of_im_lt` and `dbn_H0_eq_xi`, the bridge between the ζ side and the H side.
- **Controls:** `DBNStepControls`, a template for kernel-checked positive and negative controls.

**Things Mathlib lacks that the island now has.** The Mathlib-only modules are Count, Product, Mean, Linear, Hurwitz and Step. None of them imports Φ, H or ζ, so they are the cleanest upstream candidates.
- **Hadamard factorisation, even / order < 2 case.** HADAMARD_PLAN §2 notes there is no Hadamard/Weierstrass factorisation in Mathlib at the pin or on master as of 09-23.
  - Pieces: `summable_zero_multiplicity_rpow` (convergence exponent), `evenProduct` with growth, zero set and orders, `exists_exp_eq_of_ne_zero`, `circleAverage_abs_re_le` (Jensen in the mean), and `eq_linear_of_circleAverage_abs_re_le` (Borel-Carathéodory in the mean, so a sub-quadratic mean |Re H| forces H affine).
- **Hurwitz's theorem**, zero-free form (`hurwitz_ne_zero`). Design memo §3.1 records that Mathlib has no Hurwitz, Rouché or argument principle.
- **Riemann's symmetric integral** for any `WeakFEPair` (`weakFEPair_Λ₀_eq`) and for Λ₀ (`completedRiemannZeta₀_eq_integral_psi`).
- **Integral lemmas:** the whole-line Gamma integral `integral_cexp_mul_exp_neg_exp` and the substitution `integral_Ioi_one_eq_integral_exp_four_mul`.
- **Overlap to check:** there is a separate `examples/borel_caratheodory` island with `borel_caratheodory_value` (:236) and `borel_caratheodory_deriv_family` (:309). DBNHadamardLinear instead uses Mathlib's Borel-Carathéodory (header :9-10).

## 6. Design memos vs what was built

**Foundations memo** (`DBN_FOUNDATIONS_C2C4_2026-09-17.md`, 233 lines):
- Planned C2 route (§6): integration by parts on (1,∞), then x = e^{4u}. Built: substitution first (module B), then integration by parts on (0,∞) in u (module D).
- Planned C3 route: Laguerre-Pólya / Pólya-type factorisation, "the first months of C3 are that infrastructure". It was abandoned for heat approximants, the step lemma, Hadamard and Hurwitz.
- The Λ discipline (§5) was kept: Λ is not defined anywhere. The three prerequisite lemmas are non-empty (now true at 1/2), up-set (not built) and bounded below / Newman (not built).
- It reported 31 guard lines; there are now 325.

**C2 memo** (`DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md`, §5 table :255-263):

| Module | Estimated lines | Actual |
|---|---|---|
| A | 350-500 | 264 |
| B | 150-250 | 134 |
| C | 250-400 | 684 (overrun, 66 theorems) |
| D | 200-300 | 88 |
| E | 50-100 | 64 |
| **Total** | **1000-1550** | **1234** |

Other deviations:
- Step A(iv): the memo's indicator transport through `integral_comp_rpow_Ioi` was replaced by Mellin-level lemmas (DBNXiRiemann header).
- The proposed sub-nodes A-D (`RH_dbn_xi_riemann_integral` etc.) were never registered; there are only the 4 dbn node files.
- "No tsum/integral interchange" held.

**C3 memo** (`DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md`, §4 :316-350, total "about 4500, range 3500-6000"):

| Obligation | Estimated lines | Actual |
|---|---|---|
| L1 (strip) | ~950 | DBNStrip 501 |
| L2 (approximants + closure) | ~1300 | HeatApprox 633 + Hurwitz 124 = 757 |
| L3 (factorisation) | ~1950 | Count 300 + Product 364 + Mean 235 + Linear 238 + Hadamard 452 = 1589, in 5 files instead of one `DBNHadamard.lean` |
| L4 (step lemma) | ~500 | Step 480 (+ Controls 155, not in the memo) |
| L5-L6 (assembly) | ~400 | Reduction 114 + HadamardApprox 99 = 213 |
| **Total** | **~4500** | **3695** (3540 without Controls) |

Other deviations:
- **L3d:** the minimum-modulus lemma (est. 600) was replaced by Jensen in the mean, with no exceptional circles (DBNHadamardMean header).
- **L2d:** the memo planned Fourier uniqueness from `H0_ne_zero`; the build uses `Φ_pos`, so H_t(0) > 0.
- **L2c:** the memo planned convergence on closed balls; the build proves uniform convergence on horizontal strips.
- **L5:** the memo named the file `DBNDeBruijn.lean` and the theorem `DBN.debruijn_real_zeros`. The build splits it into Reduction + HadamardApprox with the root-namespace `dbn_debruijn_real_zeros`.
- **L6:** the `real_zeros_mono` corollary was not built.
- **Registry recommendations §6 :390-400** were adopted: the C3 → C2 edge was dropped, and the `RH_dbn_H0_zero_strip` node was added as C3's only dependency. The optional `hadamard_even` infrastructure node was not added.

**HADAMARD_PLAN_2026-09-23.md** (110 lines) had no line estimates. The target signature in §1 matches `DBNHadamard.lean:321` exactly.