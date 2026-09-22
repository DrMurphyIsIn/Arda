# Shapes audit C: B7 and the xi partial fraction (2026-09-22)

conjecture1_proved = False. Nothing in this audit bears on the Riemann Hypothesis. Every
theorem surveyed is an identity about the zeros and the primes valid whether or not RH holds
(the Bombieri-Lagarias explicit formula on Li's test class, the derivative partial fraction of
xi'/xi obtained without the Hadamard product, the local-count sum, the strip derivative bound,
the real-segment nonvanishing), a finite real inequality, or an implication whose forward
direction assumes RH as a hypothesis (the forward half of Li's criterion, the forward half of
the Theta face). The converse halves that would BE RH are equivalences, not proofs.

Scope: PR #595 of DrMurphyIsIn/Arda (MERGED), the cluster
`telperion/examples/rvm_bridge/lean/E6Bridge15.lean` .. `E6Bridge27.lean` (7112 lines, read in
full: every theorem statement and every proof skeleton, with the long proofs of E6Bridge16,
E6Bridge19 and E6Bridge24 read line by line), the AxiomGuard anchors, and the rh registry
changes (21 node TOMLs and their `Statements/` mirrors, the mirrormere nodes, `attempts.jsonl`).
Classified against the 153 registered emitter kinds (`grep 'kind = "' src/telperion/*.py`),
the README "Certificate shapes" table, the cross-pollination standing order
(`docs/CROSS_POLLINATION_STANDING_ORDER.md`) and the honesty patterns
(`docs/HONESTY_PATTERNS.md`). Candidate-shape format follows
`EMITTER_ROADMAP_2026-09-02_RH_CROSSCUT.md`; verdict vocabulary matches the sibling audit
`SHAPES_AUDIT_D_LI_FACE_2026-09-22.md` so the four audits can be merged.

Method for each recurring hand-written pattern: (i) COVERED by an existing kind (named;
MISS = a standing-order miss, the emitter could have produced it; BESPOKE = covered in
principle but legitimately hand-written); (ii) NEW = new shape candidate (section 3, with
abstract statement family, untrusted certificate data, Lean skeleton, refusal conditions,
instances, cross-applicability, build cost); (iii) DISCIPLINE = a reusable analytic pattern
that is not certificate-shaped, with a note on what a certificate or numeric-channel emitter
would need.

## 1. File table

| File | Lines | What it holds | Emitted? |
|---|---|---|---|
| `E6Bridge15.lean` | 493 | B7 convergence half: conjugation symmetry of the divisor, the pairing by reindexing the window tsum over `conj`, `|Re K_n(rho)| <= 2^n/|rho|^2` by binomial expansion, the local-count majorant `liBound`, Tannery, `LiValue` as a named Prop, forward Li positivity | hand-written |
| `E6Bridge16.lean` | 877 | sharp envelope of the Wall: second Gaussian moment at a complex frequency, pole terms evaluated (`weilKernel f 0 = gaussTest c lam (i/2)`), the exact c-uniform prime constant `primeAbs`, capped archimedean floor with the `20/r^2` Stirling error, `envelopeCsharp`, seven hand numerics (`e^-6 <= 1/400`, `sqrt(2 pi) <= 2.51`, ...) | hand-written |
| `E6Bridge17.lean` | 950 | Theta face: strip bound `‖G‖(1+|z|^2) <= plainC`, RH <-> Theta positivity (converse via E6Bridge7's six steps with the bracket `cos(4 lam x y)`), the heat identity (M) by Gaussian convolution (`integral_cexp_quadratic`) summed against the majorant, `ThetaFree` monotone in the width | hand-written |
| `E6Bridge18.lean` | 355 | xi, the double-pole sum `polBound`, `XiLogDerivDerivEq` interface, real-axis decay of the sum (Tannery), Liouville with logarithmic growth, assembly modulo `XiDiffRegular` + `XiLogDerivDerivDecay` | hand-written |
| `E6Bridge19.lean` | 1594 | LiValue Taylor bookkeeping: generic `zeroBound` majorant + `summable_of_zeroBound`, generic `iteratedDeriv_tsum_ball`, power sums from the derivative (`coef`, `zterm`, `zbound`), the paired first power sum by FTC on `[0,1]` + reflection fold (`refTerm`), closed forms at `s = 1` (`eta_eq`, digamma series `dterm`/`dtail`, `tsum_odd_inv_pow`, `iteratedDeriv_psiHalf`, `archCoeff_succ`), `taylorOne_eq`, `taylorZero_eq` by antisymmetry, the binomial rearrangement onto `archSide + finiteSide`, the Lambda-form equivalence | hand-written; numerics in `docs/LIVALUE_TAYLOR_2026-09-21.md` |
| `E6Bridge20.lean` | 592 | entire extension: `xi_eq_zero_iff`, `analyticOrderAt_xi_eq`, the rest sum differentiable on a ball (M-test with the same majorant), local unit factor, pole cancellation `xiDiffExt := limUnder (nhds[≠] s)`, functional equation, `XiDiffExtGrowthRight` | hand-written |
| `E6Bridge21.lean` | 409 | real-axis decay: trigamma series across the integers by continuity, telescoping majorant `Sum 1/(x+n)^2 <= 1/(x-1/2)`, `(zeta'/zeta)' = L(log * Lambda)` and its Tannery decay, the termwise derivative on the real ray | hand-written |
| `E6Bridge22.lean` | 484 | growth bound in three regions: `lcTerm` and `LocalCountSum`, far/right comparisons, `bound_of_bound_off_zeros`, compact/strip/right assembly with `max` constants, `RightDerivBound` discharged (trigamma constant + Dirichlet constant) | hand-written |
| `E6Bridge23.lean` | 282 | `LocalCountSum` discharged: ceiling-fibre regrouping, fibre weight `4/(1+k^2)`, `log(y+4) <= 6 sqrt y` tail majorant, the constants `S1`, `S2` | hand-written |
| `E6Bridge24.lean` | 882 | `StripDerivBound` discharged: window count by five unit windows, `‖psi z‖ <= log(2+|Im z|) + pi + 7/2`, Landau repackaged, `Fwin`/`FwinExt` with the window poles divided out, Cauchy on a zero-free circle of radius in `(1/4,1/2)`, the 200-line `Fwin_bound_core` (five pieces, symmetric-difference split), the reflection half, the low-height compact bound | hand-written |
| `E6Bridge25.lean` | 129 | `NoRealZeroInUnitInterval`: `|J(sigma)| <= 1/(2 sigma)` from `Zeta0EqZeta` at N = 1, `Re zeta(sigma) < 0` on `(0,1)` | hand-written |
| `E6Bridge26.lean`, `E6Bridge27.lean` | 29, 36 | assemblies (modulo `StripDerivBound`; unconditional) | n/a |
| `AxiomGuardRvMBridge.lean` | 475 | anchors for RvMBridge15..27 (34, 27, 52, 20, 127, 32, 33, 28, 23, 30, 9, 2, 4 `#print axioms` lines respectively) | n/a |
| `missions/rh/nodes/*.toml` (21 touched) | | all `status = "proved"`, `via = "direct"`, `closure_clean = true`, blind read-backs; the reduction ladder `RH_bl_explicit_formula_of_livalue` -> `_of_partial_fraction` -> `_of_strip` -> unconditional | n/a (section 6) |

Duplication found across the cluster (written by parallel agents; the E6Bridge18 header says
"fixed for the parallel Taylor agent"), a standing-order signal in itself (section 5.2):
nine lemma groups are proved twice.

## 2. Classified findings

Verdict key: COVERED (kind), MISS, BESPOKE, NEW (section 3), FOLD-IN (section 4),
DISCIPLINE (section 5.1).

### 2.1 Pattern (1): the zero-sum majorant (finite exceptional window + local-count tail)

The workhorse of the cluster. A family `f : C -> C` supported on the nontrivial zeros is shown
summable by: `f rho = 0` off the zeros; `‖f rho‖ <= m(rho) * C_far / (1 + |gamma_rho|^2)` on
the zeros far from a centre (`|Im rho - a| >= h`, h = 1 or 2); the finitely many near zeros
(`zetaSeam.finite_window`) absorbed by a `Set.indicator`; `RvMBridge6.summable_mult_div_one_add_normSq`
closes. Thirteen calls of that lemma and 64 `indicator` occurrences in eleven files.

| Where | Term family | `C_far` | Verdict |
|---|---|---|---|
| `E6Bridge15.lean:349-410` (`liC`, `liBound`, `summable_liPaired`) | `m Re K_n(rho)` | `(9/4) 2^n` | NEW (shape A) |
| `E6Bridge18.lean:116-184` (`polBound`, `summable_polTerm`) | `m/(s-rho)^2` | `13/4 + 2 (Im s)^2` | NEW (shape A) |
| `E6Bridge19.lean:107-175` (`zeroBound`, `norm_le_zeroBound`, `summable_of_zeroBound`) | generic `(C, b)` | parameter | the abstract atom, already factored here (the shape's prelude) |
| `E6Bridge19.lean:324-355` (`zbound`) | `zterm k` on the ball | `(k+1)! 2^(k+2) (9/4)` | NEW (shape A, parametric in k) |
| `E6Bridge19.lean:586-595` (`segBound`) | `zterm 0` on the real segment | `9/4` | NEW (shape A) |
| `E6Bridge19.lean:743-773` (`summable_refTerm`) | `m (1/(1-rho) - 1/conj rho)` | `9/4` | NEW (shape A) |
| `E6Bridge17.lean:266-289` (`pmajorant`), `340-368` | plain Gaussian pair tail | `plainC c 1` | NEW (shape A, window part as a Finset `if`) |
| `E6Bridge20.lean:186-193, 221-286` (the `u` of `exists_ball_rest`) | `restTerm s0 w` uniformly on a ball | `13/4 + 2(|Im s0|+1)^2` | NEW (shape A, uniform-in-w face) |
| `E6Bridge22.lean:49-69` (`lcTerm`, `summable_lcTerm`) | `m/(1+(Im rho - a)^2)` | `13/4 + 2 a^2` | NEW (shape A, h = 0) |
| `E6Bridge24.lean:815-821` (`tsum_lcTerm_le`) | same, tsum comparison | | NEW (shape A) |

The per-instance kernel content is one two-variable rational inequality in
`(x, y) = (Re rho, Im rho - a)` on the strip `0 < x < 1`, `y^2 >= h^2`, e.g.
`1/(x^2+y^2) <= (9/4)/(1 + y^2 + (1/2-x)^2)` (`E6Bridge19.lean:120-133`, `572-583`;
`E6Bridge15.lean:360-372` re-proves it inside `norm_liPaired_le_majorant`). Cleared and
shifted by `y^2 = 1 + t` it reads `(5/4) t + (5/4) x^2 + x >= 0`, an all-nonneg-coefficient
Polya form: COVERED by `direct_polya` / `handelman` per instance, MISS in the aggregate (seven
hand `nlinarith` closers). The absorption of the finite window is the shipped
`finite_prefix_absorption` atom (NS port) transposed from `N <= n` to "outside a finite
window"; what no kind supplies is the composite over the zero index `C` with the
`IsNontrivialZero` support and the island's majorant lemma. Section 3.1.

### 2.2 Pattern (2): Taylor-coefficient ladders and closed forms (Python-checked, Lean hand-proved)

The identities `docs/LIVALUE_TAYLOR_2026-09-21.md` checks in mpmath (dps 30) and E6Bridge19
proves by hand:

| Where | What | Verdict |
|---|---|---|
| `E6Bridge19.lean:258-270` (`coef`, `coef_succ`, `norm_coef`) | `a_k = (-1)^k (k+1)!`, `a_{k+1} = a_k (-(k+2))`, `‖a_k‖ = (k+1)!` by `Nat.factorial_succ; push_cast; ring` | NEW (shape B) |
| `E6Bridge19.lean:273-301` (`zterm`, `hasDerivAt_zterm`) | `d/ds [a_k m (s-rho)^(-(k+2))] = a_{k+1} m (s-rho)^(-(k+3))` via `hasDerivAt_zpow ... .comp ... .const_mul ... .congr_deriv` | NEW (shape B, the derivative step) |
| `E6Bridge19.lean:396-411` (`zterm_at_zero`, `tsum_zterm_zero`) | `zterm k rho 0 = (k+1)! m/rho^(k+2)` (the `(-rho)^(k+2) = (-1)^k rho^(k+2)` sign bookkeeping by `linear_combination`) | NEW (shape B, evaluation face) |
| `E6Bridge19.lean:861-872` (`dcoef`), `876-934` (`dterm`, `hasDerivAt_dterm`), `937-983` (`dbound`, `norm_dterm_le`) | the same ladder for `-2/(s+2n+2)` with `a_k = -2(-1)^k k!`, plus the uniform bound `2 k!/(n+1)^2` on the ball `B(1,1/2)` | NEW (shape B, second instance; the bound is a shape-A-style majorant over `n : N`) |
| `E6Bridge19.lean:1051-1083` (`tsum_odd_inv_pow`) | `Sum_n 1/(2n+1)^m = (1 - 2^-m) zeta(m)` for `m >= 2` by `tsum_even_add_odd` | NEW (shape B, parity atom); no `dirichlet`-family kind covers the odd/even split |
| `E6Bridge19.lean:1086-1120` (`iteratedDeriv_psiHalf`) | `d^(k+1)/ds^(k+1) psi(s/2)` at 1 `= -2(-1)^(k+1)(k+1)!(1-2^-(k+2)) zeta(k+2)` | NEW (shape B, the tower closed form) |
| `E6Bridge19.lean:1123-1145` (`archCoeff_zero`, `archCoeff_succ`) | `A_0 = -(log pi)/2 - log 2 - gamma/2`, `A_{k+1} = (-1)^(k+2)(1-2^-(k+2)) zeta(k+2)` by `field_simp; ring` | NEW (shape B) |
| `E6Bridge19.lean:1219-1221` (`iteratedDeriv_one_div`) | `iteratedDeriv k (1/s) 1 = (-1)^k k!` from `iter_deriv_inv` | NEW (shape B, elementary piece) |
| `E6Bridge19.lean:1224-1236` (`taylorOne_eq`) | `taylorOne k = (-1)^k + archCoeff k - eta k` by `iteratedDeriv_add` on the three analytic pieces | NEW (shape B, linear assembly) |
| `E6Bridge19.lean:1243-1267` (`iter_deriv_comp_add_const`, `taylorZero_eq`) | Taylor data at 0 from data at 1 via `f(s) = -g(-s)`: `taylorZero k = (-1)^(k+1) taylorOne k` (`iteratedDeriv_comp_neg` + shift) | NEW (shape B, symmetry transfer) |
| `E6Bridge19.lean:1284-1294` (`liKernel_re`), `1297-1317` (`liPaired_eq_sum`, `liLimit_eq_sum`) | binomial expansion through `Complex.re` and the tsum | COVERED (`identity` for the coefficient identity), BESPOKE (`re_sum`, `Summable.tsum_finsetSum`) |
| `E6Bridge19.lean:1329-1341` (`sum_choose_alt`) | `Sum_{m<n} C(n,m+1)(-1)^m = 1` from `Int.alternating_sum_range_choose_of_ne` | COVERED (`wz` / `identity` with symbolic n), BESPOKE (Mathlib lemma is the certificate) |
| `E6Bridge19.lean:1344-1372` (`sum_choose_eta`, `sum_choose_archCoeff`), `1375-1391` (`liValue_of`) | reindexing `range n` onto `Icc 1 n` / `Icc 2 n` (`sum_Ico_eq_sum_range`) and the split into the RHDefs form | NEW (shape B, the finite-sum rearrangement face; a "reindex certificate" `(shift, first-term peel)`) |
| `E6Bridge15.lean:280-294` (`liKernel_eq_sum`, `sum_choose_succ_le`) | `K_n = -Sum C(n,m+1)(-1/rho)^(m+1)` by `add_pow`; `Sum_{m<n} C(n,m+1) <= 2^n` | COVERED (`identity`), BESPOKE (`Nat.sum_range_choose`) |

Section 3.2. The certificate discipline is the one `fwd_telescope` already uses (one-step
identity checked exactly, closed form by induction in Lean); the continuous analogue
(iterated derivatives of `(s-a)^-p` families) is not built.

### 2.3 Pattern (3): fibrewise regrouping of a zero sum by the ceiling of the ordinate

| Where | What | Verdict |
|---|---|---|
| `E6Bridge23.lean:35-50` (`one_add_sq_le_of_ceil`) | `1 + k^2 <= 4(1 + x^2)` on `ceil x = k` (two integer cases, `nlinarith [sq_nonneg (3k-4)]`) | COVERED (`handelman` on `k-1 < x <= k` per sign case), MISS |
| `E6Bridge23.lean:52-59, 75-96` | fibre weight `4/(1+k^2)`; the fibre's multiplicity sum `<= Ncount (a+k-1) (a+k)` (vocabulary bridge `zeroMult_cast_eq`) | NEW (shape C) |
| `E6Bridge23.lean:101-162` (`wt`, `wlog`, `summable_wt`, `log_add_four_le`, `log_div_le_rpow`, `summable_wlog`) | the weighted-count series over `Z`; tail majorant `log(y+4)/(1+y^2) <= 6 y^(-3/2)` from `log t <= t - 1` at `t = sqrt(y+4)` and `y + 4 <= 9y` | NEW (shape C); the log bound is a `transcendental_enclosure` log-face fold-in (`log y <= c y^alpha`) |
| `E6Bridge23.lean:169-181` (`wcount_le`) | `log(|a|+|k|+4) <= log(2+|a|) + log(|k|+4)` via `Real.log_mul` + a Polya product inequality | COVERED (`log_combination` monotone route), MISS |
| `E6Bridge23.lean:198-244` (`sum_lcTerm_le`) | `Finset.sum_fiberwise_of_maps_to` over `g = ceil(Im rho - a)`, per-fibre chain, `sum_le_tsum` | NEW (shape C, the skeleton) |
| `E6Bridge23.lean:253-270` (`tsum_wcount_le`, `local_count_sum`) | `Real.tsum_le_of_sum_le` + `C := 4 A0 (S1 + S2)` | NEW (shape C, assembly) |
| `E6Bridge24.lean:60-77` (`sum_le_Ncount`), `80-130` (`window_sum_le_five`), `133-156` (`exists_window_bound`) | a width-4 window covered by five unit windows (`Finset.Icc (-3) 1`, `single_le_sum` + `sum_comm` + `sum_filter`, `card = 5 := by decide`) | NEW (shape C, finite face) |

Section 3.3.

### 2.4 Pattern (4): the entire extension by pole cancellation (removable singularities)

| Where | What | Verdict |
|---|---|---|
| `E6Bridge20.lean:301-306` (`exists_unit_factor`), `E6Bridge24.lean:310-334` (`logDeriv_xi_local`) | `xi = (z-s0)^m u` from `analyticOrderAt_eq_natCast`; `logDeriv xi = m/(z-s0) + logDeriv u` on the punctured ball (`logDeriv_mul`, `logDeriv_fun_pow`) | DISCIPLINE; duplicated |
| `E6Bridge20.lean:317-373` (`deriv_logDeriv_xi_local`) | `deriv (logDeriv xi) w = -m/(w-s0)^2 + deriv (logDeriv u) w`, with the `m = 0` branch separate | DISCIPLINE |
| `E6Bridge20.lean:378-414, 420-455` (`exists_local_form`, `xiDiffExt`, `xiDiffExt_eventuallyEq`, `xiDiffExt_differentiable`) | `if IsNontrivialZero s then limUnder (nhds[≠] s) f else f s`; `=ᶠ H` with `H` differentiable; `Filter.Tendsto.limUnder_eq` | DISCIPLINE (generic lemma candidate `differentiable_of_punctured_eventuallyEq`) |
| `E6Bridge24.lean:288-444` (`FwinExt`, `FwinExt_eventuallyEq_at_zero`, `FwinExt_differentiableOn`) | the same construction for `logDeriv xi - Sum_{window} m/(w-rho)` on the disc `D(s,1/2)`, with `Finset.add_sum_erase` for the cancelling term | DISCIPLINE; second verbatim instance |

Not certificate-shaped: the data are Mathlib's `analyticOrderAt` and a `Finset.erase`. What a
numeric channel would need is nothing; what a Lean prelude would need is the one generic lemma
"a function agreeing off a closed discrete set with locally differentiable functions, extended
by punctured limits, is differentiable", instantiated twice here.

### 2.5 Pattern (5): termwise differentiation and analyticity of a tsum on a ball

| Where | What | Verdict |
|---|---|---|
| `E6Bridge19.lean:180-199` (`iteratedDeriv_tsum_ball`), `203-213` (`analyticAt_tsum_ball`) | generic: `g (k+1) i` the derivative of `g k i` on the ball, uniform summable bounds `u k` ⟹ `iteratedDeriv k (Sum g 0) = Sum g k` (induction + `hasDerivAt_tsum_of_isPreconnected`) | DISCIPLINE (generic Mathlib-level lemma; consumer of shapes A and B) |
| `E6Bridge19.lean:424-437` (zero series), `988-996` (digamma series), `1540-1551` (again for continuity at 0) | three instantiations | consumers |
| `E6Bridge20.lean:194-286` (`differentiableOn_tsum_of_summable_norm`), `E6Bridge21.lean:100-116` (`continuousOn_tsum`) | the first-derivative / continuity versions | consumers |

A certificate emitter for an instance is exactly shape B (the term ladder with its derivative
step) plus shape A (the uniform majorant); the generic lemma belongs in an island prelude or
upstream.

### 2.6 Pattern (6): Liouville with logarithmic growth and the constant pinned along a ray

| Where | What | Verdict |
|---|---|---|
| `E6Bridge18.lean:271-321` (`eq_const_of_log_growth`) | `‖G z‖ <= C(1 + log(2+‖z‖))` entire ⟹ constant: Cauchy on `sphere z R`, `C(1+log(2+a+R))/R -> 0` via `Real.tendsto_pow_log_div_mul_add_atTop`, `is_const_of_deriv_eq_zero` | FOLD-IN (`cauchy_deriv`, section 4.3); single instance but a named textbook atom |
| `E6Bridge18.lean:331-353` (`xi_logDeriv_deriv_eq_of`) | constant `= 0` by the real-axis limit (`tendsto_nhds_unique` against `tendsto_const_nhds`) | DISCIPLINE |
| `E6Bridge18.lean:253-266`, `E6Bridge21.lean:291-304` | the two Tannery decays (`tendsto_tsum_of_dominated_convergence` against the `sigma = 2` terms / the majorant) | DISCIPLINE (pattern 8) |

### 2.7 Pattern (7): the strip derivative bound (divide out window zeros, Cauchy, Landau ball vs window)

| Where | What | Verdict |
|---|---|---|
| `E6Bridge24.lean:479-492` (`exists_radius`) | a radius in `(1/4, 1/2)` whose circle avoids the finitely many window zeros (`Set.Ioo_infinite ... .exists_notMem_finset` on the image of `dist`) | DISCIPLINE (pattern 9, finite avoidance) |
| `E6Bridge24.lean:495-500` (`norm_deriv_FwinExt_le`), `788-810` (`target_bound_high`) | `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` at the existential radius; `B/r <= 4B` by `div_le_iff₀` + `nlinarith` | COVERED (`cauchy_deriv`, A4), BESPOKE (existential radius; the emitter emits at concrete `R`) |
| `E6Bridge24.lean:160-201` (`norm_log_le`, `norm_digamma_le_log`) | `‖psi z‖ <= log(2+|Im z|) + pi + 7/2` for `0 < Re z <= 2`, `|Im z| >= 1` from `StirlingVert.digamma_stirling` + `‖log z‖ <= log‖z‖ + pi` | DISCIPLINE (Zeta23 black box + triangle assembly) |
| `E6Bridge24.lean:210-280` (`landau_window`) | Zeta23's `zeta_logDeriv_partial_fraction` re-vocabularised (`analyticOrderNatAt` -> `zeroMult`, `22/25 * 91/50 <= 161/100`, `8/5 <= 22/25 * 91/50` by `norm_num`) | BESPOKE (seam) |
| `E6Bridge24.lean:583-600` (`hsplit`, `hFwin`) | `Sum_Z - Sum_W = Sum_{Z\W} - Sum_{W\Z}` by two `Finset.sum_sdiff` + `linear_combination` | DISCIPLINE |
| `E6Bridge24.lean:607-613` (`e1`), `653-679` (`e4`), `684-712` (`e5`) | distance-floor sums: `‖Sum_S m/(w-rho)‖ <= (1/d) Sum_S m` with `d = 3/2` (outside the window, `|Im rho - Im s| > 2`) and `d = 1/10` (outside Landau's ball) | FOLD-IN (`far_pole_sum`, section 4.4) |
| `E6Bridge24.lean:614-643` (`e2`), `649-652` (`e3`), `644-648`, `680-683` (`hlogw`, `hlogs`) | log rebasing `log(|Im w| + 3) <= L + log 2`, `log(|Im s|+6) <= L + log 3` with `L = log(2+|Im s|)` | COVERED (`log_combination` monotone route), MISS |
| `E6Bridge24.lean:540-541` (`le_mul_one_add`), `714-747` | `a + b L <= (a + b)(1 + L)`; the five-piece triangle chain (`norm_add_le` x4 under `gcongr`) then `linarith [e1..e5]` | FOLD-IN (`magnitude_split` affine-budget mode, section 4.2) |
| `E6Bridge24.lean:504-536` (`window_one_sub`, `Fwin_one_sub`), `751-785` (`sphere_bound`) | the reflection half: `window (1-s) = image (1 - .) (window s)`, `Fwin (1-s) (1-w) = -Fwin s w`, dispatch on `Re w >= 1/2` | DISCIPLINE (pattern 7, involution transport) |
| `E6Bridge24.lean:823-858` (`target_bound_low`), `E6Bridge22.lean:208-215` (`growth_compact`) | `IsCompact.bddAbove_image` of the continuous norm on a rectangle `Icc x Icc` | DISCIPLINE (pattern 10) |
| `E6Bridge24.lean:863-872` (`stripDerivBound`), `E6Bridge22.lean:305-334` (`xiDiffExtGrowthRight_of`) | region cover with `C := max 0 (max CA (max CB CC))` and `log(2+|Im s|) <= log(2+‖s‖)` | FOLD-IN (`eventual_threshold` nested-max witness, section 4.2) |

### 2.8 Pattern (8): the right half-plane, trigamma and Dirichlet constants

| Where | What | Verdict |
|---|---|---|
| `E6Bridge21.lean:169-188` (`sum_range_inv_sq_le`) | `1/a^2 <= 1/(a-1/2) - 1/(a+1/2)` telescoped: `Sum_{i<N} 1/(x+i)^2 <= 1/(x-1/2) - 1/(x+N-1/2)` | FOLD-IN (`fwd_telescope` majorant mode, section 4.1) |
| `E6Bridge21.lean:190-205` (`summable_inv_sq_real`, `tsum_inv_sq_real_le`) | `summable_of_sum_range_le`, `Real.tsum_le_of_sum_range_le` | FOLD-IN (same) |
| `E6Bridge21.lean:78-116` (`norm_trigTerm_le`, `summable_trigBound`) | `‖1/(w+n)^2‖ <= 1/(n+1/2)^2` on `Re w >= 1/2`; comparison to `4/(n+1)^2` by `nlinarith` | COVERED (`monotone_tail` / `direct_polya`), MISS |
| `E6Bridge21.lean:132-165` (`hasSum_trigamma_of_re_pos`) | the series across the positive integers by continuity of both sides on the punctured neighbourhood (`eq_of_intCast_near`) | DISCIPLINE (pattern 11, punctured-identity continuity) |
| `E6Bridge21.lean:277-287` (`norm_term_le_of_two_le`) and `E6Bridge22.lean:407-417` (`norm_term_le_of_two_le_re`) | `‖term f s n‖ <= ‖term f 2 n‖` for `Re s >= 2` (`rpow_le_rpow_of_exponent_le`) | COVERED (`rpow_budget`), MISS; duplicated real/complex |
| `E6Bridge21.lean:330-370` (`deriv_logDeriv_xi_real`) and `E6Bridge22.lean:352-391` (`deriv_logDeriv_xi_of_one_lt_re`) | the termwise derivative `-1/s^2 - 1/(s-1)^2 + (1/4) psi'(s/2) + (zeta'/zeta)'` (four `HasDerivAt` pieces, `hev.deriv_eq`, `ring`) | DISCIPLINE; duplicated real/complex (the real one is the complex one at `s = sigma`) |
| `E6Bridge22.lean:439-472` (`rightDerivBound`) | `1/4 + 1 + (1/4) T + L2` by `e1..e4` and a triangle chain; `‖-1/s^2‖ <= 1/4` from `‖s‖ >= 2` by `div_le_div_iff₀; nlinarith` | COVERED (`magnitude_split` nterm + `disk_coord`), MISS |

### 2.9 Pattern (9): B7 convergence, pairing and the forward half

| Where | What | Verdict |
|---|---|---|
| `E6Bridge15.lean:99-121` (`isNontrivialZero_conj`, `zeroMult_conj`) | conjugation symmetry of the divisor (`analyticOrderAt_zeta_conj`) | BESPOKE (seam) |
| `E6Bridge15.lean:144-149` (`conjEquiv`), `227-259` (`liZeroSum_eq_tsum_paired`) | reindex the window tsum by `conj`, `F + conj F = 2 Re F`, `mul_left_cancel₀` | DISCIPLINE (pattern 7; sibling audit D section 2.5 has the same involution regrouping on the li island) |
| `E6Bridge15.lean:298-333` (`abs_re_liKernel_le`), `E6Bridge19.lean:471-484` (`abs_re_inv_pow_le`) | the `j = 1` pairing trick: `|Re(1/rho)| = Re rho/|rho|^2 <= 1/|rho|^2`; `j >= 2` by `|rho| >= 1`; sum `<= 2^n/|rho|^2` | DISCIPLINE (the analytic reason the symmetric order converges); twice |
| `E6Bridge15.lean:415-433` (`liZeroSum_tendsto`) | Tannery for indicator sums `windowSet T` (`eventually_atTop` at `T >= |Im rho|`) | DISCIPLINE (pattern 8) |
| `E6Bridge15.lean:452-491`, `E6Bridge17.lean:197-217` | forward halves under RH: on the line `|1 - 1/rho| = 1`, every paired term `>= 0`; `Complex.re_tsum` + `tsum_nonneg` | DISCIPLINE (trivial; `li_positivity` ships the rung form, not this) |
| `E6Bridge19.lean:610-639` (`integral_zterm_zero`), `665-689` (`hasSum_integral_zterm`), `692-726` (`tsum_inv_add_inv_one_sub`) | FTC for `m/(sigma-rho)^2` on `[0,1]` (antiderivative `-m (z-rho)^-1`), the countable-subtype interchange `intervalIntegral.hasSum_integral_of_dominated_convergence`, `logDeriv xi 1 - logDeriv xi 0` | DISCIPLINE (pattern 8; the countable reindexing `zeros_countable` is duplicated in `E6Bridge17.lean:786-797`) |
| `E6Bridge19.lean:729-780` (`refTerm`, `tsum_refTerm`) | the antisymmetric family under `reflect` sums to 0 (`reflectEquiv.tsum_eq`, `linear_combination (1/2) * h`) | DISCIPLINE (pattern 7) |
| `E6Bridge19.lean:756-773` | `1/(1-rho) - 1/conj rho = (2 Re rho - 1)/((1-rho) conj rho)`, `‖2 Re rho - 1‖ <= 1`, `|Im rho|^2 <= ‖1-rho‖ ‖rho‖` | COVERED (`rational_identity` for the fold, `disk_coord` for the norm floors), MISS |

### 2.10 Pattern (10): the sharp envelope and the Theta face (E6Bridge16, E6Bridge17)

| Where | What | Verdict |
|---|---|---|
| `E6Bridge16.lean:341-347` (`e^-6 <= 1/400`), `776-782` (`e^-16 <= 1/8000000`), `681-685` (`1.648 <= e^(1/2)`), `348-350` (`sqrt(2 pi) <= 2.51`), `770-772` (`sqrt 2 <= 1.5`), `783-790` (`log pi <= 1.3863`), `467` (`pi^2/6 <= 2`) | seven hand transcendental numerics off `exp_one_gt_d9`, `pi_lt_d2`, `log_two_lt_d9` with `nlinarith [pow_le_pow_left₀ ...]` | COVERED (`exp_enclosure` for the four `exp` brackets, `algebraic_bracket` / `bracket` for the two square roots, `transcendental_enclosure` log face and `log_combination` for `log pi`, `exact_fact` for `pi^2/6`), MISS x7. The emitter outputs are byte-shaped like these `have`s |
| `E6Bridge16.lean:315-317` (`y e^-y <= 1`), `352-364` (`sqrt lam e^(-lam/2) <= 1`), `E6Bridge17.lean:129-141` (`min(1, 2 lam)(1+x^2) e^(-2 lam x^2) <= 1`), `E6Bridge16.lean:435` (`abs_one_sub_two_mul_exp_le`, from E6Bridge11) | "polynomial times `exp(-rate)` is at most a constant" via `Real.add_one_le_exp` | FOLD-IN (`poly_exp_absorption` shifted-rate mode, section 4.5) |
| `E6Bridge16.lean:295-386` (`norm_poles_le`) | the pole-term bound `(c^2+1/4) e^(-2 lam (c^2-1/4)) <= 0.13 A` for `c^2 >= 6/lam + 1`: a chain of five exp inequalities and the numerics above | COVERED in pieces (`poly_exp_absorption`, `exp_enclosure`, `direct_polya` for `c^2 + 1/4 <= (5/4) c^2`), MISS; the chain is a `MagnitudeSplit`-free product chain |
| `E6Bridge16.lean:405-449` (`primeAbsTerm_le`) | `Lambda(n)/sqrt n <= 2` (`vonMangoldt_le_log`, `log n <= 2 sqrt n`), `|1-2s| e^-s <= 2 e^(-s/2)`, `e^(-s/2) <= e^(16 lam)/n^2` by `nlinarith [sq_nonneg (log n - 16 lam)]` | COVERED (`transcendental_enclosure` log face; `direct_polya` for the completed square), MISS |
| `E6Bridge16.lean:461-469` (`primeAbs_le_crude`) | `Sum 4 e^(16 lam)/n^2 = 4 e^(16 lam) pi^2/6 <= 16 e^(16 lam)` (`hasSum_zeta_two`) | COVERED (`exact_fact` + `identity`), MISS |
| `E6Bridge16.lean:272-291` (`norm_gaussTest_half`), `282-290` (`(s i - c)^2` real/imag split with `I_sq`) | complex-square bookkeeping at `s = ±1/2` | COVERED (`identity`), BESPOKE (cast plumbing) |
| `E6Bridge16.lean:58-151` (`integral_sq_mul_cexp_gaussian_fourier'`), `171-246` (`fourier_autocorrGauss`) | the second Gaussian moment at a complex frequency by parts (`integral_mul_deriv_eq_deriv_mul_of_integrable`), solved by `linear_combination -key`; the transform of the autocorrelation | DISCIPLINE (Mathlib `fourierIntegral_gaussian`; the majorant `|x|^2 e^(-a x^2 + |Im w||x|)` is E6Bridge8's) |
| `E6Bridge16.lean:222-227` (`hE`), `E6Bridge17.lean:519-526` (`heat_A_eq`), `529-554` (`heat_integrand_eq`), `603-614` (`hexp`) | Gaussian exponent completing-the-square identities with real parameters and nonvanishing side conditions (`lam ≠ lam'`), closed by `push_cast; field_simp; ring` | COVERED (`rational_identity`), MISS; the `C`-coefficient cast plumbing is the bespoke residue (section 4.6) |
| `E6Bridge16.lean:563-598` (`integral_indicator_bumpR_tail_le'`) | tail mass beyond `|r-c| >= L`: `(r-c)^2 e^(-2 lam (r-c)^2) <= e^(-lam L^2) (r-c)^2 e^(-lam (r-c)^2)` pointwise, `integral_mono` | DISCIPLINE (the pointwise step is `poly_exp_absorption`-adjacent) |
| `E6Bridge16.lean:602-647` (`integral_bumpR_mul_psiR_ge_capped`) | capped floor: a piecewise linear minorant `Theta bump - (Theta+5) indicator` under `bump psi`, `integral_mono` | DISCIPLINE (a "capped-minorant integral" assembly) |
| `E6Bridge16.lean:669-813` (`re_weilForm_gauss_nonneg_sharp`, `maxHeartbeats 1600000`) | the assembly: ~25 `have`s, closed by `linarith only [h0, h1, hpoles, hJ', htailA, hprime', hΘA, hA]` after `clear_value` | COVERED (`cone` / Farkas: the final step is a nonneg linear combination of eight named bounds), MISS for the closer; the `have`s are the misses above |
| `E6Bridge17.lean:109-158` (`norm_plainGauss_mul_le`) | `‖G‖(1+|z|^2) <= e^(lam/2)(2c^2+13/4)/min(1,2 lam)`: `hA : 1 + (x+c)^2 + y^2 <= (2c^2+13/4)(1+x^2)` by `nlinarith` with five hints, the `min` case split | COVERED (`direct_polya` / `bilinear_corner` for `hA`; `dichotomy_glue` for `min`), MISS |
| `E6Bridge17.lean:222-245` (`exists_lam_cos_neg_one`) | `lam = (pi + 2 pi k)/(4xy) >= lam_0` with `cos = -1` (`exists_int_lt/gt`, sign split on `4xy`) | DISCIPLINE (phase selection; already in E6Bridge7's converse) |
| `E6Bridge17.lean:251-263` (`exists_generic_centre'`) | a centre in an open interval avoiding a finite bad set (`Set.Ioo_infinite ... sdiff ... nonempty`) | DISCIPLINE (pattern 9) |
| `E6Bridge17.lean:558-625` (`plainGauss_heat`), `629-653` (`real_gauss_heat`) | the Gaussian convolution via `integral_cexp_quadratic`, prefactor `sqrt(lam/lam') (1/sqrt(2 pi sigma2)) sqrt(pi/A) = 1` by `Real.sqrt_eq_one; field_simp; ring` | DISCIPLINE; the prefactor identity is a `rational_identity` under square roots (`sqrt_root_elimination` shape), MISS |
| `E6Bridge17.lean:677-750` (`integral_norm_heatF_le`), `753-783` (`summable_integral_norm_heatF`), `819-873` (`theta_heat`) | the integral-tsum interchange `integral_tsum_of_summable_integral_norm` over the countable subtype `NZ`, with the real-part plumbing (`integral_re`, `Complex.re_tsum`) | DISCIPLINE (pattern 8); the majorant is shape A |

### 2.11 Pattern (11): NoRealZeroInUnitInterval (E6Bridge25)

| Where | What | Verdict |
|---|---|---|
| `E6Bridge25.lean:40-61` (`norm_tail_integral_le`) | `‖int_1^inf (floor x + 1/2 - x) x^(-sigma-1)‖ <= (1/2) int x^(-sigma-1) = 1/(2 sigma)` (`norm_integral_le_of_norm_le`, `integral_Ioi_rpow_of_lt`) | DISCIPLINE; the sibling audit D notes the same sawtooth bound on both islands (`E6Bridge28` sharp sawtooth, `LowHeightBox`) |
| `E6Bridge25.lean:64-91` | `Re zeta(sigma) = 1/2 - 1/(1-sigma) + sigma Re J`, `sigma Re J <= 1/2`, `1 < 1/(1-sigma)` ⟹ `< 0` | COVERED (`direct_polya` for the one-variable sign), BESPOKE (the `Zeta0EqZeta` unfolding) |

## 3. Ranked NEW SHAPE candidates

Selection principle as in the roadmaps: deterministic search-free tactics (`ring`,
`positivity`, `nlinarith` with emitted hints, `linarith`, `norm_num`, `push_cast`), exact
arithmetic in the generator, the kernel as the only gate. All three are island-pinned to the
rvm_bridge vocabulary (`WeilExplicit.zeroMult`, `IsNontrivialZero`, `gammaOf`,
`RvMBridge6.summable_mult_div_one_add_normSq`, `zetaSeam.finite_window`, `Ncount`); shape B
has a Mathlib-only core.

### 3.1 Shape A (rank 1): `ZeroSumMajorantEmitter`, kind `zero_sum_majorant`

**Statement family.** For a term family `f p : C -> C` with parameters `p` (a point `s`, a
centre `a`, a Taylor index `k`, a Li index `n`, a width `lam`), a centre expression `a(p)`, a
near-radius `h in {0, 1, 2}` and a far constant `C_far(p) >= 0`:

    Summable (f p)   and   forall rho, ‖f p rho‖ <= zeroBound (C_far p) (b p) rho,

where `zeroBound C b rho := (nearWindow a h).indicator b rho + m(rho) * (C / (1 + normSq (gammaOf rho)))`
is the abstract atom of `E6Bridge19.lean:109-117` with the window `{IsNontrivialZero} ∩ {|Im rho - a| < h}`
(for `h = 0` the window is empty and the indicator term is dropped, as in `lcTerm`).

**Certificate (untrusted).** (a) the support fact `f p rho = 0` off `IsNontrivialZero` (the
generator names the `zeroMult_eq_zero_of_not_nontrivial` rewrite that closes it); (b) the
pointwise far inequality reduced to base variables: with `x = Re rho in (0,1)`,
`y = Im rho - a`, `y^2 >= h^2`, the polynomial inequality

    C_far(p) * D(x, y) - N(x, y) * (1 + y^2 + (1/2 - x)^2 + (Im-shift terms)) >= 0

for the instance's `‖f‖ = m * N/D` shape, certified as an all-nonneg-coefficient Polya form
after the domain shift `x -> x`, `y^2 -> h^2 + t` (the 9/4, `13/4 + 2 a^2`, 4 and 2 constants of
section 2.1 all pass; sympy `expand` + coefficient sign check, `handelman` fallback); (c) the
near-window bound `b p` (any explicit expression; the emitter only needs its nonnegativity for
the `indicator` case, `E6Bridge19.lean:164-166`).

**Lean skeleton** (parameterised copy of `E6Bridge19.lean:147-175` and `331-355`):

    theorem <name>_le (<params>) (rho : C) : ‖<f p> rho‖ <= zeroBound <C_far> <b> rho := by
      refine norm_le_zeroBound (fun rho h => <support_lemma> h) ?_ ?_ (by positivity) rho
      · intro rho h _; exact <near bound, often le_rfl with b := ‖f rho‖>
      · intro rho h him
        rw [<norm_unfold>]
        have hx := h.2.1; have hx1 := h.2.2
        have hy : (h:R)^2 <= (rho.im - a)^2 := <from him>
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [<emitted hint list>]                -- or: rw [<polya identity>]; positivity
    theorem <name>_summable (<params>) : Summable (<f p>) :=
      Summable.of_norm_bounded (summable_zeroBound _ _) (<name>_le _)

The prelude (`zeroBound`, `summable_zeroBound`, `norm_le_zeroBound`, `summable_of_zeroBound`,
generalised from `|Im rho| < 1` to a centred window of radius `h`) is emitted once per file.

**Refusal conditions (phantoms).** `C_far < 0`; the Polya/Handelman check fails (report the
located negative point, e.g. `h = 0` with a `1/|rho|^2` shape is refused because `|rho|` is not
bounded below on the zeros); the support fact is not a hypothesis-free rewrite; the near window
is not a bounded ordinate window (the finiteness comes only from `zetaSeam.finite_window`); a
term family whose norm is not of the form `m * N/D` with `D > 0` off the pole (a phantom: no
`Summable` claim survives a zero denominator).

**Instances.** The ten rows of section 2.1: `E6Bridge15.lean:349-410`, `E6Bridge18.lean:116-184`,
`E6Bridge19.lean:324-355`, `586-595`, `743-773`, `E6Bridge17.lean:266-289`,
`E6Bridge20.lean:186-193, 221-286`, `E6Bridge22.lean:49-69`, `E6Bridge24.lean:815-821`; the
predecessors in E6Bridge6..14 (`summable_mult_div_one_add_normSq` itself, the Gaussian
summability of E6Bridge6/7) are the same shape.

**Cross-applicability.** RH: every zero sum on this island and on the li island
(`E6Bridge28`'s paired sums, audit D section 2.5) and the Zeta23 `zero_sum_inv_sq` family;
the four Tannery/dominated-convergence consumers (pattern 8) take the emitted majorant as
their `bound`. BG: the absorption half is the shipped `finite_prefix_absorption` (NS port) and
the geometric half `low_order_tail`; a BG obligation of this exact shape (a family indexed by
a discrete multiset with a local density bound) has not been located, so the cross-flow is
RH -> Telperion only. The standing order is satisfied by building it once and letting the li
island reuse it.

**Build cost.** S-M. The prelude is 70 lines already written; the generator is the Polya
checker in `emit_direct_polya` on the shifted form plus the hint-list rendering; kernel risk is
the `nlinarith` closer on degree-4 forms (all ten instances close today with <= 3 hints).

### 3.2 Shape B (rank 2): `TaylorLadderEmitter`, kind `taylor_ladder`

The channel the lead asked for: the numeric identities checked in mpmath and proved by hand.

**Statement family.** A "ladder" is a term family `t k s = a k * (L s)^(-(k + p))` with `L`
affine (`s - rho`, `s + 2n + 2`), `p >= 1`, and a first-order coefficient recurrence
`a (k+1) = a k * r k` with `r` a polynomial in `k` (`-(k+2)`, `-(k+1)`). The emitted theorems:

  (L1) the recurrence and closed form `a k = a 0 * (-1)^k * (k+p-1)!/(p-1)!` (`coef_succ`, `dcoef_succ`);
  (L2) `‖a k‖ = |a 0| * (k+p-1)!/(p-1)!` (`norm_coef`, `norm_dcoef`);
  (L3) the derivative step `HasDerivAt (t k) (t (k+1) s) s` for `L s ≠ 0` (`hasDerivAt_zterm`, `hasDerivAt_dterm`);
  (L4) evaluation at a point with sign bookkeeping `t k s0 = a 0 * (k+p-1)!/(p-1)! * m / (rho - s0)^(k+p)` (`zterm_at_zero`);
  (L5) elementary iterated derivatives at a point: `iteratedDeriv k (1/s) 1 = (-1)^k k!`, and, given an emitted
       ladder for a series `Sum_n t k n s`, the tower `iteratedDeriv (k+1) F 1 = a (k+1) * Sum_n (L_n 1)^(-(k+2))`
       with the parity atom `Sum_n 1/(2n+1)^m = (1 - 2^-m) zeta(m)` (`m >= 2`) and its shift
       `Sum_{n>=1} = ... - 1` (`iteratedDeriv_psiHalf`, `archCoeff_succ`);
  (L6) the symmetry transfer: if `F (c - s) = -F s` (or `= F s`) then
       `iteratedDeriv k F (c - s0) = (-1)^(k+1) iteratedDeriv k F s0` (`taylorZero_eq` at `c = 1`, `s0 = 1`);
  (L7) finite binomial rearrangements `Sum_{m<n} C(n,m+1) g(m) = Sum_{j in Icc 1 n} C(n,j) g(j-1)` and the
       first-term peel onto `Icc 2 n` (`sum_choose_eta`, `sum_choose_archCoeff`), with the alternating
       identity `Sum_{m<n} C(n,m+1)(-1)^m = 1` (`sum_choose_alt`).

**Certificate (untrusted).** `(p, a 0, r)` with the closed form verified symbolically
(sympy `rsolve` or induction check to `k = 0..12` plus the ratio identity
`closed(k+1)/closed(k) = r(k)` as a rational identity in `k`); for (L5) the numeric check of the
tower at `k = 0..8` against mpmath `polygamma` and `zeta` (the `LIVALUE_TAYLOR` numerics, made
part of the certificate with `require_exact` on the rational coefficients and an interval
check on the transcendental values); for (L7) the reindex data `(shift, peel)` checked
symbolically in `n` (sympy `summation` with `binomial`).

**Lean skeleton** (parameterised copies):

    def <a> (k : N) : C := <a0> * (-1)^k * ((k + <p-1>).factorial : C) / ((<p-1>).factorial : C)
    lemma <a>_succ (k : N) : <a> (k+1) = <a> k * <r k> := by
      unfold <a>; rw [Nat.factorial_succ (k + <p-1>)]; push_cast; ring
    lemma norm_<a> (k : N) : ‖<a> k‖ = ... := by
      unfold <a>; rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, ..., Complex.norm_natCast]
    lemma hasDerivAt_<t> (k : N) (<params>) {s : C} (hne : <L s> ≠ 0) :
        HasDerivAt (<t> k) (<t> (k+1) s) s := by
      have h1 := ((hasDerivAt_zpow (-((k:Z) + <p>)) _ (Or.inl hne)).comp s <hasDerivAt_L>).const_mul (<a> k * <m>)
      refine h1.congr_deriv ?_
      rw [show (-((k:Z) + <p>) - 1) = -(((k+1 : N) : Z) + <p>) by push_cast; ring, <a>_succ]; push_cast; ring
    -- (L5) parity atom, fixed:
    theorem tsum_odd_inv_pow {m : N} (hm : 2 <= m) :
        Sum' n, 1/(2*(n:C)+1)^m = (1 - 1/(2:C)^m) * riemannZeta m := <E6Bridge19.lean:1070-1083 verbatim>
    -- (L6), fixed:
    theorem iteratedDeriv_antisym {F : C -> C} {c : C} (h : forall s, F (c - s) = -F s) (k : N) (s0 : C) :
        iteratedDeriv k F (c - s0) = (-1)^(k+1) * iteratedDeriv k F s0 := <E6Bridge19.lean:1243-1267 generalised>

**Refusal conditions (phantoms).** closed form fails the ratio identity; `p <= 0` (no zpow pole,
the ladder is a polynomial and belongs to `identity`); a non-integer exponent (rpow is out of
scope); a tower claim whose numeric check disagrees at any `k <= 8` beyond `1e-25`; a (L7)
reindex whose symbolic check fails; a (L6) symmetry not supplied as a hypothesis-free theorem
(the emitter never proves the functional equation).

**Instances.** `E6Bridge19.lean:258-301` (p = 2, `r k = -(k+2)`), `396-411` (evaluation),
`861-934` (p = 1, `r k = -(k+1)`, series over `n`), `1051-1083` (parity), `1086-1145`
(tower and `archCoeff`), `1219-1236` (elementary + linear assembly), `1243-1267` (symmetry),
`1329-1372` (reindex). Also `E6Bridge21.lean:78-89`/`E6Bridge22.lean:394-404` (the trigamma
series is the `p = 2`, `k = 0` rung of the digamma ladder) and the li island's `Q_N`
Chebyshev recurrence (audit D section 2.6) as a discrete cousin.

**Cross-applicability.** Strong. P vs NP: `fwd_telescope` is the forward-difference twin
(same certificate discipline: one-step identity, induction closed form); a shared
`LadderCore` (recurrence + closed form + norm) serves both. BG: the rational generating
functions `Ztot`/`Zopen` and the `RationalIdentityEmitter` gauge rows are coefficient
extractions of exactly this kind (`iteratedDeriv` of `1/(1 - x)^p` families), and the
Kelmans cavity computations differentiate rational forms in a parameter. RH: Zeta23's
digamma tower at `1/2`, the Li face's `taylorCoeff riemannXi n` rungs (`li_positivity`
consumes `taylorCoeff`; shape B is how a closed form for it would be certified), the sharp
envelope's Stirling error terms.

**Build cost.** S-M. Two fixed atoms (parity, symmetry) plus a per-instance renderer with
three theorems; the kernel steps are `Nat.factorial_succ; push_cast; ring` and
`hasDerivAt_zpow ... congr_deriv`, both deterministic. The numeric channel reuses the
`IntervalBracketEmitter`/`exp_enclosure` bracket discipline for the transcendental
constants.

### 3.3 Shape C (rank 3): `LocalCountFiberSumEmitter`, kind `local_count_fiber_sum`

**Statement family.** For a nonnegative weight `w : R -> R`, a fibre constant `W : Z -> R`
with `w x <= W k` on `ceil x = k`, and the island's local count
`Ncount t (t+1) <= A0 * log(|t| + 3)` (Zeta23.RvM.zeta_local_zero_count), the uniform bound

    exists C, forall a, Sum' rho, m(rho) * w (Im rho - a) <= C * (1 + log (2 + |a|)),

and its finite face: for a window of width `W0` about `a`, `Sum_{window} m(rho) <= (ceil W0 + 1) * A0 * log(|a| + W0 + 2)`.

**Certificate (untrusted).** (a) the fibre domination `w x <= W k` on `(k-1, k]` as a
polynomial inequality in `(x, k)` split on the sign of `k` (`E6Bridge23.lean:35-50`: the
constant 4 for `w = 1/(1+x^2)`; the generator computes `sup_{fibre} w / W_k` exactly and
refuses `< 1`); (b) the log split `log(|a| + |k| + c) <= log(2 + |a|) + log(|k| + c)` as the
product inequality `(2+|a|)(|k|+c) >= |a|+|k|+c` (Polya in `|a|, |k|`); (c) the tail majorant
for `W k * log(|k| + c)`: an exponent `alpha > 1` and constant `K` with
`W k * log(|k|+c) <= K |k|^-alpha` for `|k| >= 1`, certified through `log y <= 2 sqrt y`-type
bounds (`E6Bridge23.lean:123-149`: `alpha = 3/2`, `K = 6`); (d) the two absolute constants
`S1 = Sum_k W k`, `S2 = Sum_k W k log(|k|+c)` as named tsums with summability from (c); (e)
for the finite face, the cover `Finset.Icc (-(ceil W0 + 1)) (ceil W0 - 1)` and its card by `decide`.

**Lean skeleton** (parameterised copy of `E6Bridge23.lean:198-270` and `E6Bridge24.lean:80-156`):

    theorem <name>_finite_sum_le (A0) (hA0) (hloc) (a) (u : Finset C) :
        Sum_{rho in u} m rho * w (rho.im - a) <= Sum' k : Z, wcount A0 a k := by
      classical
      set u' := u.filter IsNontrivialZero; set g := fun rho => ceil (rho.im - a)
      rw [<filter_support>, <- Finset.sum_fiberwise_of_maps_to (fun rho h => Finset.mem_image_of_mem g h)]
      refine (Finset.sum_le_sum fun k _ => ?_).trans ((summable_wcount ..).sum_le_tsum _ (fun k _ => wcount_nonneg ..))
      calc _ <= W k * Sum_{fibre} m := Finset.sum_le_sum (fun rho h => <fibre_weight> ...) ...
           _ <= W k * Ncount (a + k - 1) (a + k) := mul_le_mul_of_nonneg_left (sum_zeroMult_fiber_le ..) (by positivity)
           _ <= wcount A0 a k := <hloc + log monotonicity>
    theorem <name> : exists C, forall a, Sum' rho, ... <= C * (1 + log (2 + |a|)) :=
      <E6Bridge23.lean:260-270 with C := (ceil-cover constant) * A0 * (S1 + S2)>

**Refusal conditions (phantoms).** `sup_{fibre} w > W_k` for some `k` (located); `alpha <= 1`
(the weighted count series is not summable: the phantom "`Sum 1/(1+|gamma - a|) = O(log)`"
is refused, it is false); a count bound not of the form `A0 log(|t| + c)` (then (c) changes
and the emitter has no tail certificate); a weight not nonnegative (the `tsum_le_of_sum_le`
step needs it).

**Instances.** `E6Bridge23.lean:35-270` (the whole file is one instance with `w = 1/(1+x^2)`),
`E6Bridge24.lean:60-156` (finite face, `W0 = 2`, five unit windows), and the same sum at
`a = 0` in Zeta23 (`zero_sum_inv_sq`) and E6Bridge6 (`summable_mult_div_one_add_normSq`,
which is shape C without the `log` uniformity).

**Cross-applicability.** RH: any `Sum_rho 1/(1 + (gamma - t)^2) = O(log t)` reuse
(StripDerivBound windows, the far sums of E6Bridge22, the corridor bound's `log^2 T`
counts, the mirrormere Bragg window sums). BG / P vs NP: no obligation of this shape located
(sums over a discrete set with a logarithmic local density are number-theoretic); honest
verdict: RH-internal.

**Build cost.** M. The fibrewise `Finset` skeleton is mechanical; the generator's work is
(a)-(c) as three Polya checks and one `log`-bound search; kernel risk is the integer-case
`nlinarith` in (a) (closes today with one hint).

## 4. Fold-ins (sub-modes of existing emitters, not standalone)

### 4.1 `fwd_telescope` -> telescoping MAJORANT mode

`E6Bridge21.lean:169-205`: `t n <= G n - G (n+1)` with `G >= 0` gives `Sum_{range N} t <= G 0 - G N <= G 0`,
`summable_of_sum_range_le`, `tsum <= G 0`. Certificate: `G` rational (`1/(x + n - 1/2)`),
the per-step inequality Polya after clearing (`1/a^2 <= 1/(a-1/2) - 1/(a+1/2)` iff
`a^2 - 1/4 <= a^2`). `fwd_telescope` is identity-only; `ratio_telescope` is multiplicative;
`monotone_tail` needs a nonincreasing ratio. Cross-applicable to BG geometric/harmonic tails
and the P vs NP truncation tails. Build S.

### 4.2 `magnitude_split` (nterm) -> affine-in-`L` budget, and `eventual_threshold` -> region-cover max

`E6Bridge24.lean:540-541, 714-747`; `E6Bridge22.lean:229-244, 274-283`; `E6Bridge20.lean:564-583`:
per-piece `‖T_i‖ <= a_i + b_i L`, `0 <= L`, conclude `‖Sum T_i‖ <= (Sum a_i + Sum b_i)(1 + L)`
(`le_mul_one_add` is one `nlinarith`). Plus the region cover `E6Bridge22.lean:305-334`,
`E6Bridge24.lean:863-872`: from `exists C_i` on regions `R_i` covering the domain, the witness
`max 0 (max C_1 (max C_2 C_3))` with monotone transfers (`log(2+|Im s|) <= log(2+‖s‖)`,
`C_A <= C_A (1 + L)`), which is `eventual_threshold`'s nested-max chain with regions instead
of scales. Certificate: the `(a_i, b_i)` table and the region predicates. Build S.

### 4.3 `cauchy_deriv` -> Liouville with sub-linear growth

`E6Bridge18.lean:271-321`: entire `G` with `‖G z‖ <= C(1 + g(‖z‖))`, `g(R)/R -> 0`, is constant;
shipped as a fixed atom for `g = log(2 + .)` (the `Real.tendsto_pow_log_div_mul_add_atTop`
step is the only analytic content) and, optionally, `g = rpow alpha` with `alpha < 1`. Plus the
"constant pinned by a ray limit" corollary (`E6Bridge18.lean:331-353`). Build S.

### 4.4 `far_pole_sum` -> distance-floor mode

`E6Bridge24.lean:653-679, 684-712`; `E6Bridge22.lean:151-162`: for a finite (or subtype) set `S`
of poles with `dist rho w >= d`, `‖Sum_S m/(w-rho)^q‖ <= d^-q Sum_S m`, with the
symmetric-difference split `Finset.sum_sdiff` (`E6Bridge24.lean:583-591`) as the assembly.
`far_pole_sum` is the disk-geometry version (`(R - ‖z‖)^-1`); this is the same theorem with an
explicit floor. Build S.

### 4.5 `poly_exp_absorption` -> shifted-rate mode

`E6Bridge16.lean:315-317` (`y e^-y <= 1`), `352-364` (`sqrt lam e^(-lam/2) <= 1`),
`E6Bridge17.lean:129-141` (`min(1, 2 lam)(1 + x^2) e^(-2 lam x^2) <= 1`),
`E6Bridge16.lean:563-598` (the tail split `e^(-2 lam u^2) <= e^(-lam L^2) e^(-lam u^2)` for `u^2 >= L^2`):
`P(y) e^(-y) <= K` and `P(y) e^(-r y) <= K e^(-r' y)` for `r' < r` via `Real.add_one_le_exp`.
The shipped kind proves the `1/(2 lam)` rate at `(4m)^m`; the mode takes `(P, r, r')` and
emits the constant. Build S.

### 4.6 `rational_identity` -> `C`-coefficient mode with real-parameter side conditions

`E6Bridge17.lean:519-554, 603-614`; `E6Bridge16.lean:222-227, 282-290, 372-377`: exponent
completing-the-square identities in `(c, c', lam, lam', gamma)` with `lam ≠ lam'`, `lam ≠ 0`,
closed by `push_cast; field_simp; ring`; and the square-root prefactor identity
`E6Bridge17.lean:584-598` (a `sqrt_root_elimination` row). The identity checker is the shipped
one; the mode renders the `((x : R) : C)` casts and the `exact_mod_cast` nonvanishing side
conditions. Build S.

### 4.7 `transcendental_enclosure` (log face) -> `log y <= c y^alpha`

`E6Bridge23.lean:123-132` (`log(y+4) <= 6 sqrt y`), `E6Bridge16.lean:418-426`
(`log n <= 2 sqrt n`): from `log t <= t - 1` at `t = y^alpha` (`Real.log_le_sub_one_of_pos` +
`Real.log_sqrt`/`log_rpow`). Two instances, same two-line proof. Build S.

## 5. Discipline patterns and the duplication finding

### 5.1 Analytic-discipline patterns (iii), with what a certificate would need

| # | Pattern | Instances | What an emitter would need |
|---|---|---|---|
| 7 | tsum regrouping over an involution of the zero set (`conj`, `reflect`, `1 - .`) | `E6Bridge15.lean:144-149, 227-259`; `E6Bridge19.lean:381-390, 775-780, 1492-1511`; `E6Bridge20.lean:495-516`; `E6Bridge24.lean:504-536` | nothing numeric; one island lemma `tsum_reindex_involution (e : C ≃ C) (hm : forall rho, m (e rho) = m rho)`; the sibling audit D (section 2.5, li island) found the same pattern, so the lemma is cross-island |
| 8 | dominated convergence through the zero tsum (Tannery, integral-tsum, hasSum-integral) | `E6Bridge15.lean:415-433`; `E6Bridge18.lean:253-266`; `E6Bridge19.lean:665-689`; `E6Bridge21.lean:291-304`; `E6Bridge17.lean:819-873` | the shape-A majorant as the emitted `bound`; the rest is Mathlib |
| 9 | finite avoidance (a radius / centre avoiding finitely many points) | `E6Bridge19.lean:219-231` (min over the finset), `E6Bridge20.lean:159-170` (open complement), `E6Bridge24.lean:479-492` and `E6Bridge17.lean:251-263` (`Ioo_infinite` minus finset) | one island lemma `exists_mem_Ioo_notMem_finset`; three different Mathlib routes for one fact |
| 10 | compact bound of a continuous norm on a rectangle | `E6Bridge22.lean:208-215`; `E6Bridge24.lean:823-858` | one lemma `exists_bound_on_reProdIm` |
| 11 | punctured-neighbourhood identity + continuity of both sides ⟹ identity at the point | `E6Bridge19.lean:1480-1489` (factored as `eq_of_continuousAt_of_eventually_ne`), `1190-1214` (inline, same file, before the factoring), `E6Bridge21.lean:132-165` (inline), `E6Bridge20.lean:428-449` and `E6Bridge24.lean:419-432` (the `limUnder` form) | hoist the E6Bridge19 lemma to the prelude; 11 `tendsto_nhds_unique`/`eventually_nhdsWithin_iff` sites |
| 12 | the `j = 1` pairing bound `|Re(1/rho)| <= 1/|rho|^2` on the strip | `E6Bridge15.lean:298-333`; `E6Bridge19.lean:471-484` | the strip fact `0 < Re rho < 1` is the certificate; a `disk_coord`-style row |
| 13 | Landau's local partial fraction re-vocabularised | `E6Bridge24.lean:210-280` | none; a seam to Zeta23 |
| 14 | the sawtooth tail integral `|J| <= 1/(2 sigma)` | `E6Bridge25.lean:40-61`; li island `E6Bridge28` sharp sawtooth (audit D) | none; consolidate the two islands' `|floor x + 1/2 - x| <= 1/2` bounds into one lemma |
| 15 | Gaussian convolution / Fourier at a complex frequency by parts | `E6Bridge16.lean:58-151, 171-246`; `E6Bridge17.lean:558-625` | Mathlib `integral_cexp_quadratic`, `fourierIntegral_gaussian`; the exponent identity is fold-in 4.6 |
| 16 | capped-minorant integral (`Theta bump - (Theta+5) indicator <= bump psi`) | `E6Bridge16.lean:602-647` | a piecewise-linear minorant certificate; single instance, not proposed |
| 17 | forward halves under RH (`Re` of a tsum of nonneg terms) | `E6Bridge15.lean:462-491`; `E6Bridge17.lean:197-217` | none; trivial |

### 5.2 Duplication across the cluster (parallel-agent signal)

| Lemma | First | Second |
|---|---|---|
| `xi_one_sub` | `E6Bridge19.lean:62-66` | `E6Bridge20.lean:51-54` |
| `xi_eq_zero_iff` | `E6Bridge19.lean:74-85` | `E6Bridge20.lean:71-86` |
| `logDeriv_xi_one_sub` | `E6Bridge19.lean:510-521` | `E6Bridge20.lean:471-477` |
| `deriv_logDeriv_xi_one_sub` | `E6Bridge19.lean:1514-1524` | `E6Bridge20.lean:479-492` |
| `oneSubEquiv` + `zeroMult_one_sub` | `E6Bridge19.lean:1492-1501` | `E6Bridge20.lean:495-505` |
| `tsum_zero_series_one_sub` / `tsum_polTerm_one_sub` | `E6Bridge19.lean:1504-1511` | `E6Bridge20.lean:507-516` |
| `zeros_countable` / `nontrivialZeros_countable` | `E6Bridge19.lean:642-654` | `E6Bridge17.lean:786-797` |
| the local unit factor `logDeriv xi = m/(z-s0) + logDeriv u` | `E6Bridge20.lean:317-373` | `E6Bridge24.lean:310-334` |
| `norm_term_le_of_two_le` (real) / `_re` (complex) | `E6Bridge21.lean:277-287` | `E6Bridge22.lean:407-417` |
| `deriv_logDeriv_xi_real` / `_of_one_lt_re` | `E6Bridge21.lean:330-370` | `E6Bridge22.lean:352-391` |
| `1/|rho|^2 <= (9/4)/(1+|gamma|^2)` | `E6Bridge15.lean:360-372` (inline) | `E6Bridge19.lean:120-133`, `572-583` |
| the majorant-with-indicator construction | `E6Bridge15.lean:379-410`, `E6Bridge18.lean:147-184` (hand) | `E6Bridge19.lean:109-175` (abstracted), not back-ported |

E6Bridge19 and E6Bridge20 were written concurrently against the E6Bridge18 interface and
each re-proved the shared vocabulary; the honest fix is a `RvMBridgeXi` prelude module
(xi facts, involutions, majorant atom, patterns 7/9/11) that both import, then the two
emitters of shapes A and B reference it by name.

### 5.3 Standing-order misses (ordered by count)

1. Two-variable strip inequalities by hand `nlinarith` (79 calls in the cluster): the shape-A
   constants (section 2.1, seven sites), `E6Bridge22.lean:98-142`, `E6Bridge23.lean:35-50`,
   `E6Bridge17.lean:142-144`, `E6Bridge19.lean:894-983`, `E6Bridge21.lean:91-98` -- all
   `direct_polya`/`handelman`/`bilinear_corner` rows.
2. The seven transcendental numerics of `E6Bridge16.lean` (section 2.10, first row) --
   `exp_enclosure`, `algebraic_bracket`, `transcendental_enclosure`, `log_combination`,
   `exact_fact`; and `E6Bridge23.lean:123-132`, `E6Bridge16.lean:418-426` (fold-in 4.7).
3. The log rebasings `log(x + c) <= log(2 + |a|) + log c'` (`E6Bridge24.lean:644-648, 680-683`;
   `E6Bridge23.lean:172-175`; `E6Bridge20.lean:577-579`) -- `log_combination` monotone route.
4. The Gaussian exponent identities (fold-in 4.6) -- `rational_identity`.
5. `‖term f s n‖ <= ‖term f 2 n‖` -- `rpow_budget` (twice).
6. The final Farkas closers `linarith only [eight named bounds]`
   (`E6Bridge16.lean:812-813`; `E6Bridge24.lean:745-747`; `E6Bridge22.lean:463-472`) --
   `cone` / `magnitude_split` nterm.

None of these changes a theorem; each is a place where an emitted, regenerable certificate
would replace a hand proof that the next Mathlib bump may break (the `nlinarith` hint lists
are the fragile part; `E6Bridge16.lean:667` already needs `maxHeartbeats 1600000`).

## 6. The registry changes

Twenty-one rh nodes touched (`RH_bl_explicit_formula`, its three `_of_*` reductions,
`RH_li_forward_half`, `RH_li_zero_sums_converge`, `RH_livalue`, `RH_livalue_of_partial_fraction`,
`RH_local_count_sum`, `RH_no_real_zero_unit_interval`, `RH_strip_deriv_bound`, the seven
`RH_xi_*` nodes) plus six mirrormere nodes (`MM_effective_gaussian_dominance`,
`MM_effective_threshold_unbounded`, `MM_gaussian_positivity_envelope_sharp`,
`MM_rh_iff_theta_positivity`, `MM_rh_iff_theta_widths`, `MM_theta_heat_monotone`). All carry
`status = "proved"`, `via = "direct"`, `closure_clean = true`, `artifact_kind = "lean_module"`
and a blind read-back; `attempts.jsonl` records GRANTED after audit PASS for each.

Shapes verdict on the registry: no node in the rh registry carries emitter provenance (zero
`via = "emitter"` across `missions/rh/nodes/*.toml`); every proof is `direct`. The reduction
ladder (`_of_livalue` -> `_of_partial_fraction` -> `_of_strip` -> unconditional, with each
obligation a `def : Prop` and never a `sorry`) is honesty pattern 8 applied at node
granularity and is the template the skill-extraction monitor should read: each `_of_X` node
names the exact hypothesis an emitter would have to discharge. Two cosmetic flags: the
`RH_bl_explicit_formula.toml` title still contains "Stated only, NOT proved" followed by the
REDUCED chain while `status = "proved"` (a changelog in the title field; the status and
artifact are what the grant gate reads, but a substring check on the title would misfire);
and `RH_bl_explicit_formula.toml`'s `[readback]` is the 2026-09-18 statement read-back, not
the 2026-09-21 unconditional audit that `attempts.jsonl` cites.

AxiomGuard: every module RvMBridge15..27 is anchored (section 1 table), and the audit probes
(`Probes/Audit14..19_*.lean`) are in the PR. Nothing here is an emitter-generated file, so the
"never hand-edit emitted Lean" rule is not engaged.

## 7. Not re-proposed (correctly subsumed)

- `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` at a chosen radius -> `cauchy_deriv` (A4).
- `Sum_{m<n} C(n,m+1) <= 2^n`, the alternating binomial sum -> Mathlib `Nat.sum_range_choose`,
  `Int.alternating_sum_range_choose_of_ne` (`identity` with symbolic `n` at most).
- `xi_eq_zero_iff`, `analyticOrderAt_xi_eq`, `landau_window`, `hasSum_trigamma_of_re_pos` ->
  island vocabulary / Zeta23 black boxes.
- `plainGauss_heat` -> Mathlib `integral_cexp_quadratic`.
- The RH forward halves -> trivial.
- `norm_poles_le`'s chain -> pieces of `poly_exp_absorption` and `exp_enclosure` (misses, not
  a new shape).

## 8. Suggested build order

1. **Shape A `zero_sum_majorant`** -- ten instances, the prelude exists in `E6Bridge19.lean:107-175`,
   the per-instance certificate is a Polya check; the li island reuses it at once. Top pick.
2. **Shape B `taylor_ladder`** -- the Python-checked identities of `LIVALUE_TAYLOR` become a
   certificate; shares its core with `fwd_telescope` (P vs NP) and serves BG's coefficient
   extraction; two fixed atoms (parity, symmetry) plus a three-theorem renderer.
3. **Fold-in 4.1 (telescoping majorant)** -- small, cross-cutting to BG tails, closes the
   trigamma bound and the `1/(1+k^2)` comparison.
4. **Shape C `local_count_fiber_sum`** -- one instance today, but it is the uniform-in-`a`
   form of every zero-count sum the RH campaign will keep using; RH-internal.
5. Fold-ins 4.2-4.7 and the miss backfill of section 5.3 as the consuming files are next
   touched (start with the `E6Bridge16` numerics: seven `have`s, five shipped emitters).
6. The `RvMBridgeXi` prelude (section 5.2) before any of the above lands, so the emitted
   Lean references one vocabulary.

Every item discharges a recurring, currently hand-proven step in this cluster; none
duplicates a shipped emitter (checked against the 153 kinds). The kernel (cloud CI
`lake build` under the AxiomGuard) remains the sole gate. conjecture1_proved = False.
