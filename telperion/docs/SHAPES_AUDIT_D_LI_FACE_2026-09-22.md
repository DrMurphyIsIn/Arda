# Shapes audit D: the Li face (2026-09-22)

conjecture1_proved = False. Nothing in this audit bears on the Riemann Hypothesis. Every
theorem surveyed is a hypothesis-free identity, a finite real inequality, or an implication
from a named zero-localisation hypothesis; the uniform "for all n" IS RH (upstream
`li_criterion_rh_iff`) and is not touched by any file here.

Scope: the six Lean files of the Li face (PR #596 plus the two follow-on commits on
`mm/gauss-window`), read in full, classified against the ~152 registered emitter kinds
(`grep 'kind = "' src/telperion/*.py`) and the README "Certificate shapes" table, under the
cross-pollination standing order (`docs/CROSS_POLLINATION_STANDING_ORDER.md`) and the
honesty patterns (`docs/HONESTY_PATTERNS.md`). Verdict format follows
`EMITTER_ROADMAP_2026-09-02_RH_CROSSCUT.md`.

Method for each pattern: (i) COVERED by an existing kind (named; standing-order miss if it
could have been emitted, legitimately bespoke if not); (ii) NEW SHAPE (abstract statement
family, untrusted certificate data, Lean skeleton, refusal conditions, instances,
cross-applicability, build cost); (iii) analytic-discipline pattern with no certificate.

## 1. File table

| File | Lines | Island | Holds | Emitted? |
|---|---|---|---|---|
| `examples/li_positivity/lean/LiLadderHeight.lean` | 618 | li (v4.34) | paired-sum composition, polar normal form, Lemma A / A', Lemma B (angle identity, log bound, arg bounds), Theorem C (threshold `max(1, 2N/(3 pi))`), Theorem D (rate `n+1 <= 3 pi T/2`), rung 0, h4000 composition with the real-zero residual discharged | hand-written |
| `examples/li_positivity/lean/LiLadderSharp.lean` | 163 | li | Lemma A'' (window `3 pi/2 < |b| <= 2 pi`), Lemma B'' (`1/g + 1/(2g^2) <= 1/(g - 1/2)`), Theorem C'' / D'' (rate `n+1 <= 2 pi (T - 1/2)`), h4000 sharp (rungs 0..25128) | hand-written |
| `examples/li_positivity/lean/LowHeightBox.lean` | 310 | li | sharp `{x}`-kernel bound by unit-cell midpoint reflection + `hasSum_integral_iUnion`; `2 sigma <= |s-1|`; functional-equation reflection; Box 2, Box 1, real-zero exclusion | hand-written |
| `examples/li_positivity/lean/LiBoxRungs.lean` | 302 | li | pair term as `Q_N(z)`, `z = 1/(rho(1-rho))`, cofactor identities mod `w v = 1`; LP-found nonnegative certificates on the disk with multipliers `1`, `14 s`, `s^2`; rungs 0..4 hypothesis-free | hand-written (certificates found by LP offline) |
| `examples/rvm_bridge/lean/E6Bridge28.lean` | 978 | rvm (v4.33.0-rc2) | divisor symmetry, pair identity, Lemma A, Lemma B (arctan route), Theorem C / D, involution regrouping of the tsum, rung 1, sharp sawtooth bound by integration by parts, Box 1/2 from `Zeta0EqZeta`, unpaired rungs 2..5 with the `(u, e)` parametrised certificate | hand-written |
| `examples/rvm_bridge/lean/E6Bridge29.lean` | 147 | rvm | Lemma A'', Lemma B'', Theorem C'' / D'' sharp, closed form `0 <= Re(archSide N + finiteSide N)` | hand-written |
| `docs/LI_FACE_BRIEF_2026-09-21.md` | 170 | design | the campaign brief (sections 2..5 are what the six files formalize) | n/a |
| `docs/LI_FACE_SKEPTIC_2026-09-21.md` | 241 | design | 13 verdicts, 8 corrections folded in; items 5, 8, 10 changed what the formalizers built | n/a |

Cross-island duplication found (a standing-order signal in itself, section 5): six lemma
groups are proved twice, once per island, four of them Mathlib-only.

## 2. Classified findings

Verdict key: COVERED (kind), MISS = standing-order miss (an existing emitter could have
produced it), BESPOKE = covered in principle but legitimately hand-written, NEW = new shape
candidate (section 3), DISCIPLINE = analytic pattern with no certificate data.

### 2.1 Pattern (1): the pair term as `Q_N(z)` with LP-found nonnegative certificates on a disk

| Where | What | Verdict |
|---|---|---|
| `LiBoxRungs.lean:58-71` | `liPairedSummand n rho = 2 - w^(n+1) - v^(n+1)`, `w v = 1`, zpow bookkeeping by `field_simp`/`ring` | COVERED (`rational_identity`), BESPOKE (zpow cast plumbing) |
| `LiBoxRungs.lean:89-124` | `liPairedSummand (N-1) rho = Q_N(zOf rho)` closed by `linear_combination (cofactor) * hv` with `hv : w * v = 1`; cofactors hand-written at lines 98, 106, 115, 124 | COVERED (`consequence`: equation follows from `{w v = 1}` with Groebner cofactor). MISS: the cofactors are exactly what `ConsequenceEmitter` computes. Note the sibling `exp_laurent_identity` is the `exp d * exp(-d) = 1` special case of this relation |
| `LiBoxRungs.lean:128-137` | `Re Q_1`, `Re Q_2 >= 0` on the disk by `nlinarith` | COVERED (`putinar` with constant multipliers, or `handelman`-style cone over generators `d, B`), MISS |
| `LiBoxRungs.lean:139-155` | `Re Q_3 = 15 B + 4 d^3 + ... + 4 s^3` (8 monomials), multiplier `1`, generators `d = Re z - |z|^2 >= 0` (hypothesis), `B = (Im z)^2`, `s = |z|^2` (structural), identity checked in `(Re z, Im z)` by `ring`, closed by `positivity` | NEW (shape A, section 3.1). Not `handelman` (generators are quadratic, not linear forms; the identity holds only after substitution in the base variables), not `putinar` (constant not SOS multipliers, and no LHS multiplier), not `polya_zeros` (LHS multiplier there is `(sum x)^N` on the simplex), not `rational_sos` (RHS there is unconstrained SOS) |
| `LiBoxRungs.lean:157-182` | `14 s * Re Q_4 = ...` (14 monomials), multiplier `14 s`; degenerate locus `s = 0` handled by a separate branch (`z = 0`, `P = 0`, lines 177-181); division by `mul_nonneg_iff_of_pos_left` | NEW (shape A, the multiplier face) |
| `LiBoxRungs.lean:184-212` | `s^2 * Re Q_5 = ...` (18 monomials), multiplier `s^2`, same locus branch | NEW (shape A) |
| `LiBoxRungs.lean:217-236` | Box 2 gives `Re(rho(1-rho)) >= 1`, then inversion puts `z` in the disk `|z - 1/2| <= 1/2` (`inv_re`/`inv_im`/`normSq` + `div_le_div_iff_of_pos_right`) | COVERED in spirit by `halfplane_disk` (Moebius half-plane to disk core); fold-in: an "inversion face" `Re q >= c > 0 ==> |1/q - 1/(2c)| <= 1/(2c)` |
| `LiBoxRungs.lean:240-248` | `interval_cases n` dispatch over `n <= 4` | COVERED (`case_dispatch_assembly`), BESPOKE |
| `LiBoxRungs.lean:263-281` | `Re` through the tsum with a `by_cases Summable` fallback (non-summable tsum is 0) | DISCIPLINE (honest: the sign claim survives either way; the genus route in `LiLadderHeight.lean:471-481` is the load-bearing one) |

Certificate sizes (for the build estimate of shape A):

| Rung polynomial | Multiplier | Monomials in `(d, B, s)` | Degenerate locus |
|---|---|---|---|
| `Re Q_3` | `1` | 8 | none |
| `Re Q_4` | `14 s` | 14 | `s = 0` |
| `Re Q_5` | `s^2` | 18 | `s = 0` |

`Q_6` admits no such certificate and the pair term is genuinely negative at box points
(brief section 4, skeptic item 9): the emitter's refusal is a located obstruction, not a
"gave up".

### 2.2 Pattern (2): the rung-5 parametrised certificate on the rvm island

| Where | What | Verdict |
|---|---|---|
| `E6Bridge28.lean:755-807` | `1 - 1/rho = (A + i gamma)/P`, `Re K_N = 1 - Re(A + i gamma)^N / P^N`, `Re (a + b i)^N` expanded for `N = 2..5` by `simp; ring` | COVERED (`identity` / `rational_identity`), BESPOKE (complex-real bookkeeping) |
| `E6Bridge28.lean:815-866` | rungs 2, 3, 4 unpaired: `P^N - Re(A + i gamma)^N >= 0` by hand `nlinarith` with product hints, using `beta >= 0`, `1 - beta >= 0`, `gamma^2 >= 3/4` | NEW (shape A in the base variables `(beta, gamma)` with generators `beta`, `1 - beta`, `gamma^2 - 3/4`, `a = beta^2 - beta + gamma^2`); MISS in the weaker sense that `putinar` (constant multipliers, generator products) would have found these |
| `E6Bridge28.lean:894-901` | coefficient polynomials `li5c0..li5c4` in `u = beta - 1/2` (degrees 9, 7, 5, 3, 1) | generator-side data |
| `E6Bridge28.lean:903-937` | each `c_k(u) >= 0` on `[-1/2, 1/2]` by `nlinarith` with Bernstein-shaped hints `(u + 1/2)^a (1/2 - u)^b u^{2c}` plus ad hoc squares (`sq_nonneg (u + 2/35)`, `sq_nonneg (u + 1/13)`) | COVERED (`bernstein`: univariate nonneg Bernstein coefficients on `[a, b]`, with degree elevation; `handelman`'s fast path is exactly this). MISS: five hand `nlinarith` calls where five emitted Bernstein folds would be deterministic. Risk: `min c_0 = 0.27` at `u = -0.094` is positive but the ad hoc square hints suggest the needed elevation may exceed the finder's default `max_elevation = 12`; `sturm_positive` (strict, root exclusion) is the fallback |
| `E6Bridge28.lean:940-948` | `rung5_identity`: `P^5 - Re(A + i gamma)^5 = sum_k c_k(u) e^k` with `u = beta - 1/2`, `e = gamma^2 - 3 u^2 - 3/4`, by `ring` | COVERED (`handelman` on the polyhedron `{e >= 0, u + 1/2 >= 0, 1/2 - u >= 0}` in free variables `(u, e)`, composed with a `varmap`/`identity` substitution back to `(beta, gamma)`). The whole rung-5 block is a Handelman certificate whose LP the human ran by hand. MISS |
| `E6Bridge28.lean:951-969` | assembly `add_nonneg`/`mul_nonneg`/`pow_nonneg` fold over `e >= 0` (Box 2) | COVERED (`handelman` emitted tactic shape) |

Note for the registry: the two islands certify the same five rungs by two different
certificate shapes (li: paired `Q_N(z)` on the disk with a multiplier; rvm: unpaired
`Re K_N >= 0` via a Handelman certificate in `(u, e)`). Both reach exactly `N <= 5`. Shape A
subsumes both once its generator list may contain polynomial (not only linear) constraints.

### 2.3 Pattern (3): the low-height box from an integral representation

| Where | What | Verdict |
|---|---|---|
| `LowHeightBox.lean:41-77` | unit cells `[n+1, n+2)` cover `Ici 1`, pairwise disjoint, `{x} = x - (n+1)` on a cell | DISCIPLINE (measure-theory plumbing; no certificate) |
| `LowHeightBox.lean:81-90` | `(x - c)(x^{-(sigma+1)} - c^{-(sigma+1)}) <= 0` for the decreasing kernel (Chebyshev-type sign inequality) | DISCIPLINE; the analytic core, two `le_or_gt` cases + `rpow_le_rpow_of_nonpos` |
| `LowHeightBox.lean:93-100` | centred moment of a cell vanishes | COVERED (`identity`), BESPOKE (interval integral) |
| `LowHeightBox.lean:115-155` | per-cell `int {x} g <= int (1/2) g` by congruence + `setIntegral_mono_on` + the zero centred moment | DISCIPLINE ("Euler-Maclaurin first remainder sign against a monotone kernel"); lemma-pack candidate, not an emitter (no untrusted data beyond `sigma > 0`) |
| `LowHeightBox.lean:180-193` | sum the cells: `hasSum_integral_iUnion` twice + `hasSum_le` | DISCIPLINE; the "cellwise integral inequality summed by hasSum" glue is reusable as a lemma with the cell partition and the per-cell inequality as inputs |
| `E6Bridge28.lean:526-635` | the SAME bound on the rvm island by integration by parts with `G(x) = (x - m - 1/2)^2/2 - 1/8 <= 0`, adjacent-interval sums + `intervalIntegral_tendsto_integral_Ioi` | DISCIPLINE; second proof of the same Mathlib-only fact (duplication, section 5) |
| `LowHeightBox.lean:198-213`, `E6Bridge28.lean:638-651` | `norm J(s) <= 1/(2 Re s)` from the real bound by `norm_integral_le_integral_norm` + `norm_cpow_eq_rpow_re_of_pos` | COVERED in spirit by `dominated_integrability` (bounded-factor-over-complex-power on a ray); BESPOKE |
| `LowHeightBox.lean:218-240`, `E6Bridge28.lean:656-719` | at a zero, `s/(s-1) = s J(s)` (li: `zeta_fract_repr`; rvm: `Zeta0EqZeta` at `N = 1`), hence `2 sigma <= |s - 1|` | COVERED (`dirichlet_repr` is the representation; the norm step is `magnitude_split`-type linear arithmetic), BESPOKE |
| `LowHeightBox.lean:243-261` | functional-equation reflection `zeta(1 - s) = 0` (li island has no `IsNontrivialZero` API; `GammaR s` nonzero for `Re s > 0`) | DISCIPLINE (Mathlib API composition) |
| `LowHeightBox.lean:265-284`, `E6Bridge28.lean:730-750` | Box 2 from the two squared constraints by `nlinarith`: `3(sigma^2 + (1-sigma)^2) <= 2 t^2` is `hA2 + hB2` | COVERED (`cone` / `putinar` with hypothesis basis: Box 2 is the exact nonnegative combination `1*hA2 + 1*hB2 + 2*(sigma - 1/2)^2`), MISS (small) |
| `LowHeightBox.lean:288-298`, `E6Bridge28.lean:736-743` | `3/4 <= t^2 ==> sqrt 3 / 2 <= |t|` | COVERED (`algebraic_bracket`, the `sqrt` face), BESPOKE |

### 2.4 Pattern (4): termwise trigonometric lemmas and the exchange-rate case split

| Where | What | Verdict |
|---|---|---|
| `LiLadderHeight.lean:176-197`, `E6Bridge28.lean:144-165` | `g = sinh cos - cosh sin <= 0` on `[0, pi]`: `g(0) = 0`, `g' = -2 sinh sin <= 0` via `antitoneOn_of_deriv_nonpos` + a sign-product fold | NEW (shape B, section 3.2): monotone-on-interval by derivative sign, recursive (level 2) |
| `LiLadderHeight.lean:201-217`, `E6Bridge28.lean:168-186` | `cosh t cos t <= 1` on `[0, pi/2]`: `f(0) = 1`, `f' = g <= 0` | NEW (shape B, level 1 consuming level 2) |
| `LiLadderHeight.lean:220-229`, `E6Bridge28.lean:189-196` | Lemma A: `cos` antitone on `[0, pi]` + the above | DISCIPLINE (assembly) |
| `LiLadderHeight.lean:234-241` | Lemma A': `pi/2 <= |b| <= 3 pi/2` gives `cos b <= 0`, so no condition on `a` | COVERED (`dichotomy_glue`), BESPOKE |
| `LiLadderSharp.lean:46-54`, `E6Bridge29.lean:37-46` | Lemma A'': reflect `b` to `d = 2 pi - |b|` in `[0, pi/2)`, `cos b = cos d` | DISCIPLINE (periodic window reduction); fold-in candidate for shape B as an "argument reduction" preprocessing step |
| `LiLadderSharp.lean:112-121`, `E6Bridge29.lean:106-118` | the three-window split on `|b|`: `<= pi/2` (Lemma A), `(pi/2, 3 pi/2]` (cos nonpositive), `(3 pi/2, 2 pi]` (window) | COVERED (`dichotomy_glue` over declared thresholds; thresholds symbolic in `pi`), BESPOKE |
| `E6Bridge28.lean:200-207`, `LiLadderHeight.lean:303-315` | `arctan u <= u` (via `Real.lt_tan`/`le_tan`) | COVERED in spirit (`transcendental_enclosure`), fold-in: an `arctan` face |
| `E6Bridge28.lean:209-231` | `u/2 <= arctan u` on `[0, 1]` by `monotoneOn_of_deriv_nonneg` with `1/(1+x^2) - 1/2 >= 0` | NEW (shape B, level 1; the derivative sign is a `direct_polya` fact) |
| `LiLadderHeight.lean:273-300`, `E6Bridge28.lean:335-373` | `|log|u|| <= 1/(2 gamma^2)` via `log x <= x - 1` in both directions + rational inequalities | COVERED (`transcendental_enclosure` log face upper bound + `direct_polya` for `(B/A - 1) <= 1/gamma^2`), MISS (small; the rational halves) |
| `LiLadderHeight.lean:319-350`, `E6Bridge28.lean:271-308` | the angle identity `arg u = arctan(beta/gamma) + arctan((1-beta)/gamma)` (via `tan_arg`, `arctan_add`, `abs_arg_lt_pi_div_two_iff`) | DISCIPLINE (complex-argument bookkeeping; no certificate) |
| `LiLadderHeight.lean:367-403`, `E6Bridge28.lean:322-332` | lower bound on `|arg u|` (li: through `sin(arg u) = Im u/|u|` and `A B <= 4 gamma^4`; rvm: through `u/2 <= arctan u`) | DISCIPLINE; two routes to the same bound |
| `LiLadderSharp.lean:59-65`, `E6Bridge29.lean:51-56` | `1/g + 1/(2 g^2) <= 1/(g - 1/2)` for `g > 1/2` | COVERED (`direct_polya` after clearing: `(2g+1)(2g-1) <= 4 g^2`), MISS |
| `LiLadderHeight.lean:423-449`, `LiLadderSharp.lean:85-121`, `E6Bridge28.lean:380-414`, `E6Bridge29.lean:75-118` | Theorems C / C'': `N |theta| <= N/gamma <= threshold` then the split | DISCIPLINE (assembly); the rate arithmetic `N/(gamma - 1/2) <= 2 pi` is `linarith` |
| `LiLadderHeight.lean:602-609`, `LiLadderSharp.lean:154-161` | `n <= 18848 ==> n + 1 <= 6000 pi` via `pi_gt_d4`; `n <= 25128` via `pi_gt_d6` | COVERED in spirit (`transcendental_enclosure`); fold-in: a `pi` face wrapping Mathlib's `pi_gt_d2/d4/d6` |

### 2.5 Pattern (5): tsum regrouping over an involution with fixed points

| Where | What | Verdict |
|---|---|---|
| `E6Bridge28.lean:60-66` | divisor symmetry `m(1 - conj rho) = m(rho)` (restates `RvMBridge6.zeroMult_reflect`) | DISCIPLINE (island API) |
| `E6Bridge28.lean:460-477` | `HasSum f S`, reindex by `RvMBridge6.reflectEquiv` (`Equiv.hasSum_iff`), add: `HasSum (f + f o sigma) (2 S)`, then `tsum_nonneg` on pair sums; fixed points (on-line zeros) never split out | DISCIPLINE with a lemma-pack candidate: `hasSum_involution_average : HasSum f S -> (forall x, 0 <= f x + f (sigma x)) -> 0 <= S` for any `Equiv sigma` (the involution property is not even needed for the inequality). This is the analytic (tsum) version of the finite `reflection_halving` emitter, which ships the same involution as an integer `decide` instance; a `tsum` mode of `reflection_halving` would house it. No untrusted data, so not an emitter |
| `LiLadderHeight.lean:471-490`, `LiBoxRungs.lean:263-281` | li island needs no regrouping: `pairedZero` is built into the upstream `liPairedSummand` | n/a |
| `E6Bridge28.lean:776-784` | unpaired termwise `0 <= Re K_N ==> 0 <= Re liLimit N` (`by_cases IsNontrivialZero` with `zeroMult = 0` off the divisor) | DISCIPLINE |

### 2.6 Pattern (6): the Chebyshev-type recurrence for `Q_N`

| Where | What | Verdict |
|---|---|---|
| `LiBoxRungs.lean:9-14` (docstring), `42-50` | `Q_1..Q_5` listed explicitly; the recurrence is not used in the kernel | generator-side |
| the recurrence itself | With `T_N = w^N + w^{-N}` and `z = 2 - w - 1/w`: `T_{N+1} = (2 - z) T_N - T_{N-1}` (homogeneous), hence `Q_{N+1} = (2 - z) Q_N - Q_{N-1} + 2 z` (INHOMOGENEOUS: the constant term `2 z` is forced by `Q_0 = 0`, `Q_1 = z`; checked on `Q_2, Q_3, Q_4` against the listed polynomials). The form stated in the audit brief, `Q_{N+1} = (2 - z) Q_N - Q_{N-1}`, is the `T_N` recurrence, not the `Q_N` one | COVERED as a generator tool: `second_order` certifies a homogeneous three-term recurrence with a closed form; the `T_N` form fits it directly (constant coefficients in `N`, parameter `z`), the `Q_N` form needs an inhomogeneous fold-in. In the kernel nothing is needed: each `Q_N` is certified by its `consequence` cofactor (2.1). Recommended: a `chebyshev_pair_polynomial(N)` helper in the generator producing `Q_N` and its cofactor recursively, feeding `consequence` |

### 2.7 Other findings

| Where | What | Verdict |
|---|---|---|
| `LiLadderHeight.lean:77-84`, `LiBoxRungs.lean:253-260` | the hypothesis-free paired sum by composing four upstream theorems | DISCIPLINE (pure composition; the li island's first task per the brief) |
| `LiLadderHeight.lean:145-170`, `E6Bridge28.lean:109-139` | polar real part `Re(u^N + u^{-N}) = 2 cosh(N log|u|) cos(N arg u)` | DISCIPLINE (`Complex.exp_log`, `norm_mul_exp_arg_mul_I`); a companion of `unit_modulus_sos` (which handles `|u| = 1`, where this collapses to `2 cos`) |
| `LiLadderHeight.lean:452-457`, `E6Bridge28.lean:417-425` | on-line case: `|u| = 1`, term `2(1 - cos) >= 0` | COVERED (`unit_modulus_sos`), BESPOKE (uses the island's `modulus_one_minus_one_div_on_critical_line`) |
| `LiLadderHeight.lean:518-538`, `E6Bridge28.lean:496-519` | rung 0 / rung 1: `Re(1/(rho(1-rho))) >= 0`, `Re(1/rho) >= 0` by `inv_re` + `div_nonneg` + `nlinarith` | COVERED (`direct_polya` on the real-part numerator), MISS (small) |
| `LiLadderHeight.lean:553-581` | `NoRealZeroInStrip` as a named `Prop`, discharged from Box 1; conjugation via `riemannZeta_conj` | DISCIPLINE (the skeptic's item 5(b, c) made explicit; a model of the honest named-residual pattern) |
| `LiLadderHeight.lean:586-609` | h4000 composition against the capstone's conclusion shape verbatim | DISCIPLINE |
| `E6Bridge28.lean:487-492`, `E6Bridge29.lean:140-146` | closed form `0 <= Re(archSide N + finiteSide N)` via `RvMBridge27.liValue` | DISCIPLINE; the skeptic's note stands: quote its axioms from `#print axioms` on `liValue_of_two`, `local_count_sum`, `stripDerivBound` before calling it unconditional |

## 3. Ranked NEW SHAPE candidates

Selection principle as in the roadmaps: deterministic search-free tactics (`ring`,
`positivity`, `nlinarith` with explicit hints, `linarith`, `norm_num`), exact arithmetic
in the generator, the kernel as the only gate.

### 3.1 Shape A (rank 1): `PreorderingMultiplierEmitter`, kind `preordering_multiplier`

**Statement family.** `forall x in R^k, g_1(x) >= 0 -> ... -> g_m(x) >= 0 -> 0 <= p(x)`, where
the `g_i` are POLYNOMIAL generators (a disk, a parabola, `gamma^2 - 3/4`, a cavity
constraint), not only linear forms.

**Certificate (untrusted, LP-found).** (a) a multiplier `M = prod_i g_i^{mu_i}` (usually `1`
or a power of one structural generator); (b) exponent vectors `alpha` and rational `c_alpha >= 0`
with the exact identity in the BASE variables

    M(x) * p(x) = sum_alpha c_alpha * prod_i g_i(x)^{alpha_i}      (checked by `ring` after substitution)

(c) a locus certificate for `{M = 0} cap {g >= 0}`: either the sub-instance with the extra
equation (a lower-dimensional Shape A / `consequence` call) or, when the locus is a finite
point set, the point evaluations. Generators are tagged `hyp` (carried as a theorem
hypothesis, e.g. `d = Re z - |z|^2 >= 0`) or `structural` (closed by `positivity`, e.g.
`B = (Im z)^2`, `s = (Re z)^2 + (Im z)^2`).

This is the constant-coefficient part of the Schmuedgen preordering (products of generators
with nonnegative constants) plus a positive multiplier: `handelman` with polynomial generators,
`polya_zeros`'s multiplier trick off the simplex, `rational_sos`'s Artin denominator on a
semialgebraic set. None of the four existing kinds covers the combination, and the Li rungs
need all three ingredients at once (`Q_4`: multiplier `14 s`; `Q_5`: multiplier `s^2`).

**Lean skeleton** (parameterised copy of `LiBoxRungs.lean:157-182`):

    theorem <name> (x1 ... xk : R) (h_1 : 0 <= g_1) ... : 0 <= p := by
      obtain <d, hd0, hde> : exists d, 0 <= d /\ d = <g_hyp> := <_, by linarith, rfl>
      obtain <s, hs0, hse> : exists s, 0 <= s /\ s = <g_struct> := <_, by positivity, rfl>
      set P : R := <p> with hP
      have key : <M> * P = <sum c_alpha g^alpha> := by rw [hP, hde, hse, ...]; ring
      have hcert : 0 <= <M> * P := by rw [key]; positivity
      rcases eq_or_lt_of_le <hM0> with hM | hM
      . <locus branch: sub-certificate or point evaluation>
      . exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hcert

For `M = 1` the last four lines collapse to `rw [key]; positivity` (the `re_Q3_nonneg` form).

**Refusal conditions (phantoms).** LP infeasible up to the degree cap (report the
OBSTRUCTED_AND_LOCATED verdict with a numeric negative witness when one exists, as for `Q_6`
at `(0.303, 0.931)`); any `c_alpha < 0`; a `hyp` generator that is not literally a hypothesis;
a `structural` generator that `positivity` cannot close (checked by sympy: an SOS or a product
of such); a multiplier whose zero locus inside the set has no supplied certificate; a
multiplier not itself in the cone.

**Instances.** `LiBoxRungs.lean:139-155` (`M = 1`), `157-182` (`M = 14 s`), `184-212` (`M = s^2`);
`E6Bridge28.lean:815-866` (rungs 2..4 unpaired, generators `beta`, `1 - beta`, `gamma^2 - 3/4`,
`a`; the hand `nlinarith` calls are what the LP replaces); `LowHeightBox.lean:265-284` /
`E6Bridge28.lean:746-750` (Box 2 as a degree-1 instance with hypothesis generators `hA2`, `hB2`).

**Cross-applicability.** BG: the Laplacian-ratio work certifies polynomial positivity on boxes
where the corner principle fails because the form is not multi-affine (the `RealObligationA`
generic-SPR case is sign-indefinite, and the single-pendant path-extension SOS
`Delta Aobj = P (n^2 + Q n + 4 Q)/(2 (n+1)(n+2))` is a `direct_polya`); `cavity_exchange`
refuses "a corner with a negative coefficient (Polya fails, needs SOS)": Shape A with
generators `(x - x0)`, `(x1 - x)`, `(y - y0)`, `(y1 - y)` and a multiplier is the next
rung before an SDP. P vs NP: the knapsack level-2 residual and `Xor3Structure` moment
forms have structural SOS generators. RH: every box/annulus positivity in the zero-free
region islands (`ZeroFreeRegionEmitter`'s `nlinarith` closers), the Gaussian-window
`lam <= lam_*(T)` envelope cells.

**Build cost.** M. Reuse `find_handelman_certificate`'s exact subset solver with the products
enumerated over polynomial generators, add an outer loop over multipliers `g_j^k` (`k <= 3`),
and the locus branch generator. The identity check is sympy `expand` in the base variables.
Kernel risk: `ring` on degree-10 identities in two variables (fine; `Q_5` is degree 10 and
builds today).

### 3.2 Shape B (rank 2): `DerivSignMonotoneEmitter`, kind `deriv_sign_monotone`

**Statement family.** For an elementary closed form `f` (polynomials, `exp`, `log`, `sin`,
`cos`, `sinh`, `cosh`, `arctan`, `rpow` with fixed exponent) and a rational or symbolic
interval `[a, b]` (endpoints may be `pi`-multiples), `f x <= f a` (antitone) or `f a <= f x`
(monotone) for `x in [a, b]`, and the corollary `f x <= C` when `f a = C` is `norm_num`/`simp`
provable.

**Certificate (untrusted).** (a) the derivative `f'` as a closed form (sympy `diff`, rendered as
a `HasDerivAt` chain over Mathlib's `Real.hasDerivAt_{sin,cos,sinh,cosh,exp,arctan,rpow_const}`
plus `.mul/.add/.sub/.div_const/.pow`); (b) a SIGN CERTIFICATE for `f'` on `[a, b]`, one of:
a sign-product fold from a fixed table (`sinh >= 0` on `[0, inf)`, `sin >= 0` on `[0, pi]`,
`cos >= 0` on `[-pi/2, pi/2]`, `cosh > 0`, `exp > 0`, `1/(1+x^2) in (0, 1]`), closed by
`mul_nonneg`/`nlinarith`; a `direct_polya`/`bernstein` certificate when `f'` is rational; or
a RECURSIVE Shape B instance (`f' = g` with `g a = 0` and `g` antitone, exactly Lemma A's two
levels). (c) the endpoint value `f a`.

**Lean skeleton** (parameterised copy of `LiLadderHeight.lean:201-217`):

    have hf : forall x, HasDerivAt f (<f'>) x := fun x => <derivative chain>
    have hanti : AntitoneOn f (Set.Icc a b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a b) <continuity>.continuousOn ?_ ?_
      . intro x _; exact (hf x).differentiableAt.differentiableWithinAt
      . intro x hx; rw [interior_Icc] at hx; rw [(hf x).deriv]; <sign certificate>
    have := hanti <a in Icc> <x in Icc> hax
    simpa [f] using this

**Refusal conditions.** A factor of `f'` outside the sign table on the interval (e.g. `cos` on
`[0, pi]`); a numeric sample of `f'` with the wrong sign (checked in mpmath at 50 digits on a
grid plus the endpoints, an honest negative control, never the decision); `f` not
differentiable on `[a, b]` (`log` at 0, `rpow` at 0); a recursion depth above 3; an endpoint
value the kernel cannot evaluate.

**Instances.** `LiLadderHeight.lean:176-197` and `201-217` (two-level, Lemma A);
`E6Bridge28.lean:144-186` (the same two lemmas, duplicated); `E6Bridge28.lean:209-231`
(`u/2 <= arctan u` on `[0, 1]`, monotone face, rational derivative sign); the arctan bounds
`abs_arctan_le_abs` (`LiLadderHeight.lean:303-315`) are the `tan` route to the same shape.

**Cross-applicability.** BG: the F-star and log-tangent cells (`log_combination`'s tight route
needs `log X <= Q`; a monotone-in-`mu` fact like `(7 + 3 mu)/(2 (3 + mu)) <= 17/14` on
`(0, 1/2]` is currently `gcongr`/`nlinarith`; the derivative-sign route handles the
transcendental versions `log(1 + S/d)` in `d` directly). RH: the Montgomery-Taylor
`cot(1/sqrt 2)` face that `transcendental_enclosure` deferred; the Gaussian-window envelope
`lam_*(T)` monotone in `T`; the `xi-decay` and `xi-taylor` islands' one-variable growth bounds;
every future `cosh a cos b`-type termwise lemma (the Li face's whole method rests on one).
This is the first-derivative sibling of the shipped `curvature_boundary` (second-derivative
sign), and the two compose (a concave `f` with `f'(a) <= 0` is antitone).

**Build cost.** M to L. The derivative-chain renderer is the engineering (sympy tree to
`HasDerivAt` combinators, with `congr_deriv (by ring)` to normalise); the sign table is small;
the recursion is a list. Kernel risk: `antitoneOn_of_deriv_nonpos` needs `ContinuousOn` and
`DifferentiableOn (interior)`, both derivable from the same chain.

### 3.3 Shape C (rank 3): `LiBoxRungEmitter`, kind `li_box_rung` (a dogfood family over A + `consequence`)

**Statement family.** For `1 <= N <= 5`: hypothesis-free `0 <= Re(taylorCoeff riemannXi (N-1))`
on the li island and `0 <= Re(liLimit N)` on the rvm island, superseding the Arb-hypothesis
rung certificates of the existing `li_positivity` emitter for those rungs.

**Certificate.** (a) `Q_N` and its cofactor mod `w v = 1` from `chebyshev_pair_polynomial(N)`
(section 2.6), emitted as a `consequence` instance; (b) the Shape A certificate for `Re Q_N`
on the disk `(Re z)^2 + (Im z)^2 <= Re z`; (c) the fixed prelude (`zOf_mem_disk`, the paired
sum composition, `taylorCoeff_re_nonneg_of_termwise`) as a frozen lemma pack.

**Refusal.** `N >= 6`: the LP is infeasible and the emitter reports the located negative
witness (`N = 6`: pair term `-0.715` at `(0.303, 0.931)`, inside Box 2) as
OBSTRUCTED_AND_LOCATED, per HONESTY_PATTERNS #8; it never emits a rung it cannot certify and
never claims the ladder beyond `N = 5` (the height ladder is the separate, conditional
`LiLadderHeight` route).

**Instances.** `LiBoxRungs.lean:89-124` (cofactors), `128-212` (certificates), `283-300`
(rungs). The rvm twin `E6Bridge28.lean:815-969` is the unpaired Handelman route; Shape C
would emit the paired route there too (via `pair_re_eq` and `liLimit_re_nonneg_of_pairs`).

**Cross-applicability.** None outside the Li face by construction. It ranks third because it
is the dogfood that proves Shape A and the `consequence` cofactor path end to end on a live
node (`RH_li_rungs_lt_five`), and because it retires five Arb hypotheses.

**Build cost.** S once Shape A exists (a family file plus the frozen prelude).

## 4. Fold-ins (sub-modes of existing emitters, not standalone)

- `consequence`: a `laurent` convenience mode taking a base `w` and relation `w * v = 1`
  (generalising `exp_laurent_identity`, whose relation is `exp d * exp(-d) = 1`), used for
  `LiBoxRungs.lean:89-124`.
- `second_order`: an inhomogeneous three-term mode (`A f(q+2) + B f(q+1) + C f(q) = D`) for the
  `Q_N` recurrence; or use the homogeneous `T_N` form as is.
- `halfplane_disk`: an inversion face `Re q >= c > 0 ==> |1/q - 1/(2c)| <= 1/(2c)`
  (`LiBoxRungs.lean:223-236`).
- `transcendental_enclosure`: an `arctan` face (`|arctan x| <= |x|`, `x/2 <= arctan x` on
  `[0, 1]`) and a `pi` face wrapping `Real.pi_gt_d2/d4/d6` and `pi_lt_d2/...` so rate
  corollaries like `n <= 25128 ==> n + 1 <= 2 pi (4000 - 1/2)` are emitted, not hand
  `nlinarith`.
- `reflection_halving`: a `tsum` mode shipping `hasSum_involution_average`
  (`E6Bridge28.lean:460-477`).
- `dichotomy_glue`: allow symbolic thresholds (`pi/2`, `3 pi/2`, `2 pi`) for the exchange-rate
  window split (`LiLadderSharp.lean:112-121`, `E6Bridge29.lean:106-118`).
- `bernstein`: raise the default `max_elevation` or fall through to `sturm_positive` when the
  coefficient polynomials of a Handelman-in-`(u, e)` certificate need it
  (`E6Bridge28.lean:903-937`).

## 5. Standing-order misses and the duplication finding

Emitted-able but hand-written (each a small MISS; together they are the `Q_N`/rung block):

1. `LiBoxRungs.lean:98,106,115,124` cofactors (`consequence`).
2. `LiBoxRungs.lean:128-137` `Re Q_1`, `Re Q_2` (`putinar` / Shape A with `M = 1`).
3. `E6Bridge28.lean:903-937` five Bernstein-shaped `nlinarith` calls (`bernstein`).
4. `E6Bridge28.lean:940-969` the rung-5 Handelman certificate in `(u, e)` (`handelman` +
   substitution identity).
5. `E6Bridge28.lean:815-866` rungs 2..4 unpaired (`putinar` / Shape A).
6. `LowHeightBox.lean:265-284`, `E6Bridge28.lean:746-750` Box 2 as a cone combination (`cone`).
7. `LiLadderSharp.lean:59-65`, `E6Bridge29.lean:51-56` the `g`-inequality (`direct_polya`).
8. `LiLadderHeight.lean:518-538`, `E6Bridge28.lean:500-508` rung 0/1 real-part numerators
   (`direct_polya`).
9. The rational halves of the log bound (`LiLadderHeight.lean:281-296`,
   `E6Bridge28.lean:354-365`) (`direct_polya`).

Duplication (the same Mathlib-only fact proved on both islands; the standing order asks for
one shared capability, and a shared lemma pack that both lakefiles `require` is the fix):

| Fact | li island | rvm island | Mathlib-only? |
|---|---|---|---|
| Lemma A (`cosh a cos b <= 1`, two antitone levels) | `LiLadderHeight.lean:176-229` | `E6Bridge28.lean:144-196` | yes |
| Lemma A'' (window reflection) | `LiLadderSharp.lean:46-54` | `E6Bridge29.lean:37-46` | yes |
| `1/g + 1/(2 g^2) <= 1/(g - 1/2)` | `LiLadderSharp.lean:59-65` | `E6Bridge29.lean:51-56` | yes |
| `|log|u|| <= 1/(2 gamma^2)` | `LiLadderHeight.lean:273-300` | `E6Bridge28.lean:335-373` | yes (different base object, same proof) |
| sharp `{x}`-kernel bound `<= 1/(2 sigma)` | `LowHeightBox.lean:115-193` (midpoint reflection) | `E6Bridge28.lean:526-635` (integration by parts) | yes (two different proofs) |
| Box 1 / Box 2 | `LowHeightBox.lean:265-298` | `E6Bridge28.lean:703-750` | no (island representations differ) |

Shape B would emit the first row as a frozen prelude on both islands from one certificate;
the `{x}`-kernel bound and the `g`-inequality belong in a `LiFacePrelude.lean` lemma pack.

## 6. Not re-proposed (correctly subsumed)

- The on-line case `2(1 - cos) >= 0` (`unit_modulus_sos`).
- `sqrt 3 / 2 <= |t|` from `3/4 <= t^2` (`algebraic_bracket`).
- `norm J(s) <= int norm integrand` on a ray (`dominated_integrability`).
- The finite `interval_cases` dispatch over `n <= 4` (`case_dispatch_assembly`).
- The Arb-hypothesis rung certificates (`li_positivity`) remain the right shape for rungs
  `N >= 6` below height; Shape C retires them only for `N <= 5`.

## 7. Suggested build order

1. Shape A `preordering_multiplier`: cross-cutting (Li rungs, BG cavity boxes past the corner
   principle, zero-free-region boxes), exact LP over an existing solver, `ring`/`positivity`
   Lean. Top pick.
2. Shape B `deriv_sign_monotone`: the first-derivative sibling of `curvature_boundary`;
   removes the largest duplicated block on the two islands and unblocks the deferred trig face
   of `transcendental_enclosure`.
3. Shape C `li_box_rung`: dogfood of A plus `consequence` on the live node
   `RH_li_rungs_lt_five`; retires five Arb hypotheses; refuses `N = 6` with a located witness.
4. The fold-ins of section 4 as their consuming proofs demand; the `LiFacePrelude` lemma pack
   for the duplicated Mathlib-only facts.

conjecture1_proved = False.
