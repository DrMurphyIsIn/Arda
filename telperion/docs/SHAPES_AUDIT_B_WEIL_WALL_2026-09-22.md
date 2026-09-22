# Shapes audit B: Weil's criterion both ways + the Wall map (2026-09-22)

**conjecture1_proved = False. Nothing in this document bears on RH.** This is a
Telperion shape audit under the cross-pollination standing order
(`docs/CROSS_POLLINATION_STANDING_ORDER.md`): a read of the hand-written Lean in the
Weil / Wall cluster, asking for each recurring proof pattern whether an existing
emitter kind already covers it (a standing-order miss, or legitimately bespoke), whether
it is a genuinely NEW certificate shape (abstract statement family, untrusted certificate
data, tactic skeleton, refusals, instances, cross-applicability, build cost), or whether
it is an analytic discipline that is reusable but not certificate-shaped (and then what a
numeric-channel emitter in the style of `weil_form_enclosure` would need). The audit is
about the Lean, not about RH: every theorem read is an equivalence, an unconditional
inequality about a Gaussian-weighted sum, or an instrument conditional on named
hypotheses, exactly as the PR bodies and blind-audit testimonies say.

Method. All ten island files were read in full; every theorem statement and proof
skeleton was classified. The 153 registered emitter kinds (`grep 'kind = "'` over
`src/telperion/*.py`) were read at docstring level for the overlap check; the README
"Certificate shapes" table and `docs/HONESTY_PATTERNS.md` set the vocabulary. Line numbers
are against the worktree at the merge of PR #594 plus the E6Bridge14 commit `651d6bc06`.

## Scope: PRs and files

| PR | Merged | Content | Files in this audit |
|---|---|---|---|
| #593 | 2026-09-21 | Weil's criterion in-kernel both ways on the E8 vocabulary; Gaussian dominance (O2), Gaussian approximation (O1'), Tannery transfer (O1) | `E6Bridge5` (130 lines, 6 decls), `E6Bridge6` (605, 33), `E6Bridge7` (612, 35), `E6Bridge8` (646, 47), `E6Bridge9` (51, 4); mirrormere `Statements/MM_{rh_implies_weil_positivity, weil_positivity_implies_rh(_of_gaussian), gaussian_{dominance,approx,transfer}, zeta_comb_membership(_iff_rh)}.lean` + node TOMLs |
| #594 | 2026-09-21 | The two-parameter Wall (seam A), the unconditional small-width region and envelope (seam B), the ladder-certified region instrument (seam C), the Wall map | `E6Bridge10` (577, 50), `E6Bridge11` (1498, 67), `E6Bridge12` (476, 36), `E6Bridge13` (52, 3); mirrormere `Statements/MM_{rh_iff_gaussian_positivity, rh_iff_gaussian_prime_le_arch, gaussian_explicit_formula, gaussian_positivity_{small_lam,small_lam_prime_side,envelope,of_window}, wall_map}.lean` + node TOMLs; rh `RH_weil_criterion_iff` |
| #595 (open) | -- | Effective Gaussian dominance with explicit thresholds and the localisation instrument (open lemma 1 of the wall reconciliation) | `E6Bridge14` (448, 15), commit `651d6bc06` |

All paths below are relative to `telperion/examples/rvm_bridge/lean/`.

The mirrormere registry changes are statement mirrors (`-- DO NOT EDIT BY HAND`,
`... := by sorry` bodies matched by the grant gate's normalized text containment) and
node TOMLs with blind read-backs. They introduce no proof patterns of their own; the one
registry-level shape worth naming is the cross-island HYPOTHESIS SEAM of seam C
(`WindowOnLine c D` carried as a hypothesis because the Turing ladder lives on a different
toolchain), which is the same discipline as `weil_form_enclosure`'s `henc` and
`window_form_floor`'s four named hypotheses. It is covered by that discipline, not by an
emitter; candidate N4 below is the emitter that would instantiate it.

## Summary of the classification

Sixteen recurring patterns were found. Five are COVERED by existing kinds (three of
those are standing-order misses where hand tactics were written although an emitter
exists, two are legitimately inline). Nine are NEW SHAPE candidates (ranked in the last
section). The remaining patterns are analytic disciplines (Tannery transfer, cutoff
eventual constancy, generic-centre avoidance, phase selection, window Finsets) that are
reusable as fixed library atoms but carry no certificate data; for each, the numeric
channel a `weil_form_enclosure`-style emitter would need is stated.

## Part I: patterns COVERED by an existing emitter kind

### C1. Max-of-ratios threshold witnesses: `eventual_threshold` (standing-order MISS)

Every threshold in the cluster is assembled by hand as `max 1 (max (A/(2 eta K)) (B/(2 M K)))`
followed by a `le_max_left`/`le_max_right` chain to extract each conjunct:

- `E6Bridge7.lean:554-562` (`lam0`, `hlam1`, `hlamA`, `hlamB`),
- `E6Bridge12.lean:106-109, 301-307` (`lamThreshold`, `one_le_lamThreshold`, `hlam1`, `hlam2`),
- `E6Bridge14.lean:66-75, 281-288` (`effectiveThreshold`, `one_le_effectiveThreshold`, `hthr1`, `hthr2`).

`EventualScalingThreshold` (kind `eventual_threshold`) is exactly "finitely many affine
threshold conditions `a_i < p c_i` with positive slopes, witness `p0 = max(a_i/c_i)`,
each conjunct by `div_lt_iff0` + a `le_max` chain", arity 1 to 6. The three hand instances
have arity 2 or 3 with an extra `max 1` guard (a `c_i = 1, a_i = 1` conjunct). Miss: the
witness assembly should be emitted, with the guard as one more conjunct. The exponential
CONSEQUENCE of the threshold (`A <= K e^{2 lam eta}`) is not covered and is candidate N2.

### C2. Transcendental brackets in the seam B numerics: `transcendental_enclosure`, `exp_enclosure`, `algebraic_bracket`, `log_combination` (standing-order MISS)

`E6Bridge11.lean:1061-1123` and `1437-1483` close the assembly with hand-derived rational
brackets: `sqrt lam <= 1/3000` (1063-1065), `log pi <= 1.3863` via `log 4 = 2 log 2` (1066-1073,
1438-1445), `exp(2 lam) <= 3` (1074-1076), `sqrt(32 pi lam) <= 11/3000` (1077-1083),
`64 exp(-(log 2)^2/(16 lam)) <= 1/1000` (1084-1095), `sqrt(2 pi) <= 2.51` (1097-1099),
`exp(-4) <= 1/54` (1446-1452), `sqrt 2 <= 1.5` (1453-1455). The `log` face of
`transcendental_enclosure` and `log_combination` (fold `log pi <= 2 log 2` into one log)
cover the log rows; `exp_enclosure` covers `exp` at rational points with `|x| <= 1`
(`exp(-4)` needs the `exp_neg` + fourth-power route, which the emitter's `exp_neg` mode
plus `ExactFact` handles); `algebraic_bracket` covers `sqrt 2 <= 1.5`. Two rows are NOT
covered because the radicand is not rational: `sqrt(2 pi) <= 2.51` and `sqrt(32 pi) <= 11`
compose a pi bracket (`Real.pi_lt_d2`) with `Real.sqrt_le_left`. That is a fold-in for
`algebraic_bracket`: a `sqrt_of_bracketed` mode taking `lo <= a <= hi` as a hypothesis (or
a Mathlib pi bound) and emitting `sqrt a <= sqrt hi <= q`. Miss: all eight rows are the
shape the emitters exist for; the two pi rows need the fold-in.

### C3. Box polynomial positivity by `nlinarith` with a hint list: `handelman` / `sos` (standing-order MISS, low priority)

`E6Bridge6.lean:459-461` proves `(x^2+y^2)(1+(x+c)^2+y^2) <= (2c^2+13/4)(1+x^2)^2` under
`y^2 <= 1/4` by `nlinarith` with seven hand-chosen products. This is a Handelman /
Putinar certificate on the box `y^2 <= 1/4` (multiplier `(1/4 - y^2)` times an SOS plus an
SOS). `HandelmanEmitter` / `ConstrainedSOSEmitter` FIND the certificate and emit a
deterministic `ring` + `positivity` proof, which is more robust than `nlinarith` hint
search. Same shape at `E6Bridge10.lean:198-201` (`|v||v-u| <= (v-u/2)^2 + u^2/4`, a pure SOS:
`sos`) and `E6Bridge11.lean:367-386` (`|1-2s| e^{-s} <= 2 e^{-s/2}`: the polynomial half
`1 + 2s <= 2 + s + s^2/4` is `sos`). Miss, but each instance is one line and the
`nlinarith` calls compile; regenerate only if a build becomes fragile.

### C4. Triangle-inequality fan-outs: `magnitude_split` (legitimately inline)

`E6Bridge8.lean:494-506` (bracket norm), `E6Bridge10.lean:507-514` (`archBound`),
`E6Bridge11.lean:446-455` and `1191-1200` (`norm_add_le` on the two autocorr terms),
`E6Bridge14.lean:247-251`. All are `norm_add_le` + `gcongr` in place. `MagnitudeSplitBoundEmitter`
covers the shape; using it here would cost more than it saves. Bespoke, correctly.

### C5. Isolate one zero from a Herglotz-type sum: `herglotz_lower` and `reflection_halving` (partial, analog shape)

`E6Bridge6.lean:350-373` (`zeroSide_pair_split`: `Summable.sum_add_tsum_compl` on the pair
`{rho0, reflect rho0}`, then `Finset.sum_pair`), `E6Bridge6.lean:539-555`
(`gauss_zeroSide_pair_split`), `E6Bridge12.lean:189-194` (`zeroSide_split` on a window),
`E6Bridge12.lean:419-434` and `E6Bridge14.lean:131-140` (tsum over a subtype equals a Finset
sum via `tsum_subtype` + `tsum_eq_sum` + indicator). This is the Gaussian-weight analog of
`herglotz_lower`'s "keep the equal-height zero, drop the nonnegative rest" and uses the
same reflection involution as `reflection_halving`. Neither kind emits the tsum-split
atom itself; it is candidate N9 (low).

## Part II: NEW SHAPE candidates

Each candidate: statement family, certificate data an untrusted generator computes,
Lean skeleton, refusal conditions (phantom instances), instances, cross-applicability,
build cost (S / M / L, as in the roadmaps).

### N1. `gaussian_moment` -- the Gaussian moment / Fourier ladder (TOP)

**Statement family.** For real `a > 0`, complex (or real) frequency `w`, and degree `k`,
the moments `M_k(a, w) := integral x^k exp(-a x^2) exp(i w x) dx` have the closed form
`M_k = P_k(w, 1/a) * sqrt(pi/a) * exp(-w^2/(4a))` with `P_k` a polynomial with rational
coefficients in `i w` and `1/(2a)`, determined by the recurrence
`M_{k+1} = (i w/(2a)) M_k + (k/(2a)) M_{k-1}` (one integration by parts against
`fourierIntegral_gaussian`). Real-frequency, zero-frequency (`w = 0`: `M_2 = sqrt(pi/a)/(2a)`)
and shifted (`integral_sub_right_eq_self`) specialisations are modes.

**Certificate data.** `(k, mode)`; the generator computes the exact coefficient table of
`P_0, ..., P_k` from the recurrence in sympy and re-verifies each `P_{j+1} = (iw/2a) P_j +
(j/2a) P_{j-1}` as a rational-function identity. Phantom check: `P_k` must be nonzero of
the predicted degree.

**Lean skeleton.** A fixed prelude emitted once: (i) the Gaussian integrability calculus
of `E6Bridge8.lean:35-88` (`integrable_exp_quadratic`, `_abs`, `abs_pow_le_exp`,
`integrable_abs_pow_mul_exp_quadratic_abs`, `integrable_mul_cexp_quadratic`), (ii) ONE
integration-by-parts step lemma (`E6Bridge8.lean:100-152` generalised to
`x^{j+1} exp(-a x^2)` against `exp(iwx)`: derivatives by `hasDerivAt_pow`/`.cexp`/`.comp_ofReal`,
the three integrabilities by `.mono'` against the prelude majorant, then
`integral_mul_deriv_eq_deriv_mul_of_integrable`), (iii) `M_0 = fourierIntegral_gaussian`.
Per instance: the recurrence solved by `linear_combination` / `field_simp` from the step
lemma, then the closed form by `ring`. Real-valued and `ofReal` casts by
`integral_complex_ofReal` + `push_cast; ring_nf` (the boilerplate at `E6Bridge11.lean:136-143,
279-281`).

**Refusals.** `a <= 0` (not integrable); `k` outside `[0, 6]` (kernel cost); a supplied
coefficient table that does not satisfy the recurrence exactly (never emitted; the kernel
would catch it, but the generator refuses first).

**Instances in the cluster (six, each re-proving derivatives + three integrabilities + IBP):**
`E6Bridge8.lean:94-152` (`M_1`, complex `w`), `E6Bridge11.lean:105-133` (`M_2`, `w = 0`, real),
`E6Bridge11.lean:136-143` (its complex cast), `E6Bridge11.lean:241-285` (`M_2 - (u^2/4) M_0`,
shifted), `E6Bridge11.lean:612-703` (`M_2`, real `w`, 90 lines), `E6Bridge11.lean:928-946`
(`integral_bumpR = 2 pi A`, which is `M_2` at `2 lam` shifted by `c`),
`E6Bridge10.lean:227-277` (`gaussI0`, `gaussI2`, `integral_vMaj`: `M_0`, `M_2` with shift).
Downstream consumers: `E6Bridge11.lean:725-814` (`weilKernel_autocorrGauss_line`, whose
80-line proof is `M_0` and `M_2` plus a real identity) and `E6Bridge8.lean:197-230`.

**Cross-applicability.** RH islands: every Gaussian / heat-kernel test-function
computation (the `fourier`, `survey-heat`, `xi-taylor` threads compute exactly these
moments); the archimedean `bumpR` mass and tail mass (`E6Bridge11.lean:1279-1319`) are
`M_2` at two widths. BG: no direct consumer (BG is discrete), but the prelude's
`integrable |x|^m exp(-b x^2 + k|x|)` is the continuous analog of BG's geometric-tail
majorants. Build cost: M (the prelude is a port of existing proofs; the per-`k` closure
is `ring`).

### N2. `exp_threshold` -- from a rational threshold on the width to exponential domination

**Statement family.** Two modes.
`linear` (crude): for `Q >= 0`, `a > 0`: `Q/a <= lam` implies `Q <= exp(lam a)` (via
`Real.add_one_le_exp`); the product form `exp(-lam a) (lam a) <= 1`.
`log` (sharp): `log(max 1 Q)/a <= lam` implies `Q <= exp(lam a)` (via `Real.exp_log` on
`max 1 Q`, so `Q <= 0` is not refused, it is trivial). Companion one-liners:
`exp(-x) <= 1/x` for `x > 0` and `y exp(-y) <= 1`.

**Certificate data.** The pair `(Q, a)` as symbolic parameters or rationals, the mode, and
(optionally) the downstream consequence `Q <= K exp(lam a)` with `K > 0` after clearing
`Q/K`. Phantom check: `a > 0` certified exactly when rational; when symbolic, emitted as a
hypothesis.

**Lean skeleton.** `div_le_iff0` + `Real.add_one_le_exp` + `linarith` (linear);
`div_le_iff0` + `Real.exp_log (lt_max_of_lt_left one_pos)` + `Real.exp_le_exp` (log);
`Real.exp_neg` + `inv_mul_le_iff0` for the product forms. Composes with
`eventual_threshold` (C1): that kind produces `p > max(a_i/c_i)`, this kind consumes each
conjunct into an exponential.

**Refusals.** `a <= 0`; a rational `Q` with `Q/a` or `log(max 1 Q)/a` not matching the
declared threshold expression (the generator computes and compares exactly).

**Instances (six):** `E6Bridge7.lean:575-590` (`hexpeta`, `hexpM`: linear mode, twice),
`E6Bridge12.lean:311-316` (`hexpkappa`: product form) and `297-338` overall,
`E6Bridge14.lean:78-86` (`le_exp_of_log_le`: log mode, the only place it was factored into a
lemma), `E6Bridge11.lean:1084-1095` (`exp(-x) <= 1/x` at `x >= 64000`),
`E6Bridge11.lean:910-925` (`bumpR_le`: `y exp(-y) <= 1`).

**Cross-applicability.** BG: the `MonotoneRatioTail` / `uniform_tail` geometric-tail
closings and the `LogCombination` exp-vs-rational steps are the same `1 + t <= e^t`
discipline; any "for lam beyond an explicit threshold the exponential wins" closure.
RH: seam C and the effective-dominance thresholds are the direct consumers. Nearest
existing kind: `poly_exp_absorption` (the `t <= e^t` trick at a SPLIT rate, uniform in
`lam`); this is its threshold-form sibling. Build cost: S.

### N3. `complex_re_im_split` -- real and imaginary parts of a polynomial-exponential expression in `z`

**Statement family.** For a Laurent-free polynomial `p(z; params)` over `C` with real
parameters, `(p z).re = P_re(z.re, z.im; params)` and `(p z).im = P_im(...)`, plus the
norm forms `‖p z‖^2 = P_re^2 + P_im^2` and `‖exp(q z)‖ = exp((q z).re)`.

**Certificate data.** The polynomial `p` and the two real polynomials `P_re`, `P_im`,
computed by sympy (`re`, `im` with `z = x + i y`), re-verified exactly.

**Lean skeleton.** `simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_two, ...]` then
`ring`; norms by `Complex.sq_norm`, `Complex.normSq_apply`, `Complex.norm_exp`.

**Refusals.** Non-polynomial `p` (a division must be declared with a nonzero-denominator
hypothesis); a supplied `P_re` that does not agree with sympy's.

**Instances (at least eight):** `E6Bridge6.lean:408-421` (`hre`, `hsq`, `hnormSq`),
`E6Bridge7.lean:76-86` (`norm_gaussTest`), `E6Bridge7.lean:103-118` (`hw2re`, `hw2im`, `hEre`,
`hEim`), `E6Bridge8.lean:84-85, 308-311, 409-410`, `E6Bridge10.lean:430-431`,
`E6Bridge11.lean:396, 533, 649-652, 762-765`, `E6Bridge6.lean:382-392` (`gaussTest_axis`).

**Cross-applicability.** Every complex-analysis island (`zero_free_bridge`,
`borel_caratheodory`, the xi threads) writes these by hand; BG has none. Build cost: S
(the smallest and most frequent shape in the cluster).

### N4. `window_dominance` -- the seam C instrument as a numeric-channel certificate

**Statement family.** `E6Bridge12.lean:441-451` (`gaussian_positivity_of_window_dominance`):
under `WindowOnLine c D` (cross-island hypothesis) and `1 <= lam`, the computable inequality
`tailEnvelope c D lam <= windowSum c D lam` gives `0 <= F(c, lam)`, where
`windowSum = sum over certified zeros of m (t - c)^2 exp(-2 lam (t - c)^2)` (`405-407`) and
`tailEnvelope = exp(2(lam-1)(1/4 - D^2)) * constB c` (`413`). The instrument the numerics
validate (section G; landscape memo: the whole window sum beats the tail for
`lam >= 0.27` at `D = 2`, a single near term essentially never does).

**Certificate data (the numeric channel).** Rational ordinate brackets `[t_j^lo, t_j^hi]`
with multiplicities for the zeros in `|t - c| <= D` (the same input `bragg_amplitude` takes
from the Turing ladder), an outward-rounded rational lower bound `W_lo <= windowSum`
(each summand `(t-c)^2 exp(-2 lam (t-c)^2)` enclosed by `exp_enclosure` on the bracket), a
rational upper bound `Bmax >= constB c`, and the rational `E_hi >= exp(2(lam-1)(1/4-D^2))`.
The generator certifies `E_hi * Bmax <= W_lo` exactly and refuses otherwise.

**Lean skeleton.** As `weil_form_enclosure`: named hypotheses `hwin : WindowOnLine c D`,
`hB : constB c <= Bmax`, `henc_j : t_j in [lo_j, hi_j]` and the exp brackets; the kernel
proves `tailEnvelope <= windowSum` by `Finset.sum` over the listed zeros + `norm_num` on
the rational literals, then applies the island theorem. The window Finset must be
identified with the listed zeros: this needs the ladder's count certificate
(`turing_band` / `box_localization` output: exactly these zeros in the band, with these
multiplicities), which is the second cross-island seam.

**Refusals.** Missing `Bmax` (see the open rung below); `E_hi * Bmax > W_lo` (the
instrument does not fire; nothing is emitted); a bracket list whose count disagrees with
the ladder's certified count; `lam < 1`.

**Open rung, honestly.** `constB c = sum over ALL zeros of m C_1(c)/(1 + |gamma|^2)`
(`E6Bridge7.lean:441-444`) is summable by `Zeta23.WeilEF.zero_sum_inv_sq` but has NO explicit
numeric bound on the island. A rigorous `Bmax` needs an explicit zero-counting bound
(Backlund / `N(T) <= (T/2pi) log(T/2pi e) + O(log T)` with constants) to bound the tail
beyond the ladder height, plus the ladder's certified zeros below it. `E6Bridge14.lean:426-446`
(`windowCount_le_Ncount`) is the first step (window count <= `Zeta23.Ncount`). Until that
rung exists the emitter carries `hB` as an undischarged hypothesis, exactly as
`window_form_floor` carries `hhead`. This is also what candidate N5 in the seam-C memo calls
"clustering control".

**Cross-applicability.** RH only (the effective-dominance instrument of `E6Bridge14.lean:269-351`
is the same channel with `(y0, xmin, N, Bmax, D)`). Build cost: M (the Lean is small; the
channel's honesty depends on the `Bmax` rung).

### N5. `weighted_tsum_tail_envelope` -- a tsum over a subtype bounded by a summable majorant times a constant

**Statement family.** For `f : C -> C`, `w : C -> R` with `Summable w`, `0 <= w`, a set `S`,
and a constant `E >= 0`: if `‖f rho‖ <= E * w rho` for all `rho in S`, then
`‖tsum over S of f‖ <= E * tsum w`. With the "rate-splitting" companion: for `phi <= P`
with `P < 0` and `lam >= 1`, `exp(2 lam phi) <= exp(2 (lam - 1) P) * exp(2 phi)`.

**Certificate data.** None numeric; the shape is a fixed generic atom. Optional rational
`P < 0` for the companion (refuse `P >= 0`: then the envelope grows with `lam` and the
"decoupling" is false).

**Lean skeleton.** `norm_tsum_le_tsum_norm hsumN` then `hsumN.tsum_le_tsum hmaj hsumM` then
`hsumE.tsum_subtype_le` then `tsum_mul_left`; the companion by `Real.exp_add` +
`Real.exp_le_exp` + `nlinarith [mul_le_mul_of_nonneg_left hphi (sub_nonneg.mpr hlam)]`.

**Instances.** Verbatim twice: `E6Bridge7.lean:465-483` (`tail_bound`, with the majorant
`377-435`) and `E6Bridge12.lean:269-291` (`tail_bound_window`, with `224-265`); re-derived
in `E6Bridge14.lean:303-312` (`henv`). The majorant lemma `summable_mult_div_one_add_normSq`
(`E6Bridge6.lean:483-504`) is the shared `w`.

**Cross-applicability.** Any island that bounds a zero sum off a finite set (the Li /
xi-taylor threads bound `sum m/|rho|^{k}` tails the same way); BG: the per-node
tail bounds under `TelescopingPotential` are the discrete analog. Build cost: S.

### N6. `prime_side_gauss` -- the prime side of a Gaussian-in-log autocorrelation is `O(A) * n^{-2}`-summable

**Statement family.** From a majorant `|f(log n)| <= A exp(-(log n)^2/(16 lam))` and
`Lambda(n)/sqrt n <= 2` (or `<= n`), each prime-side term is `<= K * n^{-2}` (or `n^{-3}`),
so `‖primeSide f‖ <= K * zeta(2) <= 2K`. Two modes for `K`: `sigma_gate`
(`log 2/(16 lam) >= 2` gives `K = 8 A exp(-(log 2/(16 lam) - 2) log 2)`, exponentially small
in `1/lam`) and `amgm_uniform` (`(log n)^2/(16 lam) >= 2 log n - 16 lam` by
`sq_nonneg (log n - 16 lam)`, giving `K = 8 A exp(16 lam)`, lam-uniform).

**Certificate data.** The rational exponents and the constant `K` as a closed form in
`(A, lam)`; the gate `sigma >= 2` when in `sigma_gate` mode; the rational `zeta(2) <= 2`
(`Real.pi^2/6 <= 2` from `pi_lt_d2`).

**Lean skeleton.** `interval_cases n` for `n < 2` (vonMangoldt vanishes), `vonMangoldt_le_log`,
`Real.log_le_sub_one_of_pos` on `sqrt n`, `Real.exp_le_exp` with the exponent inequality by
`nlinarith`, then `norm_tsum_le_tsum_norm` + `tsum_le_tsum` + `hasSum_zeta_two.tsum_eq`.

**Refusals.** `lam <= 0`; in `sigma_gate` mode a `lam` with `log 2/(16 lam) < 2`; a
majorant exponent that is not a Gaussian in `log n` (the `n^{-2}` bound fails).

**Instances (three, ~100 lines each, two of them near-duplicates):** `E6Bridge11.lean:417-515`
(`prime_term_bound`, `norm_primeSide_le`), `E6Bridge11.lean:1165-1239`
(`prime_term_bound_uniform`, `norm_primeSide_le_uniform`), `E6Bridge10.lean:324-397`
(`primeBound`, `summable_primeBound`: the `n^{-6}` variant used for dominated convergence).

**Cross-applicability.** RH: `bragg_floor` and `weil_form_enclosure` compute truncated
prime sums numerically; this is the symbolic, unconditional companion (the tail of a
prime sum against a Gaussian in `log n`). BG: none. Build cost: M.

### N7. `digamma_vertical_floor` -- lower bounds for `Re psi(a + i t)` on a vertical line

**Statement family.** Three floors on `Re digamma(1/4 + i t)`: a global rational floor
(`-5` for all `t`, from the vertical-line real series, `E6Bridge11.lean:148-166`), a rational
floor beyond a rational radius (`>= 2` for `|r| >= 41` with `t = r/2`,
`E6Bridge11.lean:169-192`), and the logarithmic floor `>= log(|r|/2) - 5` for `|r| >= 2`
(`E6Bridge11.lean:1242-1258`), all from `Zeta23.StirlingVert.re_digamma_stirling'` and
`Zeta23.MuFields.re_digamma_vertical`.

**Certificate data.** `(a, R0, target)` rational: the generator checks
`log(R0/2) - 5 - 5/(R0/2)^2 >= target` with an exact `exp` bracket (`exp 3 <= 2.7182818286^3`
is what the hand proof uses at `181-182`) and refuses if the margin is nonpositive.

**Lean skeleton.** The Stirling lemma + `Real.log_le_log` from an `exp` bracket
(`exp_enclosure` for `exp 3`), `div_le_iff0` for the `5/(r/2)^2` term, `linarith`.

**Refusals.** `R0` below the Stirling lemma's validity (`|t| >= 1/2`); a `target` above the
certified margin.

**Cross-applicability.** This is the digamma envelope `henv` that `window_form_floor`
(Zhu Lemma 3.1) carries as an UNDISCHARGED hypothesis in the weaker form
`Re psi(1/4 + it/2) - log pi >= log(t/2pi) - 1/t`. The Stirling floor here is cruder
(`-5` instead of `-1/t`), so it does not discharge `henv` as stated, but the emitter
would give `window_form_floor` a kernel-proved floor to consume in a relaxed mode. BG:
none. Build cost: M (depends on the Zeta23 Stirling import in the emitted island).

### N8. `indicator_split_integral_floor` -- the bump-average lower bound by an indicator split

**Statement family.** For an integrable weight `w >= 0` and a measurable `psi` with
`psi >= m1` everywhere and `psi >= m2` on the complement of a set `S` (`m2 > m1`):
`integral w psi >= m2 * integral w - (m2 - m1) * integral_S w`. With the two tail
estimates used to bound `integral_S w`: a sup bound times the measure of `S`
(`E6Bridge11.lean:951-959`, `setIntegral_bumpR_le`) or a Gaussian-halving comparison
(`E6Bridge11.lean:1279-1319`, `integral_indicator_bumpR_tail_le`).

**Certificate data.** `(m1, m2)` rational or symbolic; the tail-estimate mode and its
rational constant (`R0/lam` or `exp(-4) * 2 sqrt 2`).

**Lean skeleton.** Define `L := m2 w - (m2 - m1) S.indicator w`, prove `L <= w psi`
pointwise by `by_cases hr : r in S` + `nlinarith`, then `integral_mono` + `integral_sub` +
`integral_const_mul` + `integral_indicator`.

**Refusals.** `m2 <= m1` (the split is vacuous); an `S` without a certified tail estimate.

**Instances (two):** `E6Bridge11.lean:963-993` (`integral_bumpR_mul_psiR_ge`) and
`E6Bridge11.lean:1324-1368` (`integral_bumpR_mul_psiR_ge_envelope`).

**Cross-applicability.** RH: any archimedean-side floor against a bump; the `xi-decay`
and `survey-heat` threads. BG: the continuous analog of the hinge floor (`telperion.hinge`),
not a direct consumer. Build cost: S.

### N9. `involution_tsum` -- a tsum over an involution-symmetric family is real; finite split off a pair or window

**Statement family.** (a) If `sigma : C -> C` is an involution (`Equiv`) with
`m (sigma rho) = m rho` and `H (gammaOf (sigma rho)) = conj (H (gammaOf rho))`, then
`conj (tsum m H) = tsum m H` (`E6Bridge6.lean:165-176`, via `tsum_star` + `Equiv.tsum_eq`).
(b) `tsum f = sum_{S} f + tsum_{S^c} f` for a finite explicit `S` (pair or window), with the
real-part version and the `tsum_subtype` -> `Finset.sum` identification
(`E6Bridge6.lean:350-373`, `E6Bridge12.lean:189-194, 419-434`, `E6Bridge14.lean:131-140`).

**Certificate data.** None numeric (fixed atoms); the involution and its two invariance
facts are hypotheses.

**Lean skeleton.** As in the instances; `Summable.sum_add_tsum_compl`, `Finset.sum_pair`,
`tsum_eq_sum`, `Set.indicator_of_mem`, `Complex.re_sum`.

**Refusals.** A non-involutive `sigma` (the `Equiv` cannot be built); `S` not finite.

**Cross-applicability.** RH: `reflection_halving` (counting) and `herglotz_lower` (drop the
rest) are the two existing neighbours; this atom is what both would call. BG: none.
Build cost: S. Low priority: five instances, but each is short and the atom is thin.

## Part III: analytic-discipline patterns (reusable, not certificate-shaped)

### D1. Tannery / dominated-convergence transfer of a zero sum against the local count

`E6Bridge6.lean:576-596` (`gaussianTransfer_of_approx`) and `E6Bridge10.lean:149-167`
(`zeroSide_gaussTests_tendsto`) are the same proof: `tendsto_tsum_of_dominated_convergence
(summable_mult_div_one_add_normSq C)` with a per-`rho` case split on `IsNontrivialZero`
(off the zeros `zeroMult = 0` and both the limit and the bound are trivial). The certificate
content is the strip bound `‖H_n(z)‖ <= C/(1 + normSq z)` on `|Im z| <= 1/2`, uniform in `n`,
which is an analytic input (E6Bridge8 proves it by one integration by parts). A fixed
library atom `zeroSide_tendsto_of_strip_bound` in the island would remove the duplicate;
there is nothing for an untrusted generator to compute. A numeric-channel emitter is the
wrong tool: the limit is symbolic.

### D2. Cutoff eventual constancy inside dominated convergence

Five DCT instances share the move "the truncated integrand equals the untruncated one once
`n + 1 >= |u|`, so the pointwise limit is `tendsto_const_nhds.congr'` with `Filter.eventually_atTop`
and a `Nat.ceil` witness": `E6Bridge8.lean:356-376`, `E6Bridge10.lean:299-318` (two ceilings,
`omega`), `442-452`, `517-529`, `399-405`. The majorants are the certificate-free part
(Gaussian, `vMaj`, `kernelMaj`, `archBound`, `primeBound`). Reusable as a `ContDiffBump`-cutoff
transfer lemma parametrised by the majorant; not a certificate. What a numeric channel
would need: nothing (symbolic).

### D3. Generic centre by finite-bad-set avoidance, and the maximiser gap

`E6Bridge7.lean:219-253` (`badOf`, `badSet` as a Finset image of the window square,
`Set.Ioo_infinite.sdiff` a finite set is nonempty) and `279-308` (`exists_maximiser_gap`:
`Finset.exists_max_image` twice, second time on the window minus the pair, to get a strict
gap `eta > 0`). This is the symbolic sibling of `finite_argmax` (which needs concrete
rational competitors). A numeric-channel version exists in spirit as `E6Bridge14`'s
`(y0, xmin, N)` parameters: the gap `eta` becomes `xmin^2`, the window count `N`, the
distance floor `y0`; the emitter for that channel is N4. Not certificate-shaped here.

### D4. Phase selection

`E6Bridge7.lean:127-186` (`exists_lam_trig`): choose `lam >= lam0` with
`4 lam x y = arg(-(x+iy)^2) + 2 pi k` via `exists_int_gt`/`exists_int_lt` and
`Real.cos_add_int_mul_two_pi`. One instance; a generic atom "an affine function of a real
parameter hits any residue class mod `2 pi` beyond any threshold". Not certificate-shaped.

### D5. Window Finsets from the local zero count

`E6Bridge7.lean:201-217`, `E6Bridge12.lean:385-401`, `E6Bridge14.lean:356-360, 426-446`: build
`(zetaSeam.finite_window a b).toFinset` and its `mem` lemma, three times with different
window shapes. A single island lemma `zeroWindow c D` with `mem_zeroWindow` (E6Bridge12 has
it) should be the one everyone imports; E6Bridge7's `window rho0` and E6Bridge14's band
are re-derivations. Not a shape.

### D6. Centre-at-ordinate localisation (E6Bridge14)

`re_term_centre` (`143-161`: at `Im rho = c` the summand is `-m y^2 exp(2 lam y^2)`, phase
automatically `pi`), `re_window_sum_le` (`208-262`: the window sum bounded by the centre
term plus `N (D^2 + 1/4) exp(2 lam (Y - xmin^2))`), and the localisation instrument
`offline_zeros_small_or_margin` (`366-422`: the maximal-distance zero over a widened band is
either within `y0` of the line or sits in a margin the instrument cannot see). The
instrument is conditional on `hpos` (positivity on the band above the threshold), which is
what N4's channel would certify per centre; the parameters `(y0, xmin, N, Bmax, D)` are what
a numeric channel supplies, and `Bmax` is the open rung named under N4. The "slide the
band" dichotomy is a discipline (an instrument that reports where it is blind), in the
spirit of `HONESTY_PATTERNS.md` pattern 7 (mechanical cover versus conceptual seam), not a
shape.

### D7. Real-part-of-a-cast boilerplate

`E6Bridge5.lean:110-114`, `E6Bridge7.lean:497-503`, `E6Bridge12.lean:122-126`,
`E6Bridge14.lean:155-161`, `E6Bridge11.lean:1028-1034, 1420-1431`: "this complex expression is
the cast of that real expression, so its `.re` is that real": `push_cast; ring` then
`Complex.ofReal_re`. Six instances. A fold-in sub-mode of `identity` (`complex_cast_re`),
or absorbed by N3.

### D8. Fourier transform of a derivative (integration by parts on a compactly supported test)

`E6Bridge8.lean:520-544` (`I_mul_paperFT_eq`: `i z * paperFT g z = - integral g' exp(izu)`)
and its use `547-569` to get the `1/(1 + ‖z‖)` decay uniform in the cutoff. One instance,
but it is THE tool for every "the transform of a smooth compactly supported test decays"
step; the `n`-fold version (E8 design: "two integrations by parts") is the general atom.
Reusable library lemma; the only certificate-shaped part is the decay ORDER, which
`dominated_integrability` / `parametric_holomorphy` already parametrise by `Re p`.

## Part IV: ranked NEW SHAPE candidates

Ranking by (instances x cross-applicability) / build cost, with honesty of the channel as
a tie-breaker.

| Rank | Kind | Instances | Cross | Cost | Why here |
|---|---|---|---|---|---|
| 1 | N1 `gaussian_moment` | 6 (+2 consumers) | RH (fourier, heat, xi-taylor) | M | The most-repeated genuinely certificate-shaped work in the cluster: exact rational coefficient tables per degree, `ring`-checked; each hand instance is 30 to 90 lines of derivatives + integrability + IBP |
| 2 | N2 `exp_threshold` | 6 | RH + BG | S | Closes the gap between `eventual_threshold` (which builds the max-of-ratios witness) and the exponential consequence every threshold proof needs; log mode is the sharp form E6Bridge14 factored out |
| 3 | N3 `complex_re_im_split` | 8+ | every complex-analysis island | S | Cheapest build, highest frequency; sympy computes the split, `simp only` + `ring` checks it |
| 4 | N4 `window_dominance` | 1 (the instrument) | RH only | M | The seam C instrument as a `weil_form_enclosure`-style channel; the honest blocker is an explicit `Bmax >= constB c`, which needs a zero-counting bound the island does not have |
| 5 | N5 `weighted_tsum_tail_envelope` | 2 verbatim + 1 | RH (Li, xi tails) | S | Twenty lines duplicated exactly between E6Bridge7 and E6Bridge12 |
| 6 | N6 `prime_side_gauss` | 3 (two near-duplicates of ~100 lines) | RH | M | Symbolic unconditional prime-side bound; the `sigma_gate` / `amgm_uniform` modes are precisely the E6Bridge11 duplication |
| 7 | N7 `digamma_vertical_floor` | 3 | RH (`window_form_floor.henv`) | M | A kernel-proved digamma floor a consumer can take instead of an undischarged hypothesis |
| 8 | N8 `indicator_split_integral_floor` | 2 | RH | S | Clean generic atom, two 30-line instances |
| 9 | N9 `involution_tsum` | 5 short | RH | S | Thin atom; neighbours `reflection_halving` and `herglotz_lower` exist |

Fold-ins recorded above (not standalone kinds): `algebraic_bracket` needs a
`sqrt_of_bracketed` mode for `sqrt(2 pi)`, `sqrt(32 pi)` (C2); `identity` needs
`complex_cast_re` (D7) unless N3 absorbs it; `eventual_threshold` should accept the
`max 1 (...)` guard as an ordinary conjunct (C1).

Standing-order misses to regenerate when the files are next touched: C1 (three threshold
witnesses), C2 (eight transcendental brackets in seam B), C3 (three `nlinarith` box
positivities). None of these affects what is proved; all three would replace hand tactic
search by emitted deterministic certificates.

## What this audit does not say

It does not say any candidate advances RH or BG. N1 through N9 are certificate shapes for
steps that are already kernel-checked by hand in this cluster; building them makes the
next island cheaper and lets the CI kernel gate confirm regenerated instances. The Wall is
drawn, not crossed; `conjecture1_proved = False`.
