# Shapes audit, 48-hour synthesis (2026-09-22)

conjecture1_proved = False. Nothing here bears on RH. This document merges the four
cluster audits written under `docs/CROSS_POLLINATION_STANDING_ORDER.md`:

| Tag | Audit | Cluster |
|---|---|---|
| A | `SHAPES_AUDIT_A_MISSIONS_2026-09-22.md` | PRs #583-#592 (missions tooling, speiser box, leakage, Satake, W2b quadruple) |
| B | `SHAPES_AUDIT_B_WEIL_WALL_2026-09-22.md` | PRs #593, #594, #595 (Weil both ways, Wall map, effective dominance), `E6Bridge5..14` |
| C | `SHAPES_AUDIT_C_B7_PARTIAL_FRACTION_2026-09-22.md` | PR #595 merged, `E6Bridge15..27` (B7, xi partial fraction, LiValue Taylor) |
| D | `SHAPES_AUDIT_D_LI_FACE_2026-09-22.md` | PR #596 plus two follow-on commits on `mm/gauss-window` (the Li face, both islands) |

Citations below are `(A C2)`, `(B N5)`, `(C 5.2)`, `(D 2.4)`: audit tag plus the section
or item label inside that audit. Every claim is traceable to one of the four. Nothing in
the four audits was re-derived here; where the audits disagree on a count the later audit
wins and the discrepancy is noted. Candidate kind names were checked against the 152
`kind = "..."` classes in `src/telperion/*.py` and the README "Certificate shapes" table;
none collides. (`enclosure_interval_fold` is the near-CUE row-band checker from
zeta-23-lean, not an atom-interval fold, so the merged enclosure candidate of section 2
is new.)

## 1. Executive summary

**Scope.** Fourteen PRs (#583 through #596) plus the current branch (`mm/gauss-window`,
two follow-on commits, D section 1). Lean lines read in full, by cluster:

| Cluster | Lean lines | Source |
|---|---|---|
| A | about 2,000 (1,087 merged files on disk; `QuadrupleDefect.lean` 583 and the two Satake files, open PRs, counted from A's own line citations) | A section 1 |
| B | 5,095 (`E6Bridge5..14`) | B scope table |
| C | 7,112 (`E6Bridge15..27`) plus 475 AxiomGuard anchor lines | C section 1 |
| D | 2,518 (four li files, `E6Bridge28`, `E6Bridge29`) | D section 1 |
| Total | about 16,700 (17,200 with anchors) | |

**Classification.** 186 classified rows in 41 pattern families (A 23 rows in 7+7+9
items; B 22 entries C1-C5, N1-N9, D1-D8; C 87 table rows in 11 families; D 54 table rows
in 7 families). Verdict vocabulary is shared: COVERED / MISS / BESPOKE / NEW / FOLD-IN /
DISCIPLINE (C section 2 header, D section 2 header).

**Standing-order misses.** 20 miss groups covering roughly 135 hand-proof sites (A: 2
groups; B: 3 groups, 14 sites; C: 6 groups, about 100 sites of which 79 are hand
`nlinarith` strip inequalities, C 5.3; D: 9 groups, about 20 sites, D section 5). None
changes what is proved (B "Standing-order misses", C 5.3, D 5). Section 3.

**Duplicated lemma groups.** 23 across islands and modules: 12 in the E6Bridge15..27
cluster written by parallel agents (C 5.2), 6 li-versus-rvm (D section 5), 5 in the Weil
cluster (B N5, N6, D1, D2, D5), 1 in A (the mean-value instrument pinned to one island,
A C5/D5). One of D's six (the sawtooth kernel bound) is also C's discipline pattern 14, so
the raw 24 collapse to 23. Section 4.

**New-shape candidates.** 22 raw (A 7, B 9, C 3, D 3). After deduplication 17: three
enclosure candidates merge into one (`enclosure_tree`), B's tail envelope merges into C's
`zero_sum_majorant`, B's `involution_tsum` is demoted to a prelude lemma (no certificate
data, D 2.5 and C pattern 7 agree), and D's `li_box_rung` is the dogfood family of
`preordering_multiplier`, not a separate kind. Ten are ranked in section 2, seven are in
the appendix. Sixteen fold-in sub-modes of existing kinds are listed in section 2.3.

**Also produced.** Four honesty patterns to add (#9-#12) plus three notes (section 5);
five defects in open PRs and five registry cosmetics (section 6); a build order with
dogfood targets (section 7).

## 2. Deduplicated, ranked emitter roadmap

### 2.1 Merges performed

| Surviving kind | Merged from | Why the same shape |
|---|---|---|
| `enclosure_tree` | A N2 `RadicalExpressionEnclosure`, A N3 `LogTaylorBracket`, A N4 `AtomPolynomialEnclosure`; fold-ins B C2 `sqrt_of_bracketed`, C 4.7 `log y <= c y^alpha`, D section 4 `arctan` and `pi` faces of `transcendental_enclosure` | All are "rational two-sided enclosure of an expression tree over atoms" with the same outward-rounding fold; N4 is the consumer N2 and N3 feed and already lives in `emit_leakage_dictionary.interval_of` (A N4 g). The B and D fold-ins are new atom faces (`pi`, `arctan`, `sqrt` of a bracketed radicand). |
| `zero_sum_majorant` | C shape A; B N5 `weighted_tsum_tail_envelope` | B N5's `‖tsum_S f‖ <= E * tsum w` is the consumer of exactly the pointwise majorant C shape A certifies; the shared `w` is `summable_mult_div_one_add_normSq` in both (B N5 instances, C 2.1). Emit as a `tail_envelope` face. |
| `preordering_multiplier` | D shape A; B C3 (three `nlinarith` box positivities); the C 5.3 item 1 backfill where Polya-after-shift fails; D shape C `li_box_rung` as its dogfood family | D shape A is the only candidate with polynomial generators plus a multiplier; B C3 and the C strip inequalities are its degree-2 instances (B C3 says `handelman`/`sos`, which are the linear-generator special cases). |
| `exp_threshold` | B N2; C 4.5 `poly_exp_absorption` shifted-rate mode | Both are `Real.add_one_le_exp` disciplines with a rational or symbolic threshold; C 4.5's `P(y) e^{-r y} <= K e^{-r' y}` is B N2's product form with a rate split (B N2 names `poly_exp_absorption` as the nearest kind). |
| `gaussian_moment` | B N1; C pattern 15 (second Gaussian moment at complex frequency, heat convolution); C 4.6 `rational_identity` C-coefficient mode | C 2.10 rows `E6Bridge16.lean:58-151, 171-246` are B N1's `M_2` at a complex frequency; the completing-the-square exponent identities of C 4.6 are the per-instance certificate sub-step. |
| `complex_re_im_split` | B N3; B D7 `complex_cast_re`; C 2.10 and D 2.2 "identity, BESPOKE cast plumbing" rows | B D7 says "absorbed by N3"; the C and D bespoke rows are the same `simp only [Complex.*_re, ...]; ring` skeleton. |
| `digamma_vertical_bound` | B N7 `digamma_vertical_floor`; C 2.7 `norm_digamma_le_log` | Same source lemma (`Zeta23.StirlingVert`), floor and norm faces. |
| `indicator_split_integral_floor` | B N8; C pattern 16 capped-minorant integral; C 2.10 tail-mass row | C 2.10 `integral_bumpR_mul_psiR_ge_capped` is B N8 with `m1 = -5`, `m2 = Theta`; C listed it as single-instance, B has two more. |
| `prime_side_gauss` | B N6; C 2.10 `primeAbsTerm_le`, `primeAbs_le_crude` | C's `nlinarith [sq_nonneg (log n - 16 lam)]` route is B N6's `amgm_uniform` mode verbatim. |
| prelude lemma (not a kind) | B N9 `involution_tsum`; C pattern 7; D 2.5 `hasSum_involution_average` | Three audits, no certificate data (B N9 "fixed atoms", C 5.1 row 7 "nothing numeric", D 2.5 "not an emitter"). Section 4. |
| `deriv_sign_monotone` | D shape B, kept separate from `curvature_boundary` | D 3.2: first-derivative sibling; the two compose but do not coincide (`curvature_boundary` needs a definite `f''` sign, README table). Share the derivative-chain renderer; do not merge the kinds. |

Standalone survivors, unchanged: `taylor_ladder` (C shape B), `local_count_fiber_sum`
(C shape C), `box_net_cover` (A N1), `signed_rank_one_inertia` (A N5),
`window_dominance` (B N4), `qseries_coefficient_decide` (A N6),
`power_sum_geometric_refutation` (A N7).

### 2.2 Top ten, by value per line

Rank = (instances x cross-applicability) / build cost, honesty of the channel as
tie-breaker (B Part IV). Instances are file:line as the source audit cites them; paths
under `examples/rvm_bridge/lean/` unless another island is named.

| Rank | Kind | Instances | Cross | Cost | Merged from |
|---|---|---|---|---|---|
| 1 | `enclosure_tree` | about 30 sites, all four audits | BG + RH | S-M | A N2/N3/N4, B C2, C 4.7, D 4 |
| 2 | `zero_sum_majorant` | 13 | RH (rvm, li, Zeta23) | S-M | C A, B N5 |
| 3 | `preordering_multiplier` | 5 groups + about 85 backfill sites | BG + P vs NP + RH | M | D A, B C3, C 5.3 |
| 4 | `complex_re_im_split` | 17 | every complex island | S | B N3, B D7, C, D |
| 5 | `exp_threshold` | 10 | BG + RH | S | B N2, C 4.5 |
| 6 | `gaussian_moment` | 9 + 5 identity sub-steps | RH (fourier, heat, xi) | M | B N1, C 15, C 4.6 |
| 7 | `taylor_ladder` | 9 + 2 cousins | P vs NP + BG + RH | S-M | C B |
| 8 | `deriv_sign_monotone` | 5 (duplicated across islands) | BG + RH | M-L | D B |
| 9 | `box_net_cover` | 5 + the capstone | RH boxes | S | A N1 |
| 10 | `signed_rank_one_inertia` | 10 | BG (`HodgeRiemann`) + RH | M | A N5 |

**1. `enclosure_tree`** (A N2, A N3, A N4; B C2; C 4.7; D section 4)

- Statement family: rational two-sided enclosure `lo < E < hi` (or non-strict) for an
  expression tree `E` over `{+, -, *, /, sqrt, log, exp, pi, arctan, rational constants}`
  whose radicands are enclosed intervals, denominators bounded away from zero, and
  `log` arguments positive rationals (A N2 a, A N3 a, A N4 a).
- Certificate data: per node the outward-rounded interval; per `sqrt` node two rational
  squares (or, for a bracketed radicand, the `sqrt hi <= q` fact, B C2); per `/` node the
  denominator sign; per `log` node the Taylor order `n`, partial sum `S_n(x)` and tail
  radius `|x|^{n+1}/(1-|x|)` with the prime factorisation of `r` into `|x| < 1` atoms
  (A N3 b); per `exp` node the `ExpEnclosure` order; per `pi` node the Mathlib
  `pi_gt_d2/d4/d6` or `pi_lt_dN` choice (D 4); per `arctan` node the fixed `|arctan x| <= |x|`
  or `x/2 <= arctan x` lemma (D 4); for the polynomial consumer the monomial-wise fold and
  the product hints `mul_nonneg (sub_nonneg.2 h_lo) ...` for degree `>= 2` (A N4 b, c).
- Tactic skeleton: `sqrt` node `have h2 := Real.sq_sqrt harg; have hn := Real.sqrt_nonneg
  X; constructor <;> nlinarith [h2, hn, <child bounds>]`; `/` node `rw [lt_div_iff0 hden];
  nlinarith`; `log` node `Real.abs_log_sub_add_sum_range_le hx n` then `norm_num
  [Finset.sum_range_succ] at h; constructor <;> linarith`, fold by `Real.log_mul`
  (A N2 c, A N3 c, verbatim `LeakageDictionary.lean:282-292, 296-308, 317-324, 326-337`);
  `log y <= c y^alpha` by `Real.log_le_sub_one_of_pos` at `t = y^alpha` (C 4.7).
- Refusals: radicand interval not `>= 0`; denominator interval containing 0; claimed bracket
  not implied by the fold; `r <= 0`; `|1 - r| >= 1` without a factorisation; order `n > 64`
  (the `sum_range_succ` cost cliff); inverted bracket; atom straddling 0 under an odd power
  without a split; non-rational inputs (A N2 d, N3 d, N4 d).
- Instances. A: `quasicrystal/lean/LeakageDictionary.lean:276-279` (`sqrt_five_bounds`,
  the `algebraic_bracket` miss), `:282-292`, `:296-313`, `:317-324`, `:326-337`, `:341-347`,
  `:349-359`; `LeakageInstances.lean:173-180`, `:184-188`; recurrences
  `li_positivity/lean/BlaschkeBox.lean:121`, `E6Bridge14.lean:117`, `E6Bridge16.lean:339-340`,
  `quasicrystal/lean/SelfInversiveOfflineInstances.lean:42,140,238`, `E6Bridge2.lean:542`,
  `E6Bridge11.lean:1051`, `zeta_reflection/lean/TrigReduceOperating.lean:162,339` (A C3, C4,
  N2 e, N3 e). B: `E6Bridge11.lean:1063-1065, 1066-1073, 1074-1076, 1077-1083, 1084-1095,
  1097-1099, 1437-1445, 1446-1452, 1453-1455` (B C2). C: `E6Bridge16.lean:341-347, 776-782,
  681-685, 348-350, 770-772, 783-790, 467` (C 2.10 first row), `E6Bridge23.lean:123-132`,
  `E6Bridge16.lean:418-426` (C 4.7). D: `li_positivity/lean/LiLadderHeight.lean:602-609`,
  `LiLadderSharp.lean:154-161` (`pi` face), `E6Bridge28.lean:200-207`,
  `LiLadderHeight.lean:303-315` (`arctan` face), the rational halves of
  `LiLadderHeight.lean:281-296` / `E6Bridge28.lean:354-365` (D 2.4, D 5 item 9).
- Cross-applicability: BG `sqrt 2` and `sqrt 23` cruxes (depth-0 case, A N2 f), the per-cell
  `log(1 + S/d)` atoms that `transcendental_enclosure` bounds only to degree 3 and the `F*`
  combinations of `log_combination` (A N3 f); RH every leakage / Bragg / Weil numeric
  instance (A N4 f); the `zeta_reflection` dyadic evaluator is a third hand route to the
  same atoms (A N3 e).
- Build cost: S-M. `ExpEnclosureEmitter` is the template for the order search and refusal
  on a non-implied bracket (A N3 g); the interval fold exists in
  `emit_leakage_dictionary.py:237-264` and needs extraction (A N4 g).

**2. `zero_sum_majorant`** (C 3.1; B N5)

- Statement family: for a term family `f p : C -> C` supported on the nontrivial zeros,
  a centre `a(p)`, near-radius `h in {0,1,2}` and far constant `C_far(p) >= 0`:
  `Summable (f p)` and `forall rho, ‖f p rho‖ <= zeroBound C_far b rho` with
  `zeroBound C b rho := (nearWindow a h).indicator b rho + m(rho) * C/(1 + normSq (gammaOf rho))`
  (C 3.1). Tail-envelope face: `‖tsum_S f‖ <= E * tsum w` from `‖f rho‖ <= E * w rho` on `S`
  with the rate-splitting companion `exp(2 lam phi) <= exp(2 (lam-1) P) exp(2 phi)` for
  `phi <= P < 0`, `lam >= 1` (B N5).
- Certificate data: the support rewrite (`zeroMult_eq_zero_of_not_nontrivial`); the far
  inequality reduced to `(x, y) = (Re rho, Im rho - a)` on `0 < x < 1`, `y^2 >= h^2` and
  certified as an all-nonneg-coefficient Polya form after `y^2 -> h^2 + t` (`handelman`
  fallback); the near-window bound `b`; for the tail face the constant `E` and rational
  `P < 0` (C 3.1, B N5).
- Tactic skeleton: `refine norm_le_zeroBound (fun rho h => <support>) ?_ ?_ (by positivity) rho`,
  far case `rw [div_le_div_iff0 (by positivity) (by positivity)]; nlinarith [<hints>]`,
  summability by `Summable.of_norm_bounded (summable_zeroBound _ _) (<name>_le _)`
  (parameterised copy of `E6Bridge19.lean:147-175, 331-355`); tail face
  `norm_tsum_le_tsum_norm` + `tsum_le_tsum` + `tsum_subtype_le` + `tsum_mul_left` (B N5).
- Refusals: `C_far < 0`; Polya/Handelman check fails (report the located negative point;
  `h = 0` with a `1/|rho|^2` shape is refused); support fact not hypothesis-free; near
  window not a bounded ordinate window; norm not of the form `m * N/D` with `D > 0` off the
  pole; tail face `P >= 0` (C 3.1, B N5).
- Instances. C 2.1: `E6Bridge15.lean:349-410`, `E6Bridge18.lean:116-184`,
  `E6Bridge19.lean:107-175` (the abstract atom), `:324-355`, `:586-595`, `:743-773`,
  `E6Bridge17.lean:266-289, 340-368`, `E6Bridge20.lean:186-193, 221-286`,
  `E6Bridge22.lean:49-69`, `E6Bridge24.lean:815-821`. B N5: `E6Bridge7.lean:465-483`
  (majorant `377-435`), `E6Bridge12.lean:269-291` (`224-265`), `E6Bridge14.lean:303-312`;
  the shared `w` `E6Bridge6.lean:483-504`.
- Cross-applicability: every zero sum on the rvm and li islands and the Zeta23
  `zero_sum_inv_sq` family; the four Tannery consumers (C pattern 8) take the emitted
  majorant as their bound; Li and xi-taylor tails (B N5). BG: the discrete analogues are the
  shipped `finite_prefix_absorption` and `low_order_tail`; no BG obligation of this shape
  was located, so the flow is RH to Telperion only (C 3.1, stated honestly).
- Build cost: S-M. The 70-line prelude exists in `E6Bridge19.lean:107-175`; the generator
  is the `emit_direct_polya` checker on the shifted form; all ten instances close today
  with at most three hints (C 3.1). Prerequisite: the `RvMBridgeXi` prelude (section 4).

**3. `preordering_multiplier`** (D 3.1; B C3; C 5.3 item 1; dogfood D 3.3)

- Statement family: `forall x in R^k, g_1(x) >= 0 -> ... -> g_m(x) >= 0 -> 0 <= p(x)` with
  POLYNOMIAL generators (disk, parabola, `gamma^2 - 3/4`, box faces) (D 3.1).
- Certificate data (LP-found): multiplier `M = prod g_i^{mu_i}`; exponent vectors and
  rationals `c_alpha >= 0` with the exact identity `M * p = sum c_alpha prod g_i^{alpha_i}` in
  the base variables; a locus certificate for `{M = 0}`; generators tagged `hyp` or
  `structural` (D 3.1).
- Tactic skeleton: `obtain ⟨d, hd0, hde⟩`, `set P := ... with hP`, `have key : M * P = ... := by
  rw [...]; ring`, `have hcert : 0 <= M * P := by rw [key]; positivity`, then the locus branch
  or `(mul_nonneg_iff_of_pos_left (by positivity)).mp hcert`; `M = 1` collapses to `rw [key];
  positivity` (D 3.1, copy of `LiBoxRungs.lean:157-182`).
- Refusals: LP infeasible up to the degree cap (OBSTRUCTED_AND_LOCATED with a numeric
  negative witness, `Q_6` at `(0.303, 0.931)`); any `c_alpha < 0`; a `hyp` generator that is
  not literally a hypothesis; a `structural` generator `positivity` cannot close; a
  multiplier with an uncertified zero locus (D 3.1).
- Instances. D: `li_positivity/lean/LiBoxRungs.lean:139-155` (`M = 1`), `:157-182` (`14 s`),
  `:184-212` (`s^2`), `:128-137` (`Re Q_1`, `Re Q_2`); `E6Bridge28.lean:815-866` (rungs 2..4);
  `LowHeightBox.lean:265-284` / `E6Bridge28.lean:746-750` (Box 2, degree 1). B C3:
  `E6Bridge6.lean:459-461`, `E6Bridge10.lean:198-201`, `E6Bridge11.lean:367-386`. C 5.3
  item 1 backfill sites (where Polya-after-shift is not enough): `E6Bridge22.lean:98-142`,
  `E6Bridge23.lean:35-50`, `E6Bridge17.lean:142-144`, `E6Bridge17.lean:109-158` (`hA`),
  `E6Bridge19.lean:894-983`, `E6Bridge21.lean:91-98`.
- Cross-applicability: BG `cavity_exchange` refuses "a corner with a negative coefficient
  (Polya fails, needs SOS)" and this is the rung before an SDP; `RealObligationA`'s
  sign-indefinite generic SPR; P vs NP knapsack level-2 residual and `Xor3Structure`
  moment forms; RH every box/annulus positivity in the zero-free islands and the
  Gaussian-window envelope cells (D 3.1).
- Build cost: M. Reuse `find_handelman_certificate`'s exact subset solver over polynomial
  generators, an outer loop over multipliers `g_j^k` (`k <= 3`), the locus branch generator;
  `ring` on degree-10 identities builds today (D 3.1).
- Dogfood family `li_box_rung` (D 3.3): hypothesis-free `0 <= Re(taylorCoeff riemannXi (N-1))`
  for `N <= 5` via `chebyshev_pair_polynomial(N)` + `consequence` cofactor + this kind on the
  disk, refusing `N = 6` with the located witness; retires five Arb hypotheses on
  `RH_li_rungs_lt_five`.

**4. `complex_re_im_split`** (B N3; B D7; C 2.10; D 2.2)

- Statement family: for a polynomial `p(z; params)` over `C` with real parameters,
  `(p z).re = P_re(z.re, z.im)`, `(p z).im = P_im(...)`, `‖p z‖^2 = P_re^2 + P_im^2`,
  `‖exp(q z)‖ = exp((q z).re)`; and the cast face "this complex expression is the cast of
  that real expression, so its `.re` is that real" (B N3, B D7).
- Certificate data: `p`, `P_re`, `P_im` computed by sympy `re`/`im` at `z = x + i y`,
  re-verified exactly (B N3).
- Tactic skeleton: `simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, ...,
  Complex.I_re, Complex.I_im, pow_two]; ring`; norms by `Complex.sq_norm`,
  `Complex.normSq_apply`, `Complex.norm_exp`; cast face `push_cast; ring` then
  `Complex.ofReal_re` (B N3, B D7).
- Refusals: non-polynomial `p` without a declared nonzero-denominator hypothesis; a
  supplied `P_re` disagreeing with sympy (B N3).
- Instances. B N3: `E6Bridge6.lean:408-421, 382-392`, `E6Bridge7.lean:76-86, 103-118`,
  `E6Bridge8.lean:84-85, 308-311, 409-410`, `E6Bridge10.lean:430-431`,
  `E6Bridge11.lean:396, 533, 649-652, 762-765`. B D7: `E6Bridge5.lean:110-114`,
  `E6Bridge7.lean:497-503`, `E6Bridge12.lean:122-126`, `E6Bridge14.lean:155-161`,
  `E6Bridge11.lean:1028-1034, 1420-1431`. C 2.10: `E6Bridge16.lean:272-291, 282-290`.
  D 2.2: `E6Bridge28.lean:755-807` (`Re (a + b i)^N`, `N = 2..5`).
- Cross-applicability: every complex-analysis island (`zero_free_bridge`,
  `borel_caratheodory`, the xi threads); BG none (B N3).
- Build cost: S, "the smallest and most frequent shape in the cluster" (B N3).

**5. `exp_threshold`** (B N2; C 4.5)

- Statement family: `linear` mode `Q/a <= lam -> Q <= exp(lam a)`; `log` mode
  `log(max 1 Q)/a <= lam -> Q <= exp(lam a)`; product forms `exp(-lam a)(lam a) <= 1`,
  `exp(-x) <= 1/x`, `y exp(-y) <= 1`; shifted-rate mode `P(y) e^{-r y} <= K e^{-r' y}` for
  `r' < r` (B N2, C 4.5).
- Certificate data: `(Q, a)` rational or symbolic, the mode, optional downstream
  `Q <= K exp(lam a)`; for the shifted-rate mode `(P, r, r')` and the emitted constant `K`
  (B N2, C 4.5).
- Tactic skeleton: `div_le_iff0` + `Real.add_one_le_exp` + `linarith` (linear);
  `Real.exp_log (lt_max_of_lt_left one_pos)` + `Real.exp_le_exp` (log); `Real.exp_neg` +
  `inv_mul_le_iff0` (product) (B N2).
- Refusals: `a <= 0`; a rational `Q` whose `Q/a` or `log(max 1 Q)/a` does not match the
  declared threshold (B N2).
- Instances. B N2: `E6Bridge7.lean:575-590`, `E6Bridge12.lean:311-316` (in `297-338`),
  `E6Bridge14.lean:78-86` (`le_exp_of_log_le`, the only factored one),
  `E6Bridge11.lean:1084-1095`, `:910-925`. C 4.5: `E6Bridge16.lean:315-317, 352-364,
  563-598, 435`, `E6Bridge17.lean:129-141`.
- Cross-applicability: composes with `eventual_threshold` (B C1 produces the max-of-ratios
  witness, this consumes each conjunct); BG `MonotoneRatioTail` / `uniform_tail` closings
  and `LogCombination` exp-vs-rational steps; nearest shipped kind `poly_exp_absorption`
  (B N2).
- Build cost: S (B N2).

**6. `gaussian_moment`** (B N1; C 2.10 pattern 15; C 4.6)

- Statement family: `M_k(a, w) := integral x^k exp(-a x^2) exp(i w x) dx =
  P_k(w, 1/a) sqrt(pi/a) exp(-w^2/(4a))`, `P_k` rational-coefficient, by the recurrence
  `M_{k+1} = (i w/(2a)) M_k + (k/(2a)) M_{k-1}`; real-frequency, zero-frequency, shifted
  modes; the heat-convolution prefactor identity as a sub-step (B N1, C 2.10).
- Certificate data: `(k, mode)`; the sympy coefficient table `P_0..P_k` re-verified against
  the recurrence as a rational-function identity; the exponent completing-the-square
  identity with its nonvanishing side conditions (`lam ≠ lam'`) (B N1, C 4.6).
- Tactic skeleton: a fixed prelude (Gaussian integrability calculus `E6Bridge8.lean:35-88`,
  one integration-by-parts step lemma generalised from `E6Bridge8.lean:100-152`,
  `M_0 = fourierIntegral_gaussian`); per instance `linear_combination`/`field_simp` from the
  step lemma then `ring`; casts by `integral_complex_ofReal` + `push_cast; ring_nf`;
  exponent identities by `push_cast; field_simp; ring` (B N1, C 4.6).
- Refusals: `a <= 0`; `k` outside `[0, 6]`; a coefficient table failing the recurrence (B N1).
- Instances. B N1: `E6Bridge8.lean:94-152`, `E6Bridge11.lean:105-133, 136-143, 241-285,
  612-703, 928-946`, `E6Bridge10.lean:227-277`; consumers `E6Bridge11.lean:725-814`,
  `E6Bridge8.lean:197-230`. C: `E6Bridge16.lean:58-151, 171-246`, `E6Bridge17.lean:558-625,
  629-653` (C 2.10); identities `E6Bridge16.lean:222-227, 282-290, 372-377`,
  `E6Bridge17.lean:519-554, 603-614`, `:584-598` (C 4.6).
- Cross-applicability: every Gaussian / heat-kernel test-function computation (the
  `fourier`, `survey-heat`, `xi-taylor` threads); BG no direct consumer (B N1).
- Build cost: M; the prelude is a port of existing proofs, the per-`k` closure is `ring` (B N1).

**7. `taylor_ladder`** (C 3.2)

- Statement family: a ladder `t k s = a k * (L s)^{-(k+p)}` with `L` affine, `p >= 1`, and
  a recurrence `a (k+1) = a k * r k`; emitted theorems L1-L7: closed form, norm, derivative
  step, evaluation with sign bookkeeping, elementary iterated derivatives and the parity
  atom `sum 1/(2n+1)^m = (1 - 2^{-m}) zeta(m)`, symmetry transfer, finite binomial
  reindexing (C 3.2).
- Certificate data: `(p, a 0, r)` with the closed form checked symbolically and the ratio
  identity; the tower checked numerically at `k = 0..8` against mpmath `polygamma` and
  `zeta` with `require_exact` on the rational coefficients (the `LIVALUE_TAYLOR` numerics
  become part of the certificate); reindex data `(shift, peel)` checked in `n` (C 3.2).
- Tactic skeleton: `unfold <a>; rw [Nat.factorial_succ]; push_cast; ring`;
  `(hasDerivAt_zpow ...).comp ... .const_mul ... |>.congr_deriv (by push_cast; ring)`;
  two fixed atoms `tsum_odd_inv_pow` (`E6Bridge19.lean:1070-1083` verbatim) and
  `iteratedDeriv_antisym` (`E6Bridge19.lean:1243-1267` generalised) (C 3.2).
- Refusals: closed form fails the ratio identity; `p <= 0` (belongs to `identity`);
  non-integer exponent; tower numeric disagreement beyond `1e-25` at any `k <= 8`; a
  reindex whose symbolic check fails; a symmetry not supplied as a hypothesis-free theorem
  (C 3.2).
- Instances: `E6Bridge19.lean:258-301, 396-411, 861-934, 937-983, 1051-1083, 1086-1145,
  1219-1236, 1243-1267, 1329-1372`; cousins `E6Bridge21.lean:78-89` /
  `E6Bridge22.lean:394-404` (trigamma rung) and the li `Q_N` Chebyshev recurrence (D 2.6,
  generator-side `chebyshev_pair_polynomial(N)`) (C 3.2).
- Cross-applicability: strong. P vs NP `fwd_telescope` is the forward-difference twin (shared
  `LadderCore`); BG `Ztot`/`Zopen` coefficient extraction and Kelmans cavity derivatives;
  RH Zeta23 digamma tower, li `taylorCoeff riemannXi n` rungs (C 3.2).
- Build cost: S-M (C 3.2).

**8. `deriv_sign_monotone`** (D 3.2)

- Statement family: for an elementary closed form `f` and interval `[a, b]` (endpoints may
  be `pi`-multiples), `AntitoneOn`/`MonotoneOn f (Icc a b)` and the corollary `f x <= f a`
  (D 3.2).
- Certificate data: `f'` as a `HasDerivAt` chain (sympy `diff` rendered over Mathlib's
  `Real.hasDerivAt_*` combinators); a sign certificate for `f'` (fixed sign table,
  `direct_polya`/`bernstein` when rational, or a RECURSIVE instance, depth `<= 3`); the
  endpoint value (D 3.2).
- Tactic skeleton: `antitoneOn_of_deriv_nonpos (convex_Icc a b) <continuity> ?_ ?_`, interior
  goal `rw [interior_Icc] at hx; rw [(hf x).deriv]; <sign certificate>` (copy of
  `LiLadderHeight.lean:201-217`) (D 3.2).
- Refusals: a factor of `f'` outside the sign table on the interval; a numeric sample of
  `f'` with the wrong sign (an honest negative control, never the decision); `f` not
  differentiable on `[a, b]`; recursion depth above 3; an endpoint the kernel cannot
  evaluate (D 3.2).
- Instances: `LiLadderHeight.lean:176-197, 201-217`; `E6Bridge28.lean:144-186` (the same
  two, duplicated), `:209-231` (`u/2 <= arctan u`, monotone face); `LiLadderHeight.lean:303-315`
  (`tan` route) (D 3.2).
- Cross-applicability: BG the `(7 + 3 mu)/(2 (3 + mu)) <= 17/14` step of
  `tight_cap_enclosure` and the transcendental `log(1 + S/d)` in `d`; RH the deferred
  Montgomery-Taylor `cot(1/sqrt 2)` face of `transcendental_enclosure`, the envelope
  `lam_*(T)`, xi-decay growth bounds; composes with `curvature_boundary` (D 3.2).
- Build cost: M-L; the derivative-chain renderer is the engineering (D 3.2).

**9. `box_net_cover`** (A N1; extends `grid_modulus_nonvanishing`)

- Statement family: for a rational rectangle `R` and grid `G` with half-extents `(hw, hh)`
  and radius `delta`: `Convex R R`, `G ⊆ R`, `forall z in R, exists g in G, ‖z - g‖ <= delta`,
  plus `R` avoids the pole `1`; the three hypotheses `nonvanishing_of_grid` consumes,
  in `R` (A N1 a).
- Certificate data: the existing `GridModulusNonvanishingCertificate` payload plus the
  column list; the tiling breakpoints `(t_k + t_{k+1})/2`, `(c_j + c_{j+1})/2` (A N1 b).
- Tactic skeleton: `convex_box` = `rintro` + `simp only [Complex.add_re, ...]` + `nlinarith`;
  `gridSet_subset_box` = `rintro g (rfl | ...)` + `norm_num`; `cell` = `norm_sub_le_of_sq_le`
  + `nlinarith [mul_nonneg ...]`; `box_covered` = nested `rcases le_or_gt z.im breakpoint`
  fan-out; capstone `exact nonvanishing_of_grid convex_box hderiv hM box_covered
  gridSet_subset_box hL gap_ok s ⟨...⟩` with `gap_ok` the EMITTED rational fact cast to
  `R` (A N1 c, `SpeiserBox.lean:62-117`).
- Refusals: a non-tiling grid (`rows[k+1] - rows[k] > 2 hh`, checked in Python today but never
  turned into Lean); `hw^2 + hh^2 > delta^2`; empty grid; degenerate box; rows out of order
  (A N1 d).
- Instances: `speiser_box_probe/lean/SpeiserBoxProbe/SpeiserBox.lean:62-67, 73-79, 83-92,
  95-117, 121-125`, capstone `:225-231` (A N1 e, A C2).
- Cross-applicability: every future box on any island ("a thousand boxes like it", the node's
  own discharge plan); shares the rational-rectangle vocabulary of `disjoint_discs` and
  `box_localization`; BG none (A N1 f).
- Build cost: S; all tactics green in the island, the work is templating (A N1 g).
  Prerequisite: hoist `nonvanishing_of_grid` and `norm_sub_le_of_sq_le` into a prelude
  (A C5, A D5). Why rank 9 despite five sites: it turns an emitter whose output is
  currently decorative (A D3) into a load-bearing one.

**10. `signed_rank_one_inertia`** (A N5)

- Statement family: for rational vectors `x_1..x_m, y_1..y_k in Q^d`, the inertia of
  `A = sum x_i x_i^T - sum y_j y_j^T`: `defect A <= k`, and `= k` exactly when the `y_j` are
  linearly independent and orthogonal to every `x_i`; degenerate faces `defect = rank(span y)`
  and `defect = 0` (A N5 a).
- Certificate data: the `k x k` Gram determinant of the `y_j` (or a nonzero minor); the
  `m k` inner products `⟨y_j, x_i⟩ = 0`, exact rationals (A N5 b).
- Tactic skeleton: instantiate `QuadrupleDefect.defect_sumPairBlock_le` / `_eq`
  (`QuadrupleDefect.lean:353-356, 410-420`); LI for `k = 2` via `LinearIndependent.pair_iff`
  + coordinate `congrFun` (`:533-539`, `BraggDefect.lean:279`); general `k` via
  `Fintype.linearIndependent_iff` or `Matrix.rank` by `decide` on the Q-cleared minor;
  orthogonality by `simp [dotR, Fin.sum_univ_four]` (`:527-531`) (A N5 c).
- Refusals: singular `y`-Gram when `= k` is claimed (the parallel-channel phantom
  `:442-470`); non-orthogonal pair when `= k` is claimed (`orthogonality_is_load_bearing`
  `:477-484`); `k = 0` (A N5 d).
- Instances: `zeta_zero_localization/lean/QuadrupleDefect.lean:341-356, 410-420, 442-470,
  477-484, 527-539, 551-565, 570-581`; `BraggDefect.lean:220` (`k = 1`), `:279`, `:316`
  (`k = 2`) (A N5 e).
- Cross-applicability: BG the `HodgeRiemann` fold-in of the 2026-09-02 roadmap is this
  object with `m = 1` (signature `(1, k)`, `examples/lorentzian`); RH every W2b window
  block; island-pinned to the ported `RHLinalg` / `DefectDictionary` block like
  `interval_gram_inertia` (A N5 f).
- Build cost: M; the general-`k` LI discharge is the only new Lean (A N5 g).

### 2.3 Fold-in sub-modes (not standalone kinds)

| Existing kind | Sub-mode | Source | Instances |
|---|---|---|---|
| `eventual_threshold` | accept the `max 1 (...)` guard as a conjunct; region-cover nested-max witness | B C1, C 4.2 | `E6Bridge7.lean:554-562`, `E6Bridge12.lean:106-109, 301-307`, `E6Bridge14.lean:66-75, 281-288`; `E6Bridge22.lean:305-334`, `E6Bridge24.lean:863-872` |
| `magnitude_split` | affine-in-`L` budget `‖sum T_i‖ <= (sum a_i + sum b_i)(1 + L)` | C 4.2 | `E6Bridge24.lean:540-541, 714-747`, `E6Bridge22.lean:229-244, 274-283`, `E6Bridge20.lean:564-583` |
| `fwd_telescope` | telescoping MAJORANT mode (`t n <= G n - G (n+1)`, `tsum <= G 0`) | C 4.1 | `E6Bridge21.lean:169-205` |
| `cauchy_deriv` | Liouville with sub-linear growth + constant pinned by a ray limit | C 4.3 | `E6Bridge18.lean:271-321, 331-353` |
| `far_pole_sum` | distance-floor mode with `Finset.sum_sdiff` assembly | C 4.4 | `E6Bridge24.lean:583-591, 653-679, 684-712`, `E6Bridge22.lean:151-162` |
| `rational_identity` | `C`-coefficient mode with real-parameter side conditions (feeds `gaussian_moment`) | C 4.6 | see rank 6 |
| `transcendental_enclosure` | `log y <= c y^alpha`, `arctan`, `pi` faces (all absorbed by `enclosure_tree`) | C 4.7, D 4 | see rank 1 |
| `algebraic_bracket` | strict flag; `sqrt_of_bracketed` (absorbed by `enclosure_tree`) | A C3, B C2 | see rank 1 |
| `consequence` | `laurent` mode with base `w`, relation `w v = 1` (generalises `exp_laurent_identity`) | D 4 | `LiBoxRungs.lean:89-124` |
| `second_order` | inhomogeneous three-term mode for `Q_{N+1} = (2 - z) Q_N - Q_{N-1} + 2 z` | D 2.6, D 4 | generator-side |
| `halfplane_disk` | inversion face `Re q >= c > 0 -> |1/q - 1/(2c)| <= 1/(2c)` | D 4 | `LiBoxRungs.lean:217-236` |
| `reflection_halving` | `tsum` mode shipping `hasSum_involution_average` | D 4, B N9, C 5.1 row 7 | section 4 lemma |
| `dichotomy_glue` | symbolic thresholds (`pi/2`, `3 pi/2`, `2 pi`) | D 4 | `LiLadderSharp.lean:112-121`, `E6Bridge29.lean:106-118` |
| `bernstein` | raise `max_elevation` or fall through to `sturm_positive` | D 4 | `E6Bridge28.lean:903-937` |
| `finite_decide` | q-series coefficient table mode with anti-phantom cross-checks as refusals (`qseries_coefficient_decide`, appendix) | A N6 | `SatakeDegreeTwo.lean:179-237` |
| `leakage_dictionary` | wire the negative-control adapter (one corrupted row entry) | A C1, A D4 | `emitter_sensitivity.py:757-762` |

## 3. Standing-order misses (consolidated)

Action key: REGEN = regenerate via the named emitter when the file is next touched;
BESPOKE = leave hand-written for the stated reason; NEW = wait for the section 2 kind.

| # | Pattern | Covering emitter | Instances | Action | Source |
|---|---|---|---|---|---|
| 1 | plain `sqrt` bracket | `algebraic_bracket` | `LeakageDictionary.lean:276-279`; `BlaschkeBox.lean:121`, `E6Bridge14.lean:117`, `E6Bridge16.lean:339-340` | REGEN (strict flag) or NEW rank 1 | A C3 |
| 2 | capstone re-proves the emitted gap inline and consumes hand-written `box_covered` | `grid_modulus_nonvanishing` | `SpeiserBox.lean:225-231` | NEW rank 9 (the emitted cert is decorative until then) | A C2, A D3 |
| 3 | `log_two_gt_d9` hand-wiring, three routes to one atom | none complete (`transcendental_enclosure` log face partial) | `LeakageDictionary.lean:341-347`, `E6Bridge2.lean:542`, `E6Bridge11.lean:1051`, `TrigReduceOperating.lean:162,339` | NEW rank 1 | A C4, A N3 |
| 4 | max-of-ratios threshold witnesses | `eventual_threshold` | `E6Bridge7.lean:554-562`, `E6Bridge12.lean:106-109, 301-307`, `E6Bridge14.lean:66-75, 281-288` | REGEN (guard conjunct fold-in) | B C1 |
| 5 | seam B transcendental brackets, eight rows | `transcendental_enclosure`, `exp_enclosure`, `algebraic_bracket`, `log_combination` | `E6Bridge11.lean:1061-1123, 1437-1483` | REGEN six rows; two `pi` rows NEW rank 1 | B C2 |
| 6 | box polynomial positivity by hinted `nlinarith` | `handelman` / `sos` | `E6Bridge6.lean:459-461`, `E6Bridge10.lean:198-201`, `E6Bridge11.lean:367-386` | BESPOKE until a build turns fragile (one line each, compiles) | B C3 |
| 7 | two-variable strip inequalities by hand `nlinarith` (79 calls) | `direct_polya` / `handelman` / `bilinear_corner` | seven shape-A sites (C 2.1), `E6Bridge22.lean:98-142`, `E6Bridge23.lean:35-50`, `E6Bridge17.lean:142-144`, `E6Bridge19.lean:894-983`, `E6Bridge21.lean:91-98` | NEW rank 2 (majorant sites) and rank 3 (the rest); the hint lists are the fragile part | C 5.3 item 1 |
| 8 | seven transcendental numerics of the sharp envelope | `exp_enclosure`, `algebraic_bracket`, `transcendental_enclosure`, `log_combination`, `exact_fact` | `E6Bridge16.lean:341-347, 776-782, 681-685, 348-350, 770-772, 783-790, 467`; `E6Bridge23.lean:123-132`; `E6Bridge16.lean:418-426` | REGEN now (five shipped emitters; first dogfood of rank 1) | C 5.3 item 2, C 2.10 |
| 9 | log rebasings `log(x + c) <= log(2 + |a|) + log c'` | `log_combination` monotone route | `E6Bridge24.lean:644-648, 680-683`, `E6Bridge23.lean:172-175`, `E6Bridge20.lean:577-579` | REGEN | C 5.3 item 3 |
| 10 | Gaussian exponent completing-the-square identities | `rational_identity` | `E6Bridge17.lean:519-554, 603-614`, `E6Bridge16.lean:222-227, 282-290, 372-377` | REGEN once the `C`-coefficient mode exists (2.3) | C 5.3 item 4 |
| 11 | `‖term f s n‖ <= ‖term f 2 n‖` | `rpow_budget` | `E6Bridge21.lean:277-287`, `E6Bridge22.lean:407-417` | REGEN once, keep the complex one only | C 5.3 item 5 |
| 12 | final Farkas closers `linarith only [eight bounds]` | `cone` / `magnitude_split` nterm | `E6Bridge16.lean:812-813`, `E6Bridge24.lean:745-747`, `E6Bridge22.lean:463-472` | BESPOKE (already deterministic), except `E6Bridge16` which needs `maxHeartbeats 1600000` at `:667`: REGEN that one | C 5.3 item 6 |
| 13 | trigamma term comparison `<= 4/(n+1)^2` | `monotone_tail` / `direct_polya` | `E6Bridge21.lean:78-116` | REGEN | C 2.8 |
| 14 | `rightDerivBound` triangle chain, `‖-1/s^2‖ <= 1/4` | `magnitude_split` + `disk_coord` | `E6Bridge22.lean:439-472` | REGEN | C 2.8 |
| 15 | `1/(1-rho) - 1/conj rho` fold and norm floors | `rational_identity` + `disk_coord` | `E6Bridge19.lean:756-773` | REGEN | C 2.9 |
| 16 | prime-side `Lambda(n)/sqrt n <= 2`, completed square, `zeta(2) <= 2` | `transcendental_enclosure`, `direct_polya`, `exact_fact`, `identity` | `E6Bridge16.lean:405-449, 461-469` | NEW appendix `prime_side_gauss` | C 2.10 |
| 17 | `Q_N` cofactors mod `w v = 1` | `consequence` | `LiBoxRungs.lean:98, 106, 115, 124` | REGEN (laurent mode) | D 5 item 1 |
| 18 | `Re Q_1`, `Re Q_2`, rungs 2..4 unpaired | `putinar` / rank 3 | `LiBoxRungs.lean:128-137`, `E6Bridge28.lean:815-866` | NEW rank 3 | D 5 items 2, 5 |
| 19 | five Bernstein-shaped `nlinarith` calls and the rung-5 Handelman in `(u, e)` | `bernstein`, `handelman` + substitution identity | `E6Bridge28.lean:903-937, 940-969` | REGEN (may need `max_elevation` raised or `sturm_positive`) | D 5 items 3, 4 |
| 20 | Box 2 as a cone combination; `g`-inequality; rung 0/1 numerators; rational halves of the log bound | `cone`, `direct_polya` | `LowHeightBox.lean:265-284`, `E6Bridge28.lean:746-750`; `LiLadderSharp.lean:59-65`, `E6Bridge29.lean:51-56`; `LiLadderHeight.lean:518-538`, `E6Bridge28.lean:500-508`; `LiLadderHeight.lean:281-296`, `E6Bridge28.lean:354-365` | REGEN (small; each is one `direct_polya` row) | D 5 items 6-9 |

Legitimately bespoke and correctly subsumed (not misses): triangle fan-outs in place
(B C4), finset cardinality macros (A C6), `interval_cases` dispatch (D 2.1), the on-line
`2(1 - cos) >= 0` (`unit_modulus_sos`, D 6), Cauchy at an existential radius (C 2.7),
Mathlib binomial sums (C 7).

## 4. Duplicated lemma groups and the prelude proposal

### 4.1 Consolidated table

| # | Fact | First | Second (third) | Mathlib-only | Source |
|---|---|---|---|---|---|
| 1 | `xi_one_sub` | `E6Bridge19.lean:62-66` | `E6Bridge20.lean:51-54` | no (island xi) | C 5.2 |
| 2 | `xi_eq_zero_iff` | `E6Bridge19.lean:74-85` | `E6Bridge20.lean:71-86` | no | C 5.2 |
| 3 | `logDeriv_xi_one_sub` | `E6Bridge19.lean:510-521` | `E6Bridge20.lean:471-477` | no | C 5.2 |
| 4 | `deriv_logDeriv_xi_one_sub` | `E6Bridge19.lean:1514-1524` | `E6Bridge20.lean:479-492` | no | C 5.2 |
| 5 | `oneSubEquiv` + `zeroMult_one_sub` | `E6Bridge19.lean:1492-1501` | `E6Bridge20.lean:495-505` | no | C 5.2 |
| 6 | `tsum_*_one_sub` | `E6Bridge19.lean:1504-1511` | `E6Bridge20.lean:507-516` | no | C 5.2 |
| 7 | `zeros_countable` | `E6Bridge19.lean:642-654` | `E6Bridge17.lean:786-797` | no | C 5.2 |
| 8 | local unit factor `logDeriv xi = m/(z - s0) + logDeriv u` | `E6Bridge20.lean:317-373` | `E6Bridge24.lean:310-334` | no | C 5.2, C 2.4 |
| 9 | `norm_term_le_of_two_le` real / complex | `E6Bridge21.lean:277-287` | `E6Bridge22.lean:407-417` | yes | C 5.2 |
| 10 | `deriv_logDeriv_xi_real` / `_of_one_lt_re` | `E6Bridge21.lean:330-370` | `E6Bridge22.lean:352-391` | no | C 5.2 |
| 11 | `1/|rho|^2 <= (9/4)/(1 + |gamma|^2)` | `E6Bridge15.lean:360-372` (inline) | `E6Bridge19.lean:120-133, 572-583` | yes | C 5.2 |
| 12 | majorant-with-indicator construction | `E6Bridge15.lean:379-410`, `E6Bridge18.lean:147-184` (hand) | `E6Bridge19.lean:109-175` (abstracted, not back-ported) | no | C 5.2 |
| 13 | Lemma A (`cosh a cos b <= 1`, two antitone levels) | `LiLadderHeight.lean:176-229` | `E6Bridge28.lean:144-196` | yes | D 5 |
| 14 | Lemma A'' window reflection | `LiLadderSharp.lean:46-54` | `E6Bridge29.lean:37-46` | yes | D 5 |
| 15 | `1/g + 1/(2 g^2) <= 1/(g - 1/2)` | `LiLadderSharp.lean:59-65` | `E6Bridge29.lean:51-56` | yes | D 5 |
| 16 | `|log|u|| <= 1/(2 gamma^2)` | `LiLadderHeight.lean:273-300` | `E6Bridge28.lean:335-373` | yes | D 5 |
| 17 | sawtooth `{x}`-kernel tail bound `<= 1/(2 sigma)` | `LowHeightBox.lean:115-193` (midpoint reflection) | `E6Bridge28.lean:526-635` (parts); `E6Bridge25.lean:40-61` (crude) | yes | D 5, C 5.1 row 14 |
| 18 | Box 1 / Box 2 | `LowHeightBox.lean:265-298` | `E6Bridge28.lean:703-750` | no (representations differ) | D 5 |
| 19 | `tail_bound` (tsum tail envelope) | `E6Bridge7.lean:465-483` | `E6Bridge12.lean:269-291`; `E6Bridge14.lean:303-312` | no | B N5 |
| 20 | `prime_term_bound` / `_uniform` | `E6Bridge11.lean:417-515` | `E6Bridge11.lean:1165-1239`; `E6Bridge10.lean:324-397` | no | B N6 |
| 21 | Tannery transfer of the zero sum against the local count | `E6Bridge6.lean:576-596` | `E6Bridge10.lean:149-167` | no | B D1 |
| 22 | window Finset from the local zero count | `E6Bridge12.lean:385-401` | `E6Bridge7.lean:201-217`; `E6Bridge14.lean:356-360, 426-446` | no | B D5 |
| 23 | mean-value nonvanishing instrument pinned to one island | `SpeiserBoxProbe/GridNonvanishing.lean:46-67` | `zero_free_bridge/lean/ZeroFreeElementary.lean:230`, `DlvpZetaPoleEffective.lean:86,153` | yes | A C5, A D5 |

Also multiply-derived disciplines that belong with the preludes (C 5.1): finite avoidance
via three different Mathlib routes (`E6Bridge19.lean:219-231`, `E6Bridge20.lean:159-170`,
`E6Bridge24.lean:479-492`, `E6Bridge17.lean:251-263`; B D3 `E6Bridge7.lean:219-253`);
compact bound on a rectangle (`E6Bridge22.lean:208-215`, `E6Bridge24.lean:823-858`);
punctured-identity continuity at 11 sites (`E6Bridge19.lean:1480-1489` factored,
`:1190-1214` inline, `E6Bridge21.lean:132-165`, `E6Bridge20.lean:428-449`,
`E6Bridge24.lean:419-432`); involution regrouping at 13 sites (B N9, C 5.1 row 7, D 2.5);
cutoff eventual constancy at 5 DCT sites (B D2).

### 4.2 Prelude proposal (must land before any section 2 emitter)

C 5.2 and D 5 both say the emitted Lean must reference one vocabulary; the emitters of
ranks 2, 6, 7 and 8 reference these lemmas by name.

**P1. `RvMBridgeXi.lean`** (island `rvm_bridge`, C 5.2 recommendation). Contents: rows 1-8
and 10 of the table, keeping the complex versions (row 9 complex, row 10 complex with the
real form as a corollary at `s = sigma`); the `zeroBound` atom of `E6Bridge19.lean:107-175`
generalised from `|Im rho| < 1` to a centred window of radius `h` (row 12, the prelude of
rank 2); the 9/4 strip inequality as one lemma (row 11); `tsum_reindex_involution
(e : C ≃ C) (hm : forall rho, m (e rho) = m rho)` (C 5.1 row 7, absorbs B N9 and D 2.5's
`hasSum_involution_average`); `exists_mem_Ioo_notMem_finset` (C 5.1 row 9, B D3);
`exists_bound_on_reProdIm` (C 5.1 row 10); `eq_of_continuousAt_of_eventually_ne` hoisted
from `E6Bridge19.lean:1480-1489` (C 5.1 row 11); `differentiable_of_punctured_eventuallyEq`
(C 2.4). E6Bridge15..24 then import it and drop their copies.

**P2. `RvMBridgeGauss.lean`** (island `rvm_bridge`, from B). Contents:
`summable_mult_div_one_add_normSq` as the shared `w` (already `E6Bridge6.lean:483-504`);
one `zeroWindow c D` + `mem_zeroWindow` (B D5, take E6Bridge12's); the generic tail
envelope (row 19, becomes rank 2's `tail_envelope` face); `zeroSide_tendsto_of_strip_bound`
(row 21, B D1); a `ContDiffBump`-cutoff transfer lemma parametrised by the majorant (B D2);
the Gaussian integrability calculus `E6Bridge8.lean:35-88` and one integration-by-parts
step lemma (the rank 6 prelude, B N1); the `j = 1` pairing bound `|Re(1/rho)| <= 1/|rho|^2`
(C 5.1 row 12, twice today).

**P3. `LiFacePrelude.lean`** (cross-island, D 5 recommendation). Contents: rows 13-17
(Mathlib-only). Row 13 becomes rank 8's first frozen output on both islands; row 17 keeps
ONE proof (the midpoint-reflection one is shorter, D 2.3) and retires the two others.
Constraint the audits record: the li island is on `v4.34` and rvm on `v4.33.0-rc2`
(D section 1 file table), and `interval_gram_inertia` is pinned to `v4.32.0` (README), so a
shared pack must build under both pins; if it cannot, generate it into each island from one
source with a `generate.py --check` drift gate (the `rvm_bridge` pattern A H6 names).

**P4. `BoxNetPrelude.lean`** (hoist out of `speiser_box_probe`, A C5/D5). Contents:
`nonvanishing_of_grid` and `norm_sub_le_of_sq_le`, so that `grid_modulus_nonvanishing`
and rank 9 are portable to a second box on another island; `ZeroFreeElementary.lean:230`
and `DlvpZetaPoleEffective.lean:86,153` are the other consumers (row 23).

Registry consequence: A H6's durable fix (generate island mirrors from
`Statements/*Defs.lean`) applies to P1-P4 as well; a prelude that drifts from its
consumers is the same failure as a mirror that drifts from its statement.

## 5. Honesty patterns to add to `docs/HONESTY_PATTERNS.md`

The file has eight patterns, all probe-side. Four new patterns and three notes recur across
the four audits.

**#9 Gate non-vacuity: every refusal gate ships a positive control that trips it** (A H1).
Instances: `tests/test_missions_mirror_drift.py:139-144` (#584, "a gate that silently
matches nothing passes forever"); `antiphantom_probe.py` (#590, corrupt the eta exponent
24 to 23/25/12 and assert refusal); #592's axiom-line floor (`n < 146` fails); #591's
anchored `'Name' (depends on axioms|does not depend)` match after the substring check was
satisfied by `leak_dh_enclosure_decimal` alone; #590's `-ne 14` probe-count pin. The
negative-control harness already does this for emitters; #9 is the same discipline for CI
greps and registry scans (A H1). D 3.1's `Q_6` refusal with a located witness is the
emitter-side instance (D 2.1).

**#10 Load-bearing-hypothesis twin: a conditional theorem ships a kernel witness that
deleting its hypothesis makes it false** (A H3). Instances:
`LeakageInstances.lean:206-212` (`leak_dh_multiplicativity_is_necessary`),
`ProbeSatake.lean:54-57` (`probe_hypothesis_is_load_bearing`),
`QuadrupleDefect.lean:477-484` (`orthogonality_is_load_bearing`), `:442-470`
(`defect_parallel_channels_eq_one` against the gloss of a true theorem); non-vacuity twins
`:255-259`, `:157-162`, `:231-242` (A H3). Kernel-side form of pattern #6. Emitter-shaped:
a `--twin` face for conditional kinds (A H3 recommends it as the next harness extension).

**#11 Triviality tiering by unfolding probe** (A H4). A statement is probed with `rfl` /
`simp [defs]` / `decide` / `aesop`, each expected to FAIL; a success is a finding. Three
tiers: definitional / classical / new. Instances: #583 `simp [twoFreq, linearTorusForm,
torusOrbit]` closes the T1 dictionary (tier 1); #588 attempts ledger, all four fail on
conjunct (i) (tier 2); #590 `ProbeSatake.lean` with 14 expected failures and a CI count pin
(A H4). The count pin should become "every `example` errors" (A H4). D's skeptic memo
(13 verdicts, 8 corrections folded in, D section 1) is the same discipline applied before
formalisation.

**#12 Named-residual ledger: a conditional proof names its residual as a `def : Prop`,
the registry lists it, and the axiom guard alone is never the grant** (A H7; C section 6;
D 2.7; B N4). Instances: `SpeiserBox.lean:187-198, 225-231` takes `SecondDerivBoundOnBox`
and `GridModulusLowerBound` as hypotheses so the guard prints three standard axioms
precisely because the open content is a hypothesis (A H7, `AxiomGuardSpeiserBoxProbe.lean:10-14`);
the rh reduction ladder `_of_livalue -> _of_partial_fraction -> _of_strip -> unconditional`
with each obligation a `def : Prop` and never a `sorry` (C section 6, "honesty pattern 8 at
node granularity"); `NoRealZeroInStrip` as a named `Prop` discharged from Box 1
(`LiLadderHeight.lean:553-581`, D 2.7 "a model of the honest named-residual pattern");
`WindowOnLine c D`, `hB : constB c <= Bmax`, `henc`, `hhead` carried as hypotheses across
the toolchain seam (B scope note, B N4 "Open rung, honestly"); D 2.7's instruction to quote
`#print axioms` on `liValue_of_two`, `local_count_sum`, `stripDerivBound` before calling
the closed form unconditional. Recommended mechanism: a registry field
`[proof] open_obligations = [...]` the grant gate must find as `def`/hypothesis names in the
artifact and print in the node title (A H7); #590's registered statement containing no
`Delta`, `tau` or L-function is the accounting failure this catches (A H8).

**Notes under #8** (the verdict record):
- Crash is not a verdict: a tooling failure is `NULL`, never `OBSTRUCTED`; run the matrix,
  check the exit status, then grep (#590 `ModuleNotFoundError` read as "the clause no
  longer rejects"; #592 `tee` masking lean's exit code) (A H2).
- A boolean without a provenance field cannot carry a ruling: `closure_clean = (status ==
  "proved")` laundered a deliberate `False`; a stored `False` needs a
  `closure_override_reason` (A H5, `verify.py:475-490`).
- The trust ladder kernel > arb > mpmath-numeric ("EVIDENCE, NOT A PROOF") should be
  written once in the README trust-model section (A H7, `emitter_sensitivity.py:692-704`).

**Note under #7** (mechanical cover versus conceptual seam): an instrument that reports
where it is blind. `offline_zeros_small_or_margin` (`E6Bridge14.lean:366-422`) returns
"within `y0` of the line" or "in a margin the instrument cannot see"; the "slide the band"
dichotomy is a discipline, not a shape (B D6).

## 6. Defects and registry cosmetics (action list for the lead)

Open-PR defects (A 2.4):

1. **PR #592 breaks the `dbn` island guard.** The hunk at
   `.github/workflows/telperion-lean-e2e.yml` `@@ -2350` (working directory
   `telperion/examples/dbn/lean`) replaces `lake env lean AxiomGuardDBN.lean` with
   `AxiomGuardSpeiserBoxProbe.lean` and copies the Speiser floor comment; only
   `AxiomGuardDBN.lean` exists there. With `pipefail` the step fails; either way DBN is
   unguarded. Fix before merge (A D1).
2. **PR #591 and PR #592 both edit the leakage guard step** (`@@ -2970`); #592's version
   lacks #591's anchored-name matches and the `ofReduceNat` marker. Merge #591 first, rebase
   #592 (A D2).
3. **`SpeiserBoxCert` is decorative**: consumed only by the axiom guard, not by the capstone
   (A D3). Closed by rank 9; until then the drift gate protects nothing the capstone uses.
4. **`leakage_dictionary` has no negative-control adapter** (`NEG_CONTROL_DECLARED_UNWIRED`,
   `emitter_sensitivity.py:757-762`); the forge case is one corrupted row entry (A D4).
5. **`grid_modulus_nonvanishing` is not portable**: emitted Lean references
   `SpeiserBoxProbe.nonvanishing_of_grid` by name on one island (A D5). Closed by P4.

Registry cosmetics:

6. `RH_bl_explicit_formula.toml` title still reads "Stated only, NOT proved" followed by the
   reduced chain while `status = "proved"`; a substring check on the title would misfire.
   Its `[readback]` is the 2026-09-18 statement read-back, not the 2026-09-21 unconditional
   audit `attempts.jsonl` cites (C section 6).
7. #590's registered statement contains no `Delta`, no `tau`, no L-function; every
   `Delta`-specific theorem is unregistered. Should block a grant under the current node
   name (A H8, the #590 auditor's finding 1).
8. #590's `-ne 14` probe-count pin is brittle; replace with "every `example` errors" (A H4).
9. `mirrors.py` gates `mirrormere` verbatim and only REPORTS `rh`, `anduril`, `bg`; the
   durable fix is to generate mirrors from `Statements/*Defs.lean` (A H6).
10. No rh node carries emitter provenance (zero `via = "emitter"` across
    `missions/rh/nodes/*.toml`, C section 6); the section 7 dogfood targets are how that
    number moves off zero.

## 7. Recommended build order for the next emitter sprint

Each step names the existing hand proofs the emitter regenerates first (dogfood), so the
CI kernel gate confirms byte-equivalence or a green rebuild before the kind is used on a
new instance. The AxiomGuard stays the only gate (C section 8).

**Sprint 0, prerequisites (no new kinds).** Fix defects 1 and 2; wire the
`leakage_dictionary` adapter (defect 4); land P4 then P1, P2, P3 (section 4.2) and delete
the duplicates in table 4.1. Backfill the pure REGEN rows of section 3 that need no new
kind: rows 4, 8, 9, 13, 14, 15, 17, 20 (five shipped emitters cover the `E6Bridge16`
numerics alone, C section 8 item 5).

**Sprint 1, the three cheapest high-frequency kinds.**
1. `enclosure_tree` (rank 1). Dogfood: `LeakageDictionary.lean:276-359` (all nine bracket
   lemmas, A N2/N3), `LeakageInstances.lean:173-188` (A N4), `E6Bridge16.lean:341-350,
   681-685, 770-790, 467` (C 2.10), `E6Bridge11.lean:1061-1099, 1437-1455` (B C2),
   `LiLadderHeight.lean:602-609` and `LiLadderSharp.lean:154-161` (D `pi` face).
2. `complex_re_im_split` (rank 4). Dogfood: `E6Bridge7.lean:76-86, 103-118`,
   `E6Bridge6.lean:408-421`, the six B D7 cast sites, `E6Bridge28.lean:755-807`.
3. `exp_threshold` (rank 5) with the `eventual_threshold` guard fold-in. Dogfood:
   `E6Bridge7.lean:554-590` (threshold plus its two exponential consequences together),
   `E6Bridge14.lean:66-86`, `E6Bridge16.lean:315-317, 352-364`.

**Sprint 2, the two structural kinds.**
4. `zero_sum_majorant` (rank 2), after P1. Dogfood: `E6Bridge19.lean:324-355` (`zbound`,
   parametric in `k`), `E6Bridge18.lean:116-184` (`polBound`), `E6Bridge15.lean:349-410`
   (`liBound`), then the tail face on `E6Bridge7.lean:465-483` and `E6Bridge12.lean:269-291`
   (byte-identical today, B N5).
5. `preordering_multiplier` (rank 3). Dogfood: `LiBoxRungs.lean:139-212` (`Re Q_3`, `Q_4`,
   `Q_5` with multipliers `1`, `14 s`, `s^2`), `E6Bridge28.lean:815-866` (rungs 2..4),
   `E6Bridge6.lean:459-461` (B C3); then the `li_box_rung` family on `RH_li_rungs_lt_five`
   with the `N = 6` refusal (D 3.3), which also retires five Arb hypotheses and gives the rh
   registry its first `via = "emitter"` node.

**Sprint 3, the analytic ladders.**
6. `taylor_ladder` (rank 7). Dogfood: `E6Bridge19.lean:258-301` (`coef`, `zterm`),
   `:861-983` (`dcoef`, `dterm`, `dbound`), `:1086-1145` (`archCoeff` tower with the
   `LIVALUE_TAYLOR` numerics as certificate), `:1329-1372` (reindex).
7. `gaussian_moment` (rank 6), after P2. Dogfood: `E6Bridge11.lean:105-143` (`M_2`, `w = 0`),
   `E6Bridge8.lean:94-152` (`M_1`), `E6Bridge11.lean:612-703` (the 90-line `M_2` at real `w`),
   `E6Bridge16.lean:58-151` (complex frequency, C 2.10).
8. `box_net_cover` (rank 9), after P4. Dogfood: `SpeiserBox.lean:62-125` and the capstone
   `:225-231` consuming the emitted `gap_ok`; this is what makes defect 3 go away.

**Sprint 4, the heavier renderers.**
9. `deriv_sign_monotone` (rank 8), sharing the derivative renderer with
   `curvature_boundary`. Dogfood: Lemma A both levels (`LiLadderHeight.lean:176-217`) emitted
   into P3 once and consumed on both islands; `E6Bridge28.lean:209-231` (`arctan`, monotone
   face). Then the deferred trig face of `transcendental_enclosure` (D 3.2).
10. `signed_rank_one_inertia` (rank 10). Dogfood: `BraggDefect.lean:220` (`k = 1`), `:316`
    (`k = 2`), then `QuadrupleDefect.lean:341-356, 410-420` as instantiations; the BG
    `examples/lorentzian` `HodgeRiemann` instance as the cross-flow (A N5).

**After the sprint**, in this order: `local_count_fiber_sum` (appendix, dogfood
`E6Bridge23.lean:35-270` and `E6Bridge24.lean:60-156`), because it is the `Bmax` rung that
`window_dominance` carries as an undischarged hypothesis (B N4, `E6Bridge14.lean:426-446`
is the first step); then `prime_side_gauss`, `digamma_vertical_bound`,
`indicator_split_integral_floor`, `window_dominance`; the `finite_decide` q-series mode when
the A1b repair produces its second instance (A N6); `power_sum_geometric_refutation` only
when the degree-`d` version the node TOML commits to exists (A N7).

## Appendix: candidates 11-17

| # | Kind | Statement family (one line) | Instances | Cross | Cost | Source |
|---|---|---|---|---|---|---|
| 11 | `local_count_fiber_sum` | `exists C, forall a, sum_rho m w(Im rho - a) <= C (1 + log(2 + |a|))` by ceiling-fibre regrouping against `Ncount t (t+1) <= A0 log(|t| + 3)`; finite face `sum_window m <= (ceil W0 + 1) A0 log(|a| + W0 + 2)`. Certificate: fibre domination `w x <= W k`, log split, tail exponent `alpha > 1` with `K`, the constants `S1`, `S2`, the cover card by `decide`. Refuses `alpha <= 1` (the false phantom `sum 1/(1 + |gamma - a|) = O(log)`), a count bound not of the form `A0 log(|t| + c)`, a negative weight | `E6Bridge23.lean:35-270` (whole file), `E6Bridge24.lean:60-156`, `E6Bridge14.lean:426-446`; same sum at `a = 0` in Zeta23 `zero_sum_inv_sq` and `E6Bridge6` | RH-internal (no BG obligation located, stated honestly); gates #15 | M | C 3.3 |
| 12 | `prime_side_gauss` | from `|f(log n)| <= A exp(-(log n)^2/(16 lam))` and `Lambda(n)/sqrt n <= 2`, `‖primeSide f‖ <= K zeta(2) <= 2K`; modes `sigma_gate` (`log 2/(16 lam) >= 2`) and `amgm_uniform` (`sq_nonneg (log n - 16 lam)`). Skeleton `interval_cases n`, `vonMangoldt_le_log`, `Real.log_le_sub_one_of_pos`, `hasSum_zeta_two`. Refuses `lam <= 0`, a `sigma_gate` `lam` with `log 2/(16 lam) < 2`, a non-Gaussian majorant | `E6Bridge11.lean:417-515, 1165-1239`, `E6Bridge10.lean:324-397`; `E6Bridge16.lean:405-449, 461-469` | RH (symbolic companion of `bragg_floor`, `weil_form_enclosure`) | M | B N6, C 2.10 |
| 13 | `digamma_vertical_bound` | floors on `Re psi(1/4 + i t)` (global `-5`, `>= 2` beyond `|r| >= 41`, `>= log(|r|/2) - 5`) and the norm bound `‖psi z‖ <= log(2 + |Im z|) + pi + 7/2` on `0 < Re z <= 2`, `|Im z| >= 1`, from `Zeta23.StirlingVert`. Certificate `(a, R0, target)` with an exact `exp` bracket for the margin. Refuses `R0` below Stirling validity, a target above the margin | `E6Bridge11.lean:148-166, 169-192, 1242-1258`; `E6Bridge24.lean:160-201` | RH: gives `window_form_floor` a kernel floor for its undischarged `henv` (relaxed mode) | M | B N7, C 2.7 |
| 14 | `indicator_split_integral_floor` | `integral w psi >= m2 integral w - (m2 - m1) integral_S w` from `psi >= m1` everywhere and `>= m2` off `S`; tail modes sup-times-measure or Gaussian halving; capped-minorant face. Skeleton `by_cases hr : r in S` + `nlinarith`, `integral_mono`, `integral_indicator`. Refuses `m2 <= m1`, an `S` without a certified tail | `E6Bridge11.lean:963-993, 1324-1368` (tails `951-959`, `1279-1319`); `E6Bridge16.lean:602-647, 563-598` | RH archimedean floors (`xi-decay`, `survey-heat`); BG continuous analogue of the hinge floor only | S | B N8, C 2.10, C 5.1 row 16 |
| 15 | `window_dominance` | the seam C instrument as a `weil_form_enclosure`-style numeric channel: rational ordinate brackets with multiplicities, `W_lo <= windowSum`, `Bmax >= constB c`, `E_hi >= exp(2(lam-1)(1/4 - D^2))`, kernel proves `tailEnvelope <= windowSum` then applies `gaussian_positivity_of_window_dominance`. Refuses missing `Bmax`, `E_hi Bmax > W_lo`, a bracket count disagreeing with the ladder, `lam < 1`. Open rung: `Bmax` needs an explicit zero-count bound, i.e. #11 | `E6Bridge12.lean:441-451`; `E6Bridge14.lean:269-351` | RH only | M | B N4 |
| 16 | `qseries_coefficient_decide` | `finite_decide` sub-mode: kernel-computed coefficient table of a truncated eta-quotient to order `N` by `decide`, with Hecke / multiplicativity cross-checks as certify-time refusals (the `antiphantom_probe.py` discipline promoted). Refuses a table entry disagreeing with Python, a failed cross-check, `N` beyond the kernel budget, any `Q` in the table | `SatakeDegreeTwo.lean:179-237` (7 theorems), `zoo.py` `_delta_tau_upto`, `antiphantom_probe.py` | BG matching-polynomial tables (`R47R4Kelmans*Cert`), P vs NP Petersen precedent; RH future degree-`d` clause repairs | S | A N6 |
| 17 | `power_sum_geometric_refutation` | `(exists t, forall m >= 1, p_m = t^m)` iff all but one root vanish; at `d = 2` the cofactor `-1/2` in `linear_combination`; general `d` via Newton-Girard cofactors. Refuses `d = 1`, quantifier over `m >= 0` (the `0^0 = 1` collapse) | `SatakeDegreeTwo.lean:107-122, 147-150` (one instance) | adjacent to `second_order`; BG none | S at `d = 2` | A N7 |

Demoted, not a kind: `involution_tsum` (B N9). Instances now served by P1's
`tsum_reindex_involution` / `hasSum_involution_average`: `E6Bridge6.lean:165-176, 350-373`,
`E6Bridge12.lean:189-194, 419-434`, `E6Bridge14.lean:131-140`, `E6Bridge15.lean:144-149,
227-259`, `E6Bridge19.lean:381-390, 775-780, 1492-1511`, `E6Bridge20.lean:495-516`,
`E6Bridge24.lean:504-536`, `E6Bridge28.lean:460-477` (B N9, C 5.1 row 7, D 2.5).

## What this document does not say

It does not say any candidate advances RH or BG (B "What this audit does not say", C 3,
D header). Every kind above certifies a step already kernel-checked by hand in these
clusters; building them makes the next island cheaper and lets the CI kernel gate confirm
regenerated instances. Two candidates (ranks 2 and 11) found no BG obligation of their
shape, so for them the standing order's cross-flow is RH to Telperion only (C 3.1, C 3.3).
conjecture1_proved = False.
