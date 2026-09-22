# Shapes audit A: missions tooling + mirrormere cluster (2026-09-22)

`conjecture1_proved = False`. Nothing in this document bears on the Riemann Hypothesis.
It is a bookkeeping audit under `docs/CROSS_POLLINATION_STANDING_ORDER.md`: every
recurring hand-written proof pattern in the cluster is checked against the shipped emitter
set (README "Certificate shapes", 153 `kind = "..."` classes in `src/telperion/*.py`) and
either (i) attributed to an existing kind, (ii) written up as a candidate emitter in the
`EMITTER_ROADMAP_2026-09-02_RH_CROSSCUT.md` format, or (iii) recorded as a gate/honesty
discipline for `docs/HONESTY_PATTERNS.md`.

Cluster: PRs #583, #584, #585, #586, #588, #589 (merged) and #587, #590, #591, #592 (open)
of `DrMurphyIsIn/Arda`. Read-only audit; no files in the cluster were changed.

## 1. PRs and files read

| PR | State | Subject | Files read (Lean and Python only; TOML/JSONL/docs skimmed) |
|---|---|---|---|
| #583 | merged | T1 torus dictionary is notation; node title corrected | `missions/mirrormere/nodes/MM_torus_section_dictionary.toml`, `MM_torus_section_n2_rigidity.toml` |
| #584 | merged | mirror-drift gate | `src/telperion/missions/mirrors.py` (new), `tests/test_missions_mirror_drift.py` (new) |
| #585 | merged | `closure_clean` is a copy of status | `src/telperion/missions/verify.py`, `tests/test_missions_verify.py`, `nodes/MM_bragg_defect_witness.toml` |
| #586 | merged | MM_speiser_box_probe, kind `grid_modulus_nonvanishing` | `examples/speiser_box_probe/lean/SpeiserBoxProbe/{SpeiserBox,GridNonvanishing,Cert}.lean`, `AxiomGuardSpeiserBoxProbe.lean`, `SpeiserBoxProbe.lean`, `generate.py`, `src/telperion/emit_grid_modulus_nonvanishing.py`, `negctrl_adapters/adapter_grid_modulus_nonvanishing.py`, `emitter_sensitivity.py` (entry), CI job |
| #587 | open | W2b quadruple audit | `examples/zeta_zero_localization/lean/QuadrupleDefect.lean` (new, 583 lines), `AxiomGuardDefect.lean`, `docs/MM_W2B_QUADRUPLE_AUDIT_2026-09-19.md`, `nodes/MM_offline_pairs_le_defect.toml`, `attempts.jsonl` |
| #588 | merged | MM_leakage_composite_zero, kind `leakage_dictionary` | `examples/quasicrystal/lean/{LeakageDictionary,LeakageInstances,LeakageNode}.lean`, `AxiomGuardLeakage.lean`, `src/telperion/emit_leakage_dictionary.py`, `examples/leakage_dictionary/generate.py`, `Statements/MM_leakage_composite_zero.lean`, CI job |
| #589 | merged | statement body detection | `src/telperion/missions/statements.py`, `tests/test_missions_statement_body.py` |
| #590 | open | A1b Satake degree-2 falsification | `examples/quasicrystal/lean/{SatakeDegreeTwo,ProbeSatake}.lean` (new), `AxiomGuardQC.lean`, `examples/quasicrystal/{zoo.py,antiphantom_probe.py}`, `Statements/MM_satake_degree_two_rejects_delta.lean`, node TOML, CI job |
| #591 | open | leakage guard anchored; A2b title deflated | CI leakage guard step, `nodes/MM_leakage_composite_zero.toml`, `MM_torus_section_dictionary.toml` |
| #592 | open | island axiom guards hardened | `.github/workflows/telperion-lean-e2e.yml` (eight guard steps) |

Recurrence outside the cluster was checked by grep over `examples/**/*.lean` and
`missions/**/*.lean` (excluding `.lake`). Every "recurs at" citation below is from that scan.

## 2. Findings, classified

### 2.1 COVERED by an existing (or freshly minted) kind

**C1. Divisor-recursion coefficient chain** (`LeakageInstances.lean:37-75`, `111-149`,
one lemma per divisor `d | n`: `hb d` + `Nat.divisors` expansion by `decide` +
`Finset.sum_insert` + rewrite of smaller coefficients + `linarith`).
Kind: `leakage_dictionary` (minted in the same PR, #588). Legitimately promoted at birth;
`LeakageInstances.lean` is generated and drift-gated by `generate.py --check`. No miss.
Gap noted: the kind is `NEG_CONTROL_DECLARED_UNWIRED` (`emitter_sensitivity.py:736-762`);
no `negctrl_adapters/adapter_leakage_dictionary.py` exists, although the forge case
(corrupt one row entry, `linarith` fails) is a two-line adapter. Wire it.

**C2. Rational certificate arithmetic for the Lipschitz net** (`Cert.lean:45-74`:
covering radius, gap, column span, row tiling, all `unfold; norm_num`).
Kind: `grid_modulus_nonvanishing` (minted in #586). Promoted at birth, adapter wired
(`adapter_grid_modulus_nonvanishing.py`). **But see N1**: the emitted theorems are
consumed by nothing except the axiom guard (`AxiomGuardSpeiserBoxProbe.lean:44-48`).
The capstone `speiser_box_probe_of_numeric` (`SpeiserBox.lean:225-231`) re-proves the gap
inline with `(by norm_num)` and consumes the HAND-WRITTEN `box_covered`,
`gridSet_subset_box`, `convex_box` instead. The emitter certifies the arithmetic in `ℚ`;
the theorem that needs it is proved by hand in `ℝ`. That is a standing-order miss inside
the PR that minted the kind.

**C3. Plain square-root bracket** `lo < √a < hi` for rational `a`
(`LeakageDictionary.lean:276-279` `sqrt_five_bounds`: `Real.sq_sqrt` + `Real.sqrt_nonneg`
+ `nlinarith`).
Kind: `algebraic_bracket` (`Real.le_sqrt_of_sq_le` + `Real.sqrt_le_iff`, `norm_num`).
Standing-order MISS: this instance should have been emitted. The only difference is
strict vs non-strict, which the emitter could take as a flag. Recurs at
`li_positivity/lean/BlaschkeBox.lean:121` (`nlinarith [Real.sq_sqrt 506.5, ...]`),
`rvm_bridge/lean/E6Bridge14.lean:117`, `E6Bridge16.lean:339-340`. The NESTED and
QUOTIENT forms (`sqrt_inner_bounds` :282-292, `dhKappa_gt/lt` :296-308) are NOT covered;
see N2.

**C4. Mathlib decimal log constants** (`log_two_bounds` :341-347 via
`Real.log_two_gt_d9`/`lt_d9`). Kind: none needed; but the same hand-wiring recurs at
`rvm_bridge/lean/E6Bridge2.lean:542`, `E6Bridge11.lean:1051`,
`zeta_reflection/lean/TrigReduceOperating.lean:162,339`. Folded into N3.

**C5. Mean-value inequality on a convex set** (`GridNonvanishing.lean:46-67`
`nonvanishing_of_grid`, via `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`).
Recurs at `zero_free_bridge/lean/ZeroFreeElementary.lean:230`,
`DlvpZetaPoleEffective.lean:86,153` (the `_deriv_le` variant). Thin certificate, heavy
fixed skeleton: a LEMMA-PACK item (the `parametric_holomorphy` precedent), not an emitter.
Recommendation: hoist `nonvanishing_of_grid` and `norm_sub_le_of_sq_le` into a shared
prelude module; the `grid_modulus_nonvanishing` emitter depends on them by name but they
live only on the `speiser_box_probe` island, so the kind is not portable to a second box.

**C6. Explicit finset cardinality from pairwise distinctness**
(`QuadrupleDefect.lean:140-147` `quad_card_eq_four`, chain of
`Finset.card_insert_of_notMem`). Recurs at
`zeta_zero_localization/lean/BoxLocalization.lean:190`, `RHInBox.lean:267-270`,
`g1_floors/lean/Duality.lean`. No certificate data; a tactic macro, not an emitter.
Not a miss.

**C7. Kernel-computed integer table by `decide`** (`SatakeDegreeTwo.lean:215-223`
`tau_one..tau_six`). Kind: `finite_decide` covers guarded `∀ i ∈ table, P i` by kernel
`decide` and already records the "ℚ does not kernel-reduce, use ℤ" footgun that
`ProbeSatake.lean:38-43` rediscovers. The truncated power-series generator
(`cmul/cpow/etaAux`, :179-212) is new; see N6.

### 2.2 NEW SHAPE candidates

Format per the 2026-09-02 roadmap: (a) statement family, (b) certificate data,
(c) Lean skeleton, (d) refusals, (e) instances in this cluster, (f) cross-applicability,
(g) build cost.

**N1. BoxNetCover** (extend `grid_modulus_nonvanishing`; ranked 1)

- (a) For a rational rectangle `R = [r0,r1] x [i0,i1] ⊆ ℂ` and a rational grid
  `G = {c_j + i t_k}` (columns `c_j`, rows `t_k`) with cell half-extents `(hw, hh)` and
  radius `δ`: `Convex ℝ R`, `G ⊆ R`, and `∀ z ∈ R, ∃ g ∈ G, ‖z − g‖ ≤ δ`. These are the
  three hypotheses `nonvanishing_of_grid` consumes, in `ℝ`, and they are fully determined
  by the certificate the emitter already has.
- (b) Exactly the existing `GridModulusNonvanishingCertificate` payload plus the column
  list; the emitter re-derives the tiling breakpoints `(t_k + t_{k+1})/2` and
  `(c_j + c_{j+1})/2` that the `le_or_gt` case split uses.
- (c) The hand proofs are already the skeleton: `convex_box` = `rintro` + `simp only
  [Complex.add_re, ..., Complex.real_smul]` + `nlinarith` (`SpeiserBox.lean:62-67`);
  `gridSet_subset_box` = `rintro g (rfl | ... )` + `norm_num` (:77-79); `cell` =
  `norm_sub_le_of_sq_le` + `nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2),
  ...]` (:83-92); `box_covered` = nested `rcases le_or_gt z.im breakpoint` fan-out, one
  `cell` call per grid point (:95-117). For multi-column grids add one outer `le_or_gt`
  level on `z.re`. Then emit the capstone by `exact nonvanishing_of_grid convex_box
  hderiv hM box_covered gridSet_subset_box hL gap_ok s ⟨...⟩` with `gap_ok` the EMITTED
  rational fact cast to `ℝ`, so the emitted certificate becomes load-bearing.
- (d) Refuse: a grid that does not tile (`rows[k+1] − rows[k] > 2 hh`, already checked
  in Python, :251-255, but never turned into Lean); `hw² + hh² > δ²`; an empty grid; a
  degenerate box; rows out of increasing order.
- (e) `SpeiserBox.lean:62-67`, `73-79`, `83-92`, `95-117`, `121-125`
  (`box_subset_compl_one` is a fourth determined fact: the box avoids the pole `1`).
- (f) Any future box on any island (the node TOML's own discharge plan is "a thousand
  boxes like it"); `disjoint_discs` and `box_localization` share the rational-rectangle
  vocabulary; RH-side `zero_free_bridge` boxes. BG: none direct.
- (g) Small (S). All tactics are already green in this island; the work is templating.

**N2. RadicalExpressionEnclosure** (extends `algebraic_bracket`; ranked 3)

- (a) Rational two-sided enclosure `lo < E < hi` for an expression tree `E` over
  `{+, −, ×, /, √, rational constants}` whose radicands are themselves enclosed
  intervals (nested radicals) and whose denominators are bounded away from zero.
- (b) Per node, the interval computed by exact outward rounding; per `√` node the two
  rational squares; per `/` node the sign certificate of the denominator interval.
- (c) Per `√` node: `have h2 : (√X)^2 = X := Real.sq_sqrt harg; have hn := Real.sqrt_nonneg
  X; constructor <;> nlinarith [h2, hn, <child bounds>]`; per `/` node:
  `rw [lt_div_iff₀ hden]`/`div_lt_iff₀` + `nlinarith [<child bounds>]`. This is verbatim
  `LeakageDictionary.lean:282-292` and `:296-308`.
- (d) Refuse: a radicand interval not `≥ 0`; a denominator interval containing `0`; a
  claimed `(lo, hi)` not implied by the folded interval; non-rational inputs.
- (e) `LeakageDictionary.lean:282-292` (`sqrt_inner_bounds`, nested), `:296-313`
  (`dhKappa_gt`, `dhKappa_lt`, `dhKappa_bounds`, quotient). Recurs:
  `quasicrystal/lean/SelfInversiveOfflineInstances.lean:42,140,238`
  (`Real.sq_sqrt hq1.le, hq2.le` inside `nlinarith`/`simp`), `BlaschkeBox.lean:121`.
- (f) BG: the `√2` crux (`e2_two_rhoB`) and `√23` are the depth-0 case; the Laplacian
  ratio `ρ_B` route has quadratic-irrational constants. RH: every quasicrystal constant
  (DH `κ`, Golden-ratio `√5` atoms), the `zeta_reflection` dyadic evaluator produces exactly
  these as inputs.
- (g) Small-to-medium (S-M): sympy interval fold is trivial; the `nlinarith` hint lists
  need the product hints for degree-2 nodes (the hand proofs show which).

**N3. LogTaylorBracket** (the `log` twin of `ExpEnclosureEmitter`; ranked 2)

- (a) Rational two-sided enclosure `lo ≤ log r ≤ hi` for a positive rational `r`, at a
  chosen Taylor order `n`, via Mathlib's `Real.abs_log_sub_add_sum_range_le
  (hx : |x| < 1) (n) : |Σ_{i<n} x^{i+1}/(i+1) + log(1−x)| ≤ |x|^{n+1}/(1−|x|)`, with
  `r = 1 − x`, and the multiplicative fold `log(∏ p^e) = Σ e·log p` (`Real.log_mul`,
  `Real.log_pow`) to reach any positive rational from `|x| < 1` atoms.
- (b) The order `n`, the rational partial sum `S_n(x)` and the tail radius
  `|x|^{n+1}/(1−|x|)`, both exact; the prime factorization of `r` and the atom table
  (`log 2` from `Real.log_two_{gt,lt}_d9` or itself from the series at `x = −1`, which is
  outside the radius, so `2 = (3/2)·(4/3)` or the Mathlib constant).
- (c) `have hx : |x| < 1 := by rw [abs_lt]; constructor <;> norm_num; have h :=
  Real.abs_log_sub_add_sum_range_le hx n; rw [show (1:ℝ) − x = r by norm_num] at h;
  rw [abs_le] at h; norm_num [Finset.sum_range_succ] at h; constructor <;> linarith
  [h.1, h.2]` (verbatim `LeakageDictionary.lean:317-324` at `x = −1/2`, `n = 24`); the
  fold by `Real.log_mul (by norm_num) (by norm_num)` + `linarith` (`:326-337`,
  `:349-359`). The emitter picks the least `n` whose box fits the claimed bracket,
  exactly as `ExpEnclosureEmitter` does for `exp`.
- (d) Refuse: `r ≤ 0`; `|1 − r| ≥ 1` without a factorization; a claimed bracket the
  Taylor box does not imply; order `n > 64` (the `norm_num [Finset.sum_range_succ]`
  unfolding cost cliff); an inverted bracket.
- (e) `LeakageDictionary.lean:317-324` (`log_three_halves_bounds`), `:326-337`
  (`log_six_bounds`), `:349-359` (`log_three_bounds`), `:341-347` (`log_two_bounds`).
  Recurs (hand-wired `log_two_gt_d9`): `rvm_bridge/lean/E6Bridge2.lean:542`,
  `E6Bridge11.lean:1051`, `zeta_reflection/lean/TrigReduceOperating.lean:162,339`. The
  `zeta_reflection` island carries a THIRD independent log route (`CertVerify` dyadic
  interval arithmetic); three hand routes for one atom is the signature of a missing kind.
- (f) BG: the per-cell `log(1 + S/d)` atoms that `transcendental_enclosure` bounds only
  to degree 3 (`Real.exp_bound'`), and the `F*` log-combinations of `log_combination`;
  N3 gives width-controllable two-sided brackets that both could consume. RH: every
  `log p` atom in every leakage/Bragg instance. This is the highest-reuse candidate.
- (g) Small (S). `ExpEnclosureEmitter` is the template (order search, outward rounding,
  refusal on non-implied bracket); the Lean lemma is pinned in v4.32.0
  (`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`).

**N4. AtomPolynomialEnclosure** (shared consumer core for N2/N3; ranked 4)

- (a) Given hypotheses `lo_i < A_i < hi_i` for atoms `A_i` (square roots, logs, a named
  constant) and a polynomial `P ∈ ℚ[A]`, the rational enclosure `L < P(A) < U`.
- (b) The expanded polynomial; the monomial-wise interval fold (already implemented as
  `emit_leakage_dictionary.interval_of`, :237-264, sign-aware for even powers); the list
  of product hints `mul_nonneg`/`mul_pos` of bound differences that `nlinarith` needs for
  degree `≥ 2` monomials.
- (c) `obtain ⟨hb0lo, hb0hi⟩ := <atom lemma>; ... ; constructor <;> nlinarith [hb0lo,
  hb0hi, ..., sq_nonneg A_k]` (verbatim `LeakageInstances.lean:173-180`); for degree
  `≥ 3` emit explicit `have := mul_nonneg (sub_nonneg.2 hb0lo) (sub_nonneg.2 hb1lo)`
  products rather than trusting `nlinarith`'s degree-2 search.
- (d) Refuse: a claimed `(L, U)` outside the monomial-wise fold; an atom with no
  interval; an atom interval straddling `0` under an odd power without the split.
- (e) `LeakageInstances.lean:173-180` (`leak_dh_enclosure`), `:184-188` (decimal
  corollary), `LeakageDictionary.lean:296-308` (`dhKappa` is `P/Q` in two atoms).
- (f) BG: this is the shape of every compact-core cell after `transcendental_enclosure`
  replaces `e_v` by a bracket; the 2026-09-02 roadmap built `transcendental_enclosure`
  precisely to feed such an `nlinarith` and left the consumer hand-written. RH: all
  Weil-form/Bragg numeric instances.
- (g) Small (S), if factored out of `emit_leakage_dictionary.py` where it already lives.

**N5. SignedRankOneSumInertia** (generalizes `defect_witness`, sister of
`interval_gram_inertia`; ranked 5)

- (a) For explicit rational vectors `x_1..x_m, y_1..y_k ∈ ℚ^d`, the inertia of the signed
  Gram sum `A = Σ x_i x_iᵀ − Σ y_j y_jᵀ`: `defect A ≤ k` unconditionally and
  `defect A = k` exactly when the `y_j` are linearly independent and orthogonal to every
  `x_i`; plus the two degenerate faces `defect = rank(span y)` for parallel channels and
  `defect = 0` when the on-line channel absorbs the off-line one.
- (b) The `k × k` Gram determinant of the `y_j` (nonzero for LI) or a nonzero `k × k`
  minor; the `m·k` inner products `⟨y_j, x_i⟩ = 0`, all exact rationals.
- (c) Instantiate `QuadrupleDefect.defect_sumPairBlock_le` / `defect_sumPairBlock_eq`
  (`:353-356`, `:410-420`); LI for `k = 2` via `LinearIndependent.pair_iff` + coordinate
  `congrFun` (`:533-539`, `BraggDefect.lean:279`); general `k` via
  `Fintype.linearIndependent_iff` on the explicit matrix, or `Matrix.rank` of the
  concatenated `k × d` matrix by `decide` on the ℚ-cleared integer minor; orthogonality
  by `simp [dotR, Fin.sum_univ_four]` (`:527-531`).
- (d) Refuse: a singular `y`-Gram when `= k` is claimed (the parallel-channel
  configuration `:442-470` is the phantom the kernel already exhibits); a non-orthogonal
  pair when `= k` is claimed (`orthogonality_is_load_bearing`, `:477-484`); `k = 0`.
- (e) `QuadrupleDefect.lean:341-356`, `410-420`, `442-470`, `477-484`, `551-565`,
  `570-581`; `BraggDefect.lean:220` (`bragg_defect_eq_one`, `k = 1`), `:316`
  (`defect_eq_two`, `k = 2`).
- (f) BG: the `HodgeRiemann` fold-in listed in the 2026-09-02 roadmap ("Lorentzian-
  signature reverse Cauchy-Schwarz as a completing-the-square Gram") is the SAME object
  with `m = 1` (one positive channel, signature `(1, k)`); `examples/lorentzian` would be
  the BG instance. RH: every W2b window block. Island-pinned to the ported `RHLinalg` /
  `DefectDictionary` block, like `interval_gram_inertia`.
- (g) Medium (M): the general-`k` LI discharge is the only new Lean; everything else is
  instantiation of the three theorems #587 already proved.

**N6. QSeriesCoefficientDecide** (sub-mode of `finite_decide`; ranked 6)

- (a) A kernel-computed coefficient table of a truncated q-product / eta-quotient
  `∏ (1 − q^n)^{e_n}` to order `N`, emitted as `coeff k = v_k := by decide`, together
  with the arithmetic cross-checks (Hecke recursion `τ(p²) = τ(p)² − p^{k−1}`, coprime
  multiplicativity) as further `decide` theorems.
- (b) The exponent vector, the order `N`, the table `v_k` computed in Python, and the
  cross-check pairs; the emitter REFUSES to emit if its own table fails a cross-check
  (the `antiphantom_probe.py` discipline, promoted from a probe to a certify-time gate).
- (c) `cmul`/`cone`/`cpow`/`oneSubQPow`/`etaAux` over `List ℤ` (`SatakeDegreeTwo.lean:
  179-212`) with `set_option maxRecDepth 100000`; `theorem tau_k : tau k = v := by decide`
  (`:215-223`); cross-checks `:234-237`.
- (d) Refuse: a table entry that disagrees with the Python computation; a cross-check
  that fails; `N` beyond the kernel budget (measure it; `tauOrder = 6` builds); any `ℚ`
  in the table (the FiniteDecide footgun).
- (e) `SatakeDegreeTwo.lean:179-237` (7 theorems), `examples/quasicrystal/zoo.py`
  `_delta_tau_upto` (the Python twin, PR #590), `antiphantom_probe.py`.
- (f) BG: matching-polynomial / permanent coefficient tables for named trees
  (`R47R4Kelmans*Cert`) are integer tables of the same kind; the P-vs-NP ladder's
  Petersen certificate is the precedent. RH: any modular-form coefficient instance in a
  future degree-`d` clause repair (the node TOML says the repair needs "`d` parameters
  per prime", so more of these are coming).
- (g) Small (S). One generator, one `decide` template.

**N7. PowerSumGeometricRefutation** (ranked 7, prospective)

- (a) For a degree-`d` Newton power sum `p_m = Σ_j α_j^m`, `(∃ t, ∀ m ≥ 1, p_m = t^m)`
  iff all but one `α_j` vanish; at `d = 2` the certificate is the single cofactor
  `−1/2` in `linear_combination (−1/2) * h2` after substituting `h1`.
- (b) For general `d`: the Newton-Girard elimination cofactors expressing the elementary
  symmetric functions `e_2..e_d` from `p_1..p_d`; the emitter computes them exactly.
- (c) `SatakeDegreeTwo.lean:107-122`: specialize the `∀ m` hypothesis at `m = 1..d`,
  `simp only [powerSum, pow_one]`, `rw [← h1] at h2`, `linear_combination`. Backward
  direction by `simp [zero_pow (Nat.one_le_iff_ne_zero.mp hm)]`.
- (d) Refuse `d = 1` (vacuously geometric); quantifier over `m ≥ 0` (Lean `0^0 = 1`
  collapses the predicate, the auditor's load-bearing-guard finding).
- (e) One instance only (`:107-122`, `:147-150`); listed because the A1b node's own
  REPAIR paragraph commits to the degree-`d` version.
- (f) Adjacent to `second_order_recurrence` (closed forms of sequences with
  characteristic roots `α, β`). BG: none.
- (g) Small (S) at `d = 2`; medium at general `d`.

### 2.3 GATE / HONESTY patterns (missions tooling)

Each entry says whether it belongs in `docs/HONESTY_PATTERNS.md`. The current file has
eight patterns, all probe-side (`ProbeVerdict` modules). Three of the disciplines below
recur across three or more PRs in this cluster and are not in the file.

**H1. Gate non-vacuity: a gate must be shown able to fire** (PRs #584, #590, #591,
#592). Instances: `test_the_scan_actually_finds_the_known_mirrors`
(`tests/test_missions_mirror_drift.py:139-144`, "a gate that silently matches nothing
passes forever"); `antiphantom_probe.py` (corrupt the eta exponent 24 to 23/25/12 and
assert the cross-checks REFUSE, "a gate nobody has ever seen fire is not a gate");
#592's axiom-line floor (`n < 146` fails: "a guard that elaborates to NOTHING passes
`! grep -q sorryAx`"); #591's anchored `'Name' (depends on axioms|does not depend)` match
after the substring check was satisfied by `leak_dh_enclosure_decimal` alone; #590's
`-ne 14` probe-count pin. **Belongs in HONESTY_PATTERNS.md as pattern #9**: every
refusal gate ships a positive control that trips it. The negative-control harness
already does this for emitters (forge → kernel rejects); H1 is the same discipline for
CI greps and registry scans.

**H2. Crash is not a verdict** (PR #590 CI job): run the falsification matrix first,
check the exit status, and only then grep for the mathematical string; a
`ModuleNotFoundError` had been read out as "the clause no longer rejects L(s,Δ)".
Also #592: `2>&1` + `set -euo pipefail` because `tee` masked lean's exit code and stderr
never reached the grepped file. **Belongs in HONESTY_PATTERNS.md** as a corollary of
pattern #8's taxonomy: a tooling failure is `NULL`, never `OBSTRUCTED`; the CI text
should say so explicitly (the #590 job does).

**H3. Load-bearing-hypothesis twin** (PRs #587, #588, #590). Every conditional theorem
ships a kernel witness that deleting its hypothesis makes it false:
`LeakageInstances.lean:206-212` (`leak_dh_multiplicativity_is_necessary`),
`ProbeSatake.lean:54-57` (`probe_hypothesis_is_load_bearing`),
`QuadrupleDefect.lean:477-484` (`orthogonality_is_load_bearing`), `:442-470`
(`defect_parallel_channels_eq_one` against the GLOSS of a true theorem), and the
non-vacuity twins (`exists_nondegenerate_cm_logDerivCoeff` :255-259,
`satake_pair_exists` :157-162, `quad_online_card` :231-242). **Belongs in
HONESTY_PATTERNS.md as pattern #10**; it is the kernel-side form of pattern #6
(circularity/strength: a reduction needs a separating witness). It is also
emitter-shaped: a `--twin` face for conditional kinds that emits the hypothesis-dropped
refutation next to the theorem. Recommend as the next harness extension after H1.

**H4. Triviality tiering by unfolding probe** (PRs #583, #588, #590). A statement is
probed with `rfl` / `simp [defs]` / `decide` / `aesop`, each expected to FAIL; a probe
that succeeds is a finding. #583: `simp [twoFreq, linearTorusForm, torusOrbit]` closes
the T1 dictionary, tier 1 (notation); #588 attempts ledger: all four fail on conjunct
(i), tier 2 (classical, content is the formalization); #590: `ProbeSatake.lean` with 14
expected failures and a CI count pin. **Belongs in HONESTY_PATTERNS.md as pattern #11**
with the three-tier scale the 2026-09-20 auditor used (definitional / classical /
new). A `probe_triviality.py` that generates the probe file from a statement module is
a natural small tool; the count pin (`-ne 14`) is brittle and should become
"every `example` errors", which is what the gate means.

**H5. A boolean without a provenance field cannot carry a ruling** (PR #585).
`grant_status` writes `closure_clean = (status == "proved")`, so a deliberate `False`
from a read-back ("carries the Arb `exp` hypothesis") was laundered to `True`; it
cannot be repaired because authored nodes default to `False` and a default is
indistinguishable from a ruling (`verify.py` comment block, `:475-490`). The fix is the
ascent-plan `closure_override_reason` field, an owner's decision. Belongs in
HONESTY_PATTERNS.md as a note under pattern #8: a `VALIDATED` needs evidence, and a
stored `False` needs a reason, or it will be overwritten by the next grant.

**H6. Statement-artifact coherence requires vocabulary coherence** (PR #584). The grant
gate matches statement to artifact by normalized containment; if an island's re-declared
`def` drifts, the gate passes and the node reads `proved` about different constants.
`mirrors.py` gates `mirrormere` (31 declarations verbatim) and only REPORTS `rh`,
`anduril`, `bg` (cosmetic namespace/binder differences; "a noisy gate gets switched
off"). The durable fix named in the module is to GENERATE mirrors (the `rvm_bridge`
`generate.py --check` pattern). Not a HONESTY_PATTERNS item; it is a registry design
invariant for `MISSIONS_DESIGN`. Recommend a follow-up that makes `Statements/*Defs.lean`
the generator input for every island mirror.

**H7. Named open obligations are invisible to the axiom guard** (PR #586). The capstone
`speiser_box_probe_of_numeric` takes `SecondDerivBoundOnBox` and `GridModulusLowerBound`
as hypotheses (`SpeiserBox.lean:187-198`, `:225-231`), so the guard prints the three
standard axioms precisely BECAUSE the open content is a hypothesis, not a `sorry`
(`AxiomGuardSpeiserBoxProbe.lean:10-14` says so; #591's comment block says the same for
name-only greps: "a theorem weakened by an added hypothesis passes every one of them").
Recommend a registry field `[proof] open_obligations = [...]` that the grant gate must
find as `def`/hypothesis names in the artifact and print in the node title, so a
conditional proof cannot be granted as unconditional by the axiom check alone.
Also #586 introduced the trust class `"mpmath-numeric"` below `"arb"`; the
`emitter_sensitivity` entry (`:692-704`) records it, and the certificate labels it
"EVIDENCE, NOT A PROOF". That ladder (kernel > arb > mpmath-numeric) should be written
down once, in the trust-model section of the README.

**H8. Deflation is recorded in the title, and the blind read-back records what the
auditor was not shown** (PRs #583, #587, #590, #591). Titles rewritten to the deflated
claim (`MM_torus_section_n2_rigidity`: "RESTATES its sibling ... counts as ACCOUNTING";
`MM_leakage_composite_zero`: "a FORMALIZATION win, not new mathematics";
`MM_offline_pairs_le_defect`: "the CONDITIONAL rigidity direction"); each `[readback]`
names what the auditor saw (statement + MMDefs only; or built Lean and ran probes).
Already the missions discipline; noted for recurrence. The #590 auditor's finding 1
(the REGISTERED statement contains no Δ, no τ, no L-function; every Δ-specific theorem
is unregistered) is the accounting analogue of H7 and should block a grant of that node
under its current name.

**H9. Last-declaration proof-body detection** (PR #589). Depth-0 `:=` scan of the final
declaration, skipping comments, strings, and binder defaults `(h : a := b)`. Tooling
correctness, not an honesty pattern; the tests pin the live malformation
(`sorry := by sorry`).

### 2.4 Defects found incidentally (not shape findings)

**D1. PR #592 (open) breaks the `dbn` island guard.** The hunk at
`.github/workflows/telperion-lean-e2e.yml` `@@ -2350` (working-directory
`telperion/examples/dbn/lean`) replaces `lake env lean AxiomGuardDBN.lean` with
`lake env lean AxiomGuardSpeiserBoxProbe.lean` and copies the Speiser floor comment
("17 anchors ... at least 15"). Only `AxiomGuardDBN.lean` exists in `examples/dbn/lean`.
With `pipefail` the step fails on a missing file; either way the DBN island is no longer
guarded. Copy-paste error; must be fixed before merge.

**D2. PR #591 and PR #592 both edit the same leakage guard step** (`@@ -2970`); they
will conflict on merge, and #592's version lacks #591's anchored-name matches and the
`ofReduceNat` marker. Merge #591 first and rebase #592.

**D3. The emitted `SpeiserBoxCert` is decorative** (see C2/N1): consumed only by the axiom
guard, not by the capstone. Until N1 lands, the emitter's kernel theorems certify
arithmetic that the proof re-derives by hand, so the drift gate protects nothing the
capstone depends on.

**D4. `leakage_dictionary` has no negative-control adapter** (`NEG_CONTROL_DECLARED_
UNWIRED`, `emitter_sensitivity.py:757-762`), although the forge case is one corrupted
row entry. The AXLE registry tolerates the state; the standing order does not intend it
to be permanent.

**D5. Portability of `grid_modulus_nonvanishing`** (see C5): the emitted Lean references
`SpeiserBoxProbe.nonvanishing_of_grid` by name, which exists only on one island. A second
box on another island cannot use the kind without copying the instrument. Hoist the two
general lemmas into a prelude module.

## 3. Ranked NEW SHAPE candidates

| Rank | Candidate | Why this rank | Cost |
|---|---|---|---|
| 1 | **N1 BoxNetCover** (extend `grid_modulus_nonvanishing`) | Turns an emitter whose output is currently decorative (D3) into one whose output the capstone consumes; the tactic skeleton is already green in `SpeiserBox.lean:62-117`; every future box needs it | S |
| 2 | **N3 LogTaylorBracket** | Three independent hand routes to `log p` atoms in the repo (`abs_log_sub_add_sum_range_le`, `log_two_gt_d9` wiring, `CertVerify` dyadic); direct twin of the shipped `ExpEnclosureEmitter`; feeds BG `log(1+S/d)` cells with controllable width | S |
| 3 | **N2 RadicalExpressionEnclosure** | `algebraic_bracket` was MISSED for `sqrt_five_bounds`; the nested and quotient faces (`κ`) have no kind at all; recurs on four islands | S-M |
| 4 | **N4 AtomPolynomialEnclosure** | The consumer that N2/N3 (and the shipped `transcendental_enclosure`) feed; already implemented as `interval_of` inside `emit_leakage_dictionary.py`, needs only extraction | S |
| 5 | **N5 SignedRankOneSumInertia** | Instantiates the three general theorems #587 proved; retires `bragg_defect_eq_one`/`defect_eq_two` as hand instances; is the BG `HodgeRiemann` fold-in from the 2026-09-02 roadmap | M |
| 6 | **N6 QSeriesCoefficientDecide** | Seven `decide` theorems plus the anti-phantom cross-checks, promoted from probe to certify-time refusal; more instances promised by the A1b repair plan | S |
| 7 | **N7 PowerSumGeometricRefutation** | One instance today; listed because the degree-`d` version is committed to in the node TOML | S |

Honesty-pattern additions recommended for `docs/HONESTY_PATTERNS.md`, in order:
**H1 gate non-vacuity** (four PRs), **H3 load-bearing-hypothesis twin** (three PRs),
**H4 triviality tiering** (three PRs), then H2 and H5 as notes under pattern #8.

`conjecture1_proved = False`.
