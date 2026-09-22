# COMPUTE JOB PLAN -- `AND_ladder_1e13` (ANDURIL G5, height 10^13)

*Authored 2026-09-22 on worktree `arda-goal-weil`, branch `mm/gauss-window`. Design memo
plus costed compute plan. NO Lean work was done, NO registry mutation was made, NO build
was started. The node stays `draft`. This document changes nothing about the registry;
every registry action named below is for the lead to take or refuse.*

**`conjecture1_proved = False`. Nothing in this document proves, or contributes a proof
step toward, the Riemann Hypothesis.** `AND_ladder_1e13` is a FINITE verification target
(every zero with `0 < Im rho <= 10^13` on the line). A finite prefix is not evidence for
RH; certified prefixes are morally forced by on-line verification (RH_ASCENT_PLAN F5,
standing label: *instrumentation, not evidence*). RH-equivalent nodes (`RH_conjecture`,
`MM_zeta_comb_membership`) are out of scope here.

---

## 0. Verdict in one paragraph

**HOLD. Do not staff. Keep `draft` as the campaign's honesty marker** (RH_ASCENT_PLAN F5-4,
WALL_BACKLOG_MAP row `AND_ladder_1e13`). No Lean route exists today, no artifact, no
attempt, no build here or anywhere. This plan is the only output the node admits now:
the exact theorem, the route, the named obligations with honest sizes, the compute jobs
with their certificate shapes, and the trust seam. It also records **two findings that
tighten the charter** and that the lead should carry before any staffing decision:

1. **The registered statement is at HEIGHT 10^13, i.e. about 4.3 x 10^13 zeros** (section 1.2).
   The charter's "surpass 10^13 certified zeros (Gourdon)" is a zero COUNT whose height is
   about 2.45 x 10^12. The node as registered is 4.3x Gourdon and 3.5x Platt-Trudgian by
   zero count. Every cost below is given for both readings; the lead must pick one.
2. **A3 as chartered (theta branch + RS main sum + Gabcke C0 remainder, evaluated per grid
   point) cannot reach 10^13 at any compute budget** (section 5.1: about 10^7 core-years even
   natively compiled). G5 additionally needs a VERIFIED FFT-amortized multi-evaluation
   (Odlyzko-Schoenhage / Platt) inside the native island -- an unauthored, unpriced,
   first-of-kind obligation this memo names `A5` (section 4, O4). Without it the 10^13 rung
   has no route at all, native or not.

---

## 1. The statement, exactly

### 1.1 As registered (island vocabulary)

`telperion/missions/anduril/lean/Statements/AND_ladder_1e13.lean` (generated, by-design
placeholder proof, no artifact linked):

```lean
theorem all_nontrivial_zeros_up_to_height_1e13 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 10000000000000 → ρ.re = 1 / 2
```

This is VERBATIM the conclusion type of the island capstones (`AllZeros_h280000.lean:569`,
`all_nontrivial_zeros_up_to_height_280000_of_bands`) with the literal replaced. `riemannZeta`
is Mathlib's; no pre-restriction to the strip; trivial zeros are excluded by `0 < ρ.im`.
Consumers downstream (`AllZerosUpToHeight.height_chain`, the Bragg/W4a instruments) see
exactly this shape, so a G5 artifact would be consumed with no adapter.

### 1.2 What the height literal means numerically (the discrepancy to flag)

Riemann-von Mangoldt, `N(T) ~ (T/2π) log(T/(2πe)) + 7/8`:

| Height `T` | `N(T)` (zeros with `0 < Im <= T`) | density / unit height | RS main-sum length `sqrt(T/2π)` |
|---|---|---|---|
| 2.8e5 (h280000, node) | 4.32e5 | 1.70 | 211 |
| 6.8e5 (live climb top, `arda-million` state, 2026-09-22) | 1.16e6 measured | 1.84 | 329 |
| 1e6 (`AND_ladder_1e6`) | 1.75e6 | 1.91 | 399 |
| 1e9 (`AND_ladder_1e9`) | 2.85e9 | 3.01 | 1.26e4 |
| 2.445e12 (Gourdon's 10^13-th zero) | 1.00e13 | 4.25 | 6.24e5 |
| 3e12 (Platt-Trudgian record) | 1.24e13 | 4.28 | 6.91e5 |
| **1e13 (this node)** | **4.31e13** | **4.47** | **1.26e6** |

So the registered node is about **4.3 x 10^13 zeros**, not "~10^10 zeros" (the triage
figure handed to this task is wrong by three orders of magnitude) and not "10^13 zeros"
(the charter's Gourdon phrase). Two consistent readings exist; this plan prices both:

* **G5-H** (as registered): `Im ρ ≤ 10^13`, N = 4.31e13.
* **G5-Z** (charter's Gourdon phrase): `Im ρ ≤ 2.445e12`, N = 1.00e13 (height literal
  would need to be a certified upper bound on the 10^13-th ordinate, e.g. `2.45e12`).

**Lead decision D1:** keep G5-H (retitle to say "about 4.3e13 zeros") or re-register as
G5-Z. Not for this agent to change; the statement file is generated from the node.

### 1.3 What a G5 artifact would and would NOT establish

WOULD: a kernel-checked (with `Lean.ofReduceBool`, see section 6) theorem that every
zeta zero of positive imaginary part up to the literal lies on the line; a certified
zero count `N(T)` to that height; the input every finite Mirrormere instrument rides on
(Bragg boxes, Li/Weil finite bounds at certified height, W4a `Λ`-bounds in the
Platt-Trudgian shape).

WOULD NOT: anything about RH. No zero-free region beyond the literal, no uniformity in
`T`, no statement about `Λ`, `λ_n` for all `n`, or the Weil form on all test functions.
It would not even be kernel-only: the charter's hybrid dial admits `native_decide` for
this era, so its axiom set is strictly larger than the 3-axiom ladder below 10^9.

---

## 2. Triage, verified against the files

| Item | State (verified 2026-09-22) |
|---|---|
| Node | `kind = goal`, `status = draft`, `created 2026-09-14`; deps = the three ladder rungs + `AND_em_zeta_strip`, `AND_em_tail3_number`, `AND_stirling_binet_k1`, `AND_checkline_correct`, `AND_g2_reflected_band`. |
| Attempts | none for `AND_ladder_1e13` in `missions/anduril/attempts.jsonl` (17 records total; ladder entries are the migration/audit-only records for h280000/1e6/1e9). |
| `AND_ladder_h280000` | open. Artifact exists on `rh/million-turing` with ~280 per-segment `BandHyp` binders + `hγ`; hypothesis-free capstone (StripClear two-box glue, `height_floor_of_box_certs`) NOT landed; `million-turing -> main` reconcile NOT landed. |
| `AND_ladder_1e6` | open, wall-clock only, disk-bound (F5-3). Live climb is past 680000 (27,503 ok bands; driver mean 130 s/band above 600k). |
| `AND_ladder_1e9` | open and MIS-FILED (BACKLOG_MAP R8): title gates on A3; `depends_on` omits the three A3 bricks, which are not registered as nodes. |
| A3 bricks (theta branch, RS main sum, Gabcke C0) | not nodes, not files. `ThetaValue`/`ThetaConverge`/`StirlingBinet`/`StirlingK4` on the reflection island are the substrate for the theta branch only. |
| Native island `zeta_reflection_native` | does not exist in any of the ~40 sibling worktrees (`ls -d ~/arda-*/telperion/examples/zeta_reflection*` finds only `zeta_reflection`). Charter E1 trust base (`+Lean.ofReduceBool`, spot-check protocol) unwritten. |
| Builds here | only `rvm_bridge` and `li_positivity` are built in this worktree. `zeta_zero_localization` built copies exist (`arda-million` 25G, `arda-anduril-b2` 15G) -- irrelevant, nothing to build for this node. No build started. |
| C2 journal sharding | `campaign_shard.py` + `RUNNER_SHARD_DESIGN.md` exist (append-only per-shard JSONL, `merge-shards`, stretch-cache union, per-zero delta-dyadic archive format specified but producer not built). B2 lake sharding: pilot green per ROADMAP. C1 grid sweep (`platt_grid`, `_online_sweep_zero_count_grid`) landed in `generate.py`. |
| Compute | M3 Ultra only. Charter: cluster decision at G4. |

Docs consulted: PROGRAM_ANDURIL_2026-09-12 (charter 1/D4/E1), ROADMAP_ANDURIL_MIRRORMERE_2026-09-14
(G5 row), RH_ASCENT_PLAN_2026-09-18 (F5-4 "do not staff"), WALL_BACKLOG_MAP_2026-09-18 (row
`AND_ladder_1e13`, op R8), REFLECTION_TRACK_DESIGN, RUNNER_SHARD_DESIGN, A0_SPIKE_REPORT,
MILLION_ROADMAP_2026-09-09.

---

## 3. Why only one architecture composes into the registered theorem

Three trust dials are on the table. Two of them do not scale to a single theorem at 10^13
for STRUCTURAL reasons that are independent of compute budget. This is the design finding
that fixes the plan.

**(K) Kernel-only `decide`.** A0 measured ~1.0-1.9e4 interval-ops/s in the kernel and ~3.4e3
on the `hornerD` path (A0_SPIKE_REPORT). One RS grid point at 10^13 is ~1.26e6 terms x
~100 Int-ops = ~1.3e8 Int-ops = **2.3 kernel-hours per point**. Not a production path at any
height past ~10^3 (A0's own re-based caps). Retained ONLY as the E1 spot-check mechanism
(section 6.3).

**(H) Hypothesis-carrying bands (today's T5 trust class) under `native_decide`.** Each band
theorem takes the Arb enclosures as hypotheses (`memR (gLine (p i)) box_i`, the five edge
`argChange` enclosures). Per band this is cheap. But the chain lemmas
(`height_chain`, `all_nontrivial_zeros_in_segment_on_line`) consume CONCLUSIONS, so every
band's hypotheses propagate to the capstone as binders: h280000 already carries ~280
`BandHyp` binders (B1 bundling made them one per segment, not zero). At 4.3e9-4.3e10
bands there is no capstone with that many binders, and the only way to bundle them into
one uniform hypothesis is to make the 10^14-entry box table a Lean term, which is the
100-440 TB object the charter calls the irreducible certificate mass. **(H) does not
compose into `all_nontrivial_zeros_up_to_height_1e13` at all.** It is a per-band
instrument (fine for Bragg boxes), not a route to the node.

**(R) Reflected bands: the kernel (native) computes the sign boxes and the count itself;
per-band theorem is hypothesis-free** (`ReflectedBand.Statement d`, `checkBand_correct`,
REFLECTION_TRACK_DESIGN section 3; pilot shape landed at t = 14 as
`ReflectedBand_t14.pilot` / `FullyReflectedBand_t14.band`; the zero-hypothesis first zero
landed as `ForgeFirstZeroKernel`). Hypothesis-free conclusions fold with no binder growth
(section 5, job J4). **(R) is the only architecture that composes.** Its cost is the cost
of evaluating zeta rigorously INSIDE verified Lean code, which is the whole of section 5.

Consequence: G5 = (R) + `native_decide` + a verified fast evaluator. "Native island" is
necessary but nowhere near sufficient.

---

## 4. Mathematical route, lemmas available, named obligations

### 4.1 Route (per band, all in-kernel under (R))

1. **On-line sign chain.** Grid heights `t_0 < ... < t_n` in `[T0, T1]`; enclose
   `gLine t_i = Re Λ(1/2 + i t_i)` (up to the positive factor handled by
   `ZeroSignDecomp_t14`'s phase decomposition: sign of `Z(t) = e^{iθ(t)} ζ(1/2+it)`); check
   `n` sign alternations (`checkLine`, `checkLine_correct`, `checkBandFull_correct`). Gives
   `n` distinct on-line zeros of `completedRiemannZeta` in `[T0, T1]` (Hardy's Z; Titchmarsh
   ch. 4).
2. **Count pinning to `n`.** Two options, both needing effective constants:
   * (a) the island's T5 RvM edge decomposition (`TuringBand.turing_band_on_line`: five
     `argChange` enclosures on the box `[-1,2] x [T0,T1]`, `hpinL`/`hpinH`). At 10^13 the two
     horizontal edges need OFF-line RS evaluation at `σ ∈ [-1, 2]` with a rigorous remainder
     for general `s` (Arias de Reyna 2011 gives such bounds; Gabcke 1979 is on-line only),
     plus Backlund cell subdivision (charter A2 item 5, not built).
   * (b) Turing's method proper (Turing 1953; Lehman 1970; Trudgian 2011 constants): the
     count is `θ(T)/π + 1 + S(T)` with `|∫_{t1}^{t2} S(t) dt| ≤ 2.067 + 0.059 log(t2/2π)`
     (Trudgian's Theorem 2.2 shape), discharged from ON-line Gram-block sign data only. No
     off-line evaluations. This is the route Platt-Trudgian used and is what
     MILLION_ROADMAP called "T4, the crux". NOT formalized here; `RH_backlund_S_bound`-class
     results on `rvm_bridge` are existential-constant, not effective.
   Recommendation: (b). It removes the off-line RS obligation entirely.
3. **theta(T).** Continuous-branch `Im log Γℝ` via Stirling/Binet (K = 4 at 10^13 for
   ~1e-3 absolute accuracy, needed for the Gram-point grid and for 2(b)):
   `StirlingBinet.logDeriv_gammaR_stirling` (K = 1, proved), `StirlingK4` (height-aware
   ingredients, proved; exact K=4 cos-form pending a Mathlib digamma/trigamma bridge),
   `ThetaValue`/`ThetaConverge` (φ(14) box + both Tendsto obligations discharged: the
   theta-value instrument exists at small height via the Euler route).
4. **Riemann-Siegel main sum + remainder.** `Z(t) = 2 Σ_{n ≤ ν} n^{-1/2} cos(θ(t) - t log n) + R(t)`,
   `ν = floor(sqrt(t/2π))`, Gabcke C0: `|R(t)| ≤ 0.053 t^{-3/4}` for `t ≥ 200`. At 10^13:
   `ν = 1.26e6`, `|R| ≤ 3e-11`. Tables of `log n` and `n^{-1/2}` for `n ≤ 1.26e6` are shared
   per block and verified once by algebraic certificate (`CertVerify`: `invSqrtCert`,
   `lnCert`); `t log n` needs ~104-bit arguments to reduce mod 2π to ~60 bits (`TrigReduce`,
   `TrigReduceD`, instrument A, proved at θ ~ 74; needs the general large-argument case).
5. **Amortization (the new piece).** Per-point RS is ~1.3e8 Int-ops; at 8.6e13 grid points
   that is ~1e22 Int-ops (section 5.1). Platt's rigorous multi-evaluation
   (`acb_dirichlet_platt_multieval`; Platt 2017; Odlyzko-Schoenhage 1988) evaluates a
   uniform grid of `A·B` points around `T` at polylog cost per point via Taylor expansion of
   the Dirichlet sum in `t` plus an FFT, with rigorous error terms. **A verified
   implementation of this inside the native island (`A5`) is the compute-enabling
   obligation.** No prior art in any proof assistant.
6. **Segment/capstone glue.** `AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line`
   (indexed `hbands : ∀ i, i < n → ...`, chain-scout: already the right shape),
   `height_chain (A B)`, StripClear `height_floor_of_box_certs` (discharges `hγ`, the
   55/16 floor, from two winding-0 box certificates at ANY capstone height).

### 4.2 Mathlib and island lemmas available now

Mathlib (v4.32.0 pin, `81a5d257`): `riemannZeta`, `completedRiemannZeta`,
`riemannZeta_one_sub`/functional equation, `Gammaℝ`, `riemannZeta_ne_zero_of_one_le_re`,
`Real.exp_bound'`, `Complex.Gamma` Stirling-free basics, Bernoulli numbers
(`Mathlib.NumberTheory.Bernoulli`), `Real.pi` bounds. ABSENT: Euler-Maclaurin identity
(island has it), Riemann-Siegel, Gabcke, Turing's method, any `S(T)` bound.

Island `zeta_zero_localization` (v4.32): `TuringBand.BandStatement`,
`turing_band_on_line`, `band_count_eq`, `RHInBox.rh_in_box_of_certificate`,
`AllZerosUpToHeight.{all_nontrivial_zeros_in_segment_on_line, height_chain}`,
`StripClear.{height_floor_of_box_certs, all_nontrivial_zeros_up_to_height_100_strip_cleared}`,
`DiffractionCore.{argChangeVert, argChangeHoriz, theta_eq_argChangeVert_gammaR}`,
`XiLineZeros.gLine`, `ZetaZeroConfinement`.

Island `zeta_reflection` (v4.32, path-requires the sibling): `DIntvDef`/`DIntvCorrect`
(pure-Int dyadic core, `add_sound`/`mul_sound`/... proved; `Rat` refuted as non-reducible
by A0), `TaylorKernels`, `CertVerify`, `TrigReduce`/`TrigReduceD`, `LogZetaSeries`,
`EMZeta`/`EMZetaComplex.em_zeta_strip`/`EMZetaTail.em_tail3_number`, `StirlingBinet`,
`StirlingK4`, `CheckBand.{checkLine, checkLine_correct}`, `FullyReflectedBand_t14.{Cell,
checkBandFull, checkBandFull_correct}`, `ThetaValue`, `ThetaConverge`,
`ZeroSignDecomp_t14`, `ForgeFirstZeroKernel.first_zero_kernel` (the zero-hypothesis first
zero, 3-axiom clean). All guards print `[propext, Classical.choice, Quot.sound]`; no
`Lean.ofReduceBool` anywhere in the corpus (guards explicitly flag it).

### 4.3 Named obligations (honest sizes; none started)

Sizes are Lean lines (L) and agent-weeks (aw). "First-of-kind" means no formalization in
any assistant is known (numerics-scout finding 3).

| # | Obligation | Depends on | Size | Notes |
|---|---|---|---|---|
| O1 | **theta branch at height** (`θ(t)` box to 1e-3 for all `t ≤ 10^13`, K = 4 Binet, continuous branch) | `StirlingBinet`, `StirlingK4`, `ThetaConverge`; Mathlib digamma/trigamma bridge (gap) | 1500-2500 L, 3-5 aw | Charter A3 brick 1. Small-height instance exists (φ(14)). |
| O2 | **RS main sum enclosure** (finite sum with verified `log n`, `n^{-1/2}` tables, mod-2π reduction of `t log n` at 104+ bits, `DIntv` accumulation with proven rounding) | `CertVerify`, `TrigReduce` general case, `DIntvCorrect` | 800-1500 L, 2-4 aw | Charter A3 brick 2. Mechanical given O1's phase; the mod-2π general case is the real work. |
| O3 | **Gabcke C0 remainder** `|R(t)| ≤ 0.053 t^{-3/4}`, `t ≥ 200` | saddle-point / contour layer; nothing in corpus | 4000-8000 L, 8-14 aw, first-of-kind | Charter A3 brick 3, the research summit. Pivot ladder per charter: explicit-constant AFE, then terminal EM-only (which does NOT reach 10^9, let alone 10^13). |
| O4 | **`A5`: verified FFT-amortized multi-evaluation** (Odlyzko-Schoenhage / Platt): Taylor expansion of the RS/Dirichlet sum in `t` about grid centers with rigorous truncation, verified (or certified-output) FFT over `DIntv`, per-point error bound composing with O3 | O1-O3, a verified FFT (none in Mathlib) | 8000-15000 L, 6-18 months, first-of-kind, **unpriced until a design memo** | NEW. Without it G5 has no route (section 5.1). Alternative "verify-not-compute": the untrusted driver supplies the FFT output and the kernel checks it by a cheaper certificate -- no such certificate is known for Dirichlet-sum values; do not assume one. |
| O5 | **Effective Turing method** (route 2(b)): Lehman/Trudgian `∫ S` bound with explicit constants, Gram-block counting theorem | Backlund-class machinery (`rvm_bridge` has existential constants only), O1 | 2000-4000 L, 4-8 aw | Replaces the off-line RS obligation of route 2(a). Either 2(a)+Arias-de-Reyna or 2(b)+O5 is mandatory; neither exists. |
| O6 | **`checkBandRS`**: RS-era `BandData` (grid, per-block table ids, count witness) -> `Bool`, `Array`-shaped per A0, once-proven `checkBandRS_correct` producing the exact T5 conclusion Π-type (`band_t5shape` adapter) | O1, O2, O3, O5, `checkBandFull_correct` | 800-1200 L, 2-3 aw | Charter A4 productionization at the RS era. |
| O7 | **Native island charter + guard** (`zeta_reflection_native/`): lakefile sharing everything above `CheckBand`, `AxiomGuardNative` printing the EXPANDED expected set `[propext, Classical.choice, Quot.sound, Lean.ofReduceBool]` and FAILING on `sorryAx`; E1 spot-check protocol text; CI job that is a required check | none (policy) | 200-400 L + doc, 1 aw | Charter E1. Nothing here is mathematics. Must exist before any `native_decide` term is committed anywhere. |
| O8 | **Balanced chain fold (B3)**: `segment_fold : (∀ i < K, conclusion (A + i Δ) (A + (i+1) Δ)) → conclusion up to A + K Δ`, applied at three levels (band -> block -> superblock -> root) so no file imports more than ~10^3 oleans | `all_nontrivial_zeros_in_segment_on_line` (already indexed) | 100-200 L, 0.5 aw | Mechanical. Needed because a 10^7-deep linear `height_chain` import spine is not buildable. |
| O9 | **h280000 hypothesis-free capstone + reconcile** (F5-1): StripClear two-box glue at the capstone, `million-turing -> main` | nothing mathematical | glue only | Gate (1) of the charter; the only workable anduril leaf today. |
| O10 | **Registry hygiene** (lead only): D1 height-vs-count; R8 author O1-O5 as `draft` nodes and add them to `AND_ladder_1e9.depends_on` and `AND_ladder_1e13.depends_on`; retitle 1e13 with the zero count | -- | -- | Read-only for this agent. |

Total new mathematics on the critical path to G5: O1 + O2 + O3 + O4 + O5 = roughly
**16,000-31,000 lines, 12-24+ months of focused work, two first-of-kind formalizations**
(Gabcke; verified multieval). The charter's "A3 12-20 aw" covers O1-O3 only and reaches
G4 (10^9) in principle, not G5.

---

## 5. The compute jobs

All figures are for **G5-H** (N = 4.31e13, height 1e13) with the **G5-Z** (N = 1.00e13,
height 2.445e12) figure in brackets where it differs by more than the rounding. Units:
core-years (cy) = 3.15e7 core-seconds. Every number that rests on an unmeasured
constant is marked `[N0]` and is exactly what job J0 measures.

### 5.0 Sizing constants

* Grid points per zero: 2.0 (uniform Gram-like grid + close-pair refinement fallback;
  Platt-Trudgian effective ratio is of this order). `[N0]`
* Band = 10^5 zeros (~2.2e4 height units at the top). Bands: **4.3e8** [1.0e8].
  (Bands of 10^4 zeros would be 4.3e9 and make the per-file Lean overhead in J3 the
  dominant cost; see the table in 5.3.)
* Block = 10^7 height units = one lake package (B2 shape, larger than the 25,000-height
  pilot): ~4.5e7 zeros, ~450 bands. Blocks: **10^6** [2.4e5].
* Fold: level-1 = 10^3 blocks (10^3 files), level-2 = 10^3 level-1 (1 file) [G5-Z:
  245 level-1 files, 1 level-2]. No file imports more than ~10^3 oleans.
* Native `DIntv` throughput: 3e7 Int-ops/s/core for 128-bit boxed GMP `Int` (A0's kernel
  figure is 1.5e4; the native/kernel ratio ~2e3 is an estimate). `[N0]`
* Lean per-band overhead (parse + elaborate an `Array Int` literal of ~2e5 entries +
  compile to C + clang + link + `native_decide`): 30 s. `[N0]` (A0: 20k-literal `Array`
  elaborates without the typeclass blowup; no timing at 2e5.)

### 5.1 The evaluator cost floor (why A5 is mandatory)

| Evaluator inside the native island | Int-ops total | core-years at 3e7 ops/s | Verdict |
|---|---|---|---|
| Plain per-point RS (O1-O3 as chartered): 8.6e13 points x 1.26e6 terms x ~100 ops | ~1.1e22 | **~1.1e7 cy** [~2.5e6] | Infeasible by 4 orders of magnitude on any cluster. |
| Same, kernel-only `decide` at 1.5e4 ops/s | ~1.1e22 | ~2.3e10 cy | Spot-check only (one point = 2.3 h). |
| Verified multieval (O4/A5), scaled from Platt-Trudgian's ~3.7 cy for height 3e12 in optimized FLINT C (PROGRAM_ANDURIL driver-scout 1, arXiv:2004.09765) x (4.31e13 / 1.24e13) x slowdown S for verified Lean native code, S in [10, 100] `[N0]` | -- | **130-1300 cy** [30-300] | Feasible on a 10^4-core cluster: 5-47 days [1-11 days]. This is the ONLY feasible row. |

The first row is the finding: the charter's D4 ("10^13 after A3") is not costed correctly.
A3 (O1-O3) alone is a G4 (10^9: 2.85e9 zeros x 2 points x 1.26e4 terms x 100 = 7e15 ops =
~7 core-days native; ~15,000 core-years kernel-only, so G4 is also native-bulk, as A0
already concluded) instrument. G5 needs O4.

### 5.2 Job list

| Job | What | Inputs | Output / certificate shape | Wall-clock and cores | Composes as |
|---|---|---|---|---|---|
| **J0 `N0` benchmark spike** (do FIRST, cheap, the only job that can start now with zero risk) | Measure on the existing `zeta_reflection` island: (i) `native_decide` throughput of `hornerD`/`checkBandFull` over `DIntv` at 128 bits, (ii) elaboration + compile time of an `Array Int` literal at 2e4, 2e5, 2e6 entries, (iii) `#print axioms` on a `native_decide` toy to confirm the expanded set is exactly `+Lean.ofReduceBool` on v4.32, (iv) FLINT `acb_dirichlet_platt_multieval` core-seconds per 10^5 zeros at T = 1e9 and, if reachable, 1e11 | `Spike/BenchExpD.lean`, `gen_spike.py`, bundled libflint | `docs/N0_NATIVE_SPIKE_REPORT.md`; a throwaway `Spike/NativeToy.lean` NOT guard-imported and NOT in defaultTargets | 1-2 days, 1 machine | Re-bases every `[N0]` constant here. Requires the lead's OK to use `native_decide` in a spike file at all (charter says it lives only in the flagged island; a spike in a non-default target still needs an explicit exemption note). |
| **J1 Driver campaign (untrusted candidate producer)** | C1 `platt_grid` multieval sweep over height shards; close-pair refinement; emit per band: grid heights, count witness `n`, per-block table candidates (`log n`, `n^{-1/2}` dyadics); per-zero delta-dyadic archive (RUNNER_SHARD_DESIGN format; producer still to be written) | `campaign_shard.py --shard FROM TO`, `arb_platt.platt_grid`, C3 width policy | `state/shard_*.jsonl` (band journal), `certs/zeros_*.jsonl.gz` (archive, ~10 B/zero gz: **~430 TB** [100 TB]), `tables/block_*.dy` | ~13 cy [3 cy] in FLINT (PT scaling); 1-2 weeks on 10^3 cores | Nothing in the theorem depends on J1's numbers being right; J1 only makes J3 succeed first time. The archive feeds Bragg/W4a, not the node. |
| **J2 Per-block table certificates** | Kernel-verified (native) algebraic certificates for the block's `log n`, `n^{-1/2}` tables (`n ≤ sqrt(T_top/2π)`), π, Bernoulli constants; theta constants | J1 tables, `CertVerify` | one `Tables_b<k>.lean` per block: `theorem tables_ok : checkTables tb = true := by native_decide` + `tables_correct` | 10^6 files x ~1 min = ~2 cy; trivially parallel | Imported by every band file in the block. |
| **J3 Native band checks (the bulk)** | For each band: `def d : BandDataRS := <Array literals>`; `theorem ok : checkBandRS d = true := by native_decide`; `theorem band : ReflectedBand.Statement d := checkBandRS_correct d ok`; `theorem band_t5shape : <T5 conclusion Π-type> := ...` | J1 band records, J2 tables, O1-O6 | `RBand_<lo>_<hi>.lean` + `.olean`, one per band (4.3e8 files) | evaluator: 130-1300 cy (5.1) + Lean overhead 4.3e8 x 30 s = **410 cy** `[N0]`; total **540-1700 cy** [125-400]; on 10^4 cores: 20-62 days [5-15 days] | `band_t5shape` is consumed by `all_nontrivial_zeros_in_segment_on_line` exactly as T5 bands are (interchangeability was the A4 design goal). |
| **J4 Fold builds (B2 packages + B3 fold)** | Per block: segment lemma over its ~450 bands (indexed `hbands`); level-1 fold over 10^3 blocks; level-2 fold; root `height_chain` from the reconciled h-current capstone; `hγ` via StripClear two-box glue | J3 oleans, O8, O9 | `AllZeros_b<k>.lean` (10^6), `Fold1_<j>.lean` (10^3), `Fold2.lean`, `AllZeros_h1e13.lean` with the VERBATIM registered conclusion and NO binders | ~10^6 x 1 min + fold files; ~2 cy; bounded by olean I/O | The root theorem IS the node statement. |
| **J5 Kernel-only spot checks (E1)** | Sample bands uniformly at random (seeded, published seed); in each sampled band re-verify ONE grid point's sign box by plain RS under pure `decide` (2.3 kernel-hours/point at 1e13; ~15 min at 1e9) and check the native box and the kernel box overlap with the same sign; also re-run `checkBandRS d` under pure `decide` for the combinatorial half (cheap, O(n)) | J3 files, O2 with a `decide`-friendly path (`List`, structural) | `SpotCheck_<band>.lean` with `#print axioms` = 3-axiom on the spot theorem | e.g. 10^4 samples x 2.3 h = 2.6 cy; 1 week on 10^3 cores | Does not enter the theorem. Documents the trust dial. Charter E1's "random BAND re-verification under pure decide" is NOT affordable at 1e13 (one band = 10^5 zeros x 2 points x 2.3 h = 52 cy); this plan replaces it with POINT-level re-verification and says so. |
| **J6 Guard, hash, independent re-run (E2)** | `AxiomGuardNative` over every band/fold theorem (expanded set exactly, `sorryAx` fails the job); SHA-256 of every `RBand_*.lean` and `.olean`; a second-site re-run of a random 1% of J3 with a different C compiler | J3, J4, O7 | `guards/*.log`, `hashes.jsonl`, re-run report | guard pass over 4.3e8 files: ~0.5 cy; re-run 1%: 5-17 cy | Trust documentation only. |
| **J7 Capstone assembly + N(T) cross-check + registry** | Root file build; exact `N(10^13)` cross-check against the fold's certified count; readback audit; grant (lead) | J4-J6 | `AllZeros_h1e13.lean`, audit testimony, `mission grant` (lead) | hours | Node proved (with the expanded axiom set stated in the title). |

### 5.3 Roll-up

| Scenario | Verification compute | Driver | Storage | Wall on 10^4 cores | Wall on the M3 Ultra alone (24 lanes) |
|---|---|---|---|---|---|
| G5-H, S = 10, band 10^5 | ~540 cy | 13 cy | 430 TB archive + ~50 TB Lean sources/oleans `[N0]` | ~20 days | ~23 years |
| G5-H, S = 100, band 10^5 | ~1700 cy | 13 cy | same | ~62 days | ~70 years |
| G5-H, band 10^4 (overhead-dominated) | +4100 cy of Lean overhead | | | +150 days | -- |
| G5-Z, S = 10-100 | 125-400 cy | 3 cy | 100 TB + ~12 TB | 5-15 days | 5-17 years |
| Any scenario WITHOUT O4 (plain RS) | ~10^7 cy | -- | -- | ~1000 years | -- |

The M3 Ultra column is the honest answer to "can we do it here": no. The charter's
"decision point at G4" for procurement is right; nothing in this plan should trigger
procurement before O4 has a design memo and J0 numbers exist.

---

## 6. The trust seam

### 6.1 Axiom set of the final theorem

`[propext, Classical.choice, Quot.sound, Lean.ofReduceBool]`. The last axiom is what
`native_decide` adds: it asserts that the compiled evaluation of a closed `Bool` term agrees
with kernel reduction. The trusted base therefore grows from the Lean kernel to: the Lean
compiler (IR + C emission), the C compiler, the runtime (GMP-backed `Int`), and the
hardware of every node that ran J3. This is the charter's "trust dial" and it must be
stated in the node title and in every artifact header. Nothing below 10^9 may inherit it:
the kernel-only ladder and the native island stay separate packages with separate guards
(O7), and the `zeta_zero_localization` and `zeta_reflection` guards continue to FAIL on
`Lean.ofReduceBool`.

### 6.2 Hypotheses that remain, by job

* J3 band theorems (`band`, `band_t5shape`): **none** beyond the axioms above. This is the
  whole point of (R). Every numeric fact (tables, theta, RS sum, Gabcke remainder, Turing
  count) is computed by `checkBandRS` and justified by the once-proven `checkBandRS_correct`,
  whose own proof is 3-axiom (it is a theorem about a function, not a computation).
* J4 folds: none; the fold lemmas are 3-axiom; the root inherits `ofReduceBool` from J3.
* `hγ` (55/16 floor): discharged by StripClear's two winding-0 certificates (Arb-free after
  the reflection of those two small boxes, or as the two explicit `hleft`/`hband` inputs
  if not reflected -- in which case they are the ONLY residual Arb-class hypotheses in the
  whole ladder and must be listed as such).
* The reconciled prefix (`h<current>` capstone from the T5 era, gate O9): 3-axiom but
  HYPOTHESIS-CARRYING today (per-segment `BandHyp`), so its Arb enclosures remain
  hypotheses of the root unless the T5 prefix is itself re-verified reflected (a separate
  ~10^6-zero job, cheap under J3, recommended so the root has zero Arb inputs).
* J1's driver output: trusted for NOTHING. A wrong grid makes J3 fail, not lie.
* J5/J6: outside the theorem; they bound what `Lean.ofReduceBool` is being trusted for.

### 6.3 Spot-check protocol (proposed E1 text)

1. Fix a published seed; sample `m` bands uniformly from the J3 set (`m = 10^4` at 1e13).
2. For each sampled band, sample one interior grid index; re-derive that point's sign box
   with the plain RS path (O2) under pure `decide`; assert overlap and sign agreement with
   the native box, as a 3-axiom theorem.
3. Re-run the band's `checkBandRS d = true` under pure `decide` for the combinatorial half.
4. Publish the list of sampled (band, index) pairs, the axiom prints, and the wall-times.
5. Any disagreement halts the campaign; the affected block is re-run on a different node
   with a different C compiler before anything else proceeds.

What this protocol does NOT do: it does not make the root theorem kernel-only, and it does
not check the multieval algorithm's FFT output at points that were not sampled. It bounds
the failure probability of the compiled path under an independence assumption that must
be stated as such.

---

## 7. What can actually be started now (and what must not)

CAN (cheap, honest, no charter violation):
* J0 with the lead's explicit exemption for one non-default-target spike file, or J0 parts
  (ii)-(iv) without any `native_decide` at all.
* An O4 design memo: the Odlyzko-Schoenhage / Platt multieval as a Lean-verifiable
  algorithm, error-term structure, what a certified-output variant would need. Pure
  writing; prices the summit before anyone climbs it.
* O7 as a document (native island charter + expected-axiom text), no Lean.
* O10 registry ops by the lead (D1; R8 for `AND_ladder_1e9`; retitle 1e13 with the zero
  count and the expanded axiom set).

MUST NOT (per ASCENT_PLAN F5-4, BACKLOG_MAP, and this memo):
* Staff O1-O5 against this node. If A3 is staffed at all it is for G4, and G4 itself is
  native-bulk per A0 (the "kernel-only 10^9" reading is not supported by measurement).
* Procure compute. Nothing is ready to consume it; the first 12-24 months are Lean work.
* Register any `native_decide` term in an existing island, or create the native island
  before O7's guard and CI check exist.
* Describe any of this as progress toward RH in a status update.

---

## 8. Sources

* Turing, A. M. (1953). Some calculations of the Riemann zeta-function. Proc. LMS (3) 3, 99-117.
* Lehman, R. S. (1970). On the distribution of zeros of the Riemann zeta-function. Proc. LMS (3) 20, 303-320. (Turing's method made rigorous.)
* Trudgian, T. (2011). Improvements to Turing's method. Math. Comp. 80, 2259-2279. (Effective constants for the `∫ S` bound.)
* Backlund, R. (1914, 1918). Sur les zeros de la fonction zeta(s) de Riemann; Ueber die Nullstellen der Riemannschen Zetafunktion.
* Gabcke, W. (1979). Neue Herleitung und explizite Restabschaetzung der Riemann-Siegel-Formel. Dissertation, Goettingen. (C0 remainder `|R| ≤ 0.053 t^{-3/4}`.)
* Arias de Reyna, J. (2011). High precision computation of Riemann's zeta function by the Riemann-Siegel formula, I. Math. Comp. 80, 995-1009. (Rigorous RS remainders for general `s`; needed only on route 2(a).)
* Odlyzko, A. M. and Schoenhage, A. (1988). Fast algorithms for multiple evaluations of the Riemann zeta function. Trans. AMS 309, 797-809.
* Platt, D. J. (2017). Isolating some non-trivial zeros of zeta. Math. Comp. 86, 2449-2467. (Rigorous multi-evaluation; the FLINT `acb_dirichlet_platt_multieval` method.)
* Platt, D. and Trudgian, T. (2021). The Riemann hypothesis is true up to 3*10^12. Bull. LMS 53, 792-797. arXiv:2004.09765. (Rigorous-numeric record; the ~3.7 core-year figure as recorded in PROGRAM_ANDURIL driver-scout 1.)
* Gourdon, X. (2004). The 10^13 first zeros of the Riemann zeta function, and zeros computation at very large height. Unpublished note. (Numerical, not rigorous-interval; the "10^13 zeros" count.)
* Titchmarsh, E. C., rev. Heath-Brown (1986). The Theory of the Riemann Zeta-Function, 2nd ed., ch. 4 (Riemann-Siegel), ch. 9 (`N(T)`, `S(T)`).
* Repo: PROGRAM_ANDURIL_2026-09-12.md; ROADMAP_ANDURIL_MIRRORMERE_2026-09-14.md; REFLECTION_TRACK_DESIGN.md; RUNNER_SHARD_DESIGN.md; A0_SPIKE_REPORT.md; RH_ASCENT_PLAN_2026-09-18.md (F5); WALL_BACKLOG_MAP_2026-09-18.md (row AND_ladder_1e13, op R8); MILLION_ROADMAP_2026-09-09.md; `examples/zeta_zero_localization/lean/{TuringBand,AllZerosUpToHeight,StripClear,AllZeros_h280000}.lean`; `examples/zeta_reflection/lean/{CheckBand,FullyReflectedBand_t14,ReflectedBand_t14,AxiomGuardA4}.lean`; `examples/zeta_zero_localization/{campaign.py,campaign_shard.py,campaign_state.json}` (live state read from `~/arda-million`, 2026-09-22).

*`conjecture1_proved = False`. Nothing here proves RH. The node remains `draft`; this
document recommends it stay that way.*
