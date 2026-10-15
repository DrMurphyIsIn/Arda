# Read-back testimony: AND_ladder_h11000_kernel (anduril), independent auditor A1, 2026-10-15

Verdict: **PASS**. axioms_clean = true, statement_byte_identical = true.
**conjecture1_proved = False.** This is a finite verification up to height 11000 (and 11004). It says nothing about the Riemann Hypothesis.

Who: an AI subagent (lead: session e4) working in Claude Code session 43fb6f48-008b-48a7-abad-ad5db918fecf (local id) = session_01TeEsdE4SroprJqfYm9qcKc (the claude.ai id recorded as auditor_session in the registry). Governance transparency: the read-back (this subagent, A1) and the `mission grant` were executed by the same session, session_01TeEsdE4SroprJqfYm9qcKc; the second reading (session peterwmurphy-bb) is a separate session; the author session is ef083c48-579d-4bec-a689-c30fdccec2a1. The gate requires auditor ≠ author, which holds; it does not require the granter to differ from the auditor, and here they coincide. I am not the author session ef083c48-579d-4bec-a689-c30fdccec2a1. Nothing here relies on that session's testimony: not its commit message, its "skeptic rebuild", its lane notes or its CI record. I read those files only to know what was claimed, then re-checked every claim myself. This is AI work and has not been reviewed by a human.

Tree: a fresh detached worktree of origin/main at 36f821b573d75205a0aa3cc17b345290899bbcbc (`~/arda-h11k-readback`). I made no commits and no edits to tracked files. Four probe files were created and then deleted (§3, §4, §6.1); `git status --porcelain` is empty.

## 0. The closure_clean question

**What the field means.** `closure_clean` is `Proof.closure_clean: bool = False` (`schema.py:147`). Every node starts out False.
- For a `via = "direct"` node, `verify._compute_closures` seeds from the stored flag and never recomputes it. Its docstring says: "A direct-proved node's STORED flag is authoritative and is never recomputed here".
- Only `via = "reduction"` nodes go through the dependency fixpoint (`_dep_is_clean`: target proved AND clean).
- For direct nodes, `depends_on` edges are documentary (`grant_status` docstring, point 6).
- The only place the flag is set True is `grant_status`, which writes `closure_clean = (new_status == "proved")` (`verify.py:643`).
- `registry.render_status` (`registry.py:450-463`) displays the flag only for reduction nodes.

**Why h11000 records false.** It is the default for a node that has never been granted. The node is `status = "draft"`, `via = "direct"`, and has no `[readback]` and no `[grant]` block. Its git history is commit 774429e9, "register ... (DRAFT ...)", and commit 262c66b7, "... ci-record AND.ladder_h11000_kernel (stays DRAFT)".
- The h8000 dependency's status is irrelevant to a direct node. (Also, h8000 was granted on 2026-09-25; 09-27 is the date of its Comparator record.)
- Nothing in the import closure is flagged: the marker scan in §2 is empty.

**The repo tooling, run read-only** (`PYTHONPATH=src python -m telperion.cli mission ...`):
- `mission status anduril`: `· AND_ladder_h11000_kernel  (milestone, draft)  -> AND_ladder_h8000_kernel`
- `mission verify anduril`, verbatim: `WARN  [anduril]: Example islands with Lean sources that no CI workflow builds (14): axiom_metaplectic, ... wall3. ...` followed by `verify [anduril]: OK` (rc 0).
- `mission provenance-report anduril`: `anduril: 12 proved, 1 without an independent read-back or a passing Comparator run`. h11000 is not listed because it is not proved.

**What the fixpoint computes if the node is granted (an observation, read-only).** Script: `scratchpad/simgrant.py`, run as `cd ~/arda-h11k-readback/telperion && PYTHONPATH=src python simgrant.py`.

How it works:
1. It loads the campaign and the universe from disk.
2. It replaces `save_node` with a recorder that never writes.
3. In memory only, it moves the node draft → open with a structured non-author read-back. That is what `mission audit` would do; the text is marked "SIMULATION ONLY" and is recorded nowhere.
4. It calls the real, unmodified `grant_status`.
5. It recomputes `_compute_closures`.
6. It runs `verify_campaign`, with `load_campaign` returning the in-memory state.

Output, verbatim:
```
universe loaded: True
[on disk] status=draft via=direct stored closure_clean=False readback=False grant=False
[on disk] _compute_closures[h11000] = False | compute_universe_closures[(anduril,h11000)] = False
nodes in anduril with depends_on h11000: []
[simulated grant] GATE PASSED: status=proved stored closure_clean=True
[simulated grant] grant block: artifact_sha256=757836b9800c189d4a3570597f09f60f7832e84a9bd84f99e9db8890878bac7d statement_sha256=e588743828ce0498d66fda7df2d095de7647102fcf433cb3e27851bac61afe92 gate_version=2026-09-23.1
[after simulated grant] _compute_closures[h11000] = True
[after simulated grant] closure entries that changed anywhere in anduril: {'AND_ladder_h11000_kernel': (False, True)}
[verify_campaign on simulated state] ok=True
  WARN  Example islands with Lean sources that no CI workflow builds (14): axiom_metaplectic, ...
save_node calls intercepted (NOT written): [('missions/anduril/nodes/AND_ladder_h11000_kernel.toml', 'proved', True)]
node file sha256 before == after: True a792e8f5f702e06a
git status before: '' after: ''
```

On the simulated state, the provenance report reads `13 proved, 1 without an independent read-back or a passing Comparator run`, still with "11 proved node(s) covered by a passing Comparator run". The h11000 row has `comparator_run=''`. So the tooling would correctly not count h11000 as Comparator-covered.

**Conclusion.** closure_clean = false is not a blocker. No code change is needed, and nothing turns it true by itself. A real `mission audit` (independent read-back) followed by `mission grant` would pass every gate precondition and write closure_clean = true. Both steps write to the registry, so they belong to the lead and the user.

## 1. Statement read-back (done before reading the artifact)
`Statements/AND_ladder_h11000_kernel.lean` imports only Mathlib and states
`∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 11000 → ρ.re = 1 / 2`.
- It uses Mathlib's `riemannZeta`, which is defined on all of ℂ.
- `0 < ρ.im` excludes the trivial zeros and s = 1.
- So the statement says: every zeta zero with height in (0, 11000] lies on the critical line. It is a faithful finite statement, and it is not vacuous: mpmath counts 11324 such zeros.

## 2. Canonical gate
- `R.load_campaign(missions/anduril)` finds the node with status `draft`.
- `V.statement_matches(H11K_h11000.lean, _normalized_statement)` returns **True**. The declaration is byte-identical to the statement up to `:=`.
- `regen_diff` = ''.
- `required_ci_problem` = ''. The ci_record sha 757836b9 equals the artifact on disk.
- `artifact_incompleteness_markers` finds nothing in the artifact or in any of the **531 modules** of its local import closure (532 with the guard). The closure is resolved by my own import walker over the three source roots:

  | Source root | Modules |
  |---|---|
  | zeta_reflection | 239 |
  | zeta_zero_localization | 226 |
  | zero_free_bridge | 66 |

  Every import resolved, and none was ambiguous.

## 3. Kernel
- **The build is mine and independent.** No pre-built Arb4 or H11K .olean existed on the machine, and the ~/arda-million package build was stale for this toolchain. So I used a fresh mathlib checkout at 81a5d257 (= origin/main's manifest), plus `lake exe cache get` for Mathlib and its dependencies only. Every local module (zzl_core, zero_free_bridge, zeta_reflection) was compiled from source in this worktree.
- **How it was built.** I followed CI: the 50 Arb4 edge modules and H11K_Edge_T11004 one at a time (`lake build +M`), then the 13 RS5 chunks one at a time, then `lake build H11K_h11000 H11K_AxiomGuard`. Everything ran under `ARDA_LEAN_SLOTS=1 leanlock.sh`.
  - Final step: Build completed successfully (**9190 jobs**).
  - Wall time: **9438 s** (2 h 37 min, 2026-10-14 23:46 to 2026-10-15 02:24 EDT).
  - Of the 9190 jobs, 8654 are Mathlib and its dependencies, already up to date from the cache. 536 are local.
  - Memory never dropped below 90% free. Disk went from 156 GB free to 135 GB free.
- `lake build H11K_h11000 H11K_AxiomGuard --no-build`: All targets up-to-date (9190 jobs).
- **The guard's own output.** 64 axiom lines: 28 × [propext, Classical.choice, Quot.sound], 1 × [propext, Quot.sound], 31 × [propext], and 4 with no axioms. There is no sorryAx and no error.
- **My probe** (`lake env lean`, 60 s): `#print axioms` gives **[propext, Classical.choice, Quot.sound]** for each of these:
  - the capstone `H11K_h11000.all_nontrivial_zeros_up_to_height_11000`
  - `..._11004`
  - `segment_8000_11004`
  - `box`
  - `H11K.Line.hLine`
  - `H11K.Edge.E_T11004_hAH`
  - `H11K.Slab.S_U11004_clear`
  - `Arb4.H8000.E_T31851_4_hAH`
  - `Arb4.H8000.S_L31851_4_clear`
  - `Arb4_h8000.all_nontrivial_zeros_up_to_height_8000`
  - `HeightFloor.height_floor`
  - `AllZerosUpToHeight.height_chain`
  - `AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line`

  `chk` gives [propext].
- A pure-Mathlib `example : ∀ ρ : ℂ, _root_.riemannZeta ρ = 0 → 0 < Complex.im ρ → Complex.im ρ ≤ 11000 → Complex.re ρ = 1 / 2 := H11K_h11000.all_nontrivial_zeros_up_to_height_11000` type-checks.

## 4. Trust boundary: the proof itself
**Grep.** I grepped all 532 modules (raw text, and again after comment-stripping with the repo's own lexer) for axiom, opaque, native_decide, ofReduceBool, ofReduceNat, implemented_by, extern, unsafe, skipKernelTC, sorry, sorryAx and admit.
- Raw hits: sorry 57, native_decide 14, axiom 3.
- Hits in code after stripping comments: **zero**.
- Nothing in the closure defines or redefines `riemannZeta`, and there is no `set_option debug.*` or `kernel` option.

**The capstone and its inputs.**
- The capstone has no binders. It is `height_chain 8000 11004 Arb4_h8000.all_nontrivial_zeros_up_to_height_8000 segment_8000_11004`, then weakened from 11004 to 11000.
- `segment_8000_11004` is `all_nontrivial_zeros_in_segment_on_line` with one band, `haC_11004` (proved inline) and `HeightFloor.height_floor 11004`.
- `box` is `H11K.boxCert_of_parts_sharp`. Every one of its inputs is a proved theorem:

  | Input | Discharged by |
  |---|---|
  | hLine | `H11K.Line.hLine` |
  | lower slab | `Arb4.H8000.S_L31851_4_clear` |
  | upper slab | `H11K.Slab.S_U11004_clear` |
  | top edge | `H11K.Edge.E_T11004_hAH` |
  | bottom edge | `Arb4.H8000.E_T31851_4_hAH` |
  | ValidS + K6Side | `chk` (one `decide +kernel`) |
  | cap geometry | norm_num |

- The sharp pins rest on Mathlib's `Real.pi_gt_d6` / `Real.pi_lt_d6`.

**The guard's negative controls.** The guard builds, so the kernel computed `= false` for each of its five: the old pins, n = 3542, n = 3540, a ball that is too small, and the top edge with Lo shifted by +1/10.

**My own tamper controls.** All were rejected: the kernel computed `= false` for each.

| Control | What changed |
|---|---|
| K6b, wrong top Gamma certificate | top GamD at T = 11005 |
| K6b, wrong bottom Gamma certificate | bottom GamD at T = 8000 |
| Shifted edge | `edgeRest {E_T11004 with tn := 11005}` |
| Edge enclosure, wrong upper end | Hi lowered by 1/10 |
| Slab stretched | `slabOK {S_U11004 with hi := 11004 + 1/10}` |
| Wrong π pin | upper pin built with the old 3.14 at n = 3541 |

- The positive twin (the sharp upper pin) evaluated to `true`.
- `¬ (Real.pi < 3.141592)` is proved, so a false π pin cannot be used.
- Three restatements fail to elaborate (type mismatch), as they should:
  - `BandZeros (31851/4) 11004 3542 := H11K.Line.zeros`
  - height 11005 from the 11004 theorem
  - `SlabClear 11004 (11004 + 1/10) := S_U11004_clear`

## 5. Independent numerics (mpmath, my own scripts, single-threaded BLAS)
- **Zero counts.** `nzeros`: N(7962.75) = **7788**, N(8000) = 7830, N(11000) = 11324, N(11004) = **11329**. So the band [31851/4, 11004] holds **3541** zeros, matching n.
- **The cut points match the RS5 chunk counts exactly.**

  | Cut | N |
  |---|---|
  | 509616/64 | 7788 |
  | 525170/64 | 8065 |
  | 10000 | 10142 |
  | 11000 | 11324 |
  | 11004 | 11329 |

  The differences are 277, 2077, 1182 and 5.
- **The zeros around the edges** (`zetazero`), all with Re = 0.5:

  | n | Height |
  |---|---|
  | 7788 | 7962.5625 |
  | 7789 | 7962.9565 |
  | 11329 | 11003.2835 |
  | 11330 | 11004.7802 |

  So the bottom edge 7962.75 is 0.19 / 0.21 from its neighbours. **T = 11004 lies in a wide gap**: 0.72 below it and 0.78 above it.
- **Edge argument changes** along [2, -1] + iT. I computed these with 600 and 1200 steps, and the two agree. My code reproduces the precedent's T = 41 value of 2.696558.

  | T | Numeric value | Certified interval |
  |---|---|---|
  | 11004 | 1.067683 | [1.041271, 1.075553] |
  | 7962.75 | -0.074537 | [-0.088565, -0.063918] |

- **The vertical pieces.**
  - argChange ζ on σ = 2: 0.28474, inside [-0.996, 0.996].
  - Γℝ on σ = -1: 11123.52374655, inside [L4, H4].
  - Γℝ on σ = 2: 11123.52372052, inside [L5, H5].
  - Total argument change / 2π = **3541.000**.
- **Exact pin arithmetic** (Fraction mirror of `validBS`):

  | n | Sharp pins (slack L / H, rad) | Old pins (3.14, 3.1416) |
  |---|---|---|
  | 3541 | +3.682 / +4.834, passes | fail (H slack -6.444) |
  | 3540 | fails (H slack -1.449) | fail |
  | 3542 | fails (L slack -2.601) | fail |

- **Slabs.**
  - U11004: no zero inside. The smallest |ζ| on a 21 × 7 grid is 2.94. The three cells have |ζ(centre)| of 7.48, 4.69 and 3.35, and their circle minima are 5.80, 3.89 and 2.92.
  - L31851_4 = [7962.688, 7962.75]: no zero inside (the nearest is 0.126 below). The smallest |ζ| on the grid is 0.227.

## 6. Trust boundary and scope (additions requested by the lead, 2026-10-15)

### 6.1 Comparator dependency, verbatim
**H11K_h11000 depends on the monolithic `Arb4_h8000.all_nontrivial_zeros_up_to_height_8000`, which the Comparator never replayed (it judged `Arb4_Compose_h8000`). Any "Comparator-recorded" claim for h11000 would currently be false.**

The evidence is my own Lean probe, `ProbeH11KReadbackA1_Deps2.lean` (now deleted), which reads the proof terms from the environment.
- The value of `H11K_h11000.all_nontrivial_zeros_up_to_height_11004` uses: `AllZerosUpToHeight.height_chain`, `Arb4_h8000.all_nontrivial_zeros_up_to_height_8000`, `H11K_h11000.segment_8000_11004` (plus numerals). The 11000 capstone's value uses `..._11004`.
- The value of `Arb4_h8000.all_nontrivial_zeros_up_to_height_8000` uses: `AllZerosUpToHeight.height_chain`, `Arb4_h7000.all_nontrivial_zeros_up_to_height_7000`, `AllZeros_h8000.segment_7000_8000`, `Arb4_h8000.hbands`, `HeightFloor.height_floor`. That is the monolithic chain, not the compositional implication.
- In the capstone's environment, `Arb4_Compose_h8000.ladder_h8000_of_bands` is absent, and the module `Arb4_Compose_h8000` is not imported.
- A transitive walk of the constant graph from the capstone (18490 local constants) contains `Arb4_h8000.all_nontrivial_zeros_up_to_height_8000`, `Arb4_h7000.all_...`, `Arb4_h1000.all_...`, `Arb4_h8000.hbands` and `Arb4_h1000.hbands`. It does not contain `Arb4_Compose_h8000.ladder_h8000_of_bands`.

What the Comparator did judge for h8000 was `Arb4_Compose_h8000.ladder_h8000_of_bands` plus the eight `Arb4_h<H>.hbands` (`judge_mode = "compositional"`). Its record says "the capstone's own proof was not replayed".
- The modules are byte-identical to those judged: the sha256 of all nine named modules matches (Arb4_h1000 d1e421a3 … Arb4_h8000 40a19485, Arb4_Compose_h8000 ae586cb2).
- `git diff` of all 532 closure files against the judged head 495477ce, the CI head a703613b and the authoring commit 93c06d43: 0 files changed.
- So the shared `hbands` are the judged ones. The composition actually used by h11000 is not.

No Comparator record exists for h11000. The node has no `[comparator]` block, and on main `missions-comparator-heavy.yml:17` calls h11000 "UNMEASURED". A `git grep` of main found no document claiming a Comparator record for h11000; the explorer data lists it as `draft`, `closure_clean: false`.

**What a compositional judge would need.** `H11K_h11000` imports `Arb4_h8000`, which matches the compose `forbidden_modules` regex. Its band uses `Arb4_h8000.G_T31851_4`, `Arb4.H8000.E_T31851_4` (Arb4_H8000Edges_5, sha 6a92fa0c) and `S_L31851_4` (Arb4_H8000Slabs_5, sha 04c5f42c). So the judge would need:
- an `H11K_Compose` implication (eight BandHyps + the [8000, 11004] box or segment → 11000) with no certificate import;
- a separate part whose closure is `H11K_h11000.box` (or the segment).

### 6.2 Cost accounting: fixed read-back overhead versus the band
Sources: the per-module "Built X (t)" durations in my 65 build logs, and the sequential wall times in the driver log.
- **Classification.** Modules are split by import closure:
  - LN = closure(`Arb4_h8000`);
  - BN = closure(H11K band roots: `H11K_Turing`, `H11K_EdgeSplit`, `H11K_Edge_T11004`, `H11K_Slab_U11004`, `H11K_Line`, `HeightFloor`, `AllZerosUpToHeight`, `Arb4_H8000Edges_5`, `Arb4_H8000Slabs_5`) ∪ {`H11K_h11000`, `H11K_AxiomGuard`}.

  BN ∪ LN = the full closure (532 modules).
- **Job-seconds** below are the sums of per-module build times. The parallel phases overlap, so they measure compute, not wall time. The total is 30706 s.

| Part | Modules | Job-seconds | Share |
|---|---:|---:|---:|
| Inherited [0, 8000] ladder only (LN − BN) | 333 | 25838 | 84.1% |
| Shared framework + the reused T = 31851/4 edge and slab modules (BN ∩ LN) | 158 | 4351 | 14.2% |
| H11K band only (BN − LN) | 41 | 516 | 1.7% |

- **The inherited ladder, by kind:**
  - edges: 49 modules, 7250 s
  - lines (Arb4 bandC): 42 modules, 7534 s
  - slabs: 41 modules, 3865 s
  - RHInBoxT_* statement modules: 178 modules, 7024 s
  - Arb4_h*/AllZeros_h*/glue: 166 s
- **The band only, by kind:**
  - RS5 chunk certificates (13 chunks + the T10000 aggregator): 232 s
  - the top edge `H11K_Edge_T11004`: 69 s
  - the top slab `H11K_Slab_U11004`: 19 s
  - H11K glue (EdgeSplit, Turing, Line, h11000, AxiomGuard): 67 s
  - the RS/RS4/RS5 framework, first needed by the band in this closure: 130 s
- **Wall time.** Of the 9438 s total:
  - ladder edges, one at a time: 8186 s (including the first build, 337 s, which also built the shared framework)
  - the H11K edge: 110 s
  - the 13 RS5 chunks: 394 s (including the RS framework)
  - the final parallel step: 748 s

  So the band accounts for about 0.5–0.55 ks of wall time (about 6%); the rest is read-back overhead. The ladder's wall time reflects my deliberate one-edge-at-a-time schedule (as in CI, for memory). A parallel build would shrink the overhead, not the band.
- **Unit costs, and how they scale.**
  - *Per edge*, cost grows about linearly with T, because the EM cut is N ≈ 0.3T:

    | Segment | Edges | Seconds per edge |
    |---|---:|---:|
    | h1000 | 27 | 3.9 |
    | h2000 | 30 | 11.2 |
    | h4000 | 29 | 26.9 |
    | h6000 | 28 | 45.8 |
    | h8000 | 32 | 59.6 |
    | H11K, T = 11004 (N = 3302, 25 pieces, per-piece decides) | 1 | 69 |

  - *Per zero*, for hLine: the RS5 chunks cost 222.7 s / 3541 zeros = 0.063 s per zero. The Arb4 bandC lines of segment h8000 cost 1696 s / 1127 zeros = 1.50 s per zero, about 24× more.
  - *Per band*, the wide sharp-π template needs 2 edges + 2 slabs + one `decide` (`chk`) whatever its width. Here the bottom edge and slab are reused from h8000. The Arb4 ladder needs about 27–32 bands per 1000 of height.
- **Answer.** The read-back's cost is mostly fixed: 98.3% of job-seconds is the inherited ladder and the shared framework. The Turing band's own cost is small (516 job-seconds for 3041 units of height and 3541 zeros), and it scales in two ways:
  - linearly in the number of zeros, through hLine (at about 0.06 s per zero near 10^4; the per-sample RS cost grows like √T);
  - linearly in T, through its two edges only.

  It does not scale with the number of bands, because there is one.

### 6.3 Hard case: is a near-Lehmer pair present, and was mesh sufficiency exercised?
**The mesh used by H11K_Line.** All 3554 certificate samples of the 13 chunk modules lie on the dyadic grid of step **1/64** (tq = 6 throughout). This comes from parsing the certificate data with my own `rs5parse.py`.
- One sample is chosen per inter-zero interval: 12 intervals hold two. Sample spacing is minimum 0.297, median 0.859, maximum 1.547.
- A sample's sign is certified only if its box clears the margin (13/5)·E/2^64 ≥ (13/5)·t^(-3/4). That is about 0.0031 at t = 7963 and 0.0024 at t = 11004.
- The chunks give 3541 sign changes in total, and every sample clears its margin.

**The gaps** (my mpmath zeros #7788–#11330, 3543 `zetazero` calls; 3541 lie in the band and 3540 gaps are inner). Every inner gap holds at least one certified sample. The smallest unfolded gaps, δ = gap · log(t/2π)/2π:

| Pair (n, n+1) | γ_n | γ_{n+1} | Gap | Unfolded | Certified sample | Its \|Z\|_lo / margin | Coarsest uniform mesh that separates |
|---|---|---|---|---|---|---|---|
| 11204/11205 | 10898.87456 | 10898.95116 | 0.0766 | 0.0909 | 10898.90625 | 4.27 | 1/16 |
| 9901/9902 | 9793.55000 | 9793.64762 | 0.0976 | 0.1142 | 9793.59375 | 6.29 | 1/8 |
| 8192/8193 | 8316.99170 | 8317.13803 | 0.1463 | 0.1674 | 8317.0625 | 14.11 | 1/4 |
| 8314/8315 | 8423.24065 | 8423.38906 | 0.1484 | 0.1701 | 8423.3125 | 19.36 | 1/4 |
| 9974/9975 | 9856.03139 | 9856.17706 | 0.1457 | 0.1706 | 9856.109375 | 12.48 | 1/8 |
| 9628/9629 | 9559.49788 | 9559.65100 | 0.1531 | 0.1786 | 9559.578125 | 11.52 | 1/8 |

"Coarsest uniform mesh that separates" means the coarsest dyadic grid 2^-k with a point inside the gap where |Z| clears the margin. It was computed with mpmath `siegelz` on the 1/64 grid inside the 300 smallest unfolded gaps and the gaps holding the 20 tightest samples: 289 need only 1/4, 10 need 1/8, and 1 needs 1/16. The tightest certified samples in the whole band are exactly the ones inside the two smallest gaps (ratios 4.27 and 6.29). mpmath Z(10898.90625) = −0.010621, against the certificate's sign − with |Z|_lo = 0.010414.

**Hard case present: YES (near-Lehmer, not Lehmer-grade).**
- **The pair:** zeros #11204/#11205 at 10898.87456 and 10898.95116, gap 0.0766, unfolded gap 0.0909.
- **Not below the RS5 mesh:** the gap is 4.9 steps of 1/64.
- **But below what a uniform 1/4 or 1/8 mesh can separate** with this margin. A uniform 1/4 mesh would have shown a false deficit of 2 here, which is KT45's failure mode (mesh 1/4 at 7005). The sharp pins would then have rejected the band, since n = 3539 fails just as 3540 does.
- **So the exact count 3541 did exercise mesh sufficiency.** It holds because the certificate places a sample at 697530/64 = 10898.90625 between the two zeros, certified at 4.27× its margin. The true maximum of |Z| between them is 0.01097, which is 4.5× the margin.
- **For calibration:** Lehmer's own pair, #6709/#6710 at 7005.06287 and 7005.10056 (gap 0.0377, unfolded 0.0421), has a maximum |Z| of 0.00397 against a margin of 0.00340, a ratio of only 1.12–1.17. It lies below the band, inside the inherited Arb4 ladder (segment h7000, its own evaluator). So the hardest pair in [0, 11004] is in the inherited part, not in the H11K band.

**Limit of this check.** The template is unexercised at Lehmer grade: at a Lehmer-grade pair (unfolded gap < 0.042) it may refuse on the 1/64 mesh with the 13/5 constant, and the hardest pair in [0, 11004], Lehmer's at 7005 (margin ratio 1.12–1.17), lies in the inherited Arb4 part, not in this band. Calibration (COMPUTED, contrarian session; bb-checked from the Wigner surmise, GUE small-gap CDF ≈ (π²/9)s³ over 3540 inner gaps): the expected smallest unfolded gap for a band of this size is ≈ 0.064; this band's 0.091 is in the easy tail (P(min > 0.091) ≈ 0.056); a Lehmer-grade pair appears in about 1 band in 4 of this size, so the template will meet one within a few bands; expect a refusal or a finer local mesh there, never a false theorem.

### 6.4 Purpose on record
Stated by the lead, recorded verbatim: **"template governed on [7962.75, 11004]; no live claim currently cites a band above 8000 (Q4 cites h8000)".**

The template is the wide, sharp-π Turing band, `H11K_Turing` (pins 3.141592 < π < 3.141593). The ladder's `TuringBand.band_count_eq` (3.14 < π < 3.1416) caps a band at roughly 700 zeros, and fails this band (§5). h11000 is the template's first use, which is why it is being read back. "Governed" refers to the governance step this read-back feeds: at the time of writing the node is still `draft`, with no audit and no grant (§0).

My check of the second clause:
- `~/rh-team/wall6/Q4/turing_moire.md:270-276` cites AND_ladder_h8000 (`Arb4_Compose_h8000`) and says the h11000 result "is NOT cited as a certificate here".
- `~/rh-team/wall6/gates/gate0.md:86` says "Q4's ζ holes rest on AND_ladder_h8000 ..., not on h11000 (DRAFT)".
- `~/rh-team/wall6/Q4/certs/zeta_moire_holes.json` says "h11000 is DRAFT, ungoverned -- not cited".
- `~/riemann-hypothesis-lean/docs/PROGRESS.md:576` lists `AND_ladder_h11000_kernel` as `draft`.
- On Arda main, h11000 appears only in its own node, artifacts and lane notes, in the CI workflow, in the explorer data (as draft) and in `missions-comparator-heavy.yml` (as UNMEASURED).

I found no live claim citing a band above 8000. The many `AllZeros_h<H>` modules in zeta_zero_localization with H ≥ 11000 are conditional `..._of_bands` statements; they are not hypothesis-free claims and are not cited as such.

## 7. What this establishes, and what it does not
**Established:**
- A kernel-checked, hypothesis-free Lean proof, using only the three standard axioms, that every ζ zero with 0 < Im ρ ≤ 11000 (indeed ≤ 11004) has Re ρ = 1/2.
- It was rebuilt from source in an independent tree (9190 jobs, 9438 s).
- Its band data agree with my independent numerics.
- The gate passes, and a simulated grant passes the real gate (§0).

**Not established:**
- RH, or anything above height 11004.
- Any Comparator or second-kernel replay of h11000. Any "Comparator-recorded" claim for it is currently false (§6.1).
- That CI enforces these checks. I re-checked nothing in CI; this audit ran locally.
- It trusts the Lean kernel and Mathlib's definitions.
- Independence is limited: one AI auditor, in a different session from the author, with no human review.

conjecture1_proved = False.
