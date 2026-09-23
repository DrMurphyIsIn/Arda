# Closure run 2026-09-22: synthesis and completeness critique

conjecture1_proved = False

## 1. Honesty preamble

- **Nothing in this run proves, disproves or advances the Riemann Hypothesis.** `RH_conjecture` is still `draft`.
- Every node granted in this run or earlier falls into one of five kinds:
  - an unconditional classical fact (for example zero-free regions or the Riemann-von Mangoldt count);
  - a finite certificate (for example the Li rungs 0..4, or zeros on the line up to a fixed height);
  - a named conditional;
  - an equivalence with RH (the `iff` nodes);
  - an identity between entire functions (`RH_dbn_H0_eq_xi`).
- The "iff" nodes restate RH and do not decide it.
- The Anduril height nodes are finite and rest on Arb data outside the kernel.
- This run was mostly an audit. Its main outputs are:
  - four new Telperion emitters;
  - de Bruijn-Newman groundwork (Route C);
  - an indexed h280000 wrapper that **cannot be granted** under the statement currently registered;
  - a ledger of CI gaps. Several proved nodes are kernel-clean locally but have **no working or required CI** protecting them.
- This file was written by the synthesis lane. It edits no registry file and makes no commit. It records what the lane inputs claim and what I re-checked:
  - the branch merge state;
  - `mission verify`;
  - the node statuses;
  - the lane notes on disk.
- Where the only source is an input, the text below says so.
- **Input caveat.** The JSON handed to this lane was truncated. It contained the four audit groups and two emitter lanes (enclosure_tree in full; preordering_multiplier with verdict 1 in full and verdict 2 cut off mid-sentence). It contained no result or verdict objects for the other lanes: c2a, c2c, c3, strip, h280k, crux, emit:complex_re_im_split and emit:zero_sum_majorant. For those lanes, section 3 relies only on git state, lane notes and commit messages. See section 6.

## 2. Audit ledger

Four audit groups covered 103 proved nodes: rvm_bridge 52, li_positivity+zero_free_bridge 25, zeta_reflection 6, quasicrystal+zzl+BG 20.

- **Critical findings: none.** Every audited PROVED status is mathematically justified. The evidence is kernel replays, restatement probes and `#print axioms` output of exactly `[propext, Classical.choice, Quot.sound]` (the two `[propext]`-only lines in zeta_reflection are a subset of that set).
- Everything below is about CI coverage, trust-input visibility and stale records. None of it is a false proof.

### 2a. Confirmed (major, at least two independent verifiers, none refuting)

**C1. `RH_zero_free_polylog` (rh), and the same gap for `RH_zero_free_gamma5`: no CI job checks the axiom list.**
- The li-positivity-compiles guard runs only `AxiomGuardLiPositivity.lean`. That file cannot import `ZeroFreePolylog` because of a `zeta_sphere_bound` clash.
- The `AxiomGuardZeroFree.lean` and `AxiomGuardPolylog.lean` guards exist, but no workflow runs either one.
- Both verifiers reproduced this locally: the axioms are clean, so PROVED stands.
- Refinement from the verifiers:
  - The required `unit` job runs `mission verify`, and its marker scan does reject a literal `sorry` or `axiom` token in the artifact file itself.
  - The gap is everything else: `sorryAx` terms (the scan returns `[]` for them), the imported closure (`StripBound`, `ZeroFreeBridge`, `StripRepr*`), and the axiom set.
  - Neither lakefile sets `warningAsError`. A `by sorry` downstream gives only a warning and exit 0.
- **Exact fix (workflow, lead):**
  - In `.github/workflows/telperion-lean-e2e.yml`, li-positivity-compiles guard step (around lines 128-150), add a second loop over `AxiomGuardZeroFree.lean`. Use the same `sorryAx` check, the joined-line check that every list is exactly `[propext, Classical.choice, Quot.sound]`, and a floor of at least 2.
  - Also add `AxiomGuardPolylog.lean` to the zero-free-bridge-suite `for G in` loop (around line 2136).
  - No registry op.

**C2. The six zeta_reflection (anduril) nodes have no working CI: `AND_checkline_correct`, `AND_g2_reflected_band`, `AND_em_tail3_number`, `AND_em_zeta_strip`, `AND_first_zero_kernel`, `AND_stirling_binet_k1`.**
- `.github/workflows/telperion-zeta-reflection.yml` cannot pass as written:
  - (a) At line 70, the AxiomGuard files are not `lean_lib`s. The build fails with "unknown target AxiomGuardA4".
  - (b) At line 82, `lake env` fails with "could not execute external process". The sibling zzl lakefile has 27,086 `lean_lib`s, and Lake v4.32 `leanSrcPath` does not deduplicate them, so the environment exceeds ARG_MAX.
  - (c) At line 88, the grep rejects the legitimate `[propext]`-only lines for `ReflectedBand_t14.ok` and `checkLine_sign_isSome`.
  - (d) The workflow has 0 runs.
- It is not a required check.
- `coverage.py` passes it on a text match of `lake build` alone.
- The grants date from 2026-09-18, before the coverage gate and this workflow existed.
- **Exact fix (workflow, lead):**
  - Declare the five guards as `lean_lib`s, or invoke the toolchain `lean` with a hand-built `LEAN_PATH` instead of `lake env`.
  - Build zeta_reflection against a slim zzl sub-project that declares only LambdaLineReal, XiLineZeros, DiffractionCore and their dependencies, or deduplicate `LEAN_SRC_PATH`.
  - Change the axiom check to accept any subset of the three standard axioms.
  - Run `gh workflow run telperion-zeta-reflection.yml` once and record the run id.
  - Harden `coverage.py` so that a proved node's artifact module must be a built target in a job that has actually succeeded.
- **Registry op:** annotate the six readbacks. This is a hand edit; see section 4, op R2.

**C3. `AND_g2_reflected_band` (anduril): the trust input is missing from the title, and `closure_clean` launders it.**
- `ReflectedBand_t14.pilot` takes three undischarged Arb enclosure hypotheses, `hmem0`, `hmem1` and `hmem2`. Only `ok : checkLine d.boxes = true := by decide` is decided by the kernel.
- The title does not mention those hypotheses, and `closure_clean = true`.
- This contradicts the `MM_bragg_defect_witness` precedent: an Arb hypothesis makes `closure_clean = false`, and the title says so.
- Both verifiers recomputed the three enclosures at mpmath dps 150-220. They are numerically true, at relative positions 0.397, 0.542 and 0.448, so the node is not vacuous.
- Root cause: `verify.py` grant writes `closure_clean = (status == "proved")`. A deliberate dirty flag has to be set by hand after the grant; it then survives, because `_compute_closures` treats a direct proof's stored flag as authoritative.
- **Exact fix (registry, lead):** see section 4, op R1. Do not change the statement.

**C4. BG (all 9 proved nodes): proof-lean.yml has not passed since 2026-09-09 (c710b09).**
- The scheduled main runs on 09-20, 09-21 and 09-22 were killed with exit 143 in the Build step, after about 126 minutes against a 150-minute timeout.
- The AxiomGuard, orphan and `sorry`-scan steps were skipped.
- proof-comparator.yml was last green on 2026-09-08.
- Not required. `enforce_admins` is false.
- Mitigation: no R3Cert file in the import closure of the 7 artifact modules changed after c710b09, and the lakefile, manifest and toolchain are unchanged.
- **Exact fix:**
  - Fix the cold-rebuild timeout: restore the Mathlib/.lake cache (`lake exe cache get` before the build), split the build, or raise `timeout-minutes`.
  - Rerun on main and confirm the guard passes.
  - Consider a slim required R3Cert guard job.
- **Registry op:** add a BG campaign note that its proved nodes rest on the 2026-09-09 build (section 4, op R3).

**C5. BG: 7 of the 9 node theorems are never printed by `proof/formalization/AxiomGuard.lean`, and the guard only greps for `sorryAx`.**
- Missing from the guard:
  - `cavity_recursion`
  - `fractal_tail_as_ratio`
  - `pi_utree` (its cone is printed only indirectly, via `perm_ratio_le_rate` at AxiomGuard:212)
  - `validPotentialPlain_holds` (not in `phi_le_one`'s cone; the `BG_phi_le_one -> BG_lb_classification` edge is documentary)
  - `merge_normalForm_perL`
  - `nearStar_nonpos`
  - `nearStar_tie`
- A self-declared `axiom` in those cones would pass CI. The repo-wide scan does not grep for `axiom` either.
- **Exact fix:**
  - Add fully qualified `#print axioms` lines for the 7 theorems.
  - Change the proof-lean guard step (`proof-lean.yml:153-163`) to require that every joined "depends on axioms" line is exactly `[propext, Classical.choice, Quot.sound]` (the `telperion-production.yml:126` pattern), plus an anchor-count floor.

### 2b. Unconfirmed (single auditor, no verifier pass; all minor or info)

These are credible, and the auditors attached evidence, but they did not go through the two-verifier pass.

rvm_bridge (52 nodes, verdict: no critical or major findings):
- rvm-bridge-compiles is not required, and `enforce_admins` is false.
- The guard asserts a floor of 45 lines, not the name of each node.
- `generate.py --check` covers only 5 of the 52 artifacts for vocabulary-mirror drift.
- The statement package contains `sorry` scaffold stubs (`RHDefs.lean:532 windowSet_finite`, `MMDefs.lean:470 zeroWindowSet_finite`, `MMDefs.lean:156`). They are proof-irrelevant because they are consumed via `Set.Finite.toFinset`; this is already known.
- The MMDefs provenance is stale: it cites `RvMBridge12.winSet/zeroWindow`, which now live in `RvMBridgeGauss:366-380`, and it says "NOT registered" for a node that is proved.
- The `MM_rvm_unbounded_mean_density` and `MM_zeta_ordinates_not_uniformly_discrete` titles contradict their proved status.
- Five conditional RH titles still say "in flight" for hypotheses that are now discharged.
- `Probes/Audit12_Probes.lean` has a deliberate negative-probe `sorry`, outside every closure.

li_positivity+zero_free_bridge:
- `RH_zero_free_gamma5` is covered only indirectly (see C1).
- None of the covering jobs is required.
- `RH_companion_bragg_reduction` is effectively vacuous as a conditional. Its three limit hypotheses are satisfied by constant sequences, so its real content is the unconditional split identity. The title overstates it.
- The `RH_bl_finite_multiset` `fidelity_note` still says "NOT on main CI"; that is stale.
- `verify.py` `artifact_incompleteness_markers` misses the following, and scans only the artifact file:
  - `private axiom`, `protected axiom` and `@[attr] axiom`;
  - `opaque`, `implemented_by`, `@[extern]` and `debug.skipKernelTC`.
- `build_rhdefs.py` is stale: running it in place would delete the hand-added RHDefs blocks at lines 169-207 and 366-596.
- The audit worktree's li `.lake` was stale; the auditor rebuilt it (9013 jobs).

zeta_reflection:
- The six artifact modules are not in `defaultTargets`.
- `AND_em_tail3_number` has stale line citations: `:469` should be `:626`, and `ANDDefs:65` should cite `:555`.
- The anduril `mission.toml` description and the six readbacks still say "grant deferred to the branch reconcile".
- The `AND_first_zero_kernel -> AND_g2_reflected_band` edge is documentary.
- `EMZetaComplex.lean:14` contains the bare phrase "sorry-free".

quasicrystal+zzl:
- `MM_bragg_defect_witness` is stale. `hexp` is already discharged in the kernel by `ExpEnclosureInstances.exp_tenth_bracket_defs`, and there is a `bragg_defect_witness_unconditional`, but neither is guarded. `BraggDefect.bragg_defect_witness` itself is not printed by any guard.
- `MM_offline_pairs_le_defect`: the `Standalone` mirror is not guarded.
- The `MM_nt_brick_conditional` readback says `closure_clean = false`, but the flag is true. The statement is also generic in `Ordinates`.
- `MM_torus_section_n2_rigidity` depends on the deprecated `MM_torus_section_dictionary`.
- `MM_selfinversive_iff_hardyz_real` proves one direction only.
- The AxiomGuardQC floor is 68, but there are 96 anchors, and only two node names are asserted.
- satake-degree-two-compiles is failing on a libflint tooling error.
- zzl root lakefile hygiene: the libraries are covered through `zzl_aux`.

Found by the h280k lane rather than an auditor:
- The checked-in `zzl_aux/lakefile.toml` lists `ExpEnclosureInstances`, `ExpLaurentDeficit` and `RecurrenceDeficit`, which are not monolith `lean_lib`s.
- Any `register-lakefile --sharded` rerun would silently drop them from CI. `RecurrenceDeficit` is the artifact of `MM_recurrence_deficit_eq_excess`.

## 3. Per lane

All lane branches below are ancestors of `rh/closure-base` HEAD `7c116bdef` in `/Users/peterwmurphy/arda-closure`; I checked each with `git merge-base --is-ancestor`. That branch is 22 commits ahead of `origin/main`, its working tree is clean, and `PYTHONPATH=src /usr/bin/python3 -m telperion.cli mission verify` prints OK for anduril, bg, mirrormere and rh. The one WARN lists 10 example islands that no CI builds; none of them is dbn, zeta_reflection, li_positivity or rvm_bridge.

### emit:enclosure_tree (`cl/emit-enclosure-tree` @ a6e7c77a6, merged in 6cf66249c)
- **Status:** complete.
- **Theorems:** `DogfoodEnclosureTree.*`, 40 in all:
  - the rate lemmas `li_height_rate_4000_rate` (n <= 18848) and `li_sharp_rate_4000_rate` (n <= 25128), found at the same pi rungs d4 and d6 as the hand proofs;
  - 7 `qc_*` LeakageDictionary brackets;
  - 27 `rt_*` route-coverage lemmas;
  - cross-checks that feed the rate lemmas into `li_rungs_of_bands_4000` and `li_rungs_of_bands_4000_sharp`.
- **Build:**
  - 289 passed, 103 skipped on the six targeted pytest files;
  - broad suite 2647 passed;
  - `lake env lean` on the dogfood: 40/40 with the three standard axioms;
  - `lake build DogfoodEnclosureTree` succeeded, 8750 jobs;
  - AxiomGuardLiPositivity: 19/19 new anchors clean;
  - negative-control twin: the FALSE twin fails with exit 1 and `sorryAx`; the TRUE twin is clean.
- **Skeptics:** 2 of 2 not refuted. Between them:
  - 18 and 19 phantom instances respectively, all refused;
  - hand-tampered certificates rejected by the kernel;
  - a full AxiomGuard build: 9010 and 9016 jobs, 19/19 clean;
  - the rate lemmas match `LiLadderHeight:219-226` and `LiLadderSharp:126-133` exactly.
- **Remaining:**
  - The quasicrystal copy of the probe has not been compiled on its own v4.32.0 island (only a shadow build on the li Mathlib).
  - Whether to replace the hand `pi_gt_d4`/`pi_gt_d6` steps is a lead choice.
  - Refused for now: `exp` for |x| > 1, `log` of non-rationals, symbolic parameters, mirrored arctan.

### emit:preordering_multiplier (`cl/emit-preordering-multiplier` @ 75fe41969, merged in 8a396a2f0)
- **Status:** complete.
- **Theorems:** `DogfoodPreorderingMultiplier.*`, 15 in all:
  - `re_Q1..Q5_nonneg_regen(_real)`;
  - LP-found `re_Q4/Q5_nonneg_lp(_real)`;
  - `re_Q6_disk_claim_false`: Re Q_6 = -27772/15625 at (4/5, -2/5). This is about the disk relaxation, not about any zero.
- **Build:**
  - pytest 339 passed, 105 skipped;
  - full `lake build` 9017 jobs;
  - AxiomGuardLiPositivity: 245 axiom lines, the 15 new ones exactly the three standard axioms;
  - negative-control twin: the FALSE twin is rejected, the TRUE twin is clean.
- **Skeptics:** verdict 1 not refuted. It covered:
  - 14 bad instances, all refused;
  - kernel tampers of Q3, Q4 and the Q6 witness, all rejected;
  - an independent sympy recomputation of Q_1..Q_6 and the certificates;
  - 13 opt-in kernel tests passed.
  Verdict 2 was truncated in my input. Its first words ("I reproduced every claim for emit:preorde...") read as non-refuting, but I could not see its content.
- **Remaining:**
  - Optional provenance note on `RH_li_rungs_lt_five`.
  - Next targets: the E6Bridge28 rvm rungs, Box 2.
  - Test-hygiene footguns: `test_cert_meta.py` and 7 other tests run `lake` outside the lock.

### emit:complex_re_im_split (merged in ac60f919f) and emit:zero_sum_majorant (merged in 1792bc84a)
- **Status (lane notes):** complete, merged by the lead with keep-both registry resolution. According to the merge commit message, zero_sum_majorant's rvm_bridge island built 8887 jobs with a clean three-axiom guard.
- **Skeptic verdicts:** not in my input.
- **Theorems:** not re-verified by this lane.

### c2a / c2c / strip / c3: Route C, dbn island (merged in fd4385923, 27b62c097, 1264ddd3d)
- **Granted:** `RH_dbn_H0_eq_xi` (DBNXi.lean), `RH_dbn_H0_zero_strip` (DBNStrip.lean) and `RH_dbn_rh_iff_H0_real_zeros` (DBNRealZerosIffFinal.lean) are PROVED. Grant commit 8c94ac446; the attempts rows say "two skeptics + two blind audits pass; 3-axiom clean".
  - `RH_dbn_H0_eq_xi` is an identity between entire functions.
  - `RH_dbn_rh_iff_H0_real_zeros` is an RH-equivalence. It does not decide RH.
- **c2c:** its uncommitted `DBNGKernel.lean` is byte-identical to the committed copy that came in through c2a, so nothing is lost.
- **c3:**
  - Groundwork, all axiom-clean with 124 guard lines: `DBNStep`, `DBNStepControls`, `DBNHurwitz`, `DBNHeatApprox`, `DBNDeBruijnReduction`.
  - `H_ne_zero_of_obligations` gives de Bruijn's t >= 1/2 statement, conditional on two named obligations:
    - L1 `H0ZeroFreeOffStrip`. It is now available as the contrapositive of the proved `RH_dbn_H0_zero_strip`.
    - L3 `ApproxHadamard`, an even Hadamard product for each approximant `Gδ δ k` of order <= 3/2. It is **not done**, and Mathlib has no Hadamard factorization.
- **Skeptic verdicts** for these lanes are not in my input. The grant commit records them.

### h280k (`cl/h280k` @ ec5cafc1b, merged in dd288df44)
- **Status:** artifact complete, **not grantable**.
- **Artifact:**
  - `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000` and `Guard_h280000`.
  - Per the lane notes, these were checked by direct `lean` 4.32.0 against the read-only arda-million build, plus 32 band oleans rebuilt from byte-identical sources.
  - Axioms are the three standard ones.
  - The negative control fails as it should.
  - A registry-copy check and a standalone Mathlib-only elaboration of the proposed statement both pass.
  - No `lake build` was run anywhere. CI builds only up to `H_CI = 50000`.
- **Blocker:**
  - The registered `Statements/AND_ladder_h280000.lean` (12 lines) is hypothesis-free. The artifact is conditional on `hbands` (10,379 literal strip-box claims, each the conclusion of an Arb-conditional band theorem) and on `hγ`.
  - The proposal `/Users/peterwmurphy/arda-cl-h280k/PROPOSED_AND_ladder_h280000_statement.lean` (about 22.2k lines, uncommitted, at the worktree root) is **weaker** than the registered statement.
  - Adopting it re-quantifies a registry statement, which the house rules forbid without an owner decision.
- **Skeptic verdicts:** not in my input.

### crux, audit
- **crux:** `cl/crux` sits at the base commit 3b5bcccd5 with no lane notes and no diff. Either nothing was delivered or its output never reached this worktree.
- **audit:** read-only, as section 2 describes.

## 4. Lead op list (in order)

Run all CLI commands from `/Users/peterwmurphy/arda-closure/telperion` as `PYTHONPATH=src /usr/bin/python3 -m telperion.cli ...`. After every registry edit, run `PYTHONPATH=src /usr/bin/python3 -m telperion.cli mission verify` and require OK for all four campaigns.

**Commits and branches**
1. **All lane branches are already merged into `rh/closure-base`** (`/Users/peterwmurphy/arda-closure`, HEAD 7c116bdef). There is no further lane merge to do.
   - Do not merge `cl/crux`; it is empty.
   - Do not commit the untracked `LANE_NOTES_*.md` or `PROPOSED_AND_ladder_h280000_statement.lean` from the lane worktrees into this branch unless you intend to. The PROPOSED file is an input for the owner decision in step 9.
2. Commit this file:
   ```
   git add telperion/docs/CLOSURE_RUN_2026-09-22.md
   git commit -m "docs: closure run 2026-09-22 synthesis (conjecture1_proved = False)"
   ```
3. Push `rh/closure-base` and open a PR to main. CI on that PR is the first CI evidence for the dbn island grants and the four emitters.
   - Check that dbn-compiles, li-positivity-compiles (with 34 new anchors: 19 enclosure_tree plus 15 preordering_multiplier) and rvm-bridge-compiles are green before merging, even though none of them is required.

**Registry ops.** None of these ops has a CLI command. `mission audit` on a non-draft node **overwrites** the readback and then exits 1 when the promote fails, and `link --force` repoints artifacts. So every op below is a hand edit of the node TOML, followed by `mission verify`.

4. **R1 (C3) `AND_g2_reflected_band`:** in `telperion/missions/anduril/nodes/AND_g2_reflected_band.toml`:
   - set `[proof] closure_clean = false`;
   - append to the title: "(pilot carries three Arb gLine-enclosure hypotheses hmem0/hmem1/hmem2; only `ok` is kernel-decided; closure_clean = false per the MM_bragg_defect_witness ruling)";
   - append a dated readback sentence saying the same.
   - The flag survives later grants, because direct-proof flags are authoritative in `_compute_closures`.
   - Then append an attempts row to `missions/anduril/attempts.jsonl` recording the ruling (session `closure-2026-09-22`, verdict `Proved`, detail "closure_clean set false by hand: Arb hypotheses hmem0-2").
5. **R2 (C2) the six anduril nodes:**
   - Append a dated readback note: "kernel-verified locally (audit rebuild of the 103-module closure, 2026-09-22); telperion-zeta-reflection.yml has never run and cannot pass as written; not a required check."
   - Refresh the stale mission.toml description ("no node enters as proved ...").
   - Keep status PROVED: every node's Lean is verified.
6. **R3 (C4/C5) BG campaign:** add a note to `missions/bg/mission.toml`, or to each of the 9 node readbacks: "last green proof-lean build 2026-09-09 (c710b09); 7 of 9 node theorems unguarded; axiom guard checks only sorryAx." Leave statuses unchanged.
7. **Optional minor ops** from 2b, each a hand edit that changes no status:
   - refresh the `RH_bl_finite_multiset` `fidelity_note`;
   - add the vacuity note to `RH_companion_bragg_reduction`;
   - drop the stale closure_clean sentence from the `MM_nt_brick_conditional` readback;
   - drop the deprecated `depends_on` edge from `MM_torus_section_n2_rigidity`;
   - retitle `MM_rvm_unbounded_mean_density` and `MM_zeta_ordinates_not_uniformly_discrete`;
   - refresh the "in flight" titles;
   - fix the MMDefs provenance;
   - fix the stale `AND_em_tail3_number` citations;
   - add the `RH_li_rungs_lt_five` provenance note (the emitter regeneration, plus `re_Q6_disk_claim_false`).
   - `MM_bragg_defect_witness`: a closure_clean flip to true, or a sibling unconditional node, is an **owner** ruling. Do not do it in this run.

**Workflow fixes** (separate PR; section 2a gives the exact edits)
8. C1 (the AxiomGuardZeroFree/AxiomGuardPolylog loops), C2 (zeta-reflection workflow, `coverage.py` hardening), C4 (proof-lean cache and timeout), C5 (the BG guard's 7 anchors and exact-set check). Also:
   - widen `_ASSUMPTION_DECL_RE` and add the `opaque`, `implemented_by`, `extern` and `skipKernelTC` tokens;
   - make the island compile jobs required (owner decision);
   - fix the `zzl_aux` drift before anyone reruns `register-lakefile --sharded`.

**Nodes that must NOT be granted**
9. `AND_ladder_h280000` (anduril, open). **Do not grant.**
   - The artifact does not prove the registered hypothesis-free statement.
   - Re-registering in shape A2 weakens the statement. It needs an explicit decision from the owner (the user); no lane or script can make it.
   - Only after that approval, in this order:
     1. Replace `missions/anduril/lean/Statements/AND_ladder_h280000.lean` with the rendering of `PROPOSED_AND_ladder_h280000_statement.lean` (the tool adds the header and the placeholder body), then check `regen_diff` and `mission-statements-compile`.
     2. Retitle the node as the lane proposed ("Arb-conditional finite verification to height 280000 ... NOT a proof of RH. conjecture1_proved = False").
     3. Replace the readback. The node is open, so `mission audit` records the readback and exits 1 on the promote failure; that exit is expected. Only a blind auditor may write the readback:
        `mission audit AND_ladder_h280000 --campaign anduril --text "<blind auditor's own words>" --auditor "<auditor id>"`
     4. `mission attempt ...` (row as in LANE_NOTES_h280k.md, proposal 4).
     5. `mission link AND_ladder_h280000 --campaign anduril --artifact ../../examples/zeta_zero_localization/lean/AllZeros_h280000_Indexed.lean --kind lean_module --via direct`. Then hand-add the `fidelity_note`: "kernel-checked locally by direct lean against the arda-million build, 32 band oleans rebuilt; not in CI (H_CI = 50000)".
     6. `mission grant AND_ladder_h280000 --campaign anduril`.
     7. By hand, set `closure_clean = false` (Arb box claims), as in R1.
10. `RH_dbn_debruijn_real_zeros` (rh, draft). Obligation L3 `ApproxHadamard` is unproved, and there is no assembly module.
11. `RH_conjecture` (rh, draft). This is RH.
12. `RH_weil_window_floor_of_certified_block` (rh, draft). It is conditional on four undischarged inputs, and its readback has not been audited.
13. `MM_zeta_comb_membership` (draft), `MM_satake_degree_two_rejects_delta` (draft) and `MM_speiser_box_probe` (open, no artifact).
14. `AND_ladder_1e6`, `AND_ladder_1e9` (open) and `AND_ladder_1e13` (draft). These are compute-bound or era-gated, and there are no artifacts.

## 5. What is still open after this run

Node counts on `rh/closure-base`:

| Campaign | Proved | Other |
|---|---|---|
| rh | 53 | 3 draft |
| mirrormere | 38 | 2 draft, 1 open, 1 deprecated |
| anduril | 6 | 3 open, 1 draft |

- **RH-equivalent goals (open by construction):**
  - `RH_conjecture` is RH.
  - `MM_zeta_comb_membership` (the W3c defect-0 membership of the regularized Guinand-Weil triple) is a campaign-goal restatement. Closing it is an RH-strength task.
  - The proved `iff` nodes (`RH_weil_criterion_iff`, `MM_rh_iff_*`, `RH_dbn_rh_iff_H0_real_zeros`) move the burden to equivalent positivity or reality statements, and every one of those is still open.
  - `MM_speiser_box_probe` is deliberately one finite box, not the Speiser wall. The wall itself (zeta' nonvanishing on the left half of the strip) is RH.
- **Route C (de Bruijn-Newman):**
  - `RH_dbn_debruijn_real_zeros` (Lambda <= 1/2) is unconditional mathematics, not RH, but needs L3: a Hadamard factorization for an entire even real function of order <= 3/2. Mathlib has no Hadamard theory. This is the largest real formalization gap on the route.
  - Everything past Lambda <= 1/2 toward Lambda = 0 is RH, since Lambda <= 0 is RH-equivalent.
- **Compute-bound ladders:**
  - `AND_ladder_1e6`: about 1.8M zeros; wall-clock only on the current T5 machinery.
  - `AND_ladder_1e9`: charter-gated on the A3 Riemann-Siegel era.
  - `AND_ladder_1e13`: native_decide era. It is flagged in its title and cannot be kernel-only at scale.
  - `AND_ladder_h280000`: blocked on the owner re-registration decision (section 4, op 9). The hypothesis-free form is a multi-quarter interval-arithmetic program.
- **Conditional drafts that cannot be proved as registered:**
  - `RH_weil_window_floor_of_certified_block`: four named undischarged inputs, including an Arb-certified eigenvalue floor.
  - `MM_satake_degree_two_rejects_delta`: its registered content is an elementary identity, and the Delta-specific claims are unregistered.
  - These should not be proved as stated until someone decides whether the hypotheses become registry nodes.
- **Arb trust boundary.** Every Anduril height result, and `AND_g2_reflected_band`, rests on Arb enclosures outside the kernel. `MM_bragg_defect_witness`'s enclosure is now kernel-discharged, but not guarded and not re-registered.

## 6. Completeness critique: what this run did not check

1. **Truncated inputs.**
   - I received no result or verdict JSON for c2a, c2c, c3, strip, h280k, crux, complex_re_im_split or zero_sum_majorant, and only part of preordering_multiplier's second verdict.
   - Their statuses above come from git, lane notes and commit messages, not from skeptic verdicts I could read.
   - The dbn grants depend on the lead's record ("two skeptics + two blind audits") in commit 8c94ac446. That record is not reproduced here.
2. **No CI run on `rh/closure-base`.**
   - The merged branch is 22 commits ahead of main and has never been pushed through CI.
   - Merge-time structural resolutions were done by hand: the lakefile libraries, guard blocks, and the `ofReal_exp_cpow` to `ofReal_exp_cpow_comm` rename in DBNStrip. They are checked only by the lead's local builds as described in the merge messages (dbn 8747 jobs, rvm 8887 jobs).
   - No combined build of every island at the merged HEAD is recorded.
3. **h280000 has no `lake build` evidence.** Its evidence is a direct `lean` run against mixed-date oleans: bands dated 09-13, core modules 09-16, plus 32 rebuilt oleans. Plain `lean` does not check consistency across oleans. A clean `lake build` of the block chain was not done.
4. **Islands not rebuilt by any auditor:**
   - The audit worktree had no `.lake` for quasicrystal, zeta_zero_localization or proof/formalization. The mirrormere quasicrystal and zzl evidence and all of the BG evidence therefore come from CI logs on 250f176, or 2026-09-09 for BG, not from local replays.
   - The zero_free_bridge (v4.32) home island was not probed; it was checked through a byte-identical copy on v4.34.
   - Toolchain drift: rvm probes elaborated the Defs on v4.33.0-rc2 Mathlib, not on the registry pins (rh v4.34.0-rc1, mm v4.32.0).
5. **BG semantics were not audited.** Only containment, markers and guard coverage were checked; BGDefs was not compared against the island definitions.
6. **Emitter follow-ons were not verified:**
   - The quasicrystal dogfood of enclosure_tree was never built on its own island.
   - The two unseen emitter lanes had no skeptic output in my input.
   - Nobody ran the full pytest suite at the merged HEAD. The lanes ran it on their own branches, excluding the tests that call `lake`.
7. **Anything outside the four campaigns** (`bg` beyond CI, `li_positivity` nodes on other campaigns, the 10 islands no CI builds) was out of scope.
8. **Required-check posture.** The audits all found that no island Lean job is a required check and that `enforce_admins` is false. Until the owner changes that, every PROVED status in all four campaigns can be broken on main without CI blocking the merge. This run documented that; it did not change it.
9. **Environment debris left by verifiers:**
   - `/Users/peterwmurphy/arda-cl-audit/proof/formalization/.lake`: 672 MB of package clones, gitignored, no build. A verifier's `rm` was denied. The lead should delete it.
   - One verifier ran `rm -rf` on li_positivity `Probes/` and restored the 6 tracked files. Any untracked probe files another lane had there are gone. None is known to have mattered.
   - Several lanes ran as uid 0. Lake-written `.lake` files may be root-owned in any worktree whose lane did not chown them.
10. **The gate itself** still has the marker-regex holes listed in 2b, and `coverage.py` still accepts a text match of `lake build`. Every future grant relies on both until the workflow fixes in section 4 land.
