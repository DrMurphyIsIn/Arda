# Local nanoda re-judge of the heavy-certificate nodes (October 2026)

## Purpose

Seven proved mission nodes carry `heavy_certificates = true`. Under nanoda, their exact certificates use
up a 16 GB hosted runner. So CI has only ever judged them with the Lean kernel, and each `[comparator]`
record says `second_kernel = "none: heavy_certificates"`. Lean kernels before v4.33.1 have known soundness
bugs. Both island toolchains here are older than that: zeta_reflection uses v4.32.0 and rvm_bridge uses
v4.33.0-rc2. A Lean-kernel-only verdict on these toolchains therefore isn't enough.

The owner accepted this rule on 2026-10-27: such a node stays proved only if it also passes a local
Comparator run with nanoda ON, against its current artifact, on a machine big enough to hold it. Here that
machine is the 96 GiB / 32-core Mac Studio. Each pass is recorded with
`python -m telperion.cli mission rejudge-record`. That command reads the verdict from the Comparator log
itself, never from a flag. A `REJUDGE-HEADER node=<slug> artifact_sha256=<sha>` line binds the log to
one node and one artifact. The queue script writes that header as the first line of every node log.

The run is done by `telperion/missions/judge/rejudge_queue.sh`, which:

- runs one node at a time, smallest first;
- puts every Lean and Lake call through `~/hodge-engine/leanlock.sh` with `ARDA_LEAN_SLOTS=1`;
- waits while `~/telperion-tools/rejudge/PAUSE` exists, checked before each node;
- stops on the first FAIL, refusal or build failure;
- runs two negative controls right after the first node passes.

`--dry-run` prints every command, and `--self-test` checks the non-Lean parts with stubs.

## Tool versions

| Tool | Version | Where |
|---|---|---|
| nanoda_bin | rev `37cb87b7e6cd6862ef2bd121faa9f4604f59fe96` (`telperion/NANODA_REV`), built by `.github/scripts/build-nanoda.sh` | `~/telperion-tools/nanoda-37cb87b7/target/release/nanoda_bin` |
| Comparator + lean4export, tag `v4.32.0` (zeta_reflection) | comparator commit `07bc4ea40f2266dcb861820a2ec1fa3244ed307f`; lean4export `4e7915201d3f9f04470d9eae002fa695f7cdc589`; Lean4Checker `b7398199245524275543dec6113229c9bb4902e5` | `~/telperion-tools/comparator-v4.32.0/.lake/...` |
| Comparator + lean4export, tag `v4.33.0-rc2` (rvm_bridge) | comparator commit `75c730e9b6ef5c2c3b334fad7c3d51fe20624c88`; lean4export `9fb131bb100eb32ccf6836f14e4f8328d13b6792` | `~/telperion-tools/comparator-v4.33.0-rc2/.lake/...` |
| landrun | pass-through shim, copied verbatim from `missions-comparator-heavy.yml` | `~/telperion-tools/bin/landrun` |

The tag for each island comes from `comparator_tag(island_toolchain(island_dir(...)))` in `judge.py`.
Both Comparator builds ran under leanlock with each checkout's own `.lake/packages`. No shared packages
directory was used, and `lake update` was never run.

**The landrun shim is UNSANDBOXED on macOS.** landrun is Linux-only. The shim drops landrun's options and
runs the command directly, so Comparator's sandbox (read-only `/`, a per-step environment allow-list)
doesn't apply here. Every record's note says so. The shim the plan text suggested was a different, shorter
one, and it would have broken. Comparator calls `landrun --best-effort --ro / --rw /dev ...`, and the
shorter shim skips only one word per option. It would have tried to run `/` as the command. The workflow's
shim knows that `--ro`, `--rw`, `--rwx`, `--rox`, `--env` and `--log-level` each take a value. It also
handles the `--` that the v4.33.0-rc2 Comparator puts before the command.

The stack limit is 65520 KB, the macOS hard limit. CI uses `ulimit -s unlimited`, and root can set that
here too, but on macOS every binary it then launches is killed with SIGKILL. That was measured on this
machine: 65536 KB worked, while 131072 KB and `unlimited` were both killed.

## Node order and how it was derived

The controller asked for smallest first, ordered by each node's last heavy CI `PEAK RSS comparator:` line,
or by artifact and import-closure size where that line doesn't exist. The run-level log download
(`gh run view --log`) came back empty for these runs, so the RSS lines were read from the per-job logs
(`gh api repos/DrMurphyIsIn/Arda/actions/jobs/<id>/logs`). The closure columns count island-local
modules reached by `import` from the artifact.

| # | Node | Island / route | Evidence |
|---|---|---|---|
| 1 | `MM_weil_positivity_prime_free_window` | rvm_bridge / per-PR | No heavy run: judged in the per-PR bundle. Comparator ran 3m33s, Lean-kernel-only (run 36772578397). Closure 29 modules, 0.68 MB |
| 2 | `MM_weil_positivity_window_two_fifths` | rvm_bridge / per-PR | Per-PR Comparator ran 4m51s (run 36772787177). Closure 38 modules, 0.78 MB |
| 3 | `MM_hodge1_window5493` | rvm_bridge / heavy | PEAK RSS comparator 6,790,664 kB (run 38404695545). Build peak 11.1 GB. Closure 65 modules, 8.2 MB |
| 4 | `MM_hodge1_rh_reduction` | rvm_bridge / heavy | PEAK RSS comparator 7,091,880 kB (run 38404699182). Closure 69 modules, 8.3 MB |
| 5 | `MM_hodge1_window45` | rvm_bridge / heavy | PEAK RSS comparator 8,800,056 kB (run 38404702485). Build peak 13.4 GB (Hodge1_Cert45E). Closure 53 modules, 1.0 MB |
| 6 | `AND_ladder_h8000_kernel` | zeta_reflection / heavy, compositional (9 parts) | Its heavy run, 36306561345, came before PEAK RSS lines were added. 8 segment jobs of 16 to 80 min, Comparator parts of 35 min to 1.5 h. Closure 201 modules, 6.3 MB |
| 7 | `AND_ladder_h11000_kernel` | zeta_reflection / heavy, one monolithic closure | Never judged by Comparator (see the finding below). Closure 241 modules, 8.5 MB, which contains h8000's |

Nodes 3 to 5 share most of their `heavy_build_targets`, and nodes 6 and 7 share the 8-segment ladder. The
island builds stay in `telperion/examples/<island>/lean/.lake`, so each later node's build is mostly
incremental.

**Route note (per-PR nodes 1 and 2).** These two nodes have `heavy_certificates = true` but not
`judge_via = "heavy"`. `judge.py --heavy` refuses them by design, and `--force-nanoda` requires `--heavy`,
so the CLI from Task 2 can't render them with nanoda on. The script renders them through the same library
call the CLI makes, `build_bundle(only=[slug], force_nanoda=True)`. It then fixes the require path for the
out directory, the same way `main()` does for `--heavy`. Before running anything, it asserts two things:
the challenge text is byte-identical to the committed per-PR bundle's, and the config differs from the
committed one only in `enable_nanoda` (false becomes true). As in the per-PR workflow, these nodes have no
build plan: `lake exe cache get`, then `lake build MissionChallenges.<slug>` in the bundle.

## Data finding: AND_ladder_h11000_kernel has no `[comparator]` record

Running `grep -n -A12 '^\[comparator\]' telperion/missions/anduril/nodes/AND_ladder_h11000_kernel.toml`
matches nothing (exit 1). The node's tables are `[author]`, `[ci_record]`, `[grant]`, `[proof]` and
`[readback]`. The node is `status = "proved"`, `heavy_certificates = true` and `judge_via = "heavy"`. Its
only CI evidence is `[ci_record]`: the `anduril-kernel-ladder` job of `telperion-zeta-reflection.yml`, run
36149168418, 2026-09-25, artifact sha256 `757836b9...bac7d`. That job is a Lean build, not a Comparator
verdict.

So the record isn't just missing `second_kernel`, as Step 3 of the plan assumed. No independent
Comparator judge, with either kernel, has ever accepted this node. The node's own readback says the same:
"NOT Comparator-recorded: H11K_h11000 uses the monolithic Arb4_h8000.all_nontrivial_zeros_up_to_height_8000,
which no judge replayed". It also notes that a compositional judge would need a new `H11K_Compose`.

The re-judge supersedes this. The queue judges h11000 last, as one monolithic closure with nanoda ON, and
records it with `rejudge-record`. Its log, peak RSS and verdict go in the table below. The node file was
not edited by hand. Note that the h8000 monolithic replay ran more than 4 h before CI's 300-minute
timeout, and h11000's closure contains it. This is expected to be the longest run in the queue.

## Negative controls

The controls run exactly once per invocation of the queue script. They run right after the first node that this
invocation actually judged and passed, on an APFS clone (`cp -c`) of that node's own built bundle,
`<out>-negctl`. A later pass in the same run never triggers them. With `--only` or `--from`, if
`~/telperion-tools/rejudge/negctl.result` already exists, they are skipped and the script prints that it is
skipping them. A full queue run always runs them after its own first pass.

Each control must fail for its own reason. Any other failure is INCONCLUSIVE, because it would appear to validate a
gate it never actually tested:

- **(b) Nanoda with no permitted axioms.** lean4export exports the same constants Comparator exports, from the
  untampered clone. Then nanoda_bin runs on that export with
  `{"permitted_axioms": [], "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true}`.
  - Expected: a non-zero exit plus nanoda_lib's own message, `export file declares unpermitted axiom "<name>"` (from
    `src/parser.rs`; printed as `Error: ...`). `<name>` must be one of `propext`, `Quot.sound` or
    `Classical.choice`.
  - Anything else is INCONCLUSIVE: a crash or panic, a config error, a missing binary, another axiom name, or a
    lean4export failure.
- **(a) Tampered statement.** One numeral in the bridge theorem's statement is changed (n becomes n+1), then
  Comparator runs.
  - Expected: a non-zero exit with a statement-mismatch reason. That is either Lean's `Type mismatch` reported in
    `MissionChallenges/<part>.lean`, meaning the bridge no longer elaborates against the artifact's proof (both
    toolchains print "error: Type mismatch", checked 2026-10-27), or Comparator's own
    `Challenge and solution theorem statement do not match` / `Const does not match between challenge and target`
    (`Comparator/Compare.lean`).
  - Anything else is INCONCLUSIVE, for example a bare `Child exited with 1` or an error in another file.

Outcomes:
- If either control passes, the queue stops with `NEGATIVE CONTROL PASSED -- STOP, REPORT TO OWNER` (exit 3).
- If either is INCONCLUSIVE, the queue stops with `STOP: negative control INCONCLUSIVE ... -- REPORT TO OWNER`
  (exit 5), and no marker is written, so the next run retries the controls.

The results go to `~/telperion-tools/rejudge/results.tsv` as `NEGCTL-a:<slug>` and `NEGCTL-b:<slug>`, and to
`negctl.result`.

| Control | Node / part | Verdict | Wall s | Peak kB | Log sha256 |
|---|---|---|---|---|---|
| (a) tampered statement | MM_weil_positivity_prime_free_window | CONTROL-FAILED-AS-EXPECTED | 20 | 5648832 | `ac5a4ac925e44cfe9ec9b0bdf76890ba0d08d5c229588de3178084416de70883` |
| (b) nanoda, `permitted_axioms = []` | MM_weil_positivity_prime_free_window | CONTROL-FAILED-AS-EXPECTED | 49 | 3952 | `9e66f792922f08848f90b30cb46640ecd7a7336ac113cf44671412720e94d6f6` |

## Results

The controller fills this in from `~/telperion-tools/rejudge/results.tsv` after the run. Each verdict is
the one `rejudge-record` wrote into the node's `[rejudge]` table.

| # | Node | Comparator tag | Start (UTC) | End (UTC) | Wall s | Peak RSS kB | Verdict | Log sha256 |
|---|---|---|---|---|---|---|---|---|
| 1 | MM_weil_positivity_prime_free_window | v4.33.0-rc2 | 2026-10-27T17:38:28Z | 2026-10-27T17:50:14Z | 706 | 6828976 | **PASS** | `cb433b3f9a8982872b13f1892557de477dd6f0ed491093d02a4e2e3289054503` |
| 2 | MM_weil_positivity_window_two_fifths | v4.33.0-rc2 | 2026-10-27T17:52:20Z | 2026-10-27T18:03:52Z | 692 | 10514928 | **PASS** | `f309673afdb3201b5e71cff79a2bb65bccf90b4051223d24c77ca5ad66268360` |
| 3 | MM_hodge1_window5493 | v4.33.0-rc2 | 2026-10-27T18:04:05Z | 2026-10-27T18:38:14Z | 2049 | 8335824 | **PASS** | `df1bb94ce30e57611b2120d227eafc30a67b5ef0c612c6b08368ccf387faf9f0` |
| 4 | MM_hodge1_rh_reduction | v4.33.0-rc2 | 2026-10-27T18:38:30Z | 2026-10-27T19:00:06Z | 1296 | 7831104 | **PASS** | `ff1615cb31f5df669cd3d5e2bcff52e1f025f6f0de769e0153a97b6d25981246` |
| 5 | MM_hodge1_window45 | v4.33.0-rc2 | 2026-10-27T19:00:25Z | 2026-10-27T19:17:41Z | 1036 | 11111680 | **PASS** | `1456ad42a41eb27fddf77f51562dda5055724816bebb6c41b9e36ee93aff602a` |
| 6 | AND_ladder_h8000_kernel (9 parts + compose verify) | v4.32.0 | 2026-10-27T19:18:00Z | 2026-10-28T05:41:30Z | 37410 | 13285008 | **PASS** | `4cb4ef65ffee93bb228cbaed2e65684f8a8a63b72a38cb49977c8d220a917e44` |
| 7 | AND_ladder_h11000_kernel | v4.32.0 | 2026-10-28T05:41:43Z | 2026-10-28T13:32:17Z | 28234 | 13877872 | **PASS** | `d522bcb8127ecc59e03754a9c9e91036bbd908f8133bd2903965025352a73a09` |

**Outcome (2026-10-28 13:32Z):** all 7 heavy nodes PASS. Each was accepted by the Lean kernel AND by nanoda at the pin
37cb87b7, under the 3 standard axioms. Both negative controls failed for their own reasons. The queue finished cleanly.

**AND_ladder_h11000_kernel:** this is the node's FIRST independent judge. Its title and readback say "NOT
Comparator-recorded" (no judge replayed the monolithic closure). The local monolithic Comparator run, with nanoda on,
took 28,234 s at a 13.9 GB peak and PASSED. Its `[rejudge]` is recorded. The title text is the owner's to update; it is
left unchanged here.

## nanoda-direct re-judge (2026-10-28)

Seven proved nodes have no Comparator bundle at all to re-judge them with: no `[comparator]` record, not
`heavy_certificates`. The "nanoda-direct" route (step 0b Task 3) covers them instead: lean4export plus
nanoda_bin run directly on the node's own registered theorem, with no Comparator statement-identity step.
Results are from `~/telperion-tools/rejudge/direct/results.tsv`.

| Node | Start (UTC) | End (UTC) | Wall s | Peak kB | Verdict | Log sha256 |
|---|---|---|---|---|---|---|
| MM_leakage_composite_zero | 2026-10-28T17:22:39Z | 2026-10-28T17:27:03Z | 264 | 384704 | FAIL | `a676334b47cc303b30e2aaee01df183f7fc9c62565cccd8e837822bc8921d649` |
| MM_leakage_composite_zero | 2026-10-28T17:31:25Z | 2026-10-28T17:32:30Z | 65 | 386176 | **PASS** | `cda73c8ee70e07ff5447ff6c3b39944862716d690d31f0435cfb7ba3e7ea722e` |
| AND_g2_reflected_band | 2026-10-28T17:32:34Z | 2026-10-28T17:34:14Z | 100 | 704224 | **PASS** | `2b6f70b01a8205b2e36f3e7b0a5f7fa4ae879f13bc723a961d1553a33a01ad70` |
| RH_dlvp_zero_free_region | 2026-10-28T17:34:15Z | 2026-10-28T17:37:23Z | 188 | 1214080 | **PASS** | `c004354b69f5ba4d591e6bba39dfff31f9942a94a217a93b593f7119e42c44a7` |
| MM_bragg_defect_witness | 2026-10-28T17:58:20Z | 2026-10-28T18:01:18Z | 178 | 160480 | **PASS** | `91edae45f4c929e6d441e59aa47a04df6cc6f0e668512d43f613d809d98d3b53` |
| MM_bragg_defect_witness_sie | 2026-10-28T18:01:18Z | 2026-10-28T18:01:58Z | 40 | 155264 | **PASS** | `cc1f2790d7e3e0add898c4b22a88c67468814640d4c8e2c381cb122370433a35` |
| MM_offline_pairs_le_defect | 2026-10-28T18:01:58Z | 2026-10-28T18:02:41Z | 43 | 387360 | **PASS** | `a2fc1765a5a7c229f4395200662344652256ff37141f4de83d889d314702b24c` |
| MM_recurrence_deficit_eq_excess | 2026-10-28T18:02:41Z | 2026-10-28T18:03:32Z | 51 | 151792 | **PASS** | `e1677666fe909683e9d1d0c10dd0f372227b8f83198c6b06daac95f32c93cf29` |

**MM_leakage_composite_zero FAIL (first run):** false FAIL, nanoda accepted ("no typechecker errors");
pretty-printer "Unable to print axioms" because print_axioms defaulted true -- fixed in 43cb7b349
(Ruling 0b-6) and re-run.

Negative controls (both CONTROL-FAILED-AS-EXPECTED, as required):

| Control | Start (UTC) | End (UTC) | Wall s | Peak kB | Verdict | Log sha256 |
|---|---|---|---|---|---|---|
| NEGCTL:negctl-only-zeta_reflection | 2026-10-28T17:13:18Z | 2026-10-28T17:13:25Z | 7 | 2288 | CONTROL-FAILED-AS-EXPECTED | `01c121f441164a80be284241c667b55cf1446c25afbda0ace28a7225123fe258` |
| NEGCTL:MM_leakage_composite_zero | 2026-10-28T17:32:32Z | 2026-10-28T17:32:34Z | 2 | 2288 | CONTROL-FAILED-AS-EXPECTED | `dc339f8649c161e419df7ad2083afb92943f56f2d23121a34f76a72d012e68c7` |

Notes:

- The route is nanoda-direct. It has no Comparator statement-identity step; statement identity rests on
  the gate's statement check plus the closure digest.
- The 4 zeta_zero_localization nodes were built and exported from `zzl_aux` (srcDir `".."`), because the
  monolith lakefile's 27,090 libs exceed ARG_MAX.
- The nanoda pin is `37cb87b7`, with the 3 standard axioms.
