# B2 MAIN CI — building the sharded zeta-zero ladder block-by-block

*(PROGRAM ANDÚRIL WS-B2. `conjecture1_proved = False` — finite verification
scaffolding; CI proves the certificate ladder *compiles* and is axiom-clean, NOT
that RH holds.)*

This document specifies how `main`'s CI builds the certified zero-localization
ladder after the B2 sharded layout lands, so a high in-tree capstone can be
CI-verified without hitting the E2BIG monolith wall.

## The problem CI has today

The monolith `lean/lakefile.toml` registers every module (~16k+ `[[lean_lib]]`,
2.9 MB file, 843 KB `defaultTargets` line). `lake env lean` on it fails with
`could not execute external process 'lean'` — the ~16k-module `LEAN_PATH`/argv
overflows `execvp` (E2BIG). So main CI cannot `lake env`/`lake build` the whole
ladder; today only a low capstone (the height #525's paper cites, ~160000) can be
pinned in-tree because building higher on one CI job is infeasible.

## The fix: one CI build unit per 25k block

The sharded layout gives one bounded lake package per 25k-height block
(`ZetaBands_h<top>/`, `srcDir=".."`, ~1000 modules each) plus the shared
`zzl_core` (16 modules) and `ZeroFreeBridge` (89 modules). Each block:

- is independently `lake build`-able and stays well under E2BIG (~1000-module
  `LEAN_PATH`, not 16k);
- restores `lake env lean` → `#print axioms` / editor tooling at the block level;
- rebuilds only itself when a band in it changes (no 16k-target rebuild).

CI builds these units in ascending-height order (the cross-block chain edge makes
block N depend on block N-1's top capstone), sharing Mathlib + deps ONCE.

## CI job matrix (recommended)

Two-stage: a **foundation** job the blocks depend on, then a **block matrix**.

### Stage 0 — foundation (single job, cached)

```yaml
foundation:
  steps:
    - restore-cache: key=lake-deps-v4.32.0-${{ hashFiles('lean/lake-manifest.json') }}
    - run: |
        export PATH=$HOME/.elan/bin:$PATH
        cd telperion/examples/zero_free_bridge/lean && lake build      # 89 ZFB oleans
        cd $ISLAND && lake build --dir lean/zzl_core                   # 16 core oleans
    - save-cache: [ ZFB build lib, zzl_core build lib, .lake/packages ]
```

`.lake/packages` (Mathlib + batteries/aesop/Qq/proofwidgets/importGraph/
plausible/LeanSearchClient, ~7.6 GB) is fetched once, cached, and **shared by
every block via symlink** — it is never re-fetched per block. Cache key is the
manifest hash so a dep bump busts it cleanly.

### Stage 1 — block matrix (parallel where possible)

Each block is a matrix entry. Because block N's lowest capstone imports block
N-1's top capstone, the require graph forces order; encode it as a dependency
chain OR (cheaper for CI) let each block job restore the prior block's cached
build lib:

```yaml
block:
  needs: foundation
  strategy:
    matrix: { top: [25000, 50000, 75000, ..., <H_ci>] }
    max-parallel: <node-count>
  steps:
    - restore-cache: foundation deps + prior-block build lib (block top-25000)
    - run: |
        export PATH=$HOME/.elan/bin:$PATH
        cd $ISLAND/lean/ZetaBands_h${{ matrix.top }} && lake build
    - run: |                                            # axiom battery, per block top capstone
        lake env lean -c '#print axioms
          all_nontrivial_zeros_up_to_height_${{ matrix.top }}_of_bands'
        # assert output == [propext, Classical.choice, Quot.sound], no sorryAx
    - run: rm -rf .lake/build/ir                        # disk lever: keep lib/, drop IR
    - save-cache: [ block build lib ]
```

**Ordering options:**
- *Strict chain* (simplest, slowest): `block[N] needs block[N-1]`. Serial;
  wall = sum of block times. Use for the correctness gate.
- *Prior-block-cache* (fast): each block restores block N-1's build-lib cache
  from the previous CI run; on a cold cache, fall back to a bottom-up serial
  bootstrap. Blocks then build in parallel once caches are warm. Recommended for
  the steady-state ladder CI.

Because a single band change rebuilds only its block (module identity preserved,
Replay everywhere else), the common PR touches ONE block → one matrix cell
recompiles, the rest restore from cache.

### Alternative: umbrella loop (no matrix)

For a single-runner CI, a bash loop over blocks is equivalent and simplest to
reason about:

```bash
export PATH=$HOME/.elan/bin:$PATH
cd telperion/examples/zero_free_bridge/lean && lake build && cd -
cd $ISLAND/lean/zzl_core && lake build && cd -
for top in $(ls -d $ISLAND/lean/ZetaBands_h*/ | sort -t h -k2 -n); do
  ( cd "$top" && lake build ) || exit 1
  rm -rf "$top/.lake/build/ir"
done
# whole-ladder umbrella target (composes all blocks via require graph):
cd $ISLAND/lean && lake -f lakefile.umbrella.toml build
```

The umbrella `require`s every block (validated: `register-lakefile --sharded`
writes a 23-require `lakefile.umbrella.toml` at H=560000) and needs no `lean_lib`
of its own — the capstone chain composes across packages via `height_chain`.

## Where first_zero_kernel, BraggH100, and the reflection island fit

These are **separate, bounded islands** — they are NOT in the 22,800-module band
ladder and do not hit E2BIG. They stay as their own small CI jobs, unchanged by
B2, and each carries its own `AxiomGuard*` (`#print axioms` assertion):

| Artifact | Location | CI unit |
|---|---|---|
| `first_zero_kernel` (argument-free zeta zero in (14,15), 3-axiom clean) | `examples/zeta_reflection/lean/` (`ForgeFirstZeroKernel.lean`, `AxiomGuardFirstZeroKernel.lean`) | reflection-island job — small, independent lake package with its own lakefile |
| BraggH100 (kernel Bragg amplitude / completeness over the first 100 zeros) | `examples/zeta_zero_localization/lean/BraggH100.lean` (+ `BraggSupport`, `BraggAmplitudeInstances`, `BraggDefect`, `AxiomGuardBragg`) | belongs to the low block(s) (h≤100000) — built by the block that owns those bands; its `AxiomGuardBragg` runs as that block's extra guard step |
| Reflection island (sign-decomposition, theta-box, zero-hyp) | `examples/zeta_reflection/lean/` | its own bounded lake package; already `lake env`-able (small), so no B2 change needed |

So main CI has three parallel legs:
1. **Ladder** (this doc): block matrix + umbrella — the E2BIG fix.
2. **Reflection island**: unchanged small package, includes `first_zero_kernel`.
3. **Bragg**: rides the low block that owns the first-100-zeros bands, plus the
   standalone `AxiomGuardBragg`.

The three are independent build units; a change to one does not rebuild the
others.

## How #525's paper can cite a high in-tree capstone honestly

Today the paper is pinned at ~160000 because that is the highest capstone a single
E2BIG-free CI job could build. Under B2:

- The ladder CI builds every 25k block up to a chosen CI frontier `H_ci` and runs
  the axiom battery on each block's top capstone. Green CI = every
  `all_nontrivial_zeros_up_to_height_<top>_of_bands` compiles with axioms exactly
  `[propext, Classical.choice, Quot.sound]` and **0 `sorryAx`**.
- The paper can then cite `AllZeros_h<H_ci>` — the highest block-top whose CI job
  is green — as an **in-tree, CI-verified** capstone, instead of a number that CI
  could not reach. The citation is honest precisely because CI *builds* it every
  run (not a one-off local build).
- `H_ci` is a policy dial: set it to the highest block CI can build within the job
  time budget (see below). It can lag the live climb frontier `H` (the climb runs
  hotter than CI); the paper cites `H_ci`, the memory/state tracks `H`. Both are
  honest: "certified to H, CI-verified to H_ci."

`conjecture1_proved = False` must remain in the paper: the ladder localizes zeros
to the critical line up to a finite height; it does not prove RH.

## Wall-time and disk budget for CI

Pilot-measured, per block (~1000 modules):

- **Compile (cold):** the block's own ~1000 oleans compile fresh — the same CPU
  the monolith spent once. On the pilot machine a full 1075-module block (h400000)
  is the dominant cost; the deep capstone chain tail (last ~15 capstones) is
  sequential and slow. Ballpark: a cold block ≈ tens of minutes on one CI runner;
  parallel matrix divides total wall by node count.
- **Warm (cache hit):** near-instant Replay + only the changed band recompiles.
- **Disk:** ~480 MB oleans/block if IR is pruned (`rm -rf .lake/build/ir` — the
  single biggest lever; unpruned a block is ~7 GB of IR). Deps 7.6 GB shared once.
  Whole sharded island ≈ 16 GB with IR pruned, vs 117 GB monolith `.lake`.

**Recommended CI frontier for the first honest bump:** `H_ci = 200000`
(8 blocks). This clears the current 160000 pin with margin, keeps total cold CI
wall to ~8 block-builds (parallelisable), and every block-top capstone gets an
axiom-battery gate. Raise `H_ci` incrementally as CI budget allows; the layout
imposes no ceiling (H=560000 = 23 blocks already routes cleanly).

## Retiring the monolith in CI

1. Land the block matrix + reflection + Bragg jobs alongside the existing CI.
2. Once the matrix is green for ≥1 cycle, make it the required check.
3. Delete `lean/lakefile.toml` (the 2.9 MB monolith). Sources stay put
   (`srcDir=".."`); the umbrella + blocks are the source of truth. This removes
   the E2BIG file entirely and makes `lake env` work repo-wide.

## Landed 2026-09-17 (first honest bump)

- **`zeta-ladder-suite`** replaces the monolith `zeta-localization-suite` in
  `telperion-lean-e2e.yml`: shared deps dir wired by symlink (`.lake` is
  gitignored, so CI recreates the links), `lake exe cache get` once in `zzl_core`,
  then `zzl_core` + ZeroFreeBridge, then `zzl_aux`, then every `ZetaBands_h<top>`
  with `top <= H_CI` in ascending order (strict chain, single job, IR pruned after
  each block). Per block the guard is `#print axioms
  AllZeros_h<top>.all_nontrivial_zeros_up_to_height_<top>_of_bands`, compared
  whitespace-free against exactly `[propext, Classical.choice, Quot.sound]`.
- **`H_CI = 100000`** (4 blocks). Cold-build measurement on the M3 Ultra: block
  h25000 (736 modules) = 24 min wall, ~3.5 s CPU/module; a 4-core hosted runner
  should land a block in 15–25 min. Raise `H_CI` after the first green cycle.
- **`zzl_aux`** (new, emitted by `campaign.py emit_aux_pkg`, data-driven from the
  monolith lakefile): the 686 monolith targets that are neither core nor ladder —
  the height-100 island (671 `RHInBox_*`, `NoZerosInBox_*`, `AllZeros_h100/h200`,
  `StripClear`), the Bragg family + `CosEnclosure`, `DefectDictionary`,
  `R2Rigidity`, `RHLinalg`, `ZooDH`, `AxiomGuardDefect`. The sharded layout had no
  home for these; locally that was masked by the monolith's cached oleans and would
  have broken a cold CI build. Guards `AxiomGuardBragg/Defect/Zoo` run against it.
- `bragg-amplitude-compiles` builds in `zzl_aux`; the quasicrystal island dropped
  its unused path-require on the monolith (`selfinversive-rigidity-compiles` is
  now standalone).
- The monolith `lean/lakefile.toml` and `AxiomGuardRHInBox.lean` remain for the
  LOCAL climb until the between-legs cutover (`B2_CUTOVER_PLAN.md`); CI no longer
  touches them. Retiring them is step 3 above, after one green cycle.
- `conjecture1_proved = False` — unchanged by any of this.


## 2026-09-17 addendum: the legacy boxes leave the per-PR path

The first hosted-runner run of `zeta-ladder-suite` (PR #540) never reached the
ladder step: it spent 3 h 40 min (then was cancelled; projected ~5.3 h, past the
6 h timeout) in "Build zzl_aux", because `zzl_aux` had inherited all 671
pre-band `RHInBox_*` box certificates from the monolith `defaultTargets`
(~1.9 core-min each, measured locally: 40 min wall on 32 cores). Only two of them
are imported by anything (`AllZeros_h100` / `AllZeros_h200`).

`campaign.py` now splits them: `aux_modules` keeps the non-box modules plus the
boxes reachable from them (transitively), and `legacy_box_modules` collects the
rest into a new `zzl_legacy_boxes` package (same requires). The legacy package
is re-verified by `.github/workflows/telperion-legacy-boxes.yml` (weekly +
`workflow_dispatch`, 4-way sharded, per-shard axiom guard cut from
`AxiomGuardRHInBox.lean`). The ladder job is unchanged except that step 8 is
now minutes, so the per-block timing that drives the `H_CI` decision is finally
measurable.

## Addendum 2026-09-17 (late): first hosted-runner timings + the guard as a module

- First run that reached the ladder (#552): `ZetaBands_h25000` **1778 s** (736 modules),
  `ZetaBands_h50000` **3728 s** (856 modules — per-module cost grows with height as bands
  carry more zeros). Four blocks would overrun the 6 h job, so **`H_CI = 50000`** for now.
  The path to 200000 is the prior-block-cache / matrix shape (Stage 1 above), not one job.
- The `lake env lean <guard>` step failed at h50000 with `could not execute external
  process 'lean'` on the runner even though the block had just built (h25000's guard ran
  fine). Locally the same `lake env` has a 14-entry LEAN_PATH, so this is not path size and
  could not be reproduced. The guard is now a **generated module** `Guard_h<top>.lean`
  (`campaign.py emit_guard_module`, routed into every block whose top capstone exists and
  listed in the block's `defaultTargets`): `#guard_msgs (whitespace := lax) in #print axioms
  <capstone>` makes a bare `lake build` fail on any axiom set other than the three standard
  ones. Validated locally: builds in 22 s on the built h25000 block; a corrupted expectation
  fails the build. No `lake env` anywhere in the per-PR path.
- `conjecture1_proved = False`.
