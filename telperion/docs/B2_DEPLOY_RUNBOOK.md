# B2 DEPLOY RUNBOOK — lake package sharding, pilot-proven

*(PROGRAM ANDÚRIL WS-B2. `conjecture1_proved = False` — finite verification
scaffolding, not a proof of RH.)*

This runbook records the B2 sharding pilot: the FIRST real build of the sharded
lake layout (`RUNNER_SHARD_DESIGN.md` §B2), which until now was only
golden-text validated. The pilot materialised `zzl_core` + one 25k-height block
(`ZetaBands_h400000`, the (375000,400000] range) as real lake packages and built
them green against the existing monolith `.lake`, without a Mathlib rebuild.

The headline operational result: **`lake env` works again inside a block
package** (the monolith's `lake env` is broken by E2BIG — the 16k-module
`LEAN_PATH`/argv overflows `execvp`). Sharding is therefore not just a build-time
scaling fix; it restores the day-to-day `lake env lean` / editor tooling that the
monolith has lost.

## Layout decision (made and documented)

**`srcDir = ".."` — no file moves, no source symlinks.** Each package's
`lakefile.toml` lives in its own subdirectory of the island
(`lean/zzl_core/`, `lean/ZetaBands_h400000/`) but sets `srcDir = ".."` so it reads
the FLAT `.lean` files IN PLACE from the island root. Module identity is
preserved exactly (`import RHInBox`, `import AllZeros_h400000`, … all still
resolve), so nothing in the 16k existing files changes and the monolith still
builds untouched. The alternative (physically moving ~30 core files) was
rejected: it is more invasive, breaks the monolith unless its lakefile is
simultaneously rewritten, and buys nothing over `srcDir`.

Proven behaviour (pilot):
- A package with a lakefile in `pkg/` and `srcDir = ".."` compiles a parent-dir
  `.lean` into `pkg/.lake/build/lib/lean/<Module>.olean` with the bare module
  name — verified on a scratch probe and then on all 16 core + 1075 block modules.
- Explicit `[[lean_lib]]` stanzas (one per module, exactly as
  `campaign.py:emit_block_lakefile` already emits) confine each package to its
  own modules even though `srcDir` points at a directory holding 16k `.lean`
  files. No accidental sibling pickup.

## Disk-safe dependency wiring (the "no Mathlib rebuild" rule)

A NEW package with `require mathlib { scope, rev }` will, by default, **re-clone
mathlib and its whole transitive dep set** into its own `.lake/packages` and run
`lake exe cache get` — measured at **7.7 GB** per package on the pilot machine
(mathlib repo + olean cache), even though it does NOT recompile mathlib from
source. Multiply by 25+ block packages and the disk budget is gone.

The cure, applied by `b2_pilot_emit.py:_pkg_wiring` and proven to add ~0 dep
disk:

1. **Copy the monolith's `lake-manifest.json`** into the package so every dep
   rev/url matches exactly (mathlib pinned rev `81a5d257…` = `v4.32.0`, plus
   batteries/aesop/Qq/proofwidgets/Cli/importGraph/plausible/LeanSearchClient).
2. **Symlink `<pkg>/.lake/packages` → the monolith's `.lake/packages`.** Lake
   then finds every dep already checked out AND already built in place; it clones
   nothing and rebuilds nothing.
3. **Rewrite the `ZeroFreeBridge` path dep** in the copied manifest (and the
   lakefile `require`) to be correct relative to the package's OWN depth. The
   monolith's manifest records `../../zero_free_bridge/lean` (relative to
   `lean/`); from `lean/zzl_core/` or `lean/ZetaBands_h400000/` the correct path
   is `../../../zero_free_bridge/lean`. Getting this wrong is the one failure the
   pilot hit ("package directory not found") — fixed by `os.path.relpath`.
4. **Add `zzl_core` to the block package's manifest** as a path dep
   (`../zzl_core`). It is a NEW sibling package the monolith manifest doesn't
   know about; without this, `lake build` aborts with "dependency 'zzl_core' not
   in manifest".
5. **Drop a `lean-toolchain` file** (copied from the island) in every package so
   elan pins Lean `v4.32.0` — the ambient `lake` on PATH may be a newer toolchain
   (5.0.0 / Lean 4.34.0 on the pilot machine); the file forces the correct one.

Net effect (measured): mathlib and all toolchain deps are reused IN PLACE with
zero re-clone and zero recompile.

## ZeroFreeBridge must be built first

The CoW-cloned island `.lake` contained all 16k island oleans but **no
ZeroFreeBridge oleans** (ZFB is a path dep whose build output was not part of the
clone). Core modules `ZetaZeroConfinement` and `AllZerosUpToHeight` (and every
capstone) `import DlvpZetaZeroFree` / `DlvpZetaRateEffective`, so ZFB must be
built before any shard. Build it once, reusing the same wiring (symlink its
`.lake/packages` at the monolith's):

```
cd telperion/examples/zero_free_bridge/lean
ln -s <island>/.lake/packages .lake/packages      # reuse deps in place
lake build                                          # 89 oleans; deps cached
```

Pilot cost: `lake build` (the `ZeroFreeBridge` lib + all 89 Dlvp/zero-free
lean_libs) = 8832 jobs, wall ~a few minutes, **594 MB** local oleans, no mathlib
rebuild.

## The cross-block chain edge

The capstone chain composes across blocks: `AllZeros_h376000` (first capstone of
block h400000) `import AllZeros_h375000` — the TOP capstone of the PRIOR block
(h375000). In the full sharded layout the umbrella `require`s every block
package, so this resolves as an ordinary cross-package import from
`ZetaBands_h375000`. Each capstone also chains to its own predecessor
(`AllZeros_h375000 → h374000 → … → h100`), so a block package's lowest capstone
depends, transitively, on the entire prior chain.

**Two facts make this the trickiest part of the migration:**

1. **The chain edge is transitive, not a single olean.** When Lean loads
   `AllZeros_h375000.olean` it needs the ENTIRE import closure's oleans present
   (h375000 → h374000 → … → h100 + every band each imports), even though it
   recompiles none of them. Staging just the one boundary olean fails: the build
   error simply moves down one link (`unknown module prefix 'AllZeros_h374000'`,
   then h373000, …).
2. **lake does NOT honor a pre-set `LEAN_PATH`.** It derives `LEAN_PATH` from the
   require graph and overrides the environment (confirmed from the build trace —
   a `LEAN_PATH=…` exported before `lake build` never reaches the per-module
   `lean` invocation). So the prior chain MUST come from a package that is on the
   require graph.

**Do NOT try to rebuild the prior chain inside a boundary package** — it pulls in
the whole monolith. Resolve it via a REQUIRED prior-block package instead:

- **Production:** the umbrella provides `ZetaBands_h375000` (and all lower
  blocks); the block's `require ZetaBands_h375000` puts that package's build lib
  on lake's `LEAN_PATH`, and the whole prior chain resolves package-to-package.
  This is the design's intent.
- **Pilot:** we synthesise the prior block package. `emit_prior_boundary(400000)`
  creates `ZetaBands_h375000/` whose `.lake/build/lib/lean` is a SYMLINK to the
  monolith build lib (which already holds `AllZeros_h100..h375000` + all their
  bands). `lake build` in that package `Replay`s those oleans (reuses, never
  recompiles — measured 57 s, 8721 jobs, zero recompilation) and declares
  `AllZeros_h375000` as its lean_lib. The pilot block then `require`s
  `ZetaBands_h375000` exactly as it would `require` the real prior block in
  production, so the block build needs no `LEAN_PATH` shim at all.

## Pilot build procedure (reproducible)

```
export PATH=$HOME/.elan/bin:$PATH
cd telperion/examples/zeta_zero_localization

# 0. ZeroFreeBridge (once) — see above.

# 1. Emit zzl_core + ZetaBands_h375000 (prior boundary) + ZetaBands_h400000.
python3 b2_pilot_emit.py

# 2. Build the shared core (16 modules).
cd lean/zzl_core && lake build && cd ../..

# 3. Build the prior boundary package (all Replay from the monolith build lib).
cd lean/ZetaBands_h375000 && lake build && cd ../..

# 4. Build the block (1075 modules); the cross-block chain resolves via the
#    required ZetaBands_h375000 package — no LEAN_PATH shim.
cd lean/ZetaBands_h400000 && lake build
```

### Measured pilot results

| Package | Modules | Jobs | Local olean disk | Recompiled | Reused |
|---|---|---:|---:|---|---|
| ZeroFreeBridge | 89 libs | 8832 | 594 MB | 89 ZFB oleans | mathlib + all deps |
| zzl_core | 16 | 8753 | 113 MB | 16 core oleans | mathlib + deps + ZFB |
| ZetaBands_h375000 (prior boundary) | 1 declared | 8721 | 0 (build lib symlinked to monolith) | none (all `Replay`) | the entire prior chain h100..h375000 |
| ZetaBands_h400000 | 1075 (1050 bands + 25 capstones) | 10889 | 7.2 GB | 1075 block oleans | mathlib + deps + ZFB + zzl_core + prior chain |

All three shard packages built **green** (`Build completed successfully`), 25/25
capstones present, 1075/1075 block oleans. Total NEW pilot disk (build outputs,
deps counted once via symlink): ~594 MB (ZFB) + 113 MB (zzl_core) + 7.2 GB (block)
≈ **7.9 GB** — well under the 10 GB budget; no Mathlib rebuild, no dep re-clone.

**Battery on the sharded layout — PASS, both ways.** The h400000 capstone's main
theorem `AllZeros_h400000.all_nontrivial_zeros_up_to_height_400000_of_bands`
reports axioms `[propext, Classical.choice, Quot.sound]` — the clean Lean set,
**no `sorryAx`** — via BOTH:
- `lake env lean BatteryH400000.lean` run INSIDE `ZetaBands_h400000/`, and
- direct `lean` with `LEAN_PATH` composed from the new package build libs
  (block + prior-boundary + zzl_core + ZFB + the symlinked deps), using the pinned
  v4.32.0 toolchain binary.

**E2BIG cure — CONFIRMED.** `lake env lean` runs cleanly in the block package,
whereas the SAME command in the monolith fails with `could not execute external
process 'lean'` (the 16k-module argv/env overflows `execvp`). Sharding restores
`lake env` (and therefore editor / `#print axioms` tooling) at the block level.

- **What recompiled:** only each package's OWN modules. The 16 core oleans are
  built once in zzl_core and REUSED by the block (not rebuilt) because module
  identity is preserved and zzl_core is a proper `require`. mathlib / batteries /
  aesop / … never recompiled (reused from the symlinked packages dir). The
  monolith's 16k oleans were reused only for the single cross-block capstone
  `AllZeros_h375000`; the block's own 1075 modules were compiled fresh (they are
  not shared with any built package — this is the irreducible cost of sharding,
  identical to what the monolith paid to build them the first time).
- **`lake env` restored:** in `zzl_core/` and `ZetaBands_h400000/`,
  `lake env sh -c 'echo OK'` succeeds and `LEAN_PATH` has ~12 entries. In the
  monolith, `lake env <anything>` fails with "could not execute external process"
  (E2BIG from the 16k-entry env). **This is the E2BIG cure, demonstrated.**

## Full-migration plan (all blocks + monolith retirement)

The island currently spans heights up to the live climb frontier. Each 25k-height
block is one package; at frontier H there are `ceil(H / 25000)` block packages
plus `zzl_core` plus the umbrella.

**Steps:**

1. **Build ZeroFreeBridge once** (shared by all blocks). One-time ~594 MB.
2. **Build zzl_core once** (16 modules). One-time ~113 MB.
3. **Emit all block packages** via `campaign.py register-lakefile --sharded
   --t-from 0 --t-to H --segments` (the production codegen this pilot mirrors),
   extended with the disk-safe manifest/symlink wiring proven here. This creates
   one `ZetaBands_h<top>/` per 25k block + the umbrella.
4. **Build blocks in ascending height order.** Because each block's lowest
   capstone chains to the prior block's top capstone, build block N only after
   block N-1, so the cross-package import resolves from the already-built
   sibling (no `LEAN_PATH_EXTRA` shim needed once all blocks exist — the umbrella
   `require` graph supplies it). Blocks at DIFFERENT heights are otherwise
   independent and can be farmed to separate nodes (charter: height-sharded
   multi-node), each node building a contiguous run of blocks.

**Disk requirement (full migration) — measured breakdown.** The monolith `.lake`
is **117 GB**, but that splits very unevenly:

| Component | Size | Notes |
|---|---:|---|
| `.lake/build/lib` (island **oleans**) | 7.5 GB | the load-bearing artifacts |
| `.lake/packages` (mathlib + deps) | 7.6 GB | shared ONCE via symlink, not per-block |
| `.lake/build/ir` (C intermediates, traces) | **102 GB** | needed only for native codegen, NOT for olean reuse or `#print axioms` |

So the irreducible sharded footprint is ~7.5 GB of island oleans (redistributed
across the block packages) + 7.6 GB deps (counted once) + ~0.7 GB shared shard
core (ZFB + zzl_core) ≈ **~16 GB** — provided `.lake/build/ir` is pruned after
each block builds (it is regenerable and not needed to reuse oleans or run the
axiom battery). The pilot block h400000 measured **480 MB oleans + 6.7 GB IR**;
pruning IR drops the per-block cost by ~14×. At the current H=400000 frontier
there are `ceil(400000/25000) = 16` blocks.

The dep packages are shared by symlink and counted ONCE, not per block — a strict
improvement over N independent full checkouts. **Recommendation: prune
`<block>/.lake/build/ir` after each block goes green** (keep `lib`); this is the
single biggest disk lever for the full migration and brings the whole sharded
island under ~16 GB vs the monolith's 117 GB.

**Wall time (full migration).** Dominated by compiling the island oleans once —
the same total CPU the monolith already spent (41k jobs). Sharding does not add
compile work; it adds the ability to parallelise across nodes and to rebuild only
the touched block on a change. Pilot: zzl_core ~seconds of NEW compile (deps
cached), block h400000 = `<measured>` wall for 1075 modules on the pilot machine.
A from-scratch full migration is therefore ≈ the monolith's original build time,
divisible by node count.

**Monolith retirement / cutover.**

1. Keep the monolith lakefile as the default (backward-compat, per design) until
   all blocks build green and the umbrella `lake build` (or per-block CI matrix)
   is green end to end.
2. Cut CI over to the umbrella / per-block matrix: each block is an independent
   build unit, so CI parallelises and a single band change rebuilds only its
   block, not the 16k-target monolith.
3. Retire the monolith `lakefile.toml` (16459 `[[lean_lib]]` stanzas, 843 KB
   `defaultTargets` line) only after the sharded layout is the CI source of
   truth. The flat `.lean` files stay exactly where they are (srcDir points at
   them); retirement is deleting one giant lakefile, not moving sources.

**Cutover procedure between legs (the live climb).** The live climb extends the
frontier one leg (~1000-height segment) at a time. Under sharding:

- A new leg lands entirely within the current top block until the block fills
  (25 capstones). While filling, only the top block package is re-emitted and
  rebuilt (`register-lakefile --sharded` adds the new modules to that block's
  lakefile; `lake build` in that block compiles only the new bands/capstone).
- When a leg crosses a 25k boundary, `register-lakefile --sharded` creates the
  next `ZetaBands_h<top>/` package and adds it to the umbrella. The new block's
  first capstone chains to the (now-complete) prior block's top capstone —
  resolved by the umbrella `require`, no shim.
- The band journal (C2) and the lake sharding (B2) are independent: the journal
  tracks "range certified"; the block package tracks "range compiles". A leg's
  cutover updates both — append to the shard journal, re-emit + build the top
  block package.

## Files

- `telperion/examples/zeta_zero_localization/b2_pilot_emit.py` — pilot emitter
  (srcDir + disk-safe wiring). Mirrors `campaign.py:emit_block_lakefile` and adds
  the manifest-copy / packages-symlink / cross-block LEAN_PATH wiring.
- `telperion/examples/zeta_zero_localization/lean/zzl_core/` — shared core package.
- `telperion/examples/zeta_zero_localization/lean/ZetaBands_h400000/` — pilot block.
- `telperion/examples/zeta_zero_localization/campaign.py` — production sharding
  codegen (`register_lakefile_sharded`, `emit_block_lakefile`,
  `emit_umbrella_lakefile`); the disk-safe wiring above should be folded into it
  for the full migration.
