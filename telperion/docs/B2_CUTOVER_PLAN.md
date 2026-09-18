# B2 CUTOVER PLAN — migrating the LIVE climb to the sharded lake layout

*(PROGRAM ANDÚRIL WS-B2. `conjecture1_proved = False` — this is finite
verification scaffolding for zero-localization certificates, NOT a proof of RH.)*

This document is the step-by-step procedure the main session runs at a
**between-legs boundary** to switch the live climb (`rh/million-turing`) from the
E2BIG monolith lakefile to the sharded per-block lake packages, WITHOUT
rebuilding Mathlib and WITHOUT recompiling the ~22,800 cached band/capstone
oleans.

It is the operational sibling of `B2_DEPLOY_RUNBOOK.md` (which records the
pilot). Read that first for the *why*; this doc is the *how* for the real climb.

## Preconditions (verify before starting)

1. The live climb is **quiescent** — no `emit-bands` / `campaign_shard.py
   shard-emit` / `assemble` running against `campaign_state.json`. Check:
   `pgrep -fa 'campaign.py|campaign_shard.py|emit-bands'` returns nothing.
   Sharding is a build-layer change; it must not race a band emit.
2. The last leg is fully certified: the top segment capstone `AllZeros_h<H>`
   exists as a flat `.lean` in `lean/` and its olean is in
   `lean/.lake/build/lib/lean/`. (Cutover preserves oleans; it does not create
   them.)
3. `lean/.lake/build/lib/lean` holds the current cached ladder oleans
   (~22,800 at H≈560000). Confirm: `find lean/.lake/build/lib/lean -name
   'AllZeros_h*.olean' | wc -l` ≈ number of 1000-segments.
4. `PATH=$HOME/.elan/bin:$PATH`; toolchain pinned to `v4.32.0`
   (`cat lean/lean-toolchain`).

## The blocker (FIXED — `register-lakefile --sharded` is now turnkey)

**Status: RESOLVED.** `b2_pilot_emit.py`'s disk-safe wiring has been folded into
`campaign.py`'s sharded emitter, so a single `register-lakefile --sharded` call
now emits production-ready, buildable block packages. What changed in
`campaign.py`:

- **`emit_block_lakefile(top, modules, prior_top=None)`** now emits
  `srcDir = ".."`, `[[require]] zzl_core (path ../zzl_core)`, and — when a prior
  block exists — `[[require]] ZetaBands_h<prior_top> (path ../ZetaBands_h<prior_top>)`.
  The lowest block (h25000) correctly gets NO prior require.
- **`emit_core_lakefile()` / `emit_core_pkg()`** (new) materialise the shared
  `zzl_core` package (16 core modules, `srcDir=".."`, mathlib + ZeroFreeBridge
  requires) with disk-safe wiring. `register_lakefile_sharded` emits it once per run.
- **`_pkg_wiring(pkg_dir, lean_dir, require_core, extra_path_deps)`** (ported from
  `b2_pilot_emit.py`) per package: copies + patches the monolith
  `lake-manifest.json` (rewrites the `ZeroFreeBridge` path relative to the
  package's depth), symlinks `<pkg>/.lake/packages → ../.lake/packages` (deps
  reused in place, zero re-clone), and drops a `lean-toolchain` (pins v4.32.0).
- **Full transitive prior-block closure in the manifest.** The lakefile declares
  only the IMMEDIATE prior require (lake resolves the rest via each prior's own
  lakefile), but the MANIFEST must carry EVERY lower block as a path dep —
  otherwise an isolated block build fails with
  `dependency 'ZetaBands_h<lower>' of 'ZetaBands_h<prior>' not in manifest`.
  `register_lakefile_sharded` writes the full closure (all lower blocks +
  zzl_core + ZFB) into each block's manifest via `extra_path_deps`.
- **Idempotent, non-clobbering.** `_block_is_well_wired()` checks `srcDir` +
  zzl_core require + prior-block require (when due) + `.lake/packages` symlink +
  manifest transitive closure. A correctly-wired block with no new modules is
  left byte-untouched; a stale (srcDir-less, or closure-outdated) block is
  re-emitted with the full module set. Verified: a second `register-lakefile
  --sharded` run rewrites ZERO files.

**Validation:** `register-lakefile --sharded --from 1 --to 560000 --segments`
now produces 23 block packages (736–1125 modules per 25k block) + a 23-require
umbrella, ALL with `srcDir` + full requires + disk-safe wiring; the previously
clobbered pilot h375000 is restored to a correctly-wired full block (1075
modules, prior require h350000); the pilot h400000 is preserved and re-wired with
the full closure; `zzl_core` and `ZetaBands_h400000` build green from the cached
oleans and `#print axioms` on the h400000 top capstone is the clean 3-axiom set
with 0 `sorryAx`. **No pre-cutover code change remains.**

Note: `b2_pilot_emit.py` is retained as the pilot record / reference; the
production path is now `campaign.py register-lakefile --sharded` alone.

## Topology note: transitive manifest closure vs `lake env` depth (validated)

The fixed emitter writes the FULL transitive prior-block closure into each
block's `lake-manifest.json` (every lower block as a path dep). This is REQUIRED
for an isolated block build (`cd lean/ZetaBands_h<top> && lake build`): without
it, lake aborts with `dependency 'ZetaBands_h<lower>' of 'ZetaBands_h<prior>' not
in manifest`. Validated: with the closure, `zzl_core` + the cross-block
`ZetaBands_h400000` (require → h375000, closure h25000..h375000) build green
(exit 0, 1075/1075 oleans); the manifest error is gone.

**However** — a deep block's `lake env` (used by `#print axioms` tooling)
constructs a workspace over its whole require closure, and at ~15 blocks deep
(h400000) `lake env <cmd>` fails ("could not execute external process"), whereas
at 1 block deep (h50000) it works cleanly (LEAN_PATH ~14 entries) and
`lake env lean` reports the h50000 top capstone's axioms as
`[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`, exercising the fixed
cross-block require edge (h50000 → h25000). **Implication for the cutover:**

- For BUILDS at any depth, the full-closure manifest is correct — use it.
- For `lake env` / `#print axioms` tooling on a DEEP block, prefer the
  **boundary-Replay** shape (the block requires only its immediate prior, whose
  `.lake/build/lib/lean` is symlinked at the monolith build lib), which keeps the
  env shallow. OR run the axiom battery via direct `lean` with a hand-composed
  LEAN_PATH against the block-package olean + the monolith chain cache (the
  established guard path), which does not go through `lake env`.

Both the emitter output and the guard tooling are therefore fine; just do not
rely on `lake env` for a 15+-deep block. This is a tooling-ergonomics caveat, not
a build correctness issue.

## One-time prerequisites (done once, reused by every leg thereafter)

These are NOT per-leg. Do them the first time you cut over, then never again
(unless deps change).

**P1. Build ZeroFreeBridge.** The island oleans do NOT include ZFB oleans, and
every capstone imports `DlvpZetaZeroFree` / `DlvpZetaRateEffective`.

```
cd telperion/examples/zero_free_bridge/lean
[ -e .lake/packages ] || ln -s ../../zeta_zero_localization/lean/.lake/packages .lake/packages
lake build            # 89 ZFB oleans, ~594 MB, deps cached, no mathlib rebuild
cd -
```

**P2. Emit + build `zzl_core`** (16 height-independent core modules).

```
cd telperion/examples/zeta_zero_localization
python3 campaign.py register-lakefile --sharded --from 1 --to <H> --segments  # emits zzl_core + all blocks + umbrella, disk-safe
cd lean/zzl_core && lake build && cd ../..   # 16 core oleans, ~113 MB, Replay deps
```

`zzl_core` is emitted with `srcDir=".."`, requires mathlib + ZeroFreeBridge, and
carries the copied manifest + `.lake/packages` symlink. Built once, REUSED by
every block (module identity preserved).

## Per-leg cutover — the between-legs procedure

Let `H` = the new frontier height after the leg, `TOP = ceil(H/25000)*25000` =
the current top block. Two cases:

### Case A — leg stays inside the current top block (the common case)

A 1000-height leg lands inside `ZetaBands_h<TOP>` until that block fills its 25
capstones. Only the top block is touched.

```
cd telperion/examples/zeta_zero_localization
# 1. Certify the leg as usual (unchanged): band emit + assemble.
python3 campaign_shard.py shard-emit --from <H-1000> --to <H> --jobs 8
python3 campaign_shard.py merge-shards            # -> campaign_state.json
python3 campaign.py assemble --from <H-1000> --to <H>   # writes AllZeros_h<H>.lean

# 2. Re-emit ONLY the top block package (adds the new bands + capstone to its
#    lakefile; idempotent — existing modules are skipped).
python3 campaign.py register-lakefile --sharded --from <H-1000> --to <H> --segments

# 3. Build ONLY the top block. Compiles just the NEW bands + new capstone;
#    everything below Replays.
cd lean/ZetaBands_h<TOP> && lake build && cd ../..

# 4. Prune IR for the block (disk lever; keep lib/):
rm -rf lean/ZetaBands_h<TOP>/.lake/build/ir
```

### Case B — leg crosses a 25k boundary (every 25 legs)

The leg's top capstone lands in a NEW block `ZetaBands_h<TOP>` (TOP = old top +
25000). Its lowest capstone `AllZeros_h<TOP-24000>` chains to the prior block's
top capstone `AllZeros_h<TOP-25000>`.

```
# 1. Certify the leg (unchanged): shard-emit / merge-shards / assemble as above.

# 2. Re-emit: register-lakefile --sharded CREATES ZetaBands_h<TOP>/ (with
#    srcDir + require zzl_core + require ZetaBands_h<TOP-25000>) and rewrites the
#    umbrella to require the new block.
python3 campaign.py register-lakefile --sharded --from <H-1000> --to <H> --segments

# 3. The prior block package (ZetaBands_h<TOP-25000>) must already be built green
#    from a previous leg — it is, since blocks fill in ascending order. Build the
#    new block; the cross-block chain edge resolves from the required prior block
#    (NO LEAN_PATH shim — lake derives it from the require graph).
cd lean/ZetaBands_h<TOP> && lake build && cd ../..
rm -rf lean/ZetaBands_h<TOP>/.lake/build/ir
```

## What happens to the two lakefiles

| File | During transition | Steady state |
|---|---|---|
| `lean/lakefile.toml` (the 2.9 MB monolith, 16k+ `[[lean_lib]]`) | **Left in place, unchanged.** It still works for a whole-island `lake build` (slow) but `lake env` remains E2BIG-broken. Keep it as the backward-compat default until the sharded layout is CI source of truth. | **Retired** — deleted after main CI is green on the sharded layout for ≥1 leg. Sources stay put (srcDir points at them); retirement removes one giant file, moves nothing. |
| `lean/lakefile.umbrella.toml` | Rewritten every leg by `register-lakefile --sharded` to `require` every block package that exists. Not built directly during the climb (blocks are built individually); it exists so main CI / a whole-ladder `lake -f lakefile.umbrella.toml build` can pull all blocks. | The CI source of truth. |

**Do NOT edit `lean/lakefile.toml` on `rh/million-turing` during cutover.** The
monolith stays byte-identical; sharding is purely additive (new sibling package
dirs + the umbrella).

## How assemble / build / guard / verify change per leg

| Phase | Monolith (before) | Sharded (after) |
|---|---|---|
| **band emit** | `campaign_shard.py shard-emit` → journal | unchanged |
| **assemble** | `campaign.py assemble` writes `AllZeros_h<H>.lean` (flat) | unchanged — capstones are still flat `.lean`; only the lakefile that *owns* them changes |
| **build** | (never done at scale — E2BIG) | `cd lean/ZetaBands_h<TOP> && lake build` — one bounded block, only new modules compile |
| **guard (#print axioms)** | direct `lean` + hand-built LEAN_PATH (monolith `lake env` is E2BIG-dead) | `lake env lean AxiomGuard*.lean` **works again** inside the block package (E2BIG cured); or unchanged direct-`lean` path |
| **verify** | ad hoc | `lake build` green + `#print axioms` on the top capstone = `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx` |

The band journal (C2) and lake sharding (B2) are independent axes: the journal
tracks "range **certified**"; the block package tracks "range **compiles**". A
leg updates both — append to the shard journal (unchanged), then re-emit + build
the top block (new).

## Preserving / reusing the 22,800 cached oleans (NOT rebuilt)

The cached oleans live in `lean/.lake/build/lib/lean/` under **bare module
names** (`AllZeros_h375000.olean`, `RHInBox…​olean`). Two independent reuse
mechanisms, neither of which recompiles them:

1. **Prior-chain reuse across blocks.** A block's cross-block edge (its lowest
   capstone → prior block's top capstone → … → h100) is served by the
   *required prior block package*, whose build lib already holds those oleans.
   For the FIRST cutover, the lower blocks have not been built as packages yet —
   so bootstrap them by symlinking each new block package's
   `.lake/build/lib/lean` at the monolith build lib for the Replay pass (exactly
   `b2_pilot_emit.py:emit_prior_boundary`), OR build blocks bottom-up once so
   each block's real build lib is populated. After the bootstrap, each block's
   own oleans are its own; steady-state legs only touch the top block.
2. **Within-block reuse.** When you re-emit + rebuild the top block for a new
   leg, lake `Replay`s the block's already-built bands/capstones and compiles
   only the leg's new modules (measured: only the new bands + new capstone
   recompile).

**The irreducible one-time cost** is that each block's ~1000 own oleans, which
currently live under the monolith build lib, get compiled once into that block's
own package build lib (they are not shared with any built package). This is the
SAME CPU the monolith already spent; it is parallelisable across blocks/nodes and
is a one-time full-migration cost, NOT a per-leg cost. Bootstrapping via the
`emit_prior_boundary` symlink (Replay, ~57 s/block, 0 recompile) avoids even
that for the historical blocks — recommended for the live cutover so the frontier
keeps moving while historical blocks are Replay-wrapped, not recompiled.

## Rollback plan

Sharding is **purely additive** to `rh/million-turing`: it creates
`lean/zzl_core/`, `lean/ZetaBands_h*/`, and `lean/lakefile.umbrella.toml`, and
touches NOTHING that the monolith build reads. Rollback is therefore trivial and
lossless:

1. **Stop** any in-flight block build (`pkill -f 'lake build'` in a block dir).
2. **Keep** using `lean/lakefile.toml` (the monolith) — it was never modified;
   the climb continues exactly as before on the monolith path.
3. **Optionally remove** the sharded artifacts (they are ignored by the monolith
   build; leaving them is harmless):
   `rm -rf lean/zzl_core lean/ZetaBands_h* lean/lakefile.umbrella.toml`.
   The flat `.lean` sources and `lean/.lake/build/lib/lean` oleans are untouched.
4. **No git rollback needed on `rh/million-turing`** if the block dirs were never
   committed there — do the sharding work on a branch (`b2/shard-migration`) and
   only merge once green. If they WERE committed and must be undone: `git rm -r`
   the sharded dirs; the monolith lakefile and sources are unaffected.

Because the monolith remains the byte-identical fallback throughout, a failed
cutover never blocks the climb: revert to the monolith path, keep emitting bands,
retry the sharded build offline.

## Order of operations for the FIRST live cutover (checklist)

1. [x] Fold `b2_pilot_emit.py` wiring into `campaign.py` — DONE (the emitter is
       now turnkey; see "The blocker (FIXED)" above).
2. [ ] Confirm climb quiescent; frontier leg certified.
3. [ ] P1: build ZeroFreeBridge (once).
4. [ ] `register-lakefile --sharded --from 1 --to <H> --segments` → emits
       zzl_core + all blocks + umbrella (srcDir + full requires + disk-safe
       wiring + transitive manifest closure).
5. [ ] Build `zzl_core` (once).
6. [ ] Bootstrap historical blocks: symlink each block's `.lake/build/lib/lean`
       at the monolith build lib (Replay, ~57 s/block, 0 recompile) OR build
       bottom-up on spare nodes (does not block the frontier).
7. [ ] Build the top block; `#print axioms` on `AllZeros_h<H>` = clean 3-axiom
       set, 0 `sorryAx`.
8. [ ] Prune each block's `.lake/build/ir`.
9. [ ] Thereafter: per-leg Case A/B above. Retire the monolith lakefile only
       after main CI is green on the umbrella for ≥1 leg.
