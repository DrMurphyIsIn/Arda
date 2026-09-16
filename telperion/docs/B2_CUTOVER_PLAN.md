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

## The single blocking gap (MUST fix before first cutover)

`campaign.py:register_lakefile_sharded` currently emits block lakefiles via
`emit_block_lakefile()` / `emit_umbrella_lakefile()`, which produce **incomplete**
packages:

- **no `srcDir = ".."`** → the package cannot find the flat `.lean` sources;
- **no prior-block `[[require]]`** → the cross-block chain edge does not resolve;
- **no disk-safe wiring** (`lake-manifest.json` copy, `.lake/packages` symlink,
  `ZeroFreeBridge` path rewrite, `lean-toolchain` drop) → each block would
  re-clone Mathlib (~7.7 GB/block, pilot-measured).

The disk-safe, buildable wiring lives ONLY in `b2_pilot_emit.py`
(`emit_core`, `emit_block`, `_pkg_wiring`, `emit_prior_boundary`). **Before the
first live cutover, fold `b2_pilot_emit.py`'s wiring into
`campaign.py:emit_block_lakefile` + a new `_pkg_wiring` step in
`register_lakefile_sharded`** so `register-lakefile --sharded` emits
production-ready packages in one call. Concretely `emit_block_lakefile` must add:

```
srcDir = ".."                                    # zero-move source layout
[[require]] name="zzl_core"    path="../zzl_core"
[[require]] name="ZetaBands_h<prior_top>" path="../ZetaBands_h<prior_top>"   # if prior block exists
```

and `register_lakefile_sharded` must, per package, copy+patch the monolith
`lake-manifest.json`, symlink `<pkg>/.lake/packages → ../.lake/packages`, and
drop a `lean-toolchain`. **Validation status:** running the CURRENT
`register-lakefile --sharded --from 1 --to 560000 --segments` produced 23 block
packages + a 23-require umbrella with correct module ROUTING (736–1125 modules
per 25k block, growing with height), but every emitted lakefile had `srcDir=0`
and no wiring — it also **clobbered the committed pilot h375000** (rewrote it
srcDir-less). So: the router is correct; the emitter is not yet disk-safe. Do not
run the live cutover until the fold-in lands and re-emits all blocks with
`srcDir` + wiring.

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
python3 b2_pilot_emit.py          # (or: campaign.py register-lakefile --sharded, once folded)
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

1. [ ] Fold `b2_pilot_emit.py` wiring into `campaign.py` (the blocking gap).
2. [ ] Confirm climb quiescent; frontier leg certified.
3. [ ] P1: build ZeroFreeBridge (once).
4. [ ] P2: emit + build `zzl_core` (once).
5. [ ] `register-lakefile --sharded --from 1 --to <H> --segments` → all blocks +
       umbrella (now with srcDir + wiring).
6. [ ] Bootstrap historical blocks via `emit_prior_boundary` symlink-Replay OR
       build bottom-up on spare nodes (does not block the frontier).
7. [ ] Build the top block; `#print axioms` on `AllZeros_h<H>` = clean 3-axiom
       set, 0 `sorryAx`.
8. [ ] Prune each block's `.lake/build/ir`.
9. [ ] Thereafter: per-leg Case A/B above. Retire the monolith lakefile only
       after main CI is green on the umbrella for ≥1 leg.
