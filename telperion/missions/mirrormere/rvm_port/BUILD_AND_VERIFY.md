# Build & Independent Verification — RvMUnboundedMeanDensity discharge

The node `Statements/MM_rvm_unbounded_mean_density.lean` is now sorry-free: its body is
the proof term `RvMGlue.rvm_unbounded_mean_density` (no `by sorry`).  This doc gives the
EXACT commands to independently re-run `#print axioms` and confirm the discharge is
kernel-clean.  conjecture1_proved = False — this discharges ONE analytic residual toward
the corridor bound → E8, NOT RH.

## Left-in-place oleans (this run did NOT clean lib/)

A complete v4.32 olean set for the discharge chain is left at:

    /tmp/rvm-verify/.lake/build/lib/lean/          (the port + node oleans, 260 files, ~122M)
    /tmp/rvm-verify/.lake/packages/mathlib/.lake/build/lib/lean/   (v4.32 Mathlib, dependency)

Key oleans present (spot-check):
- `Statements/MM_rvm_unbounded_mean_density.olean`   ← the sorry-free node
- `Statements/MMDefs.olean`                           ← the registry vocabulary (defines Quasicrystal.RvMUnboundedMeanDensity / zetaOrdinates)
- `RvMDischarge.olean`, `RvMDistinctBridge.olean`     ← the wiring + bridge
- `HardyTheorem/SelbergStrictCancellationZeroCover.olean`  ← the ported superlinear-distinct mainline
- all 255 ported closure modules under `HardyTheorem/`, `PrimeNumberTheorem.olean`, `ZeroFreeRegion/`, `MathlibAux/`, `RiemannExplorer.olean`

If `/tmp` was cleared, rebuild from the committed sources (see "Rebuild" below).

## Toolchain
- `leanprover/lean4:v4.32.0`
- lean binary: `/Users/peterwmurphy/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`
- Mathlib rev `81a5d257c8e4` (the v4.32.0 tag), as in `/tmp/rvm-verify/.lake/packages/mathlib`.

## THE VERIFICATION COMMAND (reproduce `#print axioms`)

`AxCheck.lean` (already at `/tmp/rvm-verify/AxCheck.lean`, also copied to this dir):
```lean
import Statements.MM_rvm_unbounded_mean_density
import HardyTheorem.SelbergStrictCancellationZeroCover
#print axioms rvm_unbounded_mean_density
#print axioms HardyTheorem.selberg_odd_zero_proportion_target_proved_mainline
```

Run it with a hand-built LEAN_PATH (avoids `lake env` E2BIG):
```bash
export PATH=$HOME/.elan/bin:$PATH
LEANBIN=/Users/peterwmurphy/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
V=/tmp/rvm-verify
LP="$V/.lake/packages/Cli/.lake/build/lib/lean:$V/.lake/packages/batteries/.lake/build/lib/lean:$V/.lake/packages/Qq/.lake/build/lib/lean:$V/.lake/packages/aesop/.lake/build/lib/lean:$V/.lake/packages/proofwidgets/.lake/build/lib/lean:$V/.lake/packages/importGraph/.lake/build/lib/lean:$V/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$V/.lake/packages/plausible/.lake/build/lib/lean:$V/.lake/packages/mathlib/.lake/build/lib/lean:$V/.lake/build/lib/lean"
cd $V
LEAN_PATH="$LP" "$LEANBIN" AxCheck.lean --root $V
```

Expected output (VERIFIED this run):
```
'rvm_unbounded_mean_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'HardyTheorem.selberg_odd_zero_proportion_target_proved_mainline' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Both 3-axiom clean, 0 sorryAx.

Note: `rvm_unbounded_mean_density` here is the node theorem from
`Statements/MM_rvm_unbounded_mean_density.lean`, which `import Statements.MMDefs;
open Quasicrystal` — so its statement is literally `Quasicrystal.RvMUnboundedMeanDensity
Quasicrystal.zetaOrdinates`, the registry node.  (MMDefs also contains an UNRELATED
`by sorry` in `RHInBoxAnalytic.divisor_ball_support_finite_of_one_notMem`, pre-existing
vocabulary scaffolding; the node's proof term does not touch it, so it does not appear in
the node's axiom set — as the clean `#print axioms` above confirms.)

## Rebuild from committed sources (if the /tmp oleans are gone)

Committed sources live under `rvm_port/`:
- `RvMDistinctBridge.lean`, `RvMDischarge.lean` — bridge + wiring.
- `ported_shim_files/` — the 3 modules carrying port shims (SelbergPerronKernel,
  SelbergJForwardBridge, SelbergNonconstantFourierMass).
- `selberg_closure_topo_order.txt` — the 255-module build order.
- The other 252 closure modules are BYTE-IDENTICAL to source
  github.com/cc-chen-tech/riemann-pnt-lean4 @ `6d07f7371ca2881de20481a638dc65e14d8f6651`
  (clone that commit; overlay the 3 shim files).
- The node + MMDefs live in `../lean/Statements/`.

Rebuild recipe:
```bash
SRC=<any v4.32 island with full Mathlib oleans>/lean   # for the CoW Mathlib cache
V=/tmp/rvm-verify
cp -Rc "$SRC/.lake" $V/.lake
# stage the 255 source modules (from the cc-chen-tech clone @ 6d07f7371) at their paths under $V,
# overlay ported_shim_files/, copy RvMDistinctBridge.lean + RvMDischarge.lean + Statements/*,
# then compile in topo order (selberg_closure_topo_order.txt) with the LEANBIN above,
# `-o .lake/build/lib/lean/<Mod>.olean --root $V`, pruning .lake/build/ir between batches.
# Finally build Statements/MMDefs.lean, Statements/MM_rvm_unbounded_mean_density.lean, then AxCheck.lean.
```

## lake wiring (committed, for a native `lake build`)
`../lean/lakefile.toml` now declares a second lib `RvMPort` (srcDir `RvMPortSrc/`,
globbing the closure) alongside `Statements`.  `RvMPortSrc/` contains the full ported
tree (255 modules + shims + bridge + discharge).  `lake env` accepts the config; a full
`lake build` rebuilds Mathlib under lake's own trace graph (hours) — for verification the
direct-lean path above is faster and is what was used to produce the axiom results.

## Drift recap (from the full port)
3 patch sites / 4 proof-carrying shim lemmas across 98K LOC (~0.04 patches/KLOC), no
axiom drift, no structural Mathlib gap.  Details in `PATCHLOG.txt` and
`FULL_PORT_COMPLETION_REPORT.md`.
