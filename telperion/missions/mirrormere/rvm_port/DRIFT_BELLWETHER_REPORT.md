# Drift-Bellwether Report — v4.33-rc2 → v4.32 API drift

Measures the true Mathlib API-drift cost of porting the cc-chen-tech RvM development
(commit `6d07f7371ca2881de20481a638dc65e14d8f6651`, toolchain `v4.33.0-rc2`) DOWN to
our v4.32 pin (`leanprover/lean4:v4.32.0`, Mathlib rev `81a5d257c8e4`), before
committing weeks to the full 255-module grind. conjecture1_proved = False.

## Method
- CoW-cloned a v4.32 island's built Mathlib olean cache
  (`arda-main-test/.../zeta_zero_localization/lean/.lake`) into `/tmp/rvm-drift`
  (resource-aware: reused ~5000+ cached oleans, no cold Mathlib build).
- Compiled source modules with the v4.32 toolchain `lean` directly against that cache,
  errors + warnings captured. Raw logs in `drift_logs/`.

## STRUCTURAL FINDING (the load-bearing result)
The source's dependency graph is NOT the sub-directory tree — the top-level files
`HardyTheorem.lean`, `RiemannExplorer.lean`, `PrimeNumberTheorem.lean`,
`ZeroFreeRegion.lean`, `ZeroFreeRegion/MeromorphicAux.lean` are SELF-CONTAINED
MONOLITHS (each imports only `Mathlib` + a few sibling monoliths, NOT the hundreds of
`HardyTheorem/*` / `PrimeNumberTheorem/*` sub-modules). So:
- `PrimeNumberTheorem` bellwether closure = 3 files (HardyTheorem + RiemannExplorer + PrimeNumberTheorem), 12.4K LOC.
- `MeromorphicAux` bellwether closure = 5 files (the above + ZeroFreeRegion + MeromorphicAux), 44.4K LOC.
Both were fully buildable THIS RUN.

## BELLWETHER BUILD RESULTS — ALL GREEN, ZERO ERRORS on v4.32

| Module | LOC | Exit | Errors | Warnings | Deprecations | Build time |
|---|---:|:--:|:--:|:--:|:--:|--:|
| `HardyTheorem.lean` | 2,143 | 0 | **0** | 0 | 0 | ~a few s |
| `RiemannExplorer.lean` | 613 | 0 | **0** | 0 | 0 | fast |
| `PrimeNumberTheorem.lean` ★ | 9,672 | 0 | **0** | 2 | 0 | 16 s |
| `ZeroFreeRegion.lean` | 5,016 | 0 | **0** | 10 | 0 | 76 s |
| `ZeroFreeRegion/MeromorphicAux.lean` ★ | 26,930 | 0 | **0** | 13 | 4 | 38 s |
| **TOTAL** | **44,374** | | **0** | **25** | **4** | |

Plus: 20 true-leaf modules (import Mathlib ONLY, ~3.4K LOC, spanning MathlibAux /
PrimeNumberTheorem / HardyTheorem / ZeroFreeRegion sub-dirs) — ALL green, 0 errors.

### BONUS: distinct-count SUB-MODULE chain (directly bridge-relevant) — ALSO GREEN
To de-risk the extrapolation to the ~209 HardyTheorem Selberg sub-modules (which the
monoliths do NOT cover), I also built the actual distinct-count sub-module chain that our
bridge consumes:

| Sub-module | LOC | Exit | Errors | Deprecations |
|---|---:|:--:|:--:|:--:|
| `PrimeNumberTheorem/NontrivialZeroMultiplicity` (defines `nontrivialZerosFinset`) | 212 | 0 | **0** | 0 |
| `HardyTheorem/CriticalLineMultiplicity` (defines `criticalLineOddZerosFinset`, `mem_criticalLineZerosFinset`) | 264 | 0 | **0** | 0 |
| `HardyTheorem/ShortIntervalDistinctZeroCount` | 59 | 0 | **0** | 0 |

These are the EXACT definitions the green `RvMDistinctBridge.lean` hypotheses map onto
(`zerosFinset`, `oddCount`, `hZmem`, `hZcard`). They build zero-drift on v4.32 — so the
distinct-count SUB-module layer (not just the complex-analysis monoliths) is confirmed
drift-free, materially strengthening the GO recommendation.

Genuineness verified: real oleans produced (MeromorphicAux 13.4 MB, PrimeNumberTheorem
4.9 MB, ZeroFreeRegion 8.6 MB); ZERO `sorry` in either bellwether; NO error-suppression
`set_option`. These are honest kernel-accepted builds.

## DRIFT TAXONOMY (across ~44K LOC)
Only 4 DEPRECATION warnings and 21 style warnings — NO hard errors. The deprecations
are the ONLY genuine API-drift signal:

| Count | Source name (v4.33-rc2) | v4.32 preferred name | Kind |
|---:|---|---|---|
| 3 | `circleIntegrable_log_norm_meromorphicOn` | `MeromorphicOn.circleIntegrable_log_norm` | renamed lemma (alias present) |
| 1 | `AnalyticAt.comp_of_eq'` | `AnalyticAt.fun_comp_of_eq` | renamed lemma (alias present) |

Style warnings (cosmetic, NOT drift, NOT blocking): 12×"unused simp argument",
8×"`tac1 <;> tac2` where `(tac1; tac2)` suffices", 1×"change tactic does nothing".

### Drift DIRECTION (the surprise, and why it's favorable)
The drift points the "wrong" way for a down-port: the v4.32 Mathlib already contains the
NEWER names as first-class theorems AND keeps DEPRECATED ALIASES for the names the
source uses. i.e. the heavy complex-analysis API (`MeromorphicOn.circleIntegrable_log_norm`,
Jensen formula, meromorphic order/divisor, Phragmén–Lindelöf, Hadamard) landed in Mathlib
BEFORE v4.32; it was merely RENAMED around the v4.32→v4.33 boundary. So source code written
against v4.33-rc2 compiles against v4.32 unchanged — it just triggers deprecation warnings.

### STRUCTURAL-GAP CHECK — NONE FOUND
Every Mathlib theorem the drift-risk bellwethers depend on is PRESENT in v4.32:
`Analysis/Complex/JensenFormula.lean`, `Analysis/Complex/CanonicalDecomposition.lean`
(analyticOrderNatAt / MeromorphicOn.divisor), `Analysis/SpecialFunctions/Integrability/
LogMeromorphic.lean`, `Analysis/Complex/PhragmenLindelof.lean`, `Analysis/Complex/
Hadamard.lean`, `NumberTheory/LSeries/RiemannZeta.lean`. No back-porting of any Mathlib
theorem is required for the bellwethers. No structural wall detected.

## DRIFT RATE
- Hard-error drift: **0 fixes / 44,374 LOC = 0.00 fixes/KLOC.**
- Deprecation drift (optional to fix — warnings only): **4 / 44,374 LOC ≈ 0.09 fixes/KLOC**,
  each a mechanical 1-token rename with the fix name printed by the compiler.

## REFINED FULL-PORT ESTIMATE
Previous estimate: "weeks-scale, multi-run, dominated by MeromorphicAux."
Bellwether evidence REVISES this SHARPLY DOWNWARD:
- The two highest-risk, largest modules (44.4K LOC, incl. the 27K MeromorphicAux
  complex-analysis core) port with ZERO code changes — they already BUILD on v4.32.
- Extrapolating 0.00 hard-fixes/KLOC across the ~98K-LOC / 255-module superlinear-distinct
  closure: expect essentially NO mechanical rewrites, only (optional) deprecation-alias
  renames on the order of ~10 sites total.
- The remaining risk is NOT drift but MECHANICS: staging ~255 files at correct namespace
  paths and building them in topological order. Since the closure is dominated by a handful
  of self-contained monoliths (the sub-`HardyTheorem/*` etc. modules are only needed for the
  Selberg mollifier mainline, which is NOT in the monolith files — see caveat below),
  the file count in the ACTUAL Selberg closure must be re-derived against the monolith
  structure, not the earlier sub-module heuristic.

  IMPORTANT RE-CHECK NEEDED: the earlier 255-module count came from following
  `HardyTheorem/SelbergStrictCancellationZeroCover.lean` (a SUB-module, which DOES import
  many `HardyTheorem/*` siblings). The monoliths above do NOT cover the Selberg mollifier
  mainline. So the Selberg-path port genuinely needs the ~209 HardyTheorem sub-modules —
  those were NOT bellwether-tested here. HOWEVER: the bellwethers were deliberately the
  HARDEST (complex-analysis) modules; the Selberg sub-modules are real-analysis /
  Fourier–Mellin / mean-square estimates, a DIFFERENT and generally LESS drift-prone area
  of Mathlib. The 0-drift result on the complex-analysis core strongly predicts low drift
  on the Selberg modules too. PARTIALLY MEASURED (not pure extrapolation): the 3-module
  distinct-count sub-chain also built zero-drift on v4.32 (see BONUS table above). The
  remaining ~206 Selberg-mollifier sub-modules are still untested individually.

Refined estimate: **days, not weeks**, for the mechanical extraction+build of the full
Selberg closure, assuming the 0-drift trend holds on the HardyTheorem sub-modules. Budget
one focused run to stage + topo-build the ~209 Selberg sub-modules and confirm the trend;
if a sub-module shows real errors (not just deprecations), re-estimate then.

## GO / NO-GO RECOMMENDATION
**GO on the full grind.** The bellwether test has retired the single biggest risk (a
structural Mathlib gap in the complex-analysis core) and shown drift is ~zero. Recommended
next increment: stage the full `SelbergStrictCancellationZeroCover` closure at namespace
paths in the CoW v4.32 env and topo-build it; expect green with at most a handful of
deprecation-alias renames. Then wire `rvm_unbounded_mean_density_of_selberg`
(already green, this repo's `RvMDistinctBridge.lean`) to the ported
`selberg_odd_zero_proportion_target_proved_mainline` and retarget the `by sorry`.

## Reproduce
```
SRC=<v4.32 island with full Mathlib oleans>/lean   # e.g. arda-main-test/.../zeta_zero_localization/lean
cp -Rc "$SRC/.lake" /tmp/rvm-drift/.lake            # CoW, ~instant on APFS
# stage the 5 monolith files at their paths, then:
cd /tmp/rvm-drift
LEAN_PATH=<lake env LEAN_PATH> \
  ~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean <Module>.lean \
  -o .lake/build/lib/lean/<Module>.olean --root /tmp/rvm-drift
```
Raw logs: `drift_logs/_*.log`.
