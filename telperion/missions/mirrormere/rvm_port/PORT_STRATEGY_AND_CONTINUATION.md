# RvM Port — Strategy, Sizing, and Continuation Plan

Goal: discharge `rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates`
(currently `by sorry` in `Statements/MM_rvm_unbounded_mean_density.lean`) by porting
the unconditional superlinear zero-density result from
`github.com/cc-chen-tech/riemann-pnt-lean4` to our v4.32 pin, kernel-clean.

conjecture1_proved = False. This discharges ONE analytic residual, not RH.

## Provenance
- Source repo: `github.com/cc-chen-tech/riemann-pnt-lean4`
- Source commit: `6d07f7371ca2881de20481a638dc65e14d8f6651` (toolchain `v4.33.0-rc2`, Mathlib `v4.33-rc2` vendored at `./vendor/mathlib`)
- Source CI axiom allowlist: `{propext, Classical.choice, Quot.sound}` — matches our target exactly (`scripts/check_axiom_allowlist.py`).
- Target predicate identity CONFIRMED: source `RiemannHypothesis.IsNontrivialZero`
  (`RiemannExplorer.lean:64`, `abbrev IsNontrivialZero s := riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1`)
  is VERBATIM our `zetaOrdinates` predicate (`MMDefs.lean:54-55`). Same def also in
  vendored `Zeta23/Statement.lean:38`, but that is NOT on the import path (see sizing).

## Sizing (Task 1) — VERIFIED by transitive import-closure computation

Own-module (Mathlib-excluded) transitive closures of the candidate seeds:

| Seed theorem | Module | Own-module closure | ~LOC |
|---|---|---|---|
| `exists_eventually_riemannZeroCount_ge_selbergScale` (MULTIPLICITY RvM) | `PrimeNumberTheorem/RiemannVonMangoldt/SelbergScale.lean` | **50** | ~40K |
| `hardy_littlewood_positive_odd_lower_bound_target_proved` (DISTINCT, LINEAR) | `HardyTheorem/HardyLittlewoodLiteratureCount.lean` | **85** | ~55K |
| union of the two above | — | **118** | ~81.5K |
| `selberg_odd_zero_proportion_target_proved_mainline` (DISTINCT, SUPERLINEAR) ★ | `HardyTheorem/SelbergStrictCancellationZeroCover.lean` | **255** | ~98K |

Vendored `Zeta23/` (316 files) is NOT on any of these paths — the Selberg *mainline*
theorem is proved "through the Fourier–Mellin/square-root zeta mollifier mainline and
NOT through Zeta23" (source docstring). Confirmed by closure computation.

Verdict: this is a LARGE but BOUNDED PNT sub-development (hundreds of modules, ~100K LOC),
NOT "thousands / the whole PNT development". The single dominant module is
`ZeroFreeRegion.MeromorphicAux` (~27K LOC). The "weeks" estimate is realistic for the
255-module superlinear-distinct path; the 118-module path is smaller but insufficient (see below).

Closure module list saved verbatim in `closure_modules.txt`.

## The DISTINCT BRIDGE — the genuine subtlety (Task 4), RESOLVED

`riemannZeroCount T := Σ_{ρ:0<im≤T} analyticOrderNatAt riemannZeta ρ` is
MULTIPLICITY-weighted (`PrimeNumberTheorem/RiemannVonMangoldt/ZeroCount.lean:56`).
`RvMUnboundedMeanDensity` needs a window `[a,a+L]` with `> r·L+1` DISTINCT ordinates
for EVERY `r` — i.e. genuine superlinear DISTINCT growth (`N(T)/T → ∞`), matching the
honest caveat already written in our `BoundaryLemmas.lean:333-341`.

What the source has:
- (M+) `riemannZeroCount T ≥ c·(T/2π)·log T` — superlinear but MULTIPLICITY (SelbergScale).
- (D−) `criticalLineOddZeroCount T ≥ C·T` — DISTINCT but only LINEAR (Hardy odd count).
- (D+) `card(nontrivialZerosFinset T) ≤ C'·T·log T` — DISTINCT UPPER O(T log T) (`RiemannPNT.lean:23189`).

(M+) alone does NOT give distinct-superlinear: `distinct ≥ riemannZeroCount / maxOrder`,
and no `maxOrder = o(log T)` bound exists unconditionally. (D−) gives only BOUNDED density.
So the 118-module (SelbergScale + Hardy-linear) path CANNOT close the target.

★ THE KEY FIND: the source ALSO proves a superlinear DISTINCT lower bound:
`theorem selberg_odd_zero_proportion_target_proved_mainline` (`SelbergStrictCancellationZeroCover.lean:242`):
```
∃ c > 0, ∃ T0, ∀ T ≥ T0,  (criticalLineOddZeroCount T : ℝ) ≥ c·(T/(2π))·log T
```
`criticalLineOddZeroCount T = card(criticalLineOddZerosFinset T)` counts DISTINCT
odd-order critical-line zeros, each once. It is SORRY-FREE and CI-axiom-audited
(`Test.SelbergStrictCancellationZeroCoverContract` is in the source allowlist;
`Test/SelbergStrictCancellationZeroCoverContract.lean` runs `#print axioms`). This is
exactly the superlinear-DISTINCT handle the bridge needs.

Elements of `criticalLineOddZerosFinset T` satisfy (via `mem_criticalLineZerosFinset`,
`CriticalLineMultiplicity.lean:23`): `IsNontrivialZero ρ ∧ ρ.re = 1/2 ∧ 0 ≤ ρ.im ≤ T`,
so `ρ.im ∈ zetaOrdinates` and lies in the window `[0,T]`, and `ρ ↦ ρ.im` is injective
on the finset (all have `re = 1/2`).

## Strategy CHOSEN: (a) minimal-module extraction of the 255-module SUPERLINEAR-DISTINCT path

Rationale: the target genuinely requires superlinear DISTINCT growth (proved above),
which ONLY `selberg_odd_zero_proportion_target_proved_mainline` supplies. Re-proving the
Selberg sqrt-zeta-mollifier mainline from Mathlib primitives (option b) is a multi-month
research effort; extraction + v4.33→v4.32 API-drift repair is the tractable path.

Home island: the li_positivity island
(`telperion/examples/li_positivity/lean/`, toolchain v4.32.0) already hosts the
RvM* vocabulary (`RvMRHInBox.lean`, `RvMBraggBridge.lean`, etc.) and is the intended
cross-island discharge site per the `MM_rvm_unbounded_mean_density.lean` header. A
built v4.32 Mathlib olean cache for CoW-cloning exists at many islands, e.g.
`arda-main-test/telperion/examples/zeta_zero_localization/lean/.lake` (5000+ oleans),
`arda-li-ladder/.../zeta_zero_localization/lean/.lake`.

## What is GREEN NOW (this run)

`RvMDistinctBridge.lean` — the DISTINCT-BRIDGE reduction, BUILT GREEN on v4.32 and
axiom-clean:
```
#print axioms RvMGlue.rvm_unbounded_mean_density_of_selberg
  ⇒ [propext, Classical.choice, Quot.sound]   (0 sorryAx)
```
It proves, taking the ported Selberg interface as an explicit hypothesis:
```
rvm_unbounded_mean_density_of_selberg
  (zerosFinset : ℝ → Finset ℂ) (oddCount : ℝ → ℕ)
  (hZcard  : ∀ T, oddCount T = (zerosFinset T).card)
  (hZmem   : ∀ T, ∀ ρ ∈ zerosFinset T,
               riemannZeta ρ = 0 ∧ ρ.re = 1/2 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T)
  (hSelberg : ∃ c>0, ∃ T0, ∀ T≥T0, (oddCount T:ℝ) ≥ c·(T/(2π))·log T)
  : RvMUnboundedMeanDensity zetaOrdinates
```
So the ENTIRE remaining task is discharging `zerosFinset`, `oddCount`, `hZcard`,
`hZmem`, `hSelberg` — which are EXACTLY `criticalLineOddZerosFinset`,
`criticalLineOddZeroCount`, `criticalLineOddZeroCount_def`,
`mem_criticalLineZerosFinset`+filter, and `selberg_odd_zero_proportion_target_proved_mainline`.
The mathematical bridge is DONE; what remains is the mechanical port of the source
modules that PROVE `hSelberg`.

Build recipe for the bridge (reproducible):
```
SRC=<any v4.32 island with full Mathlib oleans>/lean
cp -Rc "$SRC/.lake" /tmp/rvm-glue-build/.lake
# minimal lakefile.toml requiring only mathlib @ v4.32.0; drop non-mathlib path-requires from lake-manifest.json
cd /tmp/rvm-glue-build && lake build RvMGlue    # ~30s cold, 9s warm
```

## REMAINING WORK (precise, resumable)

1. **Extract the 255-module closure** of `SelbergStrictCancellationZeroCover` from
   source @ `6d07f737…` into the li_positivity island (or a new v4.32 sub-island
   `telperion/examples/rvm_density/lean/`). Use `closure_modules.txt` (that file lists
   the 118-union path; regenerate the 255 list with
   `python3 closure.py HardyTheorem.SelbergStrictCancellationZeroCover` against a fresh
   source clone — script preserved in this run's shell history / reconstruct from the doc).
2. **v4.33 → v4.32 API-drift repair.** One minor Mathlib version of drift across ~100K LOC.
   Expect: renamed lemmas, `Finset`/`MeasureTheory` API shifts, `positivity`/`gcongr`
   extension changes, occasional `simp` normal-form churn. Port bottom-up (the closure is
   a DAG; `ZeroFreeRegion.MeromorphicAux` (27K LOC) and `PrimeNumberTheorem` (9.7K LOC)
   are the roots — do these first). Keep each ported file's source module + commit cited
   in a header comment (zero-drift provenance discipline).
3. **Wire the bridge.** Instantiate `rvm_unbounded_mean_density_of_selberg` with the
   ported `criticalLineOddZerosFinset` / `criticalLineOddZeroCount` /
   `selberg_odd_zero_proportion_target_proved_mainline`. `hZmem` = `mem_criticalLineZerosFinset`
   composed with the odd-filter membership; `hZcard` = `criticalLineOddZeroCount` def unfold.
4. **Retarget** `Statements/MM_rvm_unbounded_mean_density.lean`: replace `by sorry` with the
   wired proof, `import`ing the ported island lib (cross-island per design §2).
5. **Axiom audit**: `#print axioms rvm_unbounded_mean_density` must be
   `[propext, Classical.choice, Quot.sound]`, 0 sorryAx. Add a guard file mirroring the
   source's `SelbergStrictCancellationZeroCoverContract`.

## Effort estimate (honest)
- Bridge glue: DONE (this run).
- 255-module extraction + v4.32 drift repair: the real cost. Weeks-scale, dominated by
  `MeromorphicAux` (27K) + the ~209 HardyTheorem Selberg-mollifier modules. Multi-run.
- Risk: if any source module depends on a v4.33-only Mathlib lemma with no v4.32 analogue,
  that lemma must itself be back-ported or re-proved. Probe `MeromorphicAux` + `PhragmenLindelofZeta`
  + `OscillatoryIntegral` FIRST as the drift-risk bellwethers before committing to the full extraction.

## Files in this dir
- `RvMDistinctBridge.lean` — the green, axiom-clean bridge (this run's deliverable).
- `closure_modules.txt` — 118-union import closure (provenance).
- `PORT_STRATEGY_AND_CONTINUATION.md` — this file.
