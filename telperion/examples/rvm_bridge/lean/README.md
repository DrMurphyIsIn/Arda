# rvm_bridge/lean — the E6 bridge island (Lean v4.33.0-rc2)

A self-contained Lean 4 project that discharges two registry nodes from an external,
independently machine-checked formalization: Anthropic's **zeta-23-lean** (Alpöge–Furman,
*More than two thirds of the zeta zeros are simple and on the critical line*,
arXiv:2608.13637). It is the outcome of the routes-roadmap **E6 probe** (2026-09-17,
`telperion/docs/E6_PROBE_2026-09-17.md`) and its follow-up
(`telperion/docs/RVM_CUMULATIVE_BRIDGE_2026-09-17.md`):

1. the MIRRORMERE residual `MM_rvm_unbounded_mean_density` (`E6Bridge.lean`), and
2. the RH critical-path node `RH_rvm_unconditional` — the **cumulative** Riemann–von Mangoldt
   formula `N(T) = (T/2π) log(T/2π) − T/2π + 7/8 + O(log T)` for all `T ≥ 2`, no hypotheses
   (`E6Bridge2.lean`). zeta-23-lean states only the dyadic clause; the cumulative `O(log T)`
   form is re-assembled here from its general-window internals (see below).

**No RH progress is claimed.** Both discharged statements are classical (Selberg-type density
and the von Mangoldt / Backlund zero count, Titchmarsh 9.4). `conjecture1_proved = False`.

| file | role |
|---|---|
| `lean-toolchain`, `lakefile.toml` | Lean `v4.33.0-rc2`; `Zeta23` pinned to `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (`subDir = zeta23`), which transitively pins Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` (tag `v4.33.0-rc2`) |
| `E6Bridge.lean` | the first bridge: mirrors of the two registry definitions (`MMDefs.lean:48-53`), `eventually_Ncount_ge` (the `T log T` lower bound from the RvM main clause), and the node statement `theorem rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates` verbatim |
| `E6Bridge2.lean` | the second bridge: mirror of `RvMCount.zetaZeroCount` (`RHDefs.lean`), the definitional seam `zetaZeroCount_eq_Ncount` (divisor count = Zeta23's `Ncount 0 T`), integrated Stirling on a general window (`int_mu_cumulative`), the cumulative assembly (`rvm_cumulative_eventually`, `rvm_cumulative`) and the node statement `theorem rvm_unconditional` verbatim |
| `AxiomGuardRvMBridge.lean` | CI guard: `#print axioms` for both bridges' theorems AND the consumed upstream inputs; CI fails on `sorryAx` |
| `../generate.py --check` | drift check registered in `telperion.toml`: both node statements (name + binder-free form) and the three mirrored definitions must still match the registry files verbatim, and the toolchain pin must be the zeta-23-lean pin |

## Why a third toolchain island

zeta-23-lean pins Lean `v4.33.0-rc2` / Mathlib `51e6992e`. The mirrormere statements and
the main Telperion islands are on `v4.32.0` (376 Mathlib commits earlier); `missions/rh` and
`li_positivity` are on `v4.34.0-rc1` (129 commits later). Bumping 118 upstream modules was
judged a day-scale mechanical task; a verbatim-statement island importing the upstream at its
own pin is hours and keeps the upstream unmodified. Cross-island grants are the accepted
precedent (`missions/rh/mission.toml`: one granted node's artifact lives on the v4.32
`zero_free_bridge` island).

## What is consumed from upstream, and why Theorem A rather than RvM alone

* `Zeta23.thmA₀ : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2/3 − ε) · Ncount T (2T) ≤ N0star T (2T)` —
  Theorem A in dyadic form; `N0star` is the `ncard` of the **distinct** critical-line zeros.
* `Zeta23.riemannVonMangoldt_zeta.main : ∃ C T₀, ∀ T ≥ T₀, |Ncount T (2T) − T/(2π)·ℓ₁(T)| ≤ C log T`
  — the unconditional dyadic Riemann–von Mangoldt main clause (proved upstream in `Zeta23/RvM/`).
* `Zeta23.zetaSeam.finite_window` — finitely many strip zeros in a window.

The registry predicate needs **distinct ordinates** (a `Finset ℝ`). A multiplicity-weighted
count, however sharp, cannot deliver that: the only bound on the fibre of `Complex.im` over an
ordinate is the local count `O(log T)`, which turns `T log T` into linear growth. Distinct
points on `Re = 1/2` have distinct ordinates, so a positive proportion of critical-line zeros is
exactly the missing input. This is the roadmap correction recorded in the E6 doc.

Bridge shape: window `a := T`, `L := T`; `F := image of Complex.im on {ρ ∈ zerosIn T (2T) | Re ρ = 1/2}`
(injective since `Re` is constant); `thmA₀` at `ε = 1/3` and `Ncount T (2T) ≥ (T/4π) log T`
give `r·T + 1 < F.card` for large `T`.

## The second bridge: cumulative RvM from the general-window internals

The E6 probe (Part B) found that summing the dyadic clause over `T, T/2, T/4, …` only gives an
`O(log² T)` cumulative remainder, so `RH_rvm_unconditional` is **not** a corollary of the stated
upstream theorems. `E6Bridge2.lean` re-runs the upstream's own assembly
(`Zeta23/RvM/MainTerm.lean:rvM_main_param`) on the window `[T₁, T₂]` with `T₁ ∈ [4, 5]` a
zero-free ordinate fixed once and `T₂ ∈ [T, T+1]` a zero-free ordinate near `T`, consuming as
black boxes: `N_eq_halfContour_completedZeta` (folded argument principle),
`halfContour_completedZeta_split`, `gamma_side` (Γ-side = `∫ μ`), `StirlingVert.mu_stirling`
(`|μ(τ) − (1/2π) log(τ/2π)| ≤ C/τ²`), `backlund_horizontal` (top edge), `vertical_two` (right
edge), `zeta_local_zero_count` (`N(0,T₂] → N(0,T]`), `exists_goodHeight`, `Ncount_add`,
`Ncount_mono`. The new analysis is elementary: an FTC lemma for `∫ (1/2π) log(τ/2π)` on a
general interval, the `∫ C/τ²` tail, a Lipschitz bound for the main term on `[T, T+1]`, and the
finite range `2 ≤ T < T₀` absorbed into the constant. The multiplicity seam
(`MeromorphicOn.divisor` vs `analyticOrderAt`) is `MeromorphicOn.AnalyticOnNhd.divisor_apply`
plus `Zeta23.RvM.analyticOnNhd_riemannZeta` on the open strip.

## Recorded results at the pin (local build, 2026-09-17, macOS arm64, 32 cores)

`lake update` + `lake exe cache get` + `lake build` (8,819 jobs, Zeta23 compiled from source)
+ `lake env lean AxiomGuardRvMBridge.lean`, verbatim:

```
'RvMBridge.rvm_unbounded_mean_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.eventually_Ncount_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.int_mu_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.zetaZeroCount_eq_Ncount' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.N_eq_halfContour_completedZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.halfContour_completedZeta_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.gamma_side' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.backlund_horizontal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.vertical_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.StirlingVert.mu_stirling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmA₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.riemannVonMangoldt_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.zeta_local_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.zetaSeam' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Upstream's own `AUDIT.md` at the same commit records the same three axioms for all 27 Comparator
statements (`comparator.json`, `permitted_axioms = [propext, Quot.sound, Classical.choice]`).

## Run locally

```sh
cd telperion/examples/rvm_bridge/lean
lake update            # clones anthropics/formal-math (zeta23/) and Mathlib at the pins
lake exe cache get     # Mathlib oleans for 51e6992e (~2.5 min); Zeta23 itself compiles from source (~2 min on 32 cores)
lake build
lake env lean AxiomGuardRvMBridge.lean
```

## NOTICE — attribution

This island **depends on** (does not copy) `Zeta23`, the Lean development in the `zeta23/`
directory of [anthropics/formal-math](https://github.com/anthropics/formal-math)
(historically `anthropics/zeta-23-lean`, which redirects there).

* Copyright 2026 Anthropic, PBC. Licensed under the **Apache License, Version 2.0**
  (`zeta23/LICENSE`); `zeta23/NOTICE` records that it contains software derived from
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (Kontorovich–Tao).
* Mathematics: Levent Alpöge and Ralph Furman, arXiv:2608.13637. Per upstream
  `formalization.yaml`, "All Lean code was written by Claude; the trusted statement file was
  read against the paper by a paper author"; responsible maintainer Ralph Furman.
* What this island takes is the **theorem interface** (`Zeta23.thmA₀`,
  `Zeta23.riemannVonMangoldt_zeta`, `Zeta23.zetaSeam`, and for the second bridge the RvM
  internals `Zeta23.RvM.{N_eq_halfContour_completedZeta, halfContour_completedZeta_split,
  gamma_side, backlund_horizontal, vertical_two, zeta_local_zero_count, exists_goodHeight}`
  and `Zeta23.StirlingVert.mu_stirling`) at commit
  `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (2026-09-05). Theorem A and the RvM package are
  **not** this repository's work and must not be attributed to it; the bridges (`E6Bridge.lean`,
  `E6Bridge2.lean`) are definition-level assembly plus elementary real analysis.
