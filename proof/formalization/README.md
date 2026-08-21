# R3Cert — the Lean 4 formalization

The machine-checked layer of the Brualdi–Goldwasser campaign: a single Lean 4
library (`R3Cert`, 110 modules, all imported by the root `R3Cert.lean` — a
green `lake build` compiles everything; there are no orphaned files).

> **Status: BUILDS CLEAN on Lean 4 v4.32.0 + pinned Mathlib.** No `sorry`, no
> added axioms, no `native_decide`; `#print axioms` on the capstones reports
> only `[propext, Classical.choice, Quot.sound]`. Remaining hypotheses are
> named `Prop`s carried explicitly (never axioms).
> `conjecture1_proved = False`: this library formalizes the layers listed
> below, not the whole conjecture.

## Module map (bottom to top)

| Group | Modules | What is proved |
|---|---|---|
| **Exact cruxes** | `ExactCruxes.lean`, `Sweep.lean`, `Grid.lean` | The integer/rational anchor facts, kernel-checked — e.g. `3^317·2^81 ≤ 23^129`, the tie identity `64·243·23 = 621·576`, the Pell decay, the R5 crux `(26/23)¹¹ < 621/64`. |
| **Permanent–matching bridge (H1/H2)** | `Matching.lean`, `Involution.lean`, `CavityTree.lean`, `Bridge.lean`, `BridgeStep2`–`BridgeStep4j` | `per` of an acyclic support = matching sum (the crux `acyclic_edgeSupported_involutive` is a theorem); the cavity recursion; acyclicity of the address graph; the unconditional capstones `pi_litHub'` and `amplitude_bridge_real'` tying the Branch cavity model to the finite `per L/∏deg` objects. |
| **`Φ ≤ 1`** | `Potential*.lean` (20 modules), capstone `PotentialFinal.lean:phi_le_one` | The central branch inequality, unconditional over every branch, equality exactly on the six-point rational tie variety. No smooth certificate can prove this (the continuous relaxation exceeds 1); the proof is arithmetic — a discharging hinge super-solution. |
| **Reduction layer (R47 campaign)** | `R47*.lean` (32 modules) | The objective `pi_utree`; hub-state encoding + backbone recursion; the unified merge `Step` relation; the 36-cell bilinear certificate table + 36 dispatch adapters + 72 vee/mirror branches (generated, `positivity`-closed); the merge capstone `chain_to_normalForm`; the (L) legs layer; R6 shedding; the rate-port parse. |
| **Capped-joint g-step layer** (2026-08-20) | `GStepCore.lean`, `GLemmaConfig.lean`, `GLemmaAssembly.lean`, `CappedJointConfig.lean`, `CappedJointSkeleton.lean`, `CappedJointAchievable.lean` | The achievability-corrected Case-2 (`Achievable μ := 0<μ ∧ (μ≤1/2 ∨ μ=1)`; the unconstrained hypothesis is *false* on `(1/2,1)`); `single_child_le_one`, `two_child_le_one` (unconditional for two children), `prodBcap_le_prodGlemma`; the reduction `gstep_le_one_of_glemmaBound` toward the abstract g-lemma. |
| **Near-star / tie geometry** | `NearStar.lean`, `NearStarBandSlice.lean`, `TieClosure.lean`, `TieHarmonic.lean`, `FractalTail.lean`, `HomogeneousSlice.lean` | The near-star spine arithmetic cores, the tie-boundary closure, the homogeneous-slice bounds. |
| **Supporting analysis** | `Jensen.lean`, `Hull*.lean`, `MasterCore.lean`, `Reach.lean`, `Structure.lean`, `Locality.lean`, and others | Convexity/hull machinery, the induction-step skeleton with its remaining hypotheses named explicitly, and the classification layers. |

The abstract g-lemma itself — `gV_le : g(C) ≤ γ` over the `Blk` cavity model —
is kernel-proven in the standalone package
`../../telperion/examples/g1_floors/lean/GLemma.lean`. Landed via PR #20
(merged 2026-08-21): its port into this library (`GArmExtAbstract.lean`,
`GLemmaAbstract.lean`) plus the full closure
`CappedJointClosure.lean:gstep_le_one_achievable` — the config g-step `≤ 1`
at every arity, unconditionally over achievable messages (the ℚ→ℝ cast seam
closed via `Bcap ≤ factorR` + the ported `gstep_lt_gamma`).

Generated modules carry provenance headers naming the generator and its
self-checks (regenerate and diff via `../verification/gen_r47cert_cells.py`).
Every arithmetic goal was independently verified in exact Python arithmetic
before being stated (`../verify.py`).

## Build

```bash
# 1. install elan (Lean version manager), which provides lake
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# 2. fetch deps + prebuilt Mathlib, then build (confirmed working)
cd proof/formalization
lake update            # resolves Mathlib + deps, syncs the toolchain (v4.32.0)
lake exe cache get     # downloads prebuilt Mathlib oleans (~minutes; avoids a multi-hour build)
lake build             # compiles the full R3Cert library
```

A clean `lake build` with no errors and no `sorry` warnings means every theorem
in the library is machine-verified. The same build runs in CI on every push
(`lean-verify`).

**macOS note.** On macOS 26 (Darwin 25)+, older Lean toolchains (e.g. v4.15.0)
produce native binaries that `dyld` rejects with `__DATA_CONST segment missing
SG_READ_ONLY flag`, which breaks `lake exe cache get`. The pinned **v4.32.0**
builds and runs the `cache` binary correctly.

## Version note

The `norm_num`/`decide` cruxes are robust across Mathlib versions. The
real-analytic bridges use standard monotonicity lemmas whose *names* shift
between Mathlib releases — the build is pinned to v4.32.0, where the
reverse-power lemmas carry the `₀` suffix (`le_of_pow_le_pow_left₀`,
`lt_of_pow_lt_pow_left₀`). If you retarget another Mathlib and hit an unknown
identifier, it is a one-line rename (`exact?` resolves it); every underlying
inequality is verified in exact Python arithmetic first, so the content is
settled regardless.
