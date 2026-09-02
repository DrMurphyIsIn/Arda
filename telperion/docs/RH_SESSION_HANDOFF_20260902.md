# RH session handoff — 2026-09-02

**Repo:** `DrMurphyIsIn/Arda`  **Branch:** `rh-research-artifacts`  **Tip:** `2a02505`
**Worktree used this session:** `~/arda-rh-extend`
**`conjecture1_proved = False`** — throughout. We formalize the CLASSICAL zero-free region
(elementary / Hadamard-free route), never RH itself.

## What this session did

1. **Closed caveat 3 (PR #189, merged).** `AxiomGuardRH.lean` now `#print axioms`-guards
   `zeta_log_bound`, `zeta_trunc`, `zeta_partial_sum_repr` **directly** (added `import ZetaLogBound`;
   CI builds `ZetaLogBound` before the guard in `telperion-lean-e2e` → `zero-free-elementary-compiles`).
   Previously they were guarded only transitively via the polylog region. CI confirms all three
   `[propext, Classical.choice, Quot.sound]`. Guard count: 11 theorems.

2. **Scoped path 2 (PR #190, merged).** `telperion/docs/RH_PATH2_DVP_BC_SCOPING_20260902.md`.
   Verdict below.

## Current proven state (unconditional, kernel-clean, on `rh-research-artifacts`)

| Result | Region / statement | Anchor |
|---|---|---|
| Strip representation | `ζ(s) = s/(s−1) − s∫_{x>1}{x}x^{−s−1}` on `stripDomain` | `zeta_fract_repr` (R1+R2+R3) |
| Crude growth bound | `‖ζ‖ ≤ ‖s‖/‖s−1‖ + ‖s‖/Re s` on all `Re>0` | `zeta_strip_bound` |
| Sharp near-line bound | `‖ζ(σ+it)‖ ≤ 6(1+log|t|)`, `1≤σ≤2`, `|t|≥2` | `zeta_log_bound` |
| Truncated Euler–Maclaurin | `ζ = Σ_{n≤N}n^{−s} + N^{1−s}/(s−1) − s·tail`, `0<Re s`, `s≠1` | `zeta_trunc` |
| Elementary region | `Re s > 1 − c/|t|⁵` | `riemannZeta_zero_free_poly` |
| **Polylog region (current best)** | **`Re s > 1 − c/(|t|⁴·(1+log|t|))`** | `riemannZeta_zero_free_polylog` |

All guarded by `AxiomGuardRH.lean` (elementary/repr/sharp anchors) + `AxiomGuardPolylog` (region).

## Open frontier — three tiers

### Tier 0 — BLOCKED (do not retry)
The **elementary Cauchy factor** (`zeta_hcauchy`, `zeta_deriv_bound` in `ZeroFreeElementary.lean`)
cannot be sharpened: its Cauchy sphere reaches `Re = 1/4`, where `zeta_log_bound` fails (holds only
`1≤σ≤2`). So the polylog region is the CEILING of the elementary cascade. Only the `2t` magnitude
uses the sharp bound; `zeta_hcauchy` stays crude (`|ζ|≤C|t|`, power-4). Not improvable from within.

### Tier 1 — the genuine next win: path 2 (dVP via Borel–Carathéodory)
Target: sharp **`Re s > 1 − c/log|t|`** (discharges the CONDITIONAL `dlvp_core_estimate` in
`ZeroFreeRegion.lean`). **Scoping verdict: FEASIBLE, not blocked** (full detail in
`RH_PATH2_DVP_BC_SCOPING_20260902.md`):
- The `Re<1` value-wall is AVOIDED — BC bounds `deriv(log ζ)` from `Re(log ζ)=log‖ζ‖`; the crude
  `zeta_strip_bound` (valid on all `Re>0`) suffices under the log → `log|t|` = dVP rate.
- Zero-counting gate is MET by Mathlib v4.32.0: `Analysis/Complex/JensenFormula.lean` +
  `ValueDistribution/LogCounting/{Basic,Asymptotic}` + `Hadamard.lean` + `IsolatedZeros.lean`, on top
  of this repo's `BorelCaratheodory.lean` (green).
- **REMAINING (multi-session):** bridge Mathlib's ABSTRACT log-counting to the CONCRETE ζ zero-sum
  `Σ_ρ Re(1/(s−ρ)) ≤ O(log|t|)` (the crux) → factored-BC bound on `ζ'/ζ` → discharge the `A/L/−k`
  hypotheses of `dlvp_core_estimate` → assemble the region.
- **First step if pursued:** READ `ValueDistribution/LogCounting/Basic.lean` + `JensenFormula.lean`
  APIs and prototype the concrete zero-sum bound BEFORE quoting effort. Existence ≠ usability.
- **Honest caveat:** even done, this is the classical dVP region, already formalized externally
  (`strongpnt` / `PrimeNumberTheoremAnd`) — duplicative; value is methodological. NOT toward RH.

### Tier 2 — the real RH frontier (untouched)
Past dVP: Vinogradov–Korobov rate, Weil positivity. Not approached by any current infrastructure.

## Telperion assets from the RH work (reusable)
- `emit_zero_free_region.py` — region-rate assembly; `θ` = rate lever (plug sharper growth → improved
  region auto). `emit_dominated_integrability.py`, `emit_dirichlet_repr.py`. All dogfooded (PR #184).
- `RayPowerEstimate.lean` — reusable cpow/rpow-on-rays lemma pack (support lib, import in future ζ/L work).

## Discipline & footguns (carry forward)
- **NO local Lean builds** (SoC watchdog). CI-only via `telperion-lean-e2e`. Each piece = own `lean_lib`
  + own CI job. Verify kernel-clean via `#print axioms` (`[propext, Classical.choice, Quot.sound]`),
  NOT grep for `sorry` (docstring false-positives; write "no `sorry`" not "sorry-free" — trips the scan).
- **CI log fetch:** `gh run view --log` is empty on lag → use
  `gh api repos/DrMurphyIsIn/Arda/actions/jobs/<id>/logs`. base64 `gh api` content: `tr -d '\n'` first.
- **Merges:** branch is often held by another worktree (`~/telperion-work`) → merge via
  `gh pr create … && gh pr merge --merge --admin`, not local checkout.
- **Lean footguns (accumulated):** `Filter.Eventually.of_forall` (not `eventually_of_forall`);
  `HasDerivAt.const_cpow` (no `Complex.hasDerivAt_const_cpow`); `fun_prop` can't do
  `AEStronglyMeasurable` of a norm → `Measurable.aestronglyMeasurable` then `fun_prop`; emitter
  `open Complex` breaks natCast rewrites, and `← Complex.cpow_one x` rewrites the WRONG bare x
  (rewrite the RHS exponent); a failing Lean line# TRACKS earlier lemmas as you edit above it.
- **Honesty order:** SCOPE before COMMIT. This session corrected an over-optimistic recommendation
  (the Cauchy improvement) after investigation — path 2 was scoped, not started, by request.

## Recommended next action
Decision point for the operator: commit to Tier 1 (path 2) only if the methodological payoff is the
goal (region is duplicative). If yes → start with the two Mathlib API reads above. If not → the
formalization is at a clean, fully-guarded stopping point; no loose ends.
