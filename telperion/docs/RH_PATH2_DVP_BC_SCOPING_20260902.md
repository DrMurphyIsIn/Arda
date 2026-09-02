# Path 2 (dVP via Borel–Carathéodory) — feasibility scoping

**Date:** 2026-09-02
**Branch:** `rh-research-artifacts`
**Status:** scoping only — NO implementation started. `conjecture1_proved = False`.

## Question

Is the de la Vallée Poussin route via Borel–Carathéodory (BC) a viable path to a
**substantially stronger** zero-free region than the current unconditional results —
specifically the sharp `Re s > 1 − c/log|t|` region — and does the BC application hit the
same `Re<1` wall that blocks the elementary Cauchy factor?

### Context: where the current results top out

| Result | Region | Anchor |
|---|---|---|
| Elementary (Hadamard-free) | `Re s > 1 − c/|t|⁵` | `riemannZeta_zero_free_poly` |
| Polylog (sharp bound → 2t factor) | `Re s > 1 − c/(|t|⁴·(1+log|t|))` | `riemannZeta_zero_free_polylog` |
| **dVP (target of this scoping)** | **`Re s > 1 − c/log|t|`** | `dlvp_core_estimate` (currently CONDITIONAL) |

The elementary Cauchy factor (`zeta_hcauchy`, `zeta_deriv_bound`) is **genuinely blocked**: its
Cauchy sphere reaches `Re = 1/4`, where the sharp log growth bound `zeta_log_bound` fails
(it holds only for `1 ≤ σ ≤ 2`). So the polylog region is the ceiling of the elementary cascade.
dVP requires a different mechanism — BC on the log-derivative — which is what this note scopes.

## Verdict: FEASIBLE, not blocked

### 1. The `Re<1` value-wall is AVOIDED

BC (`borel_caratheodory_deriv`, built & green in `BorelCaratheodory.lean`) bounds `‖deriv f‖`
on a smaller disk from an upper bound on `Re f` over a sphere. Applied to `f = log ζ`:

- The relevant quantity is `Re(log ζ) = log‖ζ‖`.
- The **crude** bound `zeta_strip_bound` (`‖ζ‖ ≤ ‖s‖/‖s−1‖ + ‖s‖/Re s ≈ |t|`) holds on **all** of
  `stripDomain = {0 < Re s} \ {1}` — the full right half-strip, INCLUDING `Re < 1` (down to `Re>0`).
- A BC disk of radius `R ~ 1` centred at `s₀ = 1+δ+it` reaches `Re < 1` but stays `Re > 0`, so the
  crude bound is valid across the whole disk.
- **BC takes the LOG of that bound:** `Re(log ζ) = log‖ζ‖ ≤ log(C|t|) ~ log|t|`. The dVP rate falls
  out of the *crude* bound — the sharp `zeta_log_bound` is not even required for the rate.

**Why this dodges the wall.** The elementary Cauchy factor needs a *value* bound on `ζ` at `Re<1`,
where the sharp bound provably fails. The BC route needs only a *log-of-value* bound, and the crude
bound (valid on all `Re>0`) suffices under the log. Different wall — not hit.

### 2. The real obstacle — zeros in the disk — is covered by Mathlib

BC requires `log ζ` analytic on the disk, but ζ has zeros there ⟹ `log ζ` is singular. The classical
fix: factor the zeros out (Blaschke), apply BC to the analytic remainder, and count the zeros via
Jensen. In the dVP estimate this is exactly where the ingredients of `dlvp_core_estimate` come from —
the tracked zero contributes the `−k/(σ−β)` term; the zero-count bound gives `A, L ~ log|t|`.

Mathlib v4.32.0 **has the zero-counting machinery** (checked in-tree):

- `Mathlib/Analysis/Complex/JensenFormula.lean` — Jensen's formula.
- `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/{Basic,Asymptotic}.lean` — Nevanlinna
  log-counting / zero-density.
- `Mathlib/Analysis/Complex/Hadamard.lean`, `Mathlib/Analysis/Analytic/IsolatedZeros.lean`.
- Plus this repo's `BorelCaratheodory.lean` (12 theorems, green).

So the gate that would otherwise sink this route (missing Jensen / zero-counting) is **met**.

## Remaining work (if pursued)

A substantial, multi-session assembly — NOT turnkey:

1. Relate Mathlib's **abstract** `LogCounting` / `JensenFormula` API to the **concrete** ζ zero-sum
   bound `Σ_ρ Re(1/(s−ρ)) ≤ O(log|t|)` on the disk (the crux; requires reading the two Mathlib file
   APIs before any effort estimate — existence ≠ usability).
2. Assemble the factored-BC bound on `‖(log ζ)'‖ = ‖ζ'/ζ‖` from (1) + `BorelCaratheodory.lean`.
3. Discharge the currently-hypothesised `A`, `L`, `−k/(σ−β)` inputs of `dlvp_core_estimate`
   (`ZeroFreeRegion.lean`), turning the CONDITIONAL core UNCONDITIONAL.
4. Assemble `Re s > 1 − c/log|t|`.

## Honest caveats

1. **Real work.** The (1) API-bridge is the crux and is non-trivial; do not quote effort until the
   two Mathlib files are read.
2. **Duplicative.** Even completed, this is the *classical* dVP region, already formalized externally
   (`strongpnt` / `PrimeNumberTheoremAnd`). The value here is methodological — a BC + Nevanlinna route
   exercising Mathlib's new value-distribution theory — not a new mathematical result.
3. **Not toward RH.** dVP is far short of RH; the frontier past it is the Vinogradov–Korobov rate and
   Weil positivity, untouched by this route. `conjecture1_proved = False`.

## Recommendation

Path 2 is the genuine target for a substantially stronger region and it is **achievable** (the `Re<1`
wall is dodged and the zero-counting gate exists in Mathlib) — unlike the elementary Cauchy factor,
which is blocked. Commit to it only if the methodological payoff is the goal, since the region itself
is duplicative of external work. Recommended first step if pursued: read
`ValueDistribution/LogCounting/Basic.lean` + `JensenFormula.lean` and prototype the concrete
`Σ_ρ Re(1/(s−ρ)) ≤ O(log|t|)` bound before committing to the full assembly.
