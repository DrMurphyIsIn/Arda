# Archimedean Li growth (Arc B) + Route P Bragg floor (Arc C) — campaign handoff

Machine-checked (Lean 4 kernel, `li_positivity` island, v4.34.0-rc1) results from the 2026-09-12/13
session, all merged to `main`, all kernel-clean under `{propext, Classical.choice, Quot.sound}` with
**zero `sorryAx`**, all guard-wired in `AxiomGuardLiPositivity.lean`.

## Honesty invariant (read first)

`conjecture1_proved = False`. Arc B is Γ-function calculus: the growth of the **archimedean** Li
summand is an unconditional classical fact, and proving it says nothing about RH — the companion
summand, whose temperedness IS RH (Voros's dichotomy), is untouched. Arc C certifies finite rational
inequalities whose passage to the companion coefficient runs through the **conditional, RH-hard**
exhaustion identity, carried always as an explicit undischarged hypothesis.

## Arc B — the elementary route to the archimedean growth (PRs #517, #519)

| Brick | Theorem | Statement |
|---|---|---|
| B1a | `logDeriv_phi_Gammaℝ_eq_elem` | On `‖z‖ < 1/2`: `logDeriv(Γℝ∘M) z = −(γ+log π)/2·M² − M + ∑'_j archSummand j z`, `M = (1−z)⁻¹` — the whole polygamma content as ONE elementary series of rational functions. |
| B1b.1 | `archSummand_eq_compact` / `archSummand_norm_le` / `tendstoUniformlyOn_archSummand` | `archSummand j z = M²/(2(j+1)·D_j)`, `D_j = 2(j+1)(1−z)+1`; `‖·‖ ≤ 2/(j+1)²` on `‖z‖ ≤ 1/4`; uniform convergence of partial sums. |
| B1b.2 | `taylorCoeff_Gammaℝ_elem` | `taylorCoeff Γℝ n = −(γ+log π)/2·(n+1) − 1 + ∑'_j [(n+1)/(2(j+1)) − 1 + ((2j+2)/(2j+3))^{n+1}]` — the EXACT coefficient as elementary real data (verified numerically to 40 digits before formalization). |
| B2/B3 | `taylorCoeff_Gammaℝ_re_growth` | `∀ n ≥ 2: \|Re(taylorCoeff Γℝ n) − (n/2)·log n\| ≤ 8n` — **unconditional**, explicit constant. |

**Why the reroute matters.** The contour route to this growth is blocked (Mathlib has no complex
digamma large-argument asymptotic), and the Faà di Bruno closed form (#464) is combinatorially
opaque. Composing `logDeriv_phi` + `logDeriv_Gammaℝ_eq` + `digamma_series` and clearing denominators
through the Möbius map produces rational summands with explicit Taylor coefficients — the growth
becomes a harmonic-number statement.

**Proof machinery worth reusing.**
- The **derivative/tsum swap without per-order bounds** (`iteratedDeriv_tsum_archSummand`): iterate
  `TendstoLocallyUniformlyOn.deriv` over `Finset` partial sums; one 0th-order uniform envelope
  suffices. (Mathlib has only the first-order `hasSum_deriv_of_summable_norm`.)
- `iteratedDeriv_scaledMobius`: `(a−bw)⁻¹ ↦ n!·bⁿ/(a−bz)^{n+1}` (mirror of `iteratedDeriv_mobius`).
- Per-summand growth: Bernoulli (`one_add_mul_le_pow`) lower + second-Bonferroni upper (fresh
  induction), split at `j = n`, telescoping tail `∑_{k} 1/(n+k+1)² ≤ 1/n`, Mathlib harmonic bounds.

**What is NOT claimed.** The sharper classical `(n/2)(log n + γ − 1 − log 2π) + o(n)` (the linear
term's constant) is unformalized — the `8n` window absorbs it. Nothing about total `λ_n` growth.

## Arc C — the Bragg-floor certificate family (PRs #511, #518)

- `companion_below_floor_refutes_rh` (D3 pt 1): one order with the companion coefficient strictly
  below the explicit archimedean floor `−(1 + Re taylorCoeff Γℝ n)` refutes RH — the contrapositive
  of `rh_iff_companion_ge`. Never expected to fire.
- `bragg_floor` emitter (D3 pt 2): per order, certifies the FINITE inequality
  `floor(n) ≤ braggLo − tailHi` — truncated von Mangoldt amplitude at `s₀ = 2` over `p^k ≤ 5000`,
  net of a certified tail, against the archimedean floor. Emitted `BraggFloor.lean`: 15 rungs
  (`n = 0, 6..19`) by `norm_num`, plus `bragg_below_floor_refutes_rh` carrying the companion
  identification `hcomp` as an explicit undischarged hypothesis (the RH-hard exhaustion seam of
  `RvMCompanionBraggLimit`).
- **Honest refusals**: at fixed `s₀` the amplitude is the order-0 datum; it does not clear the
  floors for `n = 1..5` and the emitter refuses those orders rather than fake the comb expansion at
  the Li base point. Trust seam: Arb (python-flint) enclosures, as in the Li ladder. Tests: 16
  emitter unit/forge/drift + registry/sensitivity gates + Lean-backed two-sided negative control.

## Verification

```bash
cd telperion/examples/li_positivity/lean
lake build                                  # island + guard
lake env lean AxiomGuardLiPositivity.lean   # all Arc B/C anchors; 0 sorryAx
```

## Open threads

1. The sharper archimedean asymptotic (linear-term constant) — elementary but bookkeeping-heavy.
2. Route P D4 (diffraction/inertia bridge via the `RHLinalg` Sylvester/`posIndex` prelude from the
   `hermitian_moment` island) — experimental, in progress at handoff.
3. The T→∞ exhaustion limits remain RH-hard — documented, not to be attempted.

`conjecture1_proved = False`.
