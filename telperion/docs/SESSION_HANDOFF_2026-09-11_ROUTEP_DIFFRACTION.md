<!-- Handoff for the Route P → log-prime diffraction (Dyson quasicrystal) work of 2026-09-11.
Self-contained: a fresh session should be able to resume D2b-2 from this doc alone.
conjecture1_proved = False throughout. -->

# Session handoff — Route P → log-prime diffraction (Dyson quasicrystal), 2026-09-11

## One-paragraph summary

Route P (`RvMWeierstrass.rh_iff_companion_ge`, #465) reduces RH to a single explicit inequality per `n`
on the **companion** Taylor coefficient against a fully-explicit archimedean floor. This session built
the **diffraction reading** of Route P: the companion coefficient *is* a von-Mangoldt (log-prime /
Bragg) moment, so RH reads as "log-prime Bragg amplitudes ≥ archimedean floor" per `n` — the Dyson
quasicrystal framing. Delivered as a linear PR stack (D1 → D2a → D2b-1), all kernel-verified locally
(axioms `[propext, Classical.choice, Quot.sound]`), plus scope/spec docs and a CI-guard hardening.
**Nothing here approaches RH.** Every reduction is category-(a) circular or category-(b) finite; the
uniform limit is category-(c) RH-hard. `conjecture1_proved = False`.

## What was built (all in `telperion/examples/li_positivity/lean/`, island toolchain `v4.34.0-rc1`)

| PR | brick | theorem (namespace `RvMWeierstrass`) | file | status |
|----|-------|--------------------------------------|------|--------|
| #471 | **D1** | `logDeriv_zetaPoleCompanion_eq_vonMangoldt` — for `Re s>1`, `logDeriv zetaPoleCompanion s = −L(Λ) s + (s−1)⁻¹` | `RvMCompanionPrime.lean` | verified local, auto-merge armed |
| #472 | **D2a** | `companion_right_edge_prime_integrand` — right-edge Bragg integrand `g·logDeriv comp = g·(−L(Λ)+(·−1)⁻¹)` | `RvMCompanionBragg.lean` | verified local, **stacked on #471** |
| #474 | **D2b-1** | `liPairedSummand_eq_liWeight_paired` — `liPairedSummand n ρ = liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ)` | `RvMLiWeightReconcile.lean` | verified local, **stacked on #472** |
| #469 | scope | `ROUTEP_DIFFRACTION_SCOPE_2026-09-11.md` | docs | auto-merge armed |
| #473 | D2b spec | `ROUTEP_D2B_WEIGHT_RECONCILIATION_SPEC_2026-09-11.md` | docs | auto-merge armed |
| #451 | CI harden | guard-as-lib (see below) | lakefile + guard | auto-merge armed, verified compiles clean |

Proofs (short):
- **D1** = `linear_combination h2 - h1` of `DiffractionCore.logDeriv_zeta_eq_companion_sub_pole` (#461)
  and `DiffractionCore.logDeriv_zeta_eq_neg_LSeries_vonMangoldt`. Discharge `s≠1` from `1<s.re`;
  `riemannZeta_ne_zero_of_one_lt_re` for `ζ≠0`.
- **D2a** = one `rw [logDeriv_zetaPoleCompanion_eq_vonMangoldt (…re computation…)]`; mirrors
  `DiffractionCore.right_edge_weighted_prime_integrand`.
- **D2b-1** = `rw [liPairedSummand_eq_two_sub_v_sub_inv, liWeight_at_zero, liWeight_at_zero,
  pairedZero_val]; set w := 1 − 1/ρ.val; hwe; hpair (1 − 1/(1−ρ) = w⁻¹); rw [hpair, inv_pow]; ring`.

## Merge mechanics (for whoever lands these)

- **Stack order:** #471 → #472 → #474 (linear). GitHub auto-retargets each child's base to `main` as
  its parent merges; arm auto-merge (`gh pr merge <n> --squash --auto`) on the child once retargeted.
- **#469 / #473 / #451** land independently off `main`.
- **Two tidy-ups:**
  1. #451 and #471 both edit the `defaultTargets` line → whichever merges second needs a trivial
     rebase (union the array).
  2. Once **#451 (guard-as-lib)** is on `main`, the `defaultTargets` entries the stack added
     (`RvMCompanionPrime`, `RvMCompanionBragg`, `RvMLiWeightReconcile`) are **redundant** — the
     guard-as-lib builds every guard import transitively. Drop them on the post-#451 rebase.

## CI-guard fix landed this session (context for the guard)

- **#448** (earlier): `zero_free_bridge` `zero-free-bridge-suite` was red since #363 — `AxiomGuardDlvp.lean`
  imported `DlvpCorridor` but it was missing from `defaultTargets`, so bare `lake build` never built it →
  `lake env lean` failed `unknown module prefix`. Fix = add `DlvpCorridor` to `defaultTargets`.
- **#451** generalizes the fix for `li_positivity`: declares **`AxiomGuardLiPositivity` itself as a
  `lean_lib` in `defaultTargets`**, so bare `lake build` compiles the guard *and its whole import
  closure*, and `lake build` (which fails on real errors) becomes the true gate. **Discovered hole:**
  the `li-positivity-compiles` guard step is `lake env lean … ; ! grep -q sorryAx` — it passes even on
  elaboration errors (only catches literal `sorryAx`). #451 closes this by making `lake build` the gate.
  Verified locally: `lake build` (8782 jobs) compiles the guard-as-lib clean, no hidden errors.

## The frontier — resume at D2b-2

Goal remaining for the diffraction reading (`ROUTEP_D2B_WEIGHT_RECONCILIATION_SPEC`, #473):

- **D2b-2 (next):** fold the FE pairing + Stratum 2 (`liCoeff_isLimit_partialSums`, #430) using the
  D2b-1 hinge to write `taylorCoeff riemannXi n` as a `divisor·liWeight (n+1)` sum matching
  `li_finite_explicit_formula`'s left side. **This is where the conditional analytic hypotheses enter**:
  `hgenus` (`Summable (1/‖ρ‖²)`) and `hhad` (Hadamard product) — carry them as documented undischarged
  hypotheses, do not try to discharge (they are RH-adjacent).
- **D2b-3:** apply `li_finite_explicit_formula` (index `n+1`) → `(boundary) − (Bragg sum)`; subtract
  `1 + taylorCoeff Γℝ n` via the split `taylorCoeff_riemannXi_split_explicit` (#463) to isolate
  `taylorCoeff companion n`; render the right edge via D2a. Result = the finite Bragg identity for the
  companion coefficient (Arb-enclosed edges = trust seam).
- **D3:** the `bragg_floor` Telperion emitter — certify `Σ_{p^k≤N} amplitude − enclosed tail ≥
  −(1 + Re taylorCoeff Γℝ n)` per `n`, + a `bragg_below_floor_refutes_rh` falsifiability atom. Register
  in `certify.py` + `emitter_sensitivity.py` + negctrl. Reuse the Li Arb backend + `UnitModulusSOS` (#467).
- **D4 (optional):** assemble the prime-side amplitudes into a Weil–Gram form + run the ported
  `RHLinalg` Sylvester/`posIndex` prelude → the (1,1)-signature reading (Bombieri inertia).

## Honesty invariants (do not violate)

- `conjecture1_proved = False` on every headline theorem/doc.
- Category discipline: **(a)** `rh_iff_companion_ge` is a circular relocation (companion carries all
  zeros); **(b)** the finite Bragg identity / rungs are finite-checkable, consistent with RH, proving
  nothing; **(c)** the *uniform* "companion = convergent prime sum at the Li base point" IS RH (von
  Mangoldt series diverges at `s=1`; the contour shift to `Re=1/2` with archimedean-residual control is
  the analytic core). Never conflate.
- Every emitted/guarded theorem `#print axioms`-clean `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`, wired into `AxiomGuardLiPositivity.lean`.

## Footguns hit this session

- **Shell is zsh:** `"$ref:path"` triggers the `:t`/`:h` history modifier and silently corrupts
  `git show ref:path` (gave a bogus 260-byte blob). Use `git show "${ref}:${path}"` with braces, or
  `git grep <ref> -- <path>` / `git cat-file`.
- **Multi-worktree cd:** always `cd … || { echo ABORT; exit 1; }` — a failed `cd` (stale remote ref)
  once ran a `git merge` in the wrong worktree, creating an unwanted merge commit on a parallel
  session's branch (recovered via `git reset --hard`; it was local-only, never pushed).
- **`li_positivity` local build is heavy:** ~8700+ jobs from source (only Mathlib is cached via
  `lake exe cache get`; `RvMDiffractionCore.lean` is 3555 lines). Verify a single new lib with
  `lake build <Lib>` then a focused `lake env lean` scratch that imports only that lib + `#print axioms`.
- **`lake-manifest.json` is untracked** in `li_positivity` — local builds regenerate it; do not commit it.
- **`defaultTargets` fragility** (the #448/#451 bug class): a guard import not built by `lake build`
  fails `lake env lean` with `unknown module prefix`. Post-#451 (guard-as-lib) this is moot.

## Key upstream / on-main references

`rh_iff_companion_ge` (#465, RvMRouteP), `taylorCoeff_riemannXi_split_explicit` (#463, RvMLiCoeffId),
`zetaPoleCompanion` + `logDeriv_zeta_eq_companion_sub_pole` (#461, RvMDiffractionCore),
`logDeriv_zeta_eq_neg_LSeries_vonMangoldt` / `right_edge_weighted_prime_integrand` /
`li_finite_explicit_formula` (RvMDiffractionCore / RvMLiStratum3, #430),
`liCoeff_isLimit_partialSums` (RvMLiStratum2, #430, conditional `hgenus`/`hhad`),
`liPairedSummand_eq_two_sub_v_sub_inv` / `liPairedSummand_re_nonneg_iff` (RvMPairedSummandAnatomy, #468),
`onLine_liPairedSummand_eq_normSq` (RvMOnLinePositivity, #466), `liWeight` + `liWeight_at_zero`
(RvMLiCountBridge). Assessment context: `RH_CLOSURE_ROUTES_ASSESSMENT_2026-09-10.md`,
`DYSON_QUASICRYSTAL_CERTIFICATES.md`.
