# Effective Riemann–von Mangoldt — Arc A handoff

Machine-checked (Lean 4 kernel) assembly that turns the Backlund `S(T)=O(log T)` bound and the exact
counting formula `N = 1 + θ(T)/π + S(T)` into an **effective** Riemann–von Mangoldt estimate: the box
winding integer (equivalently, the ξ-zero count) is pinned to the smooth main term `1 + θ(T)/π`
within an explicit `O(log T)`. **3 PRs (A1–A3)**, all on the `li_positivity` island (Lean v4.34.0-rc1),
kernel-clean under `{propext, Classical.choice, Quot.sound}` with **zero `sorryAx`**, each headline
`#print axioms`-guarded in `AxiomGuardLiPositivity.lean`.

## Honesty invariant (read first)

`conjecture1_proved = False`. This is **rigorous classical mathematics** — the effective form of a
counting formula proved by von Mangoldt in 1895 — **not** a proof of or step toward RH. A counting
formula places zeros by height; it says nothing about whether they lie on the critical line. Two
honest caveats, both the genuine classical ones:

- **`hζne` / `hζT`** — `ζ ≠ 0` on the height-`T` segment `[1/2,2]+iT`. This is the "`T` not a
  zero-ordinate" caveat: `S(T)` jumps at each ζ-zero ordinate, so the continuous-argument formula is
  stated off those heights. Carried as an explicit hypothesis, never discharged.
- **`hwind`** — the boundary winding integer enters as the *contour value* `= 2πiN`, exactly as in the
  tiled Turing ladder. The zero count is the **derived** conclusion, never an assumed input. This is
  the same Arb-shaped trust seam used throughout the section.

## The three bricks

| # | File | Theorem | Role |
|---|------|---------|------|
| A1 | `RvMBacklundExplicit` | `riemannS_abs_le_log_explicit` | Pure-in-`T` Backlund: `\|S(T)\| ≤ log((4T+19)/(2−π²/6))/log(7/6) + 2` for `T ≥ 4`, `hζne`. Majorizes the `‖F_T(2)‖` denominator of the PR-6 headline by its Jensen-centre floor `2 − π²/6` (`backlundAux_two_norm_ge`). |
| A2 | `RvMNTEffective` | `nt_effective_bound` | `\|N − 1 − θ(T)/π\| ≤ (A1 bound)` under the `xiTele_winding_eq_RvM` hypotheses + `T ≥ 4`. The error is exactly `riemannS T`; A1 closes it. |
| A3 | `RvMNTCount` | `nt_count_effective_bound` | Same bound phrased on the **box ξ-zero count**: composes `xiTele_count_eq_winding` (zero count `= N`) with A2. |

## Honest comparison with the literature

Our explicit constant is **deliberately weak** — the contribution is the kernel derivation, not the
sharpness:

- **Backlund 1918**: `|S(T)| ≤ 0.137 log T + 0.445 log log T + 4.35` (`T ≥ 200`).
- **Trudgian 2014** (best classical `S(T)`): `|S(T)| ≤ 0.110 log T + 0.290 log log T + 2.290`.
- **Hasanalizade–Shen–Wong 2021** (explicit `N(T)`): `|N(T) − (T/2π)log(T/2πe) − 7/8| ≤
  0.1038 log T + 0.2573 log log T + 9.3675` (`T ≥ 3`).

Our `log((4T+19)/(2−π²/6))/log(7/6)` is `~ log(T)/log(7/6) ≈ 6.5 log T` — far from `0.11 log T`.
Sharpening it would require Stirling/Binet asymptotics of `Γ(1/4+iT/2)` (the method behind Trudgian's
constants), which is new analysis not attempted here.

## Named future work (not attempted; not claimed)

1. **θ-Stirling asymptotic.** Replacing `θ(T)/π` by its closed form `(T/2π)log(T/2πe) + 7/8 + O(1/T)`
   needs the continuous complex `log Γ` / digamma asymptotic on the critical line — absent from the
   pinned Mathlib, the same gap documented for the Li-coefficient growth arc. Until then the main term
   stays `θ(T)/π` (itself a kernel object, `theta_eq_argChangeVert_gammaR`).
2. **Trudgian/HSW constants.** Out of scope for the same reason.
3. **Ladder trust-shrink.** The tiled Turing verification (`AllZeros_h4000`, 3474 zeros) lives in the
   **separate v4.32 island** `telperion/examples/zeta_zero_localization/lean/` and consumes per-band
   Arb winding integers as hypotheses. An effective `N(T)` in *this* v4.34 island cannot import across
   the toolchain boundary; wiring it to *derive* those per-band counts is genuine cross-island work,
   gated on unifying the two toolchains (as the Backlund/Li islands were unified in #483).

## Verification

```bash
cd telperion/examples/li_positivity/lean
lake build                                  # full island incl. AxiomGuardLiPositivity
lake env lean AxiomGuardLiPositivity.lean   # #print axioms for A1-A3 headlines; 0 sorryAx
```

`conjecture1_proved = False`.
