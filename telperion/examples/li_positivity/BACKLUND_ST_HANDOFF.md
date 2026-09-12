# Backlund `S(T) = O(log T)` — campaign handoff

Machine-checked (Lean 4 kernel) formalization of Backlund's bound on the Riemann–Siegel `S(T)`,
built in the `li_positivity` toolchain island. **16 PRs, #484–#500**, all merged to `main`
(tip at handoff: `3d4c6fc3`). Every theorem is kernel-clean under the three standard axioms
`[propext, Classical.choice, Quot.sound]` with **zero `sorryAx`**, and every headline is wired into
`AxiomGuardLiPositivity.lean` for CI verification.

## Honesty invariant (read first)

`conjecture1_proved = False`. This is a **rigorous classical result** — the standard `S(T) = O(log T)`
growth bound — **not** a proof of, or a step toward, the Riemann Hypothesis. The final theorem carries
exactly one hypothesis, `hζne` (ζ ≠ 0 on the segment `[1/2,2]+iT`), which is the genuine
"`T` not a zero-ordinate" caveat that Backlund's method inherently inherits (`S(T)` jumps at ζ-zeros).
The theorem claims exactly what it proves — no more.

## The headline theorem

`Backlund.riemannS_abs_le_log_of_ne_zero` (in `RvMBacklundLogCont.lean`):

```lean
theorem riemannS_abs_le_log_of_ne_zero {T : ℝ} (hT : 4 ≤ T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |DiffractionCore.riemannS T|
      ≤ Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2)) + 2
```

`DiffractionCore.riemannS T = (argChangeVert ζ 2 0 T + argChangeHoriz ζ T 2 (1/2)) / π` is the corpus's
branch-free Riemann–Siegel `S(T)` (continuous argument of ζ along `2 → 2+iT → 1/2+iT`, divided by π).
The RHS is an explicit `O(log T)`.

## Proof architecture — the 16 bricks

The method: `π·S(T) = [vertical leg at Re=2] + [horizontal leg at Im=T]`. The vertical leg is `O(1)`
(ζ stays in the right half-plane), the horizontal leg is `O(log T)` (its argument sweeps `≤ π` per
sign-change of `Re ζ`, and the sign-changes are counted by Jensen's formula).

| # | File | Theorem(s) | Role |
|---|------|-----------|------|
| #484 | `RvMBacklundAux` | `backlundAux`, `backlundAux_ofReal`, `backlundAux_analyticAt` | `F_T z := ½(ζ(z+iT)+ζ(z−iT))`; on the real axis `F_T σ = Re ζ(σ+iT)` |
| #485 | `RvMBacklundIVT` | `backlundAux_root_of_sign_change` | IVT: a sign change of `Re ζ` yields a root of `F_T` |
| #486 | `RvMBacklundCenter` | `re_zeta_two_ge`, `backlundAux_two_norm_ge` | `Re ζ(2+iT) ≥ 2 − π²/6 > 0`; `‖F_T 2‖ ≥ 2 − π²/6` |
| #487 | `RvMBacklundJensen` | `backlundAux_analyticOnNhd_ball`, `zeta_shift_sphere_bound`, `backlundAux_zero_count_le` | Jensen: `∑ᶠ divisor F_T (ball 2, 3/2) ≤ log((4T+19)/‖F_T 2‖)/log(7/6)` = `O(log T)` |
| #489 | `RvMBacklundConfine` | `argChangeHoriz_abs_lt_pi_of_rePos` | Confinement: `Re f > 0` on a horizontal segment ⟹ `|argChangeHoriz f| < π` |
| #490 | `RvMBacklundPartition` | `argChangeHoriz_abs_lt_pi_of_re_sign`, `argChangeHoriz_abs_le_partition` | Either-sign confinement (`logDeriv(−f)=logDeriv f`); partition sum `≤ n·π` |
| #491 | `RvMBacklundSignConst` | `argChangeHoriz_abs_lt_pi_of_re_ne_zero` | Nonvanishing ⟹ confinement (IVT sign-constancy) |
| #492 | `RvMBacklundFinite` | `backlundAux_real_zeros_finite` | `F_T`'s real zeros on `[1/2,2]` are finite (inject into the divisor support) |
| #493 | `RvMBacklundOrder` | `exists_monotone_partition_of_finite` | Sort a finite forbidden set into a monotone partition, `N ≤ card+1` (pure `Finset.orderEmbOfFin`) |
| #494 | `RvMBacklundConfineNonstrict` | `argChangeHoriz_abs_le_pi_of_re_nonneg`, `..._re_sign'` | Non-strict confinement: `Re f ≥ 0` (zeros allowed at endpoints) ⟹ `≤ π` |
| #495 | `RvMBacklundSignClosed` | `re_one_sign_of_ne_zero_Ioo` | Nonzero on the OPEN interval ⟹ one sign on the CLOSED (bridges #493 → #494) |
| #496 | `RvMBacklundCount` | `argChangeHoriz_abs_le_card_zeros` | **Capstone**: `|argChangeHoriz f T a b| ≤ (Z.card+1)·π` (abstract in `f`) |
| #497 | `RvMBacklundZeta` | `zeta_argChangeHoriz_abs_le` | ζ instantiation: bound in terms of the `F_T` zero count |
| #498 | `RvMBacklundCountJensen` | `zeta_argChangeHoriz_abs_le_log` | Explicit `O(log T)` horizontal (count `≤` Jensen via `card ≤ Σ divisor`) |
| #499 | `RvMBacklundS` | `argChangeVert_abs_lt_pi_of_rePos`, `riemannS_abs_le_log` | Vertical confinement + full `S(T)=O(log T)` (carrying `hζne`, `hlogcont`) |
| #500 | `RvMBacklundLogCont` | `continuousOn_logDeriv_zeta_segment`, `riemannS_abs_le_log_of_ne_zero` | Discharge `hlogcont` from ζ-analyticity → slimmed final theorem (only `hζne`) |

(No #488: that number was used elsewhere in the parallel stream.)

## Key ideas

- **Confinement.** The net argument change of `f` along a segment is `Im ∫ f'/f` (horizontal) or
  `(∫ f'/f).re` after an `i`-rotation (vertical). FTC via `HasDerivAt.clog_real` turns it into
  `arg f(end) − arg f(start)`. If `Re f > 0` the args live in `(−π/2, π/2)`, so the change is `< π`.
- **Either-sign / non-strict.** `logDeriv(−f) = logDeriv f`, so confinement applies to `±f`; and with
  `Re f ≥ 0` (allowing `Re = 0` at the partition endpoints, which are zeros of `Re ζ`) the args live in
  `[−π/2, π/2]`, giving `≤ π`. `f ≠ 0` keeps `f ∈ slitPlane` so the FTC still runs.
- **Counting.** Partition `[1/2,2]` at the zeros of `Re ζ`; each open piece is sign-constant, so
  contributes `≤ π`; summing gives `≤ (zeros+1)·π`. The zeros inject into the divisor support of `F_T`
  in a disk, whose weighted size Jensen's formula bounds by `O(log T)`.
- **Vertical leg is `O(1)`.** On `Re = 2`, `Re ζ(2+iy) ≥ 2 − π²/6 > 0`, so its argument change is `< π`.

## Reusable API gotchas (v4.34 / this island)

- `π` does NOT resolve to `Real.pi` under `open Complex` — write `Real.pi` explicitly.
- `Complex.abs` is removed; use `norm`/`normSq`; `abs_add` → `abs_add_le`.
- `AnalyticOnNhd.divisor_apply` / `.divisor_nonneg` live under `namespace MeromorphicOn` — call them as
  `MeromorphicOn.AnalyticOnNhd.divisor_apply` etc.
- Divisor value is `((analyticOrderAt f z).map (↑)).untop₀ : ℤ`; use
  `lift analyticOrderAt … to ℕ using (order ≠ ⊤)` + `ENat.map_natCast` (cleaner than `WithTop.coe`).
- `rcases (h : x = a) with rfl` can eliminate a *theorem parameter* `a`; use `Eq.ge`/`Eq.le`/`rw` instead.
- Path-composite continuity: `ContinuousAt.comp` mis-unifies the `+`; use the `scomp` derivative's
  `.continuousAt.continuousWithinAt` (the pattern used throughout the confinement lemmas).
- `finsum_eq_finset_sum_of_support_subset` → `finsum_eq_finsetSum_of_support_subset`.

## Verification

```bash
cd telperion/examples/li_positivity/lean
lake build                                    # full island incl. AxiomGuardLiPositivity
lake env lean AxiomGuardLiPositivity.lean     # #print axioms for every Backlund headline; 0 sorryAx
```

The guard is declared as a `lean_lib` in `lakefile.toml` and imports every Backlund module, so a bare
`lake build` compiles the whole closure.

## Next arc (not started): N(T), Riemann–von Mangoldt

`N(T) = θ(T)/π + 1 + S(T)`. Scaffolding already in `RvMDiffractionCore`:
`theta_eq_argChangeVert_gammaR` (θ IS an argument change), `zeta_total_argChange_eq_count` (box argument
principle → `2π·zero-count`), `argChangeVert_completedZeta_split`,
`completedZeta_argChange_critical_eq_zeta_add_theta`, and `argChangeL_sub_const` (the pole `+1`).
The remaining work is assembly (FE-fold; Λ-split into ζ→`πS`, Γℝ→`θ`, pole→`+1`; the final `N(T)`
statement), carrying the box-edge non-vanishing hypotheses honestly — realistically 3–5 PRs.

conjecture1_proved = False.
