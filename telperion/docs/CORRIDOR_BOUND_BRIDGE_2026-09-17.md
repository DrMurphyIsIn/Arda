# Corridor bound bridge — `RH_corridor_bound` discharged (2026-09-17)

**Status: CLOSED, kernel-checked, no `sorry`.** The RH registry node `RH_corridor_bound`
(routes-roadmap milestone E7 = A3 = B5 = D6, the unique four-consumer blocker: the classical
good-ordinate lemma) is proved verbatim as `RvMBridge3.corridor_bound` in
`telperion/examples/rvm_bridge/lean/E6Bridge3.lean`, on the `rvm_bridge` island
(Lean `v4.33.0-rc2`, zeta-23-lean pin `fbdc36bb`), from Anthropic's zeta-23-lean internals plus
Mathlib's completed-zeta functional equation.

**No RH progress is claimed.** This is Davenport ch. 15–17 / Titchmarsh Theorem 9.6(A): for every
`T ≥ 2` some height `T' ∈ [T, T+1]` has a zero-free horizontal segment `−1 ≤ σ ≤ 2` on which
`|ζ'/ζ(σ + iT')| ≤ C log² T`. It is the standard input for contour shifts in the explicit
formula. `conjecture1_proved = False`.

Branch: `rh/corridor-bound` in the `arda-corridor` worktree (on top of `rh/rvm-cumulative`;
not pushed; registry link and grant are done separately, `telperion/missions/` untouched).

## What was proved

| theorem (namespace `RvMBridge3`) | statement |
|---|---|
| `logDeriv_Gammaℝ_shift` | `Im u ≠ 0 → Γℝ'/Γℝ(u) = Γℝ'/Γℝ(u+2) − 1/u` |
| `norm_logDeriv_Gammaℝ_le_log` | `0 < Re s ≤ 4, |Im s| ≥ 2 → ‖Γℝ'/Γℝ(s)‖ ≤ log(|Im s|+3) + 5` |
| `norm_logDeriv_Gammaℝ_le_log_strip` | `−1 ≤ Re s ≤ 2, |Im s| ≥ 2 → ‖Γℝ'/Γℝ(s)‖ ≤ log(|Im s|+3) + 6` |
| `zeta_ne_zero_of_reflect` | `Im s ≠ 0, ζ(1−s) ≠ 0 → ζ(s) ≠ 0` |
| `logDeriv_zeta_reflect` | `Im s ≠ 0, Re s < 1, ζ(1−s) ≠ 0 → ζ'/ζ(s) = −ζ'/ζ(1−s) − Γℝ'/Γℝ(1−s) − Γℝ'/Γℝ(s)` |
| `Ncount_unit_windows`, `Ncount_six_windows`, `card_zerosIn_le` | `N(a, a+k] = Σ_{i<k} N(a+i, a+i+1]`; `N(a, a+6] ≤ 6 A₀ log(|a|+9)`; `#zeros in (a,b] ≤ N(a,b]` |
| `good_height_real` | `∃ C > 0, ∀ T ≥ 7 (real), ∃ R ∈ [T, T+1], ∀ s, Im s = ±R → 1/2 ≤ Re s ≤ 2 → ζ(s) ≠ 0 ∧ ‖ζ'/ζ(s)‖ ≤ C log²(T+3)` |
| `corridor_large` | the node conclusion for all `T ≥ 7` |
| `corridor_small` | `∃ M ≥ 0, ∀ T ∈ [2, 7], ∃ T' ∈ [T, T+1]`, zero-free segment and `‖ζ'/ζ‖ ≤ M` |
| `corridor_bound` | the node statement, **verbatim**: `∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Set.Icc T (T + 1), (∀ σ ∈ Set.Icc (-1 : ℝ) 2, riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0) ∧ ∀ σ ∈ Set.Icc (-1 : ℝ) 2, ‖logDeriv riemannZeta ((σ : ℂ) + (T' : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2` |

The theorem line is the node statement of
`telperion/missions/rh/lean/Statements/RH_corridor_bound.lean` verbatim (name and binder-free
form). `examples/rvm_bridge/generate.py --check` now enforces containment for this node too
(extended in this change) and is green:

```
rvm_bridge: node statement + 2 mirrored defs + toolchain pin match (examples/rvm_bridge/lean/E6Bridge.lean); RH node statement + 1 mirrored def match (examples/rvm_bridge/lean/E6Bridge2.lean); RH corridor node statement matches (examples/rvm_bridge/lean/E6Bridge3.lean)
```

An additional clean-context check (scratch, not committed): a file with `import E6Bridge3` and
only `open Complex` states the registry theorem verbatim and closes it by
`exact RvMBridge3.corridor_bound`; `#print axioms` gives the same three axioms and the printed
term shows Mathlib's `logDeriv` and `Complex.I` (no shadowing by any `Zeta23` name).

## Exact `#print axioms` output

`lake build` (8823 jobs, incremental) then `lake env lean AxiomGuardRvMBridge.lean`, verbatim:

```
'RvMBridge.rvm_unbounded_mean_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.eventually_Ncount_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.int_mu_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.zetaZeroCount_eq_Ncount' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.good_height_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.logDeriv_zeta_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.zeta_ne_zero_of_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.logDeriv_Gammaℝ_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.norm_logDeriv_Gammaℝ_le_log_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'Zeta23.WeilEF.zeta_logDeriv_partial_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.exists_far_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.logDeriv_completedZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.logDeriv_completedZeta_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.StirlingVert.digamma_stirling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` anywhere. The module compiles with no warnings.

## What remains

Nothing for this node. There is no `E6Bridge3WIP.lean`; every lemma in the module is closed.

The effective-constant form (an explicit `C`) is NOT delivered; it is the standing-queue
follow-up named in the node's own header. All constants here come from `∃`-form upstream
inputs (`zeta_logDeriv_partial_fraction`, `zeta_local_zero_count`) and from a compactness bound
(`corridor_small`), so `C` is not extracted.

## Proof outline and the lemma names used

The upstream (zeta-23-lean) already contains, for its Weil explicit formula, the good-height lemma
`Zeta23.WeilEF.good_heights_at`: for INTEGER `j ≥ 7` some `R ∈ [j, j+1]` has `ζ ≠ 0` and
`‖ζ'/ζ‖ ≤ C log²(j+3)` on `Im s = ±R`, `1/2 ≤ Re s ≤ 2`. Two gaps separate it from the node:
the node's window `[T, T+1]` is at a REAL `T` (an integer-height good ordinate does not land in
`[T, T+1]` in general: with `⌊T⌋` and `⌈T⌉` one can get `R₁ < T` and `R₂ > T+1`), and the node's
segment reaches down to `σ = −1`. Neither gap is a corollary of the stated upstream theorems; both
are closed here.

1. **Γℝ log-derivative off the real axis** (§A). `Γℝ` is nonvanishing and differentiable at every
   non-real point (`Gammaℝ_eq_zero_iff`, `Complex.differentiableAt_Gamma`). The shift
   `logDeriv Γℝ u = logDeriv Γℝ (u+2) − 1/u` follows from Mathlib's `Gammaℝ_add_two` as a germ
   identity plus `logDeriv_mul`. The bound `‖Γℝ'/Γℝ(s)‖ ≤ log(|Im s|+3) + 5` on `0 < Re s ≤ 4`,
   `|Im s| ≥ 2` is `Zeta23.RvM.logDeriv_Gammaℝ` (`= −(log π)/2 + ψ(s/2)/2`) plus
   `Zeta23.StirlingVert.digamma_stirling` (`‖ψ(w) − log w + 1/(2w)‖ ≤ 3/(Im w)²`); one shift
   extends it to `−1 ≤ Re s ≤ 2` with `+6`. (These three lemmas exist upstream in
   `Zeta23.XiPrime.*`, a separate challenge tree not built on this island; they are transcribed
   with attribution rather than imported.)
2. **Reflection** (§B). For `Im s ≠ 0`: `ζ = Λ/Γℝ` near `s` (`riemannZeta_def_of_ne_zero`), so
   `ζ'/ζ(s) = Λ'/Λ(s) − Γℝ'/Γℝ(s)` (`logDeriv_div`, `differentiableAt_completedZeta`);
   `Λ'/Λ(s) = −Λ'/Λ(1−s)` (`Zeta23.WeilEF.logDeriv_completedZeta_one_sub`); and on the right
   half-plane `Λ'/Λ(1−s) = Γℝ'/Γℝ(1−s) + ζ'/ζ(1−s)` (`Zeta23.WeilEF.logDeriv_completedZeta`).
   Zero-freeness transfers the same way: `ζ(s) = 0 ⇒ Λ(s) = 0 = Λ(1−s) ⇒ ζ(1−s) = 0`.
3. **Real-height good ordinate** (§C, `good_height_real`). Transcribes the shape of
   `Zeta23.WeilEF.good_heights_at` with `T` real: the ordinates of the nontrivial zeros in
   `(T−3, T+3]` and the negated ordinates of those in `(−T−4, −T+2]` form a finset `S` with
   `|S| ≤ 24 A₀ log(T+3)` (six unit windows of `Zeta23.RvM.zeta_local_zero_count` each side,
   via `Zeta23.Ncount_add` and `zetaZeroConfig.ncard_le_finsum_mult`);
   `Zeta23.WeilEF.exists_far_point S T` (already stated for a real endpoint) gives
   `R ∈ [T, T+1]` at distance `δ = 1/(2(|S|+1))` from `S`; then for `Im s = ±R`,
   `1/2 ≤ Re s ≤ 2`, every zero in the Landau ball about `2 ± iR` has its signed ordinate in `S`,
   so `ζ(s) ≠ 0` and `Zeta23.WeilEF.zeta_logDeriv_partial_fraction` (`|t| ≥ 6`) gives
   `‖ζ'/ζ(s)‖ ≤ C log(R+3) (1 + 2(|S|+1)) ≤ 2C(48A₀+3) log²(T+3)`.
4. **`T ≥ 7`, full segment** (§D, `corridor_large`). `σ ≥ 1/2`: step 3 at `s = σ + iR`.
   `σ < 1/2`: step 3 at `u = 1 − s = (1−σ) − iR` (`Re u ∈ (1/2, 2]`, `Im u = −R`, the other sign
   of the same good height), then step 2 and step 1: `‖ζ'/ζ(s)‖ ≤ C₁ log²(T+3) + 2 log(R+3) + 11
   ≤ (4C₁ + 15) log² T` using `log(T+3), log(R+3) ≤ 2 log T` and `log T ≥ 1`.
5. **`2 ≤ T ≤ 7`** (§E, `corridor_small`). `K = [−1,2] × [2,8]` is compact
   (`isCompact_Icc.reProdIm`); its zeros are finite (`Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact`),
   `S` = their ordinates, `δ = 1/(2(|S|+1))`. `K_δ = K ∩ {δ-far from S}` is compact
   (`IsCompact.inter_right`, `isClosed_biInter`), `ζ ≠ 0` on it (a zero's own ordinate would be
   in `S` at distance 0), so `ζ'/ζ` is continuous on it (`Zeta23.WeilEF.analyticAt_riemannZeta`)
   and bounded by `M` (`IsCompact.exists_bound_of_continuousOn`). For `T ∈ [2, 7]`,
   `exists_far_point S T` gives `T' ∈ [T, T+1] ⊂ [2, 8]` with the whole segment inside `K_δ`.
6. **Node statement** (§F, `corridor_bound`): `C = max C₁ (M / log² 2) + 1`, using
   `log T ≥ log 2 > 0` on the small range.

Lemma shapes that were sufficient as black boxes, with no upstream edits: everything named above.
Nothing from Zeta23 was insufficient. The only genuinely new proof work is the real-height
re-run of the selection (step 3, about 150 lines transcribed and adapted), the reflection
identity (step 2), the Γℝ strip bound (step 1) and the compactness argument (step 5).

## Files changed

- `telperion/examples/rvm_bridge/lean/E6Bridge3.lean` — NEW (about 640 lines), the third bridge.
- `telperion/examples/rvm_bridge/lean/lakefile.toml` — `E6Bridge3` as a `lean_lib`, in `defaultTargets`.
- `telperion/examples/rvm_bridge/lean/AxiomGuardRvMBridge.lean` — imports `E6Bridge3`; guards the
  eight new theorems and the six consumed upstream inputs.
- `telperion/examples/rvm_bridge/generate.py` — drift check extended: the RH corridor node statement
  must be contained verbatim in `E6Bridge3.lean` (no mirrored definitions: the statement is in
  Mathlib vocabulary only).
- `telperion/examples/rvm_bridge/lean/README.md` — third-bridge section, updated tables, recorded
  axiom output, NOTICE list.
- `.github/workflows/telperion-lean-e2e.yml` — unchanged: the existing `lake build` / axiom-guard
  steps cover the new module through `defaultTargets`.

## Consumers unblocked (for the registry/grant pass, done separately)

Roadmap milestones A3, B5, D6 and the limit explicit formula all consume `RH_corridor_bound`;
they can now be linked to `RvMBridge3.corridor_bound` on the `rvm_bridge` island (cross-island
grant by normalized containment, same precedent as E6 and the cumulative RvM bridge).
