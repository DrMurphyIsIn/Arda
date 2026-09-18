# RVM cumulative bridge — `RH_rvm_unconditional` discharged (2026-09-17)

**Status: CLOSED, kernel-checked, no `sorry`.** The RH registry node `RH_rvm_unconditional`
(the cumulative Riemann–von Mangoldt formula with an `O(log T)` remainder, no hypotheses) is
proved verbatim as `RvMBridge2.rvm_unconditional` in
`telperion/examples/rvm_bridge/lean/E6Bridge2.lean`, on the `rvm_bridge` island
(Lean `v4.33.0-rc2`, zeta-23-lean pin `fbdc36bb`), from Anthropic's zeta-23-lean internals.

**No RH progress is claimed.** This is the classical von Mangoldt (1905) / Backlund (1918) zero
count, Titchmarsh 9.4, machine-checked against Mathlib's `riemannZeta`.
`conjecture1_proved = False`.

Branch: `rh/rvm-cumulative` in the `arda-e6` worktree (not pushed; registry link and grant are
done separately, `telperion/missions/` untouched).

## What was proved

| theorem (namespace `RvMBridge2`) | statement |
|---|---|
| `zetaZeroCount_eq_Ncount T` | `RvMCount.zetaZeroCount T = Zeta23.Ncount 0 T` — the registry's `MeromorphicOn.divisor`-based rectangle count is Zeta23's `analyticOrderAt`-based window count |
| `int_mu_cumulative` | `∃ C ≥ 0, ∀ a b, 1 ≤ a ≤ b → |∫_a^b μ − (M b − M a)| ≤ C`, `M t = (t/2π) log(t/2π) − t/2π` (integrated Stirling on a general window) |
| `mainTerm_close` | `4 ≤ T ≤ T₂ ≤ T+1 → |M T₂ − M T| ≤ log T` |
| `rvm_cumulative_eventually` | `∃ C T₀, ∀ T ≥ T₀, |N(0,T] − M T| ≤ C log T` |
| `rvm_cumulative` | `∃ C > 0, ∀ T ≥ 2, |N(0,T] − M T| ≤ C log T` |
| `rvm_unconditional` | the node statement, **verbatim**: `∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → \|((RvMCount.zetaZeroCount T : ℕ) : ℝ) − (T / (2 * π) * Real.log (T / (2 * π)) − T / (2 * π) + 7 / 8)\| ≤ C * Real.log T` |

The definition `RvMCount.zetaZeroCount` is mirrored verbatim from
`telperion/missions/rh/lean/Statements/RHDefs.lean` (same namespace), and the theorem line is
the node statement of `telperion/missions/rh/lean/Statements/RH_rvm_unconditional.lean`
verbatim; `examples/rvm_bridge/generate.py --check` now enforces both (extended in this change)
and is green.

## Exact `#print axioms` output

`lake build` (8821 jobs, incremental) then `lake env lean AxiomGuardRvMBridge.lean`, verbatim:

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

No `sorryAx` anywhere. `python examples/rvm_bridge/generate.py --check`:

```
rvm_bridge: node statement + 2 mirrored defs + toolchain pin match (examples/rvm_bridge/lean/E6Bridge.lean); RH node statement + 1 mirrored def match (examples/rvm_bridge/lean/E6Bridge2.lean)
```

## What remains

Nothing for this node. There is no `E6Bridge2WIP.lean`; every lemma in the module is closed.

## Proof outline and the Zeta23 lemmas used

The E6 probe (Part B) was right that the cumulative `O(log T)` form is not a corollary of the
STATED upstream theorems (summing the dyadic clause gives `O(log² T)`), and right that it is
derivable from the general-window internals. The assembly is the upstream's own
`Zeta23.RvM.rvM_main_param` (`Zeta23/RvM/MainTerm.lean`) re-run on a window whose bottom is
fixed and whose top tracks `T`:

1. **Seam** (`zetaZeroCount_eq_Ncount`). On the open strip `U = {0 < Re < 1}` zeta is analytic
   (`Zeta23.RvM.analyticOnNhd_riemannZeta`, since `1 ∉ U`), so
   `MeromorphicOn.AnalyticOnNhd.divisor_apply` gives
   `divisor ζ U ρ = ((analyticOrderAt ζ ρ).map ↑).untop₀`, whose `toNat` is `zeroMult ρ` by
   `ENat.recTopCoe` (both sides send `⊤` to `0`). Off zeros `analyticOrderAt = 0`
   (`analyticOrderAt_eq_zero`), so `finsum_mem_inter_support_eq` collapses the registry's
   rectangle to Zeta23's `zerosIn 0 T`. No finiteness argument is needed here: the two finsums
   are literally equal; finiteness of the support is inherited from Zeta23's
   `zerosIn_finite` whenever `Ncount` is manipulated.
2. **Main term calculus.** `hasDerivAt_mainTerm` (`M' = (1/2π) log(τ/2π)` for `τ > 0`),
   `integral_logMain_eq` (FTC on `[a, b]`, `0 < a ≤ b`), both adapted from the upstream's dyadic
   `MuInts.integral_main_eq`.
3. **Integrated Stirling on a general window** (`int_mu_cumulative`). From
   `Zeta23.StirlingVert.mu_stirling` (`|μ(τ) − (1/2π) log(|τ|/2π)| ≤ C/τ²`, `|τ| ≥ 1`):
   `∫_a^b μ = (M b − M a) + ∫_a^b (μ − main)`, and `|∫_a^b (μ − main)| ≤ ∫_a^b C/τ² = C/a − C/b ≤ C`.
   Continuity of `μ` is `Zeta23.mu_smooth.continuous`.
4. **Lipschitz bound** (`mainTerm_close`): `|M T₂ − M T| = |∫_T^{T₂} (1/2π) log(τ/2π)| ≤ log T`
   on `[T, T+1]`, `T ≥ 4`, via `intervalIntegral.norm_integral_le_of_norm_le_const`.
5. **Eventual assembly** (`rvm_cumulative_eventually`). Fix `T₁ ∈ [4, 5]` zero-free
   (`Zeta23.RvM.exists_goodHeight 4`) and get `A₀` (`zeta_local_zero_count`), `Cμ` (step 3),
   `CB, TB` (`Zeta23.RvM.backlund_horizontal`). For `T ≥ max TB 6` pick `T₂ ∈ [T, T+1]` zero-free.
   Then, with `Zeta23.RvM.N_eq_halfContour_completedZeta`,
   `halfContour_completedZeta_split`, `gamma_side`:
   `N(T₁,T₂] = (1/π) Im halfContour(ζ'/ζ) + ∫_{T₁}^{T₂} μ`.
   Window arithmetic (`Zeta23.Ncount_add`): `N(0,T] = N(0,T₁] + N(T₁,T₂] − N(T,T₂]`, and
   `N(T,T₂] ≤ N(T,T+1] ≤ A₀ log(T+3) ≤ 2A₀ log T` (`Ncount_mono`).
   The ζ half-contour: the bottom edge at `T₁` is a FIXED real number `K₁` (no bound needed);
   the right edge is `≤ π` (`vertical_two`); the top edge is `≤ |CB| log T₂ ≤ 2|CB| log T`
   (Backlund at the zero-free `T₂ ≥ TB`). The Γ-side is `M T₂ − M T₁ + O(Cμ)`, and
   `|M T₂ − M T| ≤ log T`. Every constant is absorbed by `log T ≥ 1` (`T ≥ 6 > e`), giving
   `C = K₀ + 2A₀ + 2|CB| + 1` with `K₀ = N(0,T₁] + |M T₁| + K₁/π + 1 + Cμ`.
6. **Finite range** (`rvm_cumulative`). For `2 ≤ T < T₀' = max T₀ 6`: `N(0,T] ≤ N(0,T₀']`
   (`Ncount_mono`), `|M T| ≤ T₀' (log T₀' + 1)`, so `|N − M| ≤ K ≤ (K / log 2) log T`;
   `C' = max C (K / log 2) + 1 > 0`.
7. **Node statement** (`rvm_unconditional`): rewrite by the seam, note the node's main term is
   `M T + 7/8` definitionally, and `7/8 < 2 log T` (`Real.log_two_gt_d9`), so `C + 2` works.

Lemma shapes that were sufficient as black boxes, with no upstream edits: everything named
above. Nothing from Zeta23 was insufficient; the only genuinely new proof work is steps 2–4
and 6 (elementary real analysis, about 200 lines) plus the seam.

## Files changed

- `telperion/examples/rvm_bridge/lean/E6Bridge2.lean` — NEW (559 lines), the second bridge.
- `telperion/examples/rvm_bridge/lean/lakefile.toml` — `E6Bridge2` as a `lean_lib`, in `defaultTargets`.
- `telperion/examples/rvm_bridge/lean/AxiomGuardRvMBridge.lean` — imports `E6Bridge2`; guards the
  five new theorems and the six consumed upstream internals.
- `telperion/examples/rvm_bridge/generate.py` — drift check extended: the RH node statement must be
  contained verbatim in `E6Bridge2.lean`, and `RvMCount.zetaZeroCount` must match `RHDefs.lean`.
- `telperion/examples/rvm_bridge/lean/README.md` — second-bridge section, updated tables and
  recorded axiom output.
- `.github/workflows/telperion-lean-e2e.yml` — drift-check step name only (the existing
  `lake build` / axiom-guard steps already cover the new module through `defaultTargets`).

## Consumers unblocked (for the registry/grant pass, done separately)

`RH_corridor_bound` and the other three consumers listed in the roadmap as waiting on
`RH_rvm_unconditional` can now be linked to `RvMBridge2.rvm_unconditional` on the `rvm_bridge`
island (cross-island grant by normalized containment, same precedent as E6).
