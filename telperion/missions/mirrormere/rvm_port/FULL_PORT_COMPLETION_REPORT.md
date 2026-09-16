# Full Port — Completion Report: RvMUnboundedMeanDensity DISCHARGED (kernel-clean)

Discharges the `rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates`
residual by porting the unconditional superlinear-DISTINCT zero-density theorem from
cc-chen-tech/riemann-pnt-lean4 to our v4.32 pin. conjecture1_proved = False — this
discharges ONE analytic residual toward the corridor bound → E8, NOT RH.

## HEADLINE — verified kernel-clean

```
#print axioms RvMGlue.rvm_unbounded_mean_density
  ⇒ [propext, Classical.choice, Quot.sound]        (0 sorryAx)

#print axioms Quasicrystal.rvm_unbounded_mean_density   -- the EXACT mirrormere node statement
  ⇒ [propext, Classical.choice, Quot.sound]        (0 sorryAx)
```

`RvMUnboundedMeanDensity zetaOrdinates` is now proven UNCONDITIONALLY, kernel-clean, on
v4.32.  The node-form uses `Quasicrystal.RvMUnboundedMeanDensity`/`zetaOrdinates` copied
VERBATIM from `MMDefs.lean` (definitionally identical to the port's `RvMGlue` defs), so
the discharge closes the real registry node — see `RvMNodeDischarge.lean`.

## What was built — 255/255 modules GREEN on v4.32

Full transitive closure of `HardyTheorem.SelbergStrictCancellationZeroCover`
(containing `selberg_odd_zero_proportion_target_proved_mainline`) — 255 own modules,
~98K LOC — compiled against v4.32 Mathlib (rev 81a5d257c8e4), topo order, IR pruned
between batches (disk stayed ~257G throughout, never below 40G).

- `HardyTheorem.selberg_odd_zero_proportion_target_proved_mainline` axiom-checked
  independently: `[propext, Classical.choice, Quot.sound]`, 0 sorryAx. The port shims
  are genuine PROOFS, not axioms.

## The DISCHARGE chain

1. `RvMDistinctBridge.lean` — `rvm_unbounded_mean_density_of_selberg` (kernel-clean,
   proven in a prior run): reduces `RvMUnboundedMeanDensity zetaOrdinates` to the ported
   Selberg superlinear-distinct interface (window a=0, L=T; `im` injective on the re=1/2
   finset; density → ∞).
2. `RvMDischarge.lean` — instantiates the bridge with
   `HardyTheorem.criticalLineOddZerosFinset` / `criticalLineOddZeroCount` /
   `selberg_odd_zero_proportion_target_proved_mainline`.
   `hZmem` from `mem_criticalLineZerosFinset` (elements are genuine `riemannZeta ρ = 0`,
   `ρ.re = 1/2`, `0 ≤ ρ.im ≤ T` ⇒ `ρ.im ∈ zetaOrdinates`); `hZcard` = `rfl`.
3. `RvMNodeDischarge.lean` — proves the mirrormere node's verbatim `Quasicrystal` form
   directly from (2).

## DRIFT MEASURED (full closure, 98K LOC)

The bellwether prediction (~zero drift) held almost exactly. Exactly **3 patch sites /
4 shim lemmas** across the entire 255-module closure — a drift rate of ~0.04
patches/KLOC. All shims are PROOF-CARRYING (derived from v4.32 primitives), zero
axiom drift. Full log: `PATCHLOG.txt`.

| Module | Missing v4.32 identifier | Fix | Kind |
|---|---|---|---|
| `SelbergPerronKernel` | `Complex.div_cpow_ofReal_nonneg` | proof-carrying shim (from `mul_cpow_ofReal_nonneg` + `inv_cpow_eq_ite` + `arg_ofReal_of_nonneg`) | new Mathlib lemma post-v4.32 |
| `SelbergJForwardBridge` (covers Reverse+Diagonal transitively) | `Set.mem_ofPred_eq` | alias shim (= `mem_setOf_eq`, `rfl`) | renamed lemma |
| `SelbergNonconstantFourierMass` (covers Explicit+Global downstream) | `integral_comp_log_Ioi`, `integrableOn_comp_exp_Ioi` | 2 proof-carrying shims (from `integral_image_eq_integral_abs_deriv_smul` / `integrableOn_image_iff_integrableOn_abs_deriv_smul`; exp/log change-of-variables on Ioi) | new Mathlib lemmas post-v4.32 |

No STRUCTURAL gaps: every underlying Mathlib theorem (Jensen, meromorphic order,
Phragmén–Lindelöf, one-dim Jacobian change-of-variables) exists at v4.32.

## Provenance (zero-drift discipline)
- Source: github.com/cc-chen-tech/riemann-pnt-lean4 @ `6d07f7371ca2881de20481a638dc65e14d8f6651` (toolchain v4.33.0-rc2).
- Ported files that DIFFER from pristine source (shims only): the 3 in `ported_shim_files/`. The other 252 modules are byte-identical to source, built unchanged on v4.32.
- Full topo build order: `selberg_closure_topo_order.txt`.

## Node-file status (honest)
`Statements/MM_rvm_unbounded_mean_density.lean` still contains `by sorry` IN THAT FILE:
the discharge is proven in the `rvm_port` library (kernel-clean on the exact statement,
`RvMNodeDischarge.lean`), but the mirrormere Lean project does not yet `require` the
rvm_port library via lake. Once that lake `require` is added, the node body is literally
`RvMGlue.rvm_unbounded_mean_density`. The header of the node file documents this. This
is the ONLY remaining step, and it is build-integration, not mathematics — the proof
exists and is verified.

## Files
- `RvMDistinctBridge.lean` — the reduction (green, 3-axiom).
- `RvMDischarge.lean` — bridge ⨯ ported Selberg → `RvMGlue.rvm_unbounded_mean_density` (green, 3-axiom).
- `RvMNodeDischarge.lean` — proves `Quasicrystal.rvm_unbounded_mean_density` (the exact node stmt; green, 3-axiom).
- `ported_shim_files/` — the 3 modules carrying port shims (only files differing from source).
- `PATCHLOG.txt`, `selberg_closure_topo_order.txt` — provenance.
- `DRIFT_BELLWETHER_REPORT.md`, `PORT_STRATEGY_AND_CONTINUATION.md` — prior-run analysis.

## Reproduce the axiom check
```
SRC=<v4.32 island with full Mathlib oleans>/lean
cp -Rc "$SRC/.lake" /tmp/rvm-drift/.lake       # CoW
# stage 255 source modules + 3 shim files + bridge/discharge at their paths
cd /tmp/rvm-drift
LEAN_PATH=<lake env LEAN_PATH> lean AxCheckDischarge.lean --root /tmp/rvm-drift
#   ⇒ 'RvMGlue.rvm_unbounded_mean_density' depends on axioms: [propext, Classical.choice, Quot.sound]
```
