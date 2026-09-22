# wall_barrier -- barrier analysis for the RH wall

Branch `wall/barrier`, 2026-09-18.  `conjecture1_proved = False`.

> **RETRACTED IN PART — 2026-09-19.** `FEUniformBarrierAM`'s barrier reading is **sound but
> empty**, refuted in the kernel by `telperion/examples/wall_adversary/lean/BarrierScopeXR.lean`
> (`barrier_silent`, `transfer_to_member_fails`, `uniform_refutation_decides_nothing`). The
> theorems here remain valid; they refute only a universal over the bundle, while every wall
> clause is about ONE member. `poly_refutes_poor_bundle` in this very module shows `s * (s - 1)`
> already refutes the bundle, so the Davenport–Heilbronn witness adds nothing. Do not register
> `RH_barrier_fe_uniform`. `WallBarrierAM` (the orientation-only result) is unaffected.

Two sorry-free Lean modules, both elaborated with `lake env lean` against the v4.34
rh-statements island (`leanprover/lean4:v4.34.0-rc1`); every theorem's `#print axioms`
returns `[propext, Classical.choice, Quot.sound]`.

* `WallBarrierAM.lean` -- the symmetry barrier, sharply scoped.  FORCED generalized to
  arbitrary reflection-invariant maps (`no_invariant_orients`), and the scope limit
  (`invariant_detects`): reflection invariance obstructs ORIENTATION only, never RH.
* `FEUniformBarrierAM.lean` -- the FE-uniformity barrier.  The bundle `FEBarrier.FEData`
  (entire, self-dual, order one), the transfer theorems that turn one off-line witness into
  a refutation of every route's wall clause, and `mobius_disc_iff`, the arithmetic-free
  geometric content of Li's criterion.

The Davenport-Heilbronn off-line zero is a HYPOTHESIS of every theorem here, discharged
outside Lean by the Arb winding certificate of `telperion/docs/QC_DH_SCOUT.md` section 4.

Design memo, scope limits and the exact registry operations:
`telperion/docs/RH_BARRIER_FE_UNIFORMITY_DESIGN_2026-09-18.md`.

No RH progress is claimed.  These results bound a class of arguments; they do not advance
any of them.

## Honest grading

`poly_refutes_poor_bundle` proves, unconditionally and in the kernel, that `FEData` as
written is refuted by the polynomial `s * (s - 1)`.  So what is delivered today is the
TRANSFER SCHEMA plus a measurement of its reach, not yet the barrier over the bundle that
covers the program's actual arguments.  Enriching `FEData` with a normalized Dirichlet-series
clause is the first task; see section 7 of the design memo.
