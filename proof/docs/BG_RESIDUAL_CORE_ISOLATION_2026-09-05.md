# BG residual: independent verification + the hard core isolated to 4 tiny configs (2026-09-05)

> **CORRECTION (2026-09-05, v2 — supersedes the body below).** The "hard core = 4 tiny 3-hub
> paths; `(0,5)` fully rescued 18/18" conclusion in the body is an **ARTIFACT of two wrong
> premises**: (i) it modeled C's movers as **bare leaves** (`load=0`), whereas the genuine stuck
> configs have **load-5 arm movers** — with bare leaves a Kelmans consolidation always rescues,
> hiding the obstruction; (ii) it scanned a **bounded range** (deg_C ≤ 14), while the failures
> appear only at **large deg_C**. Re-run with the correct arm-mover model (independently, exact),
> the true picture matches the parallel session's flint self-correction: **all 5 residual cells
> fail the direct step at a finite deg_C** — thresholds `(2,5)=8, (1,5)=9, (1,4)=29, (3,5)=111,
> (0,5)=170`. `(0,5)` at its threshold is a **genuine Kelmans-local-max** (best Kelmans gain
> exactly 0) — but **dominated by a non-Kelmans arm-move C→A** (strictly raises π), so it refutes
> `(0,5)` *direct-step monotonicity*, **not** the Hdom *domination* goal. The engine-validation and
> direct-step-split sections below remain correct; the "core isolation" conclusion does not.
> Corrected self-verifying artifact: `residual_core_isolation.py` (v2, run() asserts the above).
> `conjecture1_proved = False`.

---


Independent re-derivation (own driver, own permanent) of the parallel session's residual-cell
findings. It **validates** their engine, **confirms** the direct-step split, and **sharpens** the
"anti-hubward rescues 54/54, zero genuinely stuck" claim. `conjecture1_proved = False`.
Self-verifying artifact: `proof/verification/residual_core_isolation.py` (`run()` asserts the split).

## What was independently verified (exact arithmetic)

1. **Their engine is exact.** `kelmans_mixed_load.pi_loaded` (a per-vertex factorization
   `∏F_of · psi_weighted`) equals the **literal** tree `per(L)/∏deg` on 8/8 configs incl. a mover
   config. Cross-checked with an independent matching-sum permanent DP
   (`per(L(tree)) = Σ_matchings ∏_{uncovered} deg`), itself validated against an exact Ryser
   permanent. Three independent methods agree.

2. **The direct-hubward split is real.** For cells `(1,4),(1,5),(2,5),(3,5)` the *direct* hubward
   Kelmans step (`kelmans_step(0,1)`) genuinely **decreases** π at in-scope (`z_C ≤ 3/23`)
   hub-mover configs (62 each). `(0,5)` also has 18 such failures. Matches the parallel session.

## The sharpening (corrects "anti-hubward rescues 54/54, zero genuinely stuck")

Across **all** in-scope direct-step failures, the strictly-π-increasing rescuer is:
- a **Kelmans (K)** move for most; OR
- the **leg→cherry (L)** move (= R2, already proven monotone) for the *bare-leaf-mover* configs —
  where the anti-hubward step is often **undefined** (`kelmans_step(1,0)` returns `None`: the
  acceptor A has no movers to relocate) or merely **neutral** (best Kelmans gain is *exactly 0*,
  an isomorphic recentering with no structural progress).

So "anti-hubward strictly rescues 54/54" is **too strong**: for the bare-leaf sub-family the
anti-hubward move doesn't exist / only recenters. But R-prog is **not** broken — `(L)` (proven)
covers that family.

## The genuine hard core — fully isolated, 4 tiny configs

With `K ∪ L` moves, `(0,5)` is **fully rescued (18/18)**, and each cb-heavy cell reduces to
**exactly ONE** config no `K` or `L` move strictly progresses:

| cell | the sole unrescued core (no movers, `z_C=3/23` boundary) |
|------|----------------------------------------------------------|
| (1,4) | 3-hub loaded path, loads `{A:1, B:4, C:5}` |
| (1,5) | 3-hub loaded path, loads `{A:1, B:5, C:5}` |
| (2,5) | 3-hub loaded path, loads `{A:2, B:5, C:5}` |
| (3,5) | 3-hub loaded path, loads `{A:3, B:5, C:5}` |

These are precisely what the **(H) hub-merge / de-load** rule (R5/R6) is for — consolidate the
loaded hubs into one de-loaded load-5-arm hub. R5's amplitude crux is `(26/23)^11 < 621/64`
(a *true* rational inequality, `3.51 < 9.70`), and the tex records the merge layer (R5/R6,
36-cell table, `R47StepMono`) as proven in Lean. `(H)` is a **size-changing amplitude
comparison at fixed n**, which the fixed-load-multiset `pi_loaded` engine does **not** test
directly (on 3 backbone nodes a "de-load" is just an isomorphic relabel).

## Consequence for the endgame (good news, not an obstruction)

The parallel session's "3 cells genuinely fail the direct step" is correct but does **not** block
the tree→hub reduction: the reduction never needs the *direct Kelmans* step for these configs.
Every in-scope failure admits a strictly-π-increasing move in `{K, L, H}` —
- `K` or `L` (proven) for all but 4 configs,
- `(H)`/R5 (proven merge layer) for the 4 three-hub cores.

The residual GenEnv cells were the wrong certification target: they try to certify the *direct
step* for configs the reduction resolves with a *different, already-proven* rule.

## Honest residual (the only thing still open here)

The one un-closed link is the **assembly**: that the reduction's move-selection actually applies
`(L)` / `(H)` (not the failing direct step) at these configs, and that `(H)`/R5 covers exactly the
4 three-hub cores at fixed n — i.e. wiring the proven rules into a well-founded descent. That is
the tree→hub termination obligation, not a new positivity fact. `conjecture1_proved = False`.

(Supersedes the coarser `BG_CRUX_ATTACK_2026-09-05.md`, which flagged the residual as needing a
Handelman/exact-recursion certificate on unsynced polynomials — this sharper result shows the
hard core is 4 explicit configs handled by proven rules, not a positivity gap.)
