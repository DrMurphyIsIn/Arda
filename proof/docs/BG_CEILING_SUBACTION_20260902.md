# BG classical ceiling: an explicit additive SUBACTION closes the core (2026-09-02)

**Status: MAJOR reduction, empirically decisive, NOT yet kernel-proven. `conjecture1_proved = False`.**

## The reformulation (why this is different from the failed cap)

The branch ceiling `∀ b, bell b ≤ 0` telescopes per-vertex:
`bell b = Σ_{v∈b} e_v`, `e_v = log(1 + S_v/d_v) − F*`, `S_v = Σ_{child c} bY(c)`, `d_v = deg(v)`,
`F* = log(621/64)/11`.  (Equivalently: ceiling ⟺ geomean of the cavity fields
`h_v = d_v/(d_v+S_v) ∈ (0,1]` is `≥ W^(1/11)`, `W=64/621`.)

An **additive subaction** is a function `ρ` on vertex-states with `ρ ≥ 0` and, for every vertex,
```
        (SUB)   e_v + ρ(v)  ≤  Σ_{child c} ρ(c).
```
Summing over `b` telescopes to `bell b ≤ −ρ(root) ≤ 0` — the ceiling. This is the ergodic-
optimization / Aubry–Mather "calibrated subaction" (a coboundary correction of the potential).

**Why additive beats the multiplicative cap `Bcap`.** The refuted `Le1Step` was multiplicative
(`W·a^11·∏ψ ≤ ψ`): a product of slightly-loose factors overshoots — that is exactly why it was
FALSE (`proof/docs/BG_LE1STEP_REFUTED_20260902.md`). `(SUB)` is a *sum* of local terms; slight
looseness stays bounded and telescopes. The subaction cannot hit that failure mode.

## The explicit witness (verified)

The maximizer is a **period-2 parity oscillation onto a single finite 3-state tie** (the 5-arm
cherry-spider, n=11), NOT aperiodic — so a **finite-partition, piecewise-affine subaction exists**
(Bousch). The high-degree tail is trivially slack (more children ⇒ more RHS credit). An
**affine-per-degree** `ρ(d,μ) = a_d + b_d·μ` suffices on the compact core:

| d | ρ(d,μ) | notes |
|---|--------|-------|
| 1 (leaf) | `F*` | exact tie anchor |
| 2 | `≈ −0.0609 + 0.2057·μ`, through `(μ=1/3, 2F*−log(3/2))` | cherry = tie anchor |
| 3 | `≈ −0.0116 + 0.0578·μ` | free (slack) |
| ≥4 | `0` | incl. the hub `(d=6, μ=3/23)` ⇒ ρ=0 |

**Only 3 constraints are tight (active), and they are exactly the tie's 3 states**:
`ρ(leaf)=F*`; cherry `e_cherry+ρ(2,1/3)=ρ(leaf)` ⇒ `ρ(2,1/3)=2F*−log(3/2)`; hub
`e_hub+0=5·ρ(2,1/3)` ⇒ `ρ(2,1/3)=(log(23/18)−F*)/5`. Consistency of the two is the exact
`27·23 = 621` identity (`(3/2)^5·(23/18)=621/64`, `11F*=log(621/64)`). Everything else is slack ⇒
the non-tie coefficients are FREE and can be taken with rational slack.

## Verification (decisive, empirical)

- **All 376,464 branches n≤16**: worst `(SUB)` margin `−4e-6` (float noise at the pinned leaf).
- **Continuous interior grid** (parents deg 2–6, children deg 1–10, incl. tail): worst `+1e-6` (at
  the cherry — the equality), tail (child deg≥7) worst `+0.022`. The gap is concave in the child-
  message sum ⇒ **box corners give the worst case** (this is the parallel session's ① endpoint lever).

## What this reduces the ceiling to (the remaining proof)

1. **Lean additive bridge** `ceiling_of_subaction : (ρ≥0 ∧ ∀v (SUB)) → ∀b bell b≤0` — the additive
   analog of the proven `BGSCLGStepBridge.ceiling_of_gstep`; provable sorry-free now.
2. **Finitely many per-cell inequalities** on the compact core (deg ≤ 6), each an affine-in-μ box
   check (① endpoints) + a `log(1+S/d)` enclosure (turan/jensen rational bounds); slack everywhere
   except the tie.
3. **A high-degree tail lemma** (deg ≥ 7: `Σ_c ρ(c) − ρ(v) − e_v ≥ 0` with large slack).
4. **The tie identity** `27·23 = 621` handled exactly (composes with `TightCapEnclosure`/`acl_d6`).

## Honest scope

This is an explicit, verified WITNESS + a clean reduction — not a kernel proof. The subaction values
at the tie are irreducibly transcendental (`F*`, `log(3/2)`); the proof is enclosure-conditional. No
`sorry` has been discharged yet. Dispelled en route: aperiodicity (maximizer is period-2/finite) and a
hard countable tail (slack). `conjecture1_proved = False` until the full chain lake-builds.

Repro: `/tmp/boxlp.py` (solve), `/tmp/verify2.py` (376k-tree + interior-grid validation).
