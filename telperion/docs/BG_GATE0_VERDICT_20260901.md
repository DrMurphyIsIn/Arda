# Gate 0 verdict: broom `B(c)` is NOT the global maximizer — re-scope required (2026-09-01)

Executing the `sorted-conjuring-clock` plan's **Gate 0** (de-risk: *verify the broom actually dominates before
proving it does*). The gate **fired**: the target of the plan's Lemma A / Prong A is **false**. But the
asymptotic upper bound does **not** need it — so Prong B survives, re-scoped. `conjecture1_proved = False`.

## The finding (exact, both normalizations)

The single-hub broom `B(c)` (one hub, `c` cherries) is **NOT** the size-`2c+1` maximizer of `total` for large `c`:

| size | `B(c)` (rooted) | caterpillar (rooted) | verdict |
|---|---|---|---|
| 21 | `B(10)=75.14` | `[3,3,3]=74.08` | B(c) wins (barely) |
| 27 | `B(13)=254.86` | `[4,4,4]=257.21` | **B(c) LOSES** |
| 33 | `B(16)=862.91` | `[5,5,5]=887.22` | **B(c) LOSES** |

Unrooted `rho` agrees (`[4,4,4]` beats `B(13)` by `5.9`; `[5,5,5]` beats `B(16)` by `36`). The asymptotic
per-vertex free energies make it structural:

```
S(k,5)  (star of B(5)-brooms) : 0.20659 = F*     <- the TRUE maximizer
caterpillar (uniform a=7)     : 0.20510
single-hub B(c)               : 0.20273          <- the WORST of the three
```

So **`B(c)` is the *worst* of the three asymptotically.** The plan's Lemma A — *"`B(c)` maximizes `total` at
size `2c+1`"* — is false, and the "optimum packs cherries into one hub = `B(c)`" step of the analytic
unification (`BG_BRANCH_UNIFICATION`, commit `1e391b5`) is wrong: the single-child lemma forces the *children*
to be cherries but leaves the **hub arrangement** free, and the optimal arrangement is the **nested** `S(k,5)`
(a hub of `B(5)`-brooms), not the **flat** `B(c)`.

## Why the asymptotic bound survives (only the LOCAL lemma is needed)

The branch ceiling `ell(B) ≤ 0` (⟺ the asymptotic bound `F(T) ≤ F*`) closes by **local** induction, with **no**
global maximizer claim:

```
ell(hub with children c_1..c_k)  ≤  ell(hub of k cherries) = ell(B(k))      [LOCAL: mixed ≤ B(k)]
                                  ≤  0                                       [broom optimum, GATED]
```

- **`mixed ≤ B(k)`** (a hub of `k` *arbitrary* children ≤ a hub of `k` cherries) is the **single-child extremal
  lemma at `μ_k = 3/(4k+3)`** — *local*, per-`k`, verified. It does **not** assert `B(k)` is the global
  size-`2k+1` max. Confirmed: a hub of `k` `P₃`-caterpillar children has `ell` far **below** `ell(B(k))` for
  every `k∈{3,5,8,12,15}`.
- The caterpillars that **beat** `B(c)` still satisfy the ceiling: `ell([4,4,4])=−0.028`, `ell([5,5,5])=−0.029`,
  `ell([6,6,6])=−0.035`, all `< 0`. Broom dominance being false does **not** break the ceiling.

So **Lemma 1 (local single-child lemma) is true and sufficient; Lemma A (global broom dominance) is false and
unneeded.** They are *not* the same problem — the unification conflated them.

## Re-scope (verdict)

- **DROP Prong A** (prove global `B(c)`-dominance via Csikvári / degree-weighted exchange): it targets a **false**
  statement. (A true "S(k,5)-dominance" is a different, harder problem — and still not needed for the asymptotic
  bound.)
- **KEEP Prong B** (certify the *local* single-child lemma = HYPOTHESIS (b)): correct and sufficient for the
  asymptotic upper bound. The residual is unchanged — the single-child lemma's tail — but its justification is
  now the honest *local* one, not global broom dominance.
- **RECONCILED with the parallel Lean session (no conflict in the Lean).** The definitions
  (`R47HubState.lean`) settle it: `cherryU = node [node []]` (the cherry); `armU j = node (replicate j cherryU)`
  = **B(j)** (a hub of `j` cherries); `Hub = List ℕ × ℕ`; and
  `backboneU ((arms,c)::rest) = node (arms.map armU ++ replicate c cherryU ++ [backboneU rest])` — a **spine of
  hubs**, each carrying `B(aᵢ)`-broom arms + cherries + the next spine node. So `backboneU` is the **general
  hub/spine class**, which *contains* the true maximizer `S(K,5) = backboneU [(replicate K 5, 0)]`
  (`Aobj = (26/23)(621/64)^K`, unbounded). The single-hub broom `B(c)` is merely the **degenerate instance**
  `backboneU [([], c)] = armU c`.
  - **The Lean `tree_to_hub_sized : Aobj t ≤ Aobj(backboneU s)` is SOUND** — it reduces every tree to the *rich*
    backbone class (which can dominate), not to the flat `B(c)`. And it correctly *separates* "reduce to backbone
    class" (tree→hub) from "which backbone is max" (the later `Hnorm` balancing to `IsBCHubForm {4,5}` — arms of
    length 4–5, consistent with the `c=5` optimum; `R47R6BalanceLeCert` moves `(a,b)→(a+1,b-1)`, i.e. *toward
    balanced/caterpillar*, which is the correct direction).
  - **The error is confined to the analytic unification note** (`BG_BRANCH_UNIFICATION`, commit `1e391b5`): its
    step "optimum packs cherries into one hub = `B(c)`" prematurely collapses the backbone class to the
    *degenerate* single-hub instance. Gate 0 shows that instance is suboptimal; the Lean never makes that claim.
  - **Net:** the Lean reduction, its Obligation A (the local Kelmans cavity/`pushInto` move), and Prong B's local
    single-child lemma are all consistent and correct. Only the analytic "broom dominance ⟹ optimum is `B(c)`"
    framing is wrong, and it is *not on the critical path* (the asymptotic bound uses the local lemma only).

## Gate 0's other sub-goals (for the surviving Prong B)

- **Single-child lemma at the tightest `μ_15`:** cherry wins over all branches to size 15 by `≥ 0.00167`;
  binding only at brooms `B(4), B(5)` (sizes 9, 11 — already GATED by `MixedHubKKTCertificate`).
- **Tail non-binding:** max `val = ell + μ_15·y` over `d≤6` branches drops to `< 0` for size `≥ 12`
  (`B(5)` at size 11 is the last binder, `+0.0062 < V=0.0082`); large structures sit at `≈ −0.20`. So `N₀ ≈ 12`
  for the exhaustive part; the tail is *very* non-binding (margin `~0.2`), so a **loose** cavity-contraction
  envelope (not broom-dominance-per-size) closes B2 — avoiding the circularity the frontier-induction outcome
  flagged.

`conjecture1_proved = False`. Gate 0 did its job: it stopped a multi-PR investment in proving a false theorem.
