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
- **FLAG for the parallel Lean session:** their `tree_to_hub_sized : Aobj t ≤ Aobj(backboneU s)` is sound **iff**
  `backboneU` is a *caterpillar/spine* backbone (which *can* dominate — `[4,4,4]` beats `B(13)`), **not** the
  single-hub broom `B(c)`. Their straightening measure (`strDefect = 0 iff backbone`, a spine form) suggests it
  is the spine form — consistent. But their *analytic* unification note (`1e391b5`, "optimum = `B(c)`") is the
  piece that errs. The Lean reduction and the analytic unification must be reconciled on *which* backbone.

## Gate 0's other sub-goals (for the surviving Prong B)

- **Single-child lemma at the tightest `μ_15`:** cherry wins over all branches to size 15 by `≥ 0.00167`;
  binding only at brooms `B(4), B(5)` (sizes 9, 11 — already GATED by `MixedHubKKTCertificate`).
- **Tail non-binding:** max `val = ell + μ_15·y` over `d≤6` branches drops to `< 0` for size `≥ 12`
  (`B(5)` at size 11 is the last binder, `+0.0062 < V=0.0082`); large structures sit at `≈ −0.20`. So `N₀ ≈ 12`
  for the exhaustive part; the tail is *very* non-binding (margin `~0.2`), so a **loose** cavity-contraction
  envelope (not broom-dominance-per-size) closes B2 — avoiding the circularity the frontier-induction outcome
  flagged.

`conjecture1_proved = False`. Gate 0 did its job: it stopped a multi-PR investment in proving a false theorem.
