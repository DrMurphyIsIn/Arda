# Campaign: the BG upper bound reduces to broom-dominance (2026-08-31)

Focused campaign on the arithmetic resolution of the tight-`τ` / backbone flow-freedom crux. Outcome: the open
BG upper bound is reduced to a single clean rooted-tree extremal claim. All exact (`Fraction`);
`conjecture1_proved = False`.

## The additive potential form

Define, for a ROOTED branch `B` (root degree = #children + 1, counting the up-edge),
```
ell(B) := log total(B) - |B| * F*,     F* = log(621/64)/11,     total(B) = weighted matching sum.
```
The BG upper bound `F(T) <= F*` (asymptotically) is equivalent to `ell(B) <= 0` for every rooted branch. `ell`
obeys the EXACT additive recursion (verified vs the cavity DP; `test_branch_potential.py`):
```
ell(B) = sum_{c child of root} ell(c) + (A_root - F*),     A_root = log(1 + sum_c w_{root,c} h_c),
```
`h_c = U_c/total(c)` the child cavity field. This is the additive discharge / cavity potential (the same object
the Φ¹¹ program's `cavity_potential.py` found; my classical-BG `bg_bulk_discharge.φ_v` is its edge-split form).
`ell(B) <= 0` iff the child credits `-ell(c) >= 0` cover the root excess `A_root - F*`.

## The reduction (the campaign's result)

**Exhaustive structural fact** (all rooted branches, odd `N <= 16`; `test_branch_potential` gates `N <= 13`):
for every odd size `2c+1` the `ell`-maximising (equivalently `total`-maximising) rooted branch is EXACTLY the
broom `B(c)` (`c` length-2 cherries on one hub). Even sizes are strictly below; the global max over all sizes is
`B(5)` at `ell = 0`. So `ell(B) <= 0 for all B` reduces to:

- **(A) BROOM DOMINANCE** — the broom `B(c)` maximises `total(B)` among rooted branches of size `2c+1`.  *Open;
  the campaign's remaining target.* A clean rooted-tree extremal problem — the ROOTED analog of the parallel
  Lean session's tree→hub / Kelmans reduction (their `pushInto`/`Obligation A` is the same exchange move, one
  level up).
- **(B) BROOM OPTIMUM** — `ell(B(c)) <= 0`, `= 0` iff `c = 5`.  **PROVEN** (closed all-`c` single-crossing via
  `spider_broom.broom_ratio`, kernel-gated by `evolve_nearstar`; `docs/BG_23ADIC_RECONCILIATION_20260831.md`).

**(A) + (B) + [tree→hub reduction (parallel Lean, PRs #166–#176)] ⟹ the BG upper bound.** The 23-adic tie
(`621 = 27·23`) enters only through (B), which is already closed; (A) is a *rate/total* comparison with no tie,
so it may admit a clean exchange proof (unlike the smooth-`P` no-go, which was specifically the `c`-optimum tie
that (B) resolves arithmetically).

## Why this is the right cut

The earlier tight-`τ` probe showed a universal discharge must be field-dependent and the hub-hub backbone is
flow-underdetermined — i.e. the *edge-split* form is genuinely hard. The *additive* form `ell` sidesteps the
edge-split freedom: it is a single scalar per branch obeying a clean recursion, and its maximiser per size is
the broom. This converts "find a universal field-`τ`" into "prove brooms dominate rooted branches" — a
structural exchange problem the tree→hub machinery is built for, with the only arithmetic (the `c=5` tie)
already discharged.

## The exchange is NOT naively monotone (proof-strategy finding)

Tested the obvious move — flatten a broom-child into cherries on the root: it **decreases** `total` (it demotes
the sub-hub to a bare leaf on the root, and a bare leaf on a hub is inefficient). This is the memory's
"optimal child non-monotone / near-stars don't dominate" wall, confirmed in the classical-BG total. Consequences:
- **Child-replacement** (parallel session's `R47R7ChildMono`, degree-preserving, `total` linear-nonneg in each
  child) is monotone but only reaches DEPTH-2 recursive brooms, not the single-hub broom.
- Reaching the single-hub broom needs a **degree-CHANGING** exchange (add children by absorbing a sub-hub's
  cherries onto the root) — the rooted analog of the parallel session's *open* Obligation A (`pushInto`/Kelmans
  cavity). So (A) is coupled to their open crux — but it is **tie-free** (a plain `total` comparison of a
  size-`2c+1` broom vs same-size non-brooms; no `c=5` tie), which the smooth-certificate no-go did NOT block.

## The key per-hub lemma — reduced to a single aggregate budget bound (tight at c=5)

By the recursion, `ell(B) ≤ 0` is equivalent to the **per-hub capacity bound** (verified `N ≤ 16`, tight at the
broom):
```
log(1 + Σ_c x_c)  ≤  F* + Σ_c ψ(c),        x_c = h_c / (d_root · d_c),   ψ(c) := -ell(c) ≥ 0.
```
**The `log(1 + Σ x_c)` (log of a SUM) is essential — the matching/product relaxation FAILS at the tie.** On the
exact broom `B(5)` (`d=6`, five cherries `x=1/18`), `A_hub - F* = Σψ = 0.03854` (tight), but the product bound
`Σ log(1+x_c) = 0.2705` loses `0.0252 > ` the tight margin, so `Σ log(1+x_c) - F* = 0.0638 > 0.0385 = Σψ` — the
relaxation `1+Σx ≤ ∏(1+x)` overshoots. (An earlier random-tree test that suggested the relaxed bound held was
misleading: random trees never contain the exact broom hub with its tight fields — an 8th caught overclaim.)

So the "≤ one matched edge at the root" constraint (`log(1+Σx)`, not `Σ log(1+x)`) is **load-bearing at the tie**
— which is exactly *why* smooth/independence relaxations overshoot (the memory's "no smooth certificate"
no-go). The bound is genuinely aggregate (not per-child), tight at the `c=5` cherries.

### The tangent-line route — TESTED and DEAD (smooth-certificate no-go, re-confirmed)

The natural fix — a **tangent-line linearization** of the concave `log(1+Σx_c)` at the broom point
`s* = k/(3(k+1))` (upper bound, affine ⟹ per-child separable, tight at `B(5)`) — reduces the induction step to
the per-child inequality `x_c/(1+s*) - ψ(c) ≤ C(k)/k` (i.e. "the cherry maximises `x_c/(1+s*) - ψ(c)` over all
child subtrees, for each `k`"). It passes on structured/random configs but **FAILS** on an exhaustive sweep of
ALL rooted child-subtrees:
- **`k = 1`:** a bare-leaf child gives per-child value `+0.2220 > 0.1352` (cherry).
- **`k = 40`:** a size-9 child gives `+0.00188 > -0.00157` (cherry).

The **optimal child is non-monotone in `k`** (small `k` favours a bare leaf, large `k` favours a deeper subtree,
only mid-`k` favours the cherry) — precisely the memory's "near-stars don't dominate / optimal child
non-monotone" wall. The tangent at the cherry point is too loose at low/high `k` (it fails even where the exact
bound holds). So NO smooth (tangent/product) certificate closes the induction: the bound `log(1+Σx_c) ≤ F* +
Σψ(c)` is genuinely arithmetic, matching the Φ¹¹ `23`-adic no-go. (Caught before overclaiming — an exhaustive
child sweep, not random trees, is the honest test.)

**Consequence for strategy:** the smooth-analytic route is closed; the upper bound needs either (a) the
degree-changing exchange for (A) with an integer/`23`-adic argument for the non-monotone worst child, or (b) the
transfer-operator variational bound. Both reduce to the same 23-adic core (a smooth transfer-operator
eigenfunction hits the identical no-go), and non-broom branches approach `ρ*` arbitrarily closely
(hub-of-`B(5)`, `j=40` → `1.22923`), so there is **no soft ε-margin** — the tight arithmetic is unavoidable.

### The arithmetic structure — a two-regime picture (this move)

For the UNIFORM hub `ell(k, τ) = k·ell(τ) + log(1 + k·x_τ) − F*` (`k` identical children `τ`), the exact
maximiser over all `(k, τ)` is `0` at the broom (`k = 5`, `τ = cherry`), and:
- **Tie regime** (`k = 1..6`, `ell` near `0`): the max-`ell` hub is **uniform** (all children the cherry) — the
  broom, whose `k`-optimum is (B), closed by the `R(s)` single-crossing. Exhaustive `N ≤ 14`: the max-`ell` hub
  per root-degree `k ≤ 6` is uniform.
- **Slack regime** (larger `k`, or non-uniform / deeper children): `ell` is bounded well below `0`
  (`≤ -0.14` at `k = 7`, decreasing) — the non-monotone deeper worst child only appears here, where the bound
  has ample slack.

So the plausible proof shape is **two-regime**: the tie regime reduces to the uniform/broom `R(s)` arithmetic
(generalised to bound uniform non-cherry children), and the slack regime is a soft bound bounded away from `0`.
This is a concrete lead — but a naive global "mixed ≤ uniform" is FALSE (fails at large `k` under size
constraints, though only in the slack regime), so the two regimes must be separated carefully. Genuinely open;
the tie-regime `R(s)`-generalisation is the next arithmetic target.

## Next steps

1. **Prove the per-hub capacity bound** `A_root ≤ F* + Σ_c ψ(c)` per-child (concavity/subadditivity split), or
   the degree-changing exchange for (A). Tie-free — may sidestep the `c`-optimum smooth-certificate no-go.
2. **Kernel-gate** the finite base cases (`worst_corner`/Handelman on the field box), reusing `bg_bulk_discharge`.
3. Fold into `BG_UNIFIED_PROGRAM`: upper bound = (A) [this] + (B) [done] + tree→hub [Lean].

Skill: `src/telperion/branch_potential.py` (`branch_ell`, `branch_total`, `broom_edges`). `conjecture1_proved = False`.
