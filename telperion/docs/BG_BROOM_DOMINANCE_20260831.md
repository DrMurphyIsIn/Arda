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

## The key per-child lemma

By the recursion, `ell(B) ≤ 0` is equivalent to the **per-hub capacity bound**
```
A_root ≤ F* + sum_c ψ(c),     ψ(c) := -ell(c) ≥ 0   (each child's accumulated credit),
```
verified for all trees `N ≤ 16`. A CLOSED per-child proof (each child's credit `ψ(c)` covers its marginal
contribution to `A_root`, via concavity of `log(1+Σ w h_c)` + the matching bound `1+Σx ≤ ∏(1+x)`) would give the
upper bound by induction — the concrete open target.

## Next steps

1. **Prove the per-hub capacity bound** `A_root ≤ F* + Σ_c ψ(c)` per-child (concavity/subadditivity split), or
   the degree-changing exchange for (A). Tie-free — may sidestep the `c`-optimum smooth-certificate no-go.
2. **Kernel-gate** the finite base cases (`worst_corner`/Handelman on the field box), reusing `bg_bulk_discharge`.
3. Fold into `BG_UNIFIED_PROGRAM`: upper bound = (A) [this] + (B) [done] + tree→hub [Lean].

Skill: `src/telperion/branch_potential.py` (`branch_ell`, `branch_total`, `broom_edges`). `conjecture1_proved = False`.
