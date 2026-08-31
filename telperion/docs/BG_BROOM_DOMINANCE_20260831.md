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

## Next steps

1. **Prove (A) broom dominance** via a local exchange: any rooted branch is `total`-dominated by moving a child's
   mass toward cherries on the root hub (the rooted `pushInto`). Candidate: adapt the parallel session's
   `R47R7ChildMono` / `pushInto` monotonicity to the rooted-branch total.
2. **Kernel-gate** the finite base cases of the exchange (small-branch `total` inequalities via `worst_corner`).
3. Fold into `BG_UNIFIED_PROGRAM`: upper bound = (A) [this] + (B) [done] + tree→hub [Lean].

Skill: `src/telperion/branch_potential.py` (`branch_ell`, `branch_total`, `broom_edges`). `conjecture1_proved = False`.
