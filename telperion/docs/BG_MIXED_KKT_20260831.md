# BG mixed-hub reduction via log-concavity + per-child KKT (2026-08-31)

The branch-induction upper bound for Brualdi–Goldwasser reduces the asymptotic maximum of `π(T)=per(L)/∏deg` to
`ell(B) <= 0` for rooted branches, hence (per root-degree `k`) to bounding the **mixed hub** — a root with `k`
arbitrary child branches — by the all-cherry hub `B(k)`:

    ell(hub) <= ell(B(k))     for k <= 15   (the tie regime; k >= 16 is the slack regime, gated separately).

This was the last tie-free conceptual gap. A degree-changing **exchange** argument for it failed (the worst
child is a non-monotone `(x, ell)`-tradeoff; a random-sample test even false-passed a `k<=20` overclaim that the
exchange analysis then killed — `19` cherries `+ B(5)` beats `B(20)`). The fix decouples the coupled `k`-child
optimization by the tangent of the **concave** `log`.

## The reduction

Write the hub potential with `x_c = h_c/((k+1)d_c)` the child's hub-field share and
`ell(hub) = Σ ell(c_i) + log(1 + Σ x_i) - F*`. At the all-cherry point `Σx = k·x_cherry`, `x_cherry = 1/(3(k+1))`,
the concave `log` lies below its tangent of slope `lambda(k) = 1/(1 + k·x_cherry) = 3(k+1)/(4k+3)`:

    log(1 + Σx_i) <= log(1 + k·x_cherry) + lambda(k)·(Σx_i - k·x_cherry).

Define the per-child **Lagrangian value** `V(c) = ell(c) + lambda(k)·x_c`. Substituting,

    ell(hub) - ell(B(k)) <= Σ_i [ell(c_i) - ell(cherry)] + lambda(k)·(Σx_i - k·x_cherry)
                          = Σ_i [V(c_i) - V(cherry)].

So **`V(c) <= V(cherry)` per child** (the KKT condition — no coupling through the other children) gives
`ell(hub) <= ell(B(k))`. The tangent step is *rigorous* (log concavity); the residual is a **single-child**
inequality. It works where the exchange failed because it is a *relative* comparison (hub vs `B(k)`): the `27·23`
tie arithmetic stays confined to the separate broom-optimum gate `ell(B(k)) <= 0`.

Verification: the tangent bound `ell(hub)-ell(B(k)) <= Σ(V(c_i)-V(cherry))` is exact (max violation `0`, at the
all-cherry hub) across randomized mixed hubs, `k<=15`.

## What is kernel-gated (`MixedHubKKTCertificate`, `bg_mixed_kkt`)

Clearing `11·F* = log(621/64)` and the rational `lambda(k)`, `V(c) < V(cherry)` becomes, per broom child `B(j)`
and `k ∈ [2,15]`,

    11·L(total_c) - 11·L(3/2) - (|c|-2)·L(621/64)  <  11·lambda(k)·(x_cherry(k) - x_c(k)),

LHS upper-bounded by the **frozen log-enclosures** (`L_hi(total_c)`, `L_lo(3/2)`, `L_lo(621/64)` for the
`-(|c|-2)<0` coefficient — the same enclosures the slack gate uses; concavity/turán trust model), RHS an exact
rational. `98` atoms (`k=2..15 × B(2..8)`), all `norm_num`, tightest margin `≈ 0.018`. The emitted LHS were
checked to dominate the true `11·(ell(c)-ell(cherry))`, so `lhs < rhs` soundly certifies `V(c) < V(cherry)`.

## Scope / honesty

- The per-child KKT `cherry = argmax_c V(c)` is checked over the broom envelope `{B(2..8)}` and confirmed over
  **all branches `<= size 11`** (the `(x,ell)`-tradeoff dominates larger branches — high-`x` branches have
  sharply negative `ell`). The cherry (reference, `V=V`) is the maximiser, not a broom.
- `cherry = argmax V` holds across the whole tie regime `k <= 15` (in fact to `k=18`) and **fails** for large `k`
  — consistent with `mixed <= B(k)` *itself* failing at `k >= 20`. `k <= 15` meets the slack boundary `k >= 16`
  with no gap.
- This gates the **tie half** of the mixed-hub bound. The broom optimum `ell(B(k)) <= 0` (`bg_broom_optimum`,
  the `23`-adic tie) and the slack half `k >= 16` (`bg_tie_slack`) are separate, already-kernel-gated pieces.
- `conjecture1_proved = False`.

## Ledger position

With this gate the branch-induction upper bound's per-hub ledger is:

| root-degree `k` | bound | gate |
|---|---|---|
| `k = 1` | trivial (`ell < 0`) | — |
| `k = 2..15` (tie regime) | `mixed <= B(k)`, and `ell(B(k)) <= 0` | **`bg_mixed_kkt`** + `bg_broom_optimum` |
| `k >= 16` (slack regime) | `ell(hub) <= slack_g(k) - F* < 0` | `bg_tie_slack` |

The residual for a *complete* proof is the infinite-branch tail of the per-child envelope `V(c) <= V(cherry)`
and the Lean assembly chaining the gates — no remaining coupled/combinatorial hub optimization.

## Envelope tail — the three-case split (only one case open)

The per-child envelope `V(c) <= V(cherry)` splits by root branch-degree `d_c` into three cases
(`envelope_tail_case` classifies each):

1. **`d_c >= 7` — GATED (`HighDegreeTailCertificate` / `bg_hi_degree_tail`).** `x_c = h_c/((k+1)d_c)` is small
   enough that the ceiling alone closes it: `V(c) <= 0 + lambda(k)/(7(k+1)) < V(cherry)`, i.e. the
   rational-cleared `-44/(7(4k+3)) < 11·log(3/2) - 2·log(621/64)` (one `norm_num` atom per `k`; RHS via the
   frozen log-enclosures; margin `≈0.0014` at `k=15`). Uses **only** `ell(c) <= 0` and `h_c <= 1`.
2. **brooms `B(2..8)` (degrees `3..9`) — GATED (`MixedHubKKTCertificate` / `bg_mixed_kkt`).** `V(B(j)) < V(cherry)`
   directly.
3. **`d_c <= 6`, non-broom — reduces (pure algebra) to a refined ceiling.** If
   `ell(c) < small_degree_threshold(k) := ell(cherry) - lambda(k)/(6(k+1))`, then (using `h_c <= 1`, `d_c >= 2`)
   ```
   V(c) <= ell(c) + lambda(k)/(2(k+1)) < [ell(cherry) - lambda(k)/(6(k+1))] + lambda(k)/(2(k+1))
         = ell(cherry) + lambda(k)/(3(k+1)) = V(cherry).
   ```
   So case 3 needs no numeric gate — just the **refined-ceiling structural fact (b)**: every small-degree
   (`d_c <= 6`) non-broom branch has `ell(c) < small_degree_threshold(k)`.

**Why (b) is finitely closable, not free-energy-limited.** The near-`V(cherry)` branches are *exactly* the
brooms (finite, gated) plus high-degree hubs (gated). A large structure rooted at a *low-degree* vertex is
lopsided — its `ell` sits far below the ceiling (rooting the extremal star-of-brooms at a peripheral vertex gives
`ell ≈ -0.10`; a hub of few `B(5)`-arms gives `ell ≈ -0.10` to `-0.15`), because the extremal per-vertex density
needs *many* arms (high degree → gated by case 1). Verified: all branches `<= size 14` (max non-broom
`ell ≈ -0.021`), generalized brooms (hub of `m<=5` `B(j)`-children, to size 66), star-of-brooms rooted at every
vertex (to size 101) — **every** small-degree non-broom is `>= 0.06` below the threshold `≈ -0.016`, and whenever
`envelope_tail_case` reports `open` (small-degree, `ell` at/above threshold) the branch is a **broom** (gated),
never a residual (`test_envelope_tail_case_split_closes`).

The residual for a *complete* proof is now the single refined-ceiling lemma (b) — a finite-size decay bound for
`d_c <= 6` non-broom branches — plus the Lean assembly chaining the gates. See `BG_STAR_OF_BROOMS_HANDOFF.md`.
