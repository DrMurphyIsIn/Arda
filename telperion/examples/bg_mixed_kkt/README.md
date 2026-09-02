# bg_mixed_kkt — the mixed-hub reduction (BG upper-bound campaign, kernel-gated)

The branch-induction upper bound needs `ell(hub) <= ell(B(k))` for **mixed** hubs at each root-degree `k`. For
the **tie regime `k <= 15`** this is the last tie-free conceptual piece (the slack regime `k >= 16` is gated by
`bg_tie_slack`; the broom optimum `ell(B(k)) <= 0` by `bg_broom_optimum`).

## The reduction (why it decouples)

Earlier a degree-changing *exchange* argument failed here: `mixed <= B(k)` is a coupled optimization over the `k`
children. The fix is the tangent of the **concave** `log` at the all-cherry point. With `x_cherry(k) =
1/(3(k+1))` and slope `lambda(k) = 1/(1 + k·x_cherry) = 3(k+1)/(4k+3)`, define the per-child Lagrangian value
`V(c) = ell(c) + lambda(k)·x_c`. Then, for **any** children `c_1..c_k`,

```
ell(hub) - ell(B(k)) = Σ ell(c_i) - k·ell(cherry) + [log(1+Σx_i) - log(1 + k·x_cherry)]
                    <= Σ ell(c_i) - k·ell(cherry) + lambda(k)·(Σx_i - k·x_cherry)   [tangent above the curve]
                     = Σ_i [V(c_i) - V(cherry)].
```

So if `V(c) <= V(cherry)` **per child** (no coupling through the others), then `ell(hub) <= ell(B(k))`. This
works where the exchange failed because it is a **relative** comparison (hub vs `B(k)`) — tie-free; the `27·23`
arithmetic stays confined to `ell(B(k)) <= 0`.

## What is gated

`MixedHubKKTCertificate` (`telperion.tie_regime`) emits, via the same **frozen log-enclosures** as the slack gate
(`log(p/q) ∈ [lo,hi]`, floor/ceil at 80-digit precision — the transcendental import, concavity/turan trust
model), the rational atoms proving `V(c) < V(cherry)` for every broom child `B(2..8)` and `k ∈ [2,15]`. Clearing
`11·F* = log(621/64)` and `lambda(k) = 3(k+1)/(4k+3)` (rational), each atom is

```
11·L(total_c) - 11·L(3/2) - (|c|-2)·L(621/64)  <  11·lambda(k)·(x_cherry(k) - x_c(k)),
```

with the LHS upper-bounded (`L_hi(total_c)`, `L_lo(3/2)`, and `L_lo(621/64)` for the `-(|c|-2)<0` coefficient) and
the RHS an exact rational. `98` atoms (`k=2..15 × B(2..8)`), tightest margin `≈ 0.018`.

```
python examples/bg_mixed_kkt/generate.py [--check]
```
CI job `bg-mixed-kkt-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake build`s it.

## Scope (honest)

The tangent step is **rigorous** (log concavity). The gated residual is the per-child `V(c) < V(cherry)`, checked
over the broom envelope `{B(2..8)}`; the cherry (reference, `V=V`) is omitted, and all branches `<= size 11` were
verified exhaustively to confirm the cherry is the `V`-argmax (the `(x,ell)`-tradeoff dominates larger branches —
high-`x` branches have sharply negative `ell`). The per-child KKT `cherry = argmax V` holds across `k <= 15` and
**fails** for large `k` (consistent with `mixed <= B(k)` itself failing at `k >= 20`); `k <= 15` meets the slack
boundary `k >= 16` with no gap. This gates the tie half of the mixed-hub bound; the broom optimum and slack half
are separate gates. `conjecture1_proved = False`.
