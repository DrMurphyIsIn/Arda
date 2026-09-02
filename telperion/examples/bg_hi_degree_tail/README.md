# bg_hi_degree_tail — high-degree half of the per-child envelope tail (BG upper-bound, kernel-gated)

The mixed-hub reduction (`bg_mixed_kkt`) proves `ell(hub) <= ell(B(k))` for `k <= 15` *given* the per-child
envelope inequality `V(c) <= V(cherry)` for every child branch `c`, where `V(c) = ell(c) + lambda(k)·x_c`,
`lambda(k) = 3(k+1)/(4k+3)`, `x_c = h_c/((k+1)d_c)`. This gate closes the **high-degree half** of that envelope
tail.

## The clean lemma

For any branch with root branch-degree `d_c >= 7`, using **only** the ceiling `ell(c) <= 0` (the branch-
induction hypothesis) and `h_c <= 1`:

```
V(c) = ell(c) + lambda(k)·x_c  <=  0 + lambda(k)·(1/((k+1)·7))  <  V(cherry) = ell(cherry) + lambda(k)/(3(k+1)).
```

With `x_cherry = 1/(3(k+1))` and `lambda(k)/(k+1) = 3/(4k+3)`, the final inequality is the rational-cleared

```
-44 / (7·(4k+3))  <  11·ell(cherry)  =  11·log(3/2) - 2·log(621/64).
```

No envelope enumeration — high-degree branches have `x_c` small enough that the ceiling alone suffices.

## What is gated

`HighDegreeTailCertificate` (`telperion.tie_regime`) emits one `norm_num` atom per `k ∈ [2,15]`
(`-44/(7(4k+3)) < 11·L_lo(3/2) - 2·L_hi(621/64)`), the RHS lower-bounding `11·ell(cherry)` via the same frozen
log-enclosures as the slack/KKT gates (`L_lo ≤ log ≤ L_hi`, verified to bracket the true logs; gap `~4·10⁻³⁰`).
The binding case is `k=15` (LHS closest to 0), margin `≈ 0.0014`.

```
python examples/bg_hi_degree_tail/generate.py [--check]
```
CI job `bg-hi-degree-tail-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake build`s it.

## Scope (honest)

This closes `d_c >= 7`. Combined with `bg_mixed_kkt` (which gates the broom children `B(2..8)`, i.e. degrees
`3..9`) and the exhaustive verification over all branches `<= size 11`, the **open** part of the per-child
envelope tail shrinks to small-degree **non-broom** branches (`d_c <= 6`), whose max `V` is empirically the broom
`B(4)` (margin `≈ 0.0017`) and decays with size. `conjecture1_proved = False`.
