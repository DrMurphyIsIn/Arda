# BG: the broadened tie family — the finite-n maximizer, constructed (2026-09-05)

Constructs the "broadened tie family" the Hdom bridge (`R47HdomBridge.sharpRate_of_rateBound`)
flagged as the open per-size subtlety but left unbuilt. The near-star is only the *asymptotic /
large-K* maximizer; the true finite-n maximizer trades load-5 arms for (load-4 arm + cherry) pairs.
Verified by THREE independent exact engines (a3_derisk cavity, `pi_loaded`, literal matching
permanent). `conjecture1_proved = False`. Self-verifying: `proof/verification/broadened_tie_family.py`.

## The size-preserving trade

A load-5 arm is 11 vertices; a load-4 arm (9) + a cherry (2) is also 11. So at each aligned size
`n = 1+11K`, the trade

    one load-5 arm  ⟷  one load-4 arm + one cherry

preserves `n`. The maximizer is a single hub with **`(K−m)` load-5 arms + `m` load-4 arms + `m`
cherries**, optimized over the trade count `m`.

## Value formula (closed form, exact — matches the engine for all K,m)

Per-child cavity data: load-5 arm `(Ztot(dtSub)=621/64, q=3/23)`, load-4 arm `(513/80, 3/19)`,
cherry `(3/2, 1/3)`. For degree `d = K+m`:

    V(K,m) = (621/64)^(K−m) · (513/80)^m · (3/2)^m · (1 + qSum/d),
    qSum   = (K−m)·(3/23) + m·(3/19) + m·(1/3).

The tie value at aligned size `n=1+11K` is `max_m V(K,m)`.

## The optimal trade count m(K) and the transition

| K | 1 | 2 | 3 | 4 | 5 | 6–11 | 12–14 | 15–17 | 18–19 | 20–22 | **≥23** |
|---|---|---|---|---|---|------|-------|-------|-------|-------|---------|
| m(K) | 1 | 2 | 3 | 4 | 5 | 5 | 4 | 3 | 2 | 1 | **0** |

`m` rises to its cap 5 (K≤11), then falls as the growing hub degree makes further trades
unprofitable; trading stops once `d = K+m` reaches ≈23. **The near-star (`m=0`) is the maximizer
iff K ≥ 23** (n ≥ 254).

## Consequence for the proof

The near-star tie **is not** the finite-n maximizer for K<23: a hub-with-cherries strictly beats it
at the SAME size — e.g. K=5 / n=56 by **5.48%** (exact: near-star `52200362289231/536870912` vs
broadened `10754162441504397/104857600000`). Therefore:

- `SharpRateNF` / `conjecture1_of_layers_fixedN` instantiated with the **near-star** tie is **FALSE
  for K<23** — this is why the `hrate` bound `(26/23)/rhoB·rhoB^n` is violated (that bound is only
  the large-n limit).
- A correct, provable instantiation must use **this broadened family** as `tie(n)`, with the value
  `max_m V(K,m)`. For K≥23 it coincides with the near-star, recovering the asymptotic constant.

## Honest scope

RIGOROUS: the near-star is non-maximal for K<23 (explicit trees beat it, exact, 3 engines).
The `V(K,m)` closed form is exact. CONSTRUCTED/EMPIRICAL: the `(K−m, m, m)` family is the maximizer
*within the searched single-hub configs* (arm-loads {4,5} + cherries, plus a broader {3,6}/multi-hub
sweep that found nothing higher); a fully rigorous global-maximizer claim is not yet proven. This
also only covers aligned sizes `n=1+11K`; non-aligned `n` need the size-remainder handled. These are
the natural next steps toward a correct `tie(n)` and a provable `SharpRateNF`. `conjecture1_proved = False`.
