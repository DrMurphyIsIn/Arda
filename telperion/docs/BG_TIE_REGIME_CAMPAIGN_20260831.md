# Campaign: the tie-regime R(s)-generalization (BG upper bound, uniform hubs)

Dedicated campaign to close the tie-regime of the BG upper bound (`docs/BG_BROOM_DOMINANCE_20260831.md`).
`conjecture1_proved = False`. All exact (`Fraction`); skill `src/telperion/tie_regime.py`, tests
`tests/test_tie_regime.py`.

## The reduction chain (where this fits)

```
BG upper bound  ==  ell(B) <= 0 for all rooted branches B
   (ell(B) = log total(B) - |B| F*,  F* = log(621/64)/11,  additive recursion ell(B) = Σ_c ell(c) + (A_root - F*))
  <=  brooms dominate rooted branches per size            [BG_BROOM_DOMINANCE]
  <=  UNIFORM hubs: ell(k, tau) <= 0  +  mixed <= uniform (near the tie)  +  slack regime
  <=  [THIS CAMPAIGN] uniform tie-regime = cherry-worst + broom optimum
```

## Phase 1 — DONE (this module, verified)

For a uniform hub of `k` children `tau`, `ell(k, tau) = k*ell(tau) + log(1 + k*x_tau) - F*`, `x_tau =
h_tau/((k+1)d_tau)`. Established:

1. **Envelope = brooms.** Per child branch-degree `d`, the `ell`-maximising branch is the broom `B(d-1)`
   (`d=2`->cherry, `d=3`->B(2), ..., `d=6`->B(5) at `ell=0`, the tie). The worst uniform child lies among brooms.
2. **Cherry is the worst uniform child (tie regime).** Verified over all branches (`k = 1..8`):
   `ell(k, cherry) >= ell(k, tau)` for every `tau`. (The cherry's small `d=2` gives the largest `x_tau`, which
   beats its `ell` penalty.)
3. **Cherry-worst is ARITHMETIC and SLACK.** `ell(k,cherry) - ell(k,B(j)) >= 0` iff the EXACT rational
   `cherry_vs_broom_ratio(k,j) = exp(11*(...)) >= 1` (the `11 = 2*5+1` clears both `F*` and the 11th root); the
   ratio is `>= 1.95` (min at `(2,2)`) -- **not tight**, so cherry-worst is TIE-FREE. Only the final broom step
   `ell(hub of k cherries) = ell(B(k)) <= 0` carries the `27*23` tie -- and that is **PROVEN** (the `R(s)`
   single-crossing, `spider_broom.broom_ratio`, kernel-gated by `evolve_nearstar`).

**So the uniform tie-regime = [cherry-worst, slack, open] + [broom optimum, tight, proven].**

## Phase 2 — the target: prove cherry-worst (slack, so tractable)

`ell(k, cherry) >= ell(k, tau)` for all rooted branches `tau` and tie-regime `k`. Since it is slack (ratio
`>= 1.95`), a soft/analytic argument should suffice (no delicate 23-adic single-crossing). Route:
1. **Reduce to the envelope** — the worst `tau` per degree is `B(d-1)` (Phase 1.1); a branch off the envelope
   has strictly lower `ell_tau` and `h_tau`, so is dominated. So it suffices to bound `tau = B(j)`.
2. **cherry vs `B(j)`** — the rational inequality `cherry_vs_broom_ratio(k, j) >= 1` in integers `(k, j)`. With
   `>= 1.95` slack, prove via a monotone/factorisation argument (kernel-gate the family, or a Handelman/
   `worst_corner` bound on the exponentiated rational).
3. **Non-envelope `tau`** — Pareto domination: `F_k(tau) = k*ell_tau + log(1+k*x_tau)` is increasing in both
   `ell_tau` and `h_tau`; the envelope maximises `ell_tau` per degree, and a small-`h` argument caps the rest.

## Phase 3 — beyond uniform (the remaining tie-regime pieces)

- **mixed <= uniform near the tie** — exhaustive `N <= 14`: the max-`ell` hub per root-degree `k <= 6` is uniform
  (only the slack regime `k >= 7` goes non-uniform, an artifact of the size cap). Prove that near the tie the
  worst hub is uniform (a convexity/exchange argument on the children multiset).
- **slack regime** — `k` large or deep children: `ell` bounded `<= -0.14`, a soft bound bounded away from `0`.

## Honest scope

The uniform tie-regime is the cleanest, most tractable slice (cherry-worst is slack; the tie is already proven).
Phases 2-3 are genuine work but no longer need a new 23-adic argument -- the `27*23` tie is fully discharged by
the broom optimum. The remaining pieces are slack inequalities + a convexity reduction. This is the concrete
open frontier of the BG upper bound. `conjecture1_proved = False`.
