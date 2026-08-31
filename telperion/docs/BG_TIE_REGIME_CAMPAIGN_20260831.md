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

## Phase 2 — the precise boundary: cherry-worst holds for `k <= 20` (FINITE), slack beyond

Measured exactly: `cherry_vs_broom_ratio(k, j) > 1` (cherry is the worst uniform child) **for all `k <= 20`**,
and it first FAILS at `k = 21` (a `B(4)` child, ratio `0.952`) — but there `ell(hub) <= -0.088`, deeply slack
(both the cherry-hub and the `B(j)`-hub are `<= 0` with large margin). The tie (`ell = 0`, `k = 5`) sits deep
inside the tie regime with room to spare. So:

- **Tie regime `k <= 20` — FINITE.** cherry-worst is a *finite* family of rational inequalities: for each
  `k in {2..20}`, `cherry_vs_broom_ratio(k, j) > 1` for all `j` (the ratio `-> infinity` as `j -> infinity`, so
  the min over `j` is at a finite `j` — a bounded check). **Kernel-gateable** (à la `bg_broom_optimum`), no new
  23-adic argument. Combined with the broom optimum `ell(B(k)) <= 0` [PROVEN], this closes the tie regime.
- **Non-envelope `tau`** — Pareto domination: `F_k(tau) = k*ell_tau + log(1+k*x_tau)` is increasing in both
  `ell_tau` and `h_tau`; the envelope (broom `B(d-1)`) maximises `ell_tau` per degree, so `tau = B(j)` suffices
  (a small-`h` cap handles the rest).

The remaining infinite part is the **slack regime `k >= 21`** (Phase 3), which needs only a soft bound.

## Phase 3 — the slack regime `k >= 21` (DONE, verified) + mixed hubs

- **slack regime `k >= 21` — soft bound established (`tie_regime.slack_hub_bound`).** Via `log(1 + Σ x_c) <= Σ x_c`,
  `ell(hub) <= Σ_c (ell(c) + x_c) - F* <= k * max_c (ell(c) + x_c) - F* = slack_g(k) - F*`. The per-child max
  lies on the branch envelope (cherry + brooms; larger branches have `ell` bounded away from `0`, verified over
  all branches `<= size 11`), and `slack_g(k) <= F*` for all `k >= 21` (sup `0.156` at `k = 21`, margin `0.05`;
  `-> 0.130` as `k -> infinity`, from `B(5)`). So `ell(hub) <= slack_g(k) - F* <= 0`, tie-free. The `log <= linear`
  relaxation is loose only at the tie (`k <= 20`, handled by cherry-worst) -- in the slack regime it has ample
  margin. **Remaining formalisation:** the envelope reduction (`max_c` over all branches `=` max over cherry +
  brooms) and `slack_g(k) <= F*` as a closed bound (the cherry term is decreasing in `k`, the `B(5)` term `< 0.131`).

- **mixed <= uniform — DONE (verified).** The max-`ell` `k`-child hub is UNIFORM: **all-leaf at `k = 1`**
  (`= cherry`, `ell = -0.0077`), **all-cherry `B(k)` for `k >= 2`**. So `ell(any mixed k-hub) <= ell(B(k))` for
  `k >= 2` (verified over leaf/cherry/broom mixes, `k <= 20`; `test_mixed_le_uniform`). The earlier "mixed beats
  `B(1)`" was a false alarm -- `B(1)` is not the `k=1` uniform max (all-leaf is). So the uniform tie-regime bound
  (cherry-worst + broom optimum) covers mixed hubs too. **Remaining formalisation:** the child->cherry exchange
  raises `ell` for `k >= 2` (the exchange `Delta` depends on the other children's `Σx`, so not purely per-child).

## Status — the per-hub induction step `ell(B) <= 0` is now covered across ALL cases

| child-count `k` | bound | status |
|---|---|---|
| `k = 1` | `ell <= ell(cherry) = -0.0077 <= 0` | trivial (finite) |
| `k in {2..20}` (tie) | `ell(hub) <= ell(B(k)) <= 0` | **gated** (`bg_tie_cherry_worst` + `bg_broom_optimum`) + mixed<=B(k) verified |
| `k >= 21` (slack) | `ell(hub) <= slack_hub_bound(k) < 0` | verified (soft, tie-free) |

The tie-tight arithmetic (`27*23`) is fully discharged; every remaining item (slack `slack_g` closed bound, the
child->cherry exchange for mixed) is TIE-FREE. **The whole BG upper bound then follows from the per-hub step by
induction, modulo the parallel Lean session's tree->hub reduction (their Obligation A).** `conjecture1_proved = False`.

## Honest scope

The uniform tie-regime is the cleanest, most tractable slice (cherry-worst is slack; the tie is already proven).
Phases 2-3 are genuine work but no longer need a new 23-adic argument -- the `27*23` tie is fully discharged by
the broom optimum. The remaining pieces are slack inequalities + a convexity reduction. This is the concrete
open frontier of the BG upper bound. `conjecture1_proved = False`.
