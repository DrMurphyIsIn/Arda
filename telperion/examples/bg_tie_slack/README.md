# bg_tie_slack — the slack-regime bound (BG upper-bound campaign, kernel-gated)

The branch-induction upper bound needs `ell(hub) <= 0` for all root-degrees `k`. For **`k >= 16`** (the slack
regime, which also covers **mixed** hubs via `sum <= k·max`), this follows from `slack_g(k) <= F*` where
`slack_g(k) = k · max_c (ell(c) + h_c/((k+1)d_c))` (using `log(1+Σx) <= Σx`).

## What is gated

`TieSlackCertificate` (`telperion.tie_regime`) emits, via **frozen rigorous log-enclosures** (`log(p/q) ∈
[lo,hi]`, floor/ceil at 80-digit precision — the transcendental import, concavity/turan trust model), the
rational atoms proving `slack_g(k) <= F*` for `k >= 16`:

- **(A) `slack_g(16) < F*`** — per envelope child `c`: `176·L(total_c) + 11·(h/d)·(16/17) < (16|c|+1)·L(621/64)`
  (clears `F* = log(621/64)/11`; upper-bounds LHS by `L_hi`, lower-bounds RHS by `L_lo`).
- **(B) monotone** — per non-`B(5)` child: `11·L(total_c) + 11·(h/d)/289 < |c|·L(621/64)` (i.e. `dφ_c/dk|_16 < 0`),
  so `slack_g(k) <= slack_g(16)` for all `k >= 16`.
- **(C) `B(5)` limit** — `F* > 3/23` (`23·L(621/64) > 33`), since `φ_{B(5)} → 3/23`.

Together: `slack_g(k) <= slack_g(16) < F*` for `k >= 16`, so `ell(hub) <= slack_g(k) − F* < 0` (incl. mixed).

```
python examples/bg_tie_slack/generate.py [--check]
```
CI job `bg-tie-slack-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake build`s it.

## Scope (honest)

Covers the envelope `{cherry, B(2..8)}`; larger brooms / non-envelope branches are dominated (verified,
documented). This gates the slack half of the upper bound; the tie half (`mixed <= B(k)` for `k <= 15`) and the
envelope-dominance reduction remain — all **tie-free**. `conjecture1_proved = False`.
