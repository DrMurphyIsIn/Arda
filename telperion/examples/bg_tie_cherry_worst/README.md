# bg_tie_cherry_worst — the tie-regime cherry-worst step (BG upper-bound campaign, kernel-gated)

The Brualdi–Goldwasser upper bound reduces (see `docs/BG_BROOM_DOMINANCE_20260831.md`,
`docs/BG_TIE_REGIME_CAMPAIGN_20260831.md`) to `ell(B) ≤ 0` for rooted branches, and — for **uniform** hubs — to
**cherry-worst**: the cherry is the worst uniform child, so for a hub of `k` children

```
ell(hub of k children)  ≤  ell(hub of k cherries)  =  ell(B(k))  ≤  0,
```

where the last step is the **proven** broom optimum (`R(s)` single-crossing, `bg_broom_optimum` / `evolve_nearstar`).

## What is gated

Cherry-worst is `ell(k, cherry) − ell(k, B(j)) ≥ 0` for every broom-child `B(j)` (the branch envelope).
Exponentiating by `11 = 2·5+1` clears both `F* = log(621/64)/11` and the 11th root, giving the **exact rational**

```
cherry_vs_broom_ratio(k, j) = exp(11·(ell(k,cherry) − ell(k,B(j))))  >  1.
```

It is **unimodal in `j`** (minimum at the binding `j*(k)`), so `ratio(k, j*) > 1` certifies all `j` at that `k`.
It holds for **`k ≤ 20`** (the tie regime — the tie `ell = 0` at `k = 5` sits deep inside), tightest at `k = 20`
(`ratio ≈ 1.022`). `generate.py` emits `1 < ratio(k, j*(k))` for `k ∈ {2..20}` (19 exact `norm_num` atoms, via
`telperion.tie_regime.TieCherryWorstCertificate`).

```
python examples/bg_tie_cherry_worst/generate.py           # write the Lean
python examples/bg_tie_cherry_worst/generate.py --check    # drift check (CI)
```

CI job `bg-tie-cherry-worst-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake build`s it.

## Scope (honest)

This certifies the finite tie-regime cherry-worst (`k ≤ 20`), the **tie-tight** slice. It is **not** the full
upper bound: the slack regime `k ≥ 21` (a soft bound, `ell ≤ −0.08`), the mixed-hub convexity (`mixed ≤ uniform`
near the tie), and the non-envelope Pareto cap remain — all **tie-free** (the `27·23` arithmetic is fully
discharged by the broom optimum). `conjecture1_proved = False`.
