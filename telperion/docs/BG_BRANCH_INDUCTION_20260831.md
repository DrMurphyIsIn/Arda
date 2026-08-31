# The branch-induction route to the asymptotic BG upper bound (bypasses tree→hub)

A self-contained proof STRUCTURE for the asymptotic Brualdi–Goldwasser upper bound `F* ≤ log(621/64)/11`, by
induction on rooted-branch structure — **independent of** the parallel Lean session's tree→hub reduction /
Obligation A. `conjecture1_proved = False`; two verified-not-formalised lemmas remain (stated below).

## The claim and the boundary bound

Target: `F(T) = lim_n (1/n) log π(T) ≤ F*` for trees (`π = per(L)/∏deg`). Define, for a rooted BRANCH `B` (root
with a phantom up-edge, degree `= #children + 1`), `ell(B) = log total(B) − |B| F*`.

**Boundary lemma (verified, all trees `N ≤ 13`, all roots):** `1 ≤ π(T)/branch_total(T, r) ≤ 4/3`, so
`|log π(T) − log branch_total(T, r)| ≤ log(4/3) = O(1)`, independent of `n` (only the root's `+1` up-edge
differs). Hence
```
ell(B) ≤ 0 for all rooted branches B   ==>   π(T) ≤ (4/3)·e^{n F*}   ==>   (1/n) log π(T) ≤ F* + O(1/n) → F*.
```
So the asymptotic upper bound reduces ENTIRELY to `ell(B) ≤ 0` for all rooted branches — no tree→hub needed.

## The induction (on `|B|`)

- **Base:** `B = leaf`. `ell = log 1 − 1·F* = −F* < 0`. ✓
- **Step (the per-hub bound):** `B` = a hub with `k` children `c_1,…,c_k`; IH `ell(c_i) ≤ 0`. Then
  `ell(B) = Σ_i ell(c_i) + log(1 + Σ_i x_i) − F*`, `x_i = h_{c_i}/((k+1) d_{c_i})`, and `ell(B) ≤ 0`:

  | `k` | bound | status |
  |---|---|---|
  | `1` | `ell ≤ ell(cherry) = −0.0077 ≤ 0` | trivial |
  | `2..20` (tie) | `ell(hub) ≤ ell(B(k)) ≤ 0` | **kernel-gated** (`bg_tie_cherry_worst` + `bg_broom_optimum`) + `mixed ≤ B(k)` |
  | `≥ 21` (slack) | `ell(hub) ≤ slack_g(k) − F* < 0` | verified (`slack_hub_bound`) |

  Everything arithmetically delicate (the `27·23` tie via the broom optimum, and the cherry-worst boundary at
  `k = 20`) is **kernel-gated**. The base + step give `ell(B) ≤ 0` for all rooted branches by induction.

## The two remaining lemmas (verified, tie-free, to formalise)

1. **`mixed ≤ B(k)` (`k ≥ 2`):** for any `k` children with `ell(c_i) ≤ 0`, `ell(hub) ≤ ell(B(k))` (the all-cherry
   hub is the worst). **EXHAUSTIVELY verified** over ALL rooted branches with root-degree `k ≤ 7` (`N ≤ 16`;
   TIGHT: `max ell = ell(B(k))`), and **targeted** for `k = 8..20` against all envelope competitors (uniform
   `B(j)` + random cherry/broom mixes; tightest margin `0.002` at `k = 20`). No counterexample -- contrast the
   tangent route, which had them (`test_mixed_le_Bk_exhaustive`). The `mixed ≤ B(k)` earlier "caveat" is thus
   discharged empirically. Formalisation still open: the max-`ell` `k`-hub is uniform (all-cherry, `k≥2`) -- a
   knapsack-type statement (`ell(hub) = Σ ell(c_i) + log(1+Σx_i) − F*`; for fixed `Σx` maximise `Σ ell(c_i)`),
   whose clean proof (child→cherry exchange; `Δ` couples through the other children's `Σx`) remains.
2. **Slack bound (`k ≥ 21`):** `slack_g(k) = k·max_env(ell(c)+x_c) ≤ F*` via the branch envelope (cherry + brooms;
   larger branches have `ell` bounded away from 0). Verified (sup `0.156` at `k=21`, margin `0.05`).

## Significance

This route makes the asymptotic upper bound **self-contained on the analytic side** — the parallel Lean
session's tree→hub / Obligation A (the long-standing "wall") is NOT required for the *asymptotic* maximum
(the growth rate `F*`), only for a structural/finite-`n` domination statement. Combined with the lower bound
(the `S(k,5)` star-of-brooms achieves `F*`), completing the two lemmas above would resolve the **asymptotic**
Brualdi–Goldwasser maximum. `conjecture1_proved = False` (the two lemmas are verified, not yet formal).

See `BG_TIE_REGIME_CAMPAIGN_20260831.md`, `BG_BROOM_DOMINANCE_20260831.md`, `BG_23ADIC_RECONCILIATION_20260831.md`,
skills `branch_potential.py` / `tie_regime.py`.
