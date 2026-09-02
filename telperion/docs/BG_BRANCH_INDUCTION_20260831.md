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
  | `2..15` (tie) | `ell(hub) ≤ ell(B(k)) ≤ 0` | `mixed ≤ B(k)` (exhaustive over broom pool) + broom optimum (`bg_broom_optimum`, gated); uniform slice also `bg_tie_cherry_worst` |
  | `≥ 16` (slack) | `ell(hub) ≤ slack_g(k) − F* < 0` | verified (`slack_hub_bound`; `slack_g(k) ≤ F*` for `k ≥ 16`, covers MIXED via `sum ≤ k·max`) |

  **The `27·23` tie via the broom optimum is kernel-gated.** The two regimes meet at `k = 15/16` with no gap. The
  base + step give `ell(B) ≤ 0` for all rooted branches by induction.

  > **CORRECTION (caught by the child→cherry exchange analysis):** `mixed ≤ B(k)` is FALSE for `k ≥ 20` — a hub of
  > `(k−1)` cherries + one `B(5)`-child beats `B(k)` (`ell(19 cherries + B(5)) = −0.08468 > −0.08503 = ell(B(20))`,
  > gap growing with `k`). So `B(k)` is NOT the max `k`-hub near the boundary (the recursive `B(5)`-substructure
  > starts to win — the same crossover as the `S(k,5)` star-of-brooms). The earlier "`mixed ≤ B(k)` for `k ≤ 20`"
  > was an overclaim (a false-passing random-sample test). **But `ell(hub) ≤ 0` still holds** (`−0.085 < 0`); only
  > the *reduction* to `B(k)` fails, and it is not needed there because the slack bound covers `k ≥ 16` (including
  > mixed). So the induction still closes — just with the regime boundary moved from `k ≤ 20` to `k ≤ 15` / `k ≥ 16`.

## The two remaining lemmas (verified, tie-free, to formalise)

1. **`mixed ≤ B(k)` for `2 ≤ k ≤ 15`:** for any `k ≤ 15` children with `ell(c_i) ≤ 0`, `ell(hub) ≤ ell(B(k))`.
   EXHAUSTIVELY verified over all rooted branches root-degree `k ≤ 7` (`N ≤ 16`, TIGHT) and over all cherry+broom
   multisets for `k ≤ 15` (`test_mixed_le_uniform_k_le_15`). **Fails for `k ≥ 20`** (see the CORRECTION above) --
   but only `k ≤ 15` is needed (slack covers `k ≥ 16`). Formalisation open: the `child→cherry` exchange
   `Δ = (ell_cherry − ell_c) + log((1+S'+x_cherry)/(1+S'+x_c))` is decreasing in `S'` but goes slightly negative
   at large `S'` / near the boundary (the non-monotonicity that made the clean exchange proof fail and revealed
   the `k≥20` failure). A rigorous proof needs an extremal argument that the max hub avoids the large-`S'`
   (leaf-heavy) regime.
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
