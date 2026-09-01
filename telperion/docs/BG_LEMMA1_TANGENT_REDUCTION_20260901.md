# Lemma 1 (`mixed ≤ B(k)`, `k ≤ 15`) via concavity-tangent linearization (2026-09-01)

The branch-induction route to the asymptotic BG upper bound (`BG_BRANCH_INDUCTION_20260831.md`) reduces to
two verified-not-formalised lemmas. **Lemma 1** — *for any `k ≤ 15` children with `ell(c_i) ≤ 0`,
`ell(hub) ≤ ell(B(k))`* — was the harder one: its natural `child→cherry` exchange `Δ` is **non-monotonic in
`S'`** (goes slightly negative near the leaf-heavy boundary), which is what made the clean exchange proof
fail and hid the `k ≥ 20` crossover. This note gives a clean reduction that **dissolves the
non-monotonicity**. `conjecture1_proved = False`.

## Setup (additive potential, exact)

For a rooted branch, `ell(B) = log total(B) − |B|·F*`, `F* = log(621/64)/11`, and the exact hub recursion is
`ell(hub) = Σ_i ell(c_i) + log(1 + Σ_i x_i)`, `x_i = h_{c_i}/((k+1)·d_{c_i})`. Write `y_c := h_c/d_c`
(intrinsic to the child), so `x_i = y_i/(k+1)`. The cherry child (size-2, armmid+leaf) has
`ell(cherry) = −0.00771`, `y_cherry = 1/3`, and `B(k)` = the all-cherry hub (`ell(B(5)) = 0` reproduces the
broom optimum exactly).

## The reduction

**Step 1 — concavity tangent (a genuine upper bound, not a heuristic).** `log` is concave, so
`log(1+a) ≤ log(1+b) + (a−b)/(1+b)` (tangent at `b`). Take `a = Σx_i`, `b = k·x_cherry`:

```
Δ := ell(hub) − ell(B(k))
   = Σ_i [ell(c_i) − ell(cherry)] + [log(1+Σx_i) − log(1+k·x_cherry)]
   ≤ Σ_i [ell(c_i) − ell(cherry)] + (Σx_i − k·x_cherry)/(1 + k·x_cherry)
   = Σ_i { [ell(c_i) + μ_k·y_{c_i}] − [ell(cherry) + μ_k·y_cherry] },
```

where the tangent slope collapses to the **exact rational**

```
μ_k = 1 / ((k+1)(1 + k·x_cherry)) = 3/(4k+3)          (x_cherry = (1/3)/(k+1)).
```

**Step 2 — single-child extremal lemma.** *The cherry maximises `ell(c) + μ·y_c` over ALL rooted branches
`c` for `μ ≥ μ* ≈ 0.039`.* (Verified over all 53 272 rooted branches up to size 14;
`bg_single_child_lagrangian.py`. Remaining for full rigour: the size-`≥ 15` tail — large branches have
`ell` decaying below the cherry value, the same branch-envelope bound the slack lemma uses.)

**Step 3 — shadow-price bound.** `μ_k = 3/(4k+3)` is decreasing in `k`, and for `k ≤ 15`,
`μ_k ≥ 3/63 = 1/21 ≈ 0.0476 > μ* ≈ 0.039` — a comfortable margin.

**Conclusion.** For `k ≤ 15`, each bracket in Step 1's sum is `≤ 0` by Steps 2–3, so `Δ ≤ 0`, i.e.
`ell(hub) ≤ ell(B(k))`. ∎ (modulo the single-child tail bound). Verified end-to-end on 4000 random hubs
(`bg_lemma1_tangent_reduction.py`): the tangent bound holds every time, every Lagrangian bracket `≤ 0`,
worst `Δ = −0.264 ≤ 0`.

## Why this is the right move

The earlier attempt tracked the exact exchange `Δ(c, S')`, which is non-monotonic in `S'` and dips negative
near the boundary — no clean sign. **Linearising the `log` at the all-cherry point** replaces the coupled,
non-monotone `Δ` with a *sum of independent single-child brackets* at a fixed rational price `μ_k`, and the
whole `k`-dependence becomes the scalar inequality `μ_k = 3/(4k+3) ≥ μ*`. The crossover is now transparent:
`μ_k < μ*` at `k ≈ 19–20`, exactly the `k ≥ 20` failure the doc found empirically. The non-monotonicity was
an artefact of not linearising.

## What remains

- **Single-child tail bound** (`size ≥ 15`): show `max_c (ell(c) + μ·y_c) = cherry` for `μ ≥ μ*` extends past
  size 14. Checked (`bg_tail_bound.py`): the per-size maxima — the brooms `B(c)` — satisfy
  `ell(B(c)) + μ·y_{B(c)} < ell(cherry) + μ·y_cherry` strictly for every `c ≥ 6`, out to `c = 80`
  (size 161), and decrease monotonically. The crude split `max(ell+μy) ≤ max(ell)+μ·max(y)` does NOT
  suffice (a branch with `ell` near 0 has small `y`, but the split ignores that coupling), so the tail
  needs the **joint `(ell, y)` branch envelope** — precisely the per-size-max = broom statement, i.e.
  **Lemma A (broom dominance)** territory. So Lemma 1's tail and Lemma A are linked: the same envelope
  closes both. (For `size ≤ 14` the exhaustive 53 272-branch check is unconditional.)
- **`μ*` as an exact rational**: pin the crossover `μ*` exactly (the `B(4)`/`B(5)` vs cherry Lagrangian
  ties) so Steps 2–3 are a clean rational inequality `3/(4k+3) > μ*` for `k ≤ 15`.
- **Formalise** the tangent inequality + the finite single-child check as kernel-gated Lean.

Then Lemma 1 is proved; with the (already-verified) slack bound (`k ≥ 16`) and the proven broom optimum
(`ell(B(5)) = 0`, the `27·23` tie), the branch induction gives `ell(B) ≤ 0` for all rooted branches — the
asymptotic BG upper bound — on the analytic side alone. `conjecture1_proved = False`.
