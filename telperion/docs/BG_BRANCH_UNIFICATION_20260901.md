# Branch-induction unification: Lemma 1 and broom dominance are ONE tangent-Lagrangian problem (2026-09-01)

Culmination of the session's branch-induction work. The two open obligations of the analytic (branch-
induction) route to the asymptotic BG bound — **Lemma 1** (`mixed ≤ B(k)`, `k ≤ 15`) and **Lemma A** (broom
dominance: `B(c)` maximises `total` at size `2c+1`) — are shown to be the **same extremal problem**, both
handled by the concavity-tangent linearization. `conjecture1_proved = False`.

## The exact identity (verified)

For a hub with children `c_1,…,c_j` (root degree `j+1`), with `T_i = total(c_i)`, `U_i` the root-unmatched
weight, `h_i = U_i/T_i` the child cavity field, `d_i` the child root degree, `y_i = h_i/d_i`:

```
total(hub) = (∏_i T_i) · (1 + (1/(j+1)) Σ_i y_i)          [exact; bg_branch_unification.py]
⟹  log total(hub) = Σ_i log T_i + log(1 + (Σ_i y_i)/(j+1)).
```

This is the SAME hub form as the additive potential `ell` (`ell = log total − |B|·F*`). So maximising
`total` (Lemma A) and maximising `ell` (Lemma 1) are the same objective: **`Σ (child term) + a concave
coupling in `Σ y_i``**, child term `= log T_c` (or `ell_c`) `+ μ·y_c`.

## The unified reduction (concavity tangent)

Linearising the concave `log(1 + Σy/(j+1))` at the all-cherry point gives, for BOTH lemmas,

```
objective ≤ Σ_i [ (child_value(c_i) + μ·y_{c_i}) − (cherry_value + μ·y_cherry) ] + objective(all-cherry),
```

with the exact rational tangent slope `μ = 3/(4k+3)` (Lemma 1, fixed `k`) or the size-budget shadow price
(Lemma A). Both then reduce to ONE statement:

> **Single-child extremal lemma.** The cherry maximises `child_value(c) + μ·y_c` over all rooted branches
> `c`, for `μ ≥ μ* ≈ 0.039`. (`child_value = ell_c`; `y_c = h_c/d_c`.)

- **Lemma 1** = this with `k` fixed: `μ_k = 3/(4k+3) ≥ 1/21 > μ*` for `k ≤ 15`. **Done modulo the
  single-child lemma** (`BG_LEMMA1_TANGENT_REDUCTION`).
- **Lemma A (broom dominance)** = this with the total size fixed and `k` free — a size-budgeted *knapsack*
  of the same per-branch value, whose atomic optimal unit is the cherry (size 2), so the optimum packs
  cherries = the broom.

## Why the naive exchange failed (and why this fixes it)

The direct "replace a child by the same-size max-`total` champion" exchange is **not** monotone
(6 / 24038 counterexamples, `bg_broom_exchange.py`): `total(hub)` depends on each child through
`(U_i, T_i, d_i)` jointly, and the max-`total` child can have a worse `U_i/d_i` for the matched term. In the
identity above this is exactly the `(log T_c, y_c)` trade-off: a child with large `T` (large `log T_c`) may
have small `y_c`. The concavity-tangent linearization prices that trade-off correctly with the single
scalar `μ`, converting the coupled, non-monotone exchange into independent per-branch comparisons — the
same move that dissolved Lemma 1's non-monotonicity.

## Net state of the branch-induction route

`ell(B) ≤ 0` for all rooted branches (⟹ asymptotic BG bound) now rests on:

1. **Single-child extremal lemma** — cherry maximises `ell_c + μ·y_c` for `μ ≥ μ*`. Verified exhaustively
   over all 53 272 branches to size 14, and for the per-size maxima (brooms) to size 161. **Open: the
   size-`≥15` tail for all branches** (the `(ell,y)` frontier envelope) + `μ*` as an exact rational. This
   single lemma implies BOTH Lemma 1 (`k ≤ 15`) and Lemma A (broom dominance).
2. **Slack bound** (`k ≥ 16`) — verified (`BG_BRANCH_INDUCTION`).
3. **Broom optimum** `ell(B(5)) = 0` — PROVEN, kernel-gated (the `27·23` tie).

So the whole analytic route is reduced to **one clean per-branch extremal inequality** (no hub coupling, no
non-monotonicity, no flow-freedom). This is the irreducible core — the rooted analog of the parallel Lean
session's Obligation A (Kelmans monotonicity) — now stated as a single scalar-priced statement about
individual branches. It is the same wall that keeps BG open, but maximally localised.

## For whoever picks this up

The high-value next target is the **single-child extremal lemma** (its tail). Two angles: (a) an `(ell, y)`
frontier-envelope decay bound (brooms are the per-size frontier — this loops back to broom dominance, so it
must be proven jointly / by a self-consistent frontier induction, not bootstrapped); (b) pin `μ*` exactly
and prove `ell_c + μ y_c ≤ ell_cherry + μ y_cherry` per branch by structural induction using the identity
above (each branch is a hub; recurse — but the naive IH relaxation is too loose, as the leaf case shows, so
the induction must carry the joint `(ell, y)` pair, not just `ell`). Reusable tooling built this session:
the equality-constrained Positivstellensatz engine and the Bernstein box fast-path.
