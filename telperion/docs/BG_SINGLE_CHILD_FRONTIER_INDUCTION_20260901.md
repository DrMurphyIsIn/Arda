# Single-child frontier induction: outcome (2026-09-01)

Attack on the one remaining wall — the **single-child extremal lemma** (`ell_c + μ·y_c ≤ V` for all rooted
branches, `μ ≥ μ* ≈ 0.038`, `y_c = h_c/d_c`, `V = ell_cherry + μ·y_cherry`), which implies BOTH branch-
induction lemmas (`BG_BRANCH_UNIFICATION`). Verified to size 14; the tail was open. `conjecture1_proved =
False`.

## The idea: a concave frontier invariant

The naive IH (carry only `ell_c ≤ V − μ y_c`) is too loose (fails at the cherry, whose leaf child has
`ell = −F* ≪ V − μ`). Fix: carry the joint invariant `ell_c ≤ Φ(y_c)` for a concave `Φ` that drops fast at
high `y`. The hub recursion `ell_c = Σ_i ell_{c_i} + L₀(Y)`, `L₀(Y) = log((j+1+Y)/(j+1)) − F*`,
`Y = Σ y_{c_i}`, `y_c = 1/(j+1+Y)`, closes the induction **iff** `Φ` is *preserved*:
`Σ_i Φ(y_{c_i}) + L₀(Y) ≤ Φ(y_c)`.

## What worked, and what broke it

- **Preservation holds to size 13** for the concave broom-frontier `Φ` (vertices = brooms `B(4),B(5),B(6)`
  + cherry + leaf): worst gap `+2·10⁻⁵` (`bg_frontier_preservation.py`), with **equality at the brooms**
  (that's just the exact broom recursion). Encouraging.
- **But `Φ` (the simple broom hull) is NOT the true frontier.** The **recursive-`B(5)`** branches — a hub of
  `j` copies of `B(5)` — have `ell → −0.084` (bounded, not `→ −∞`) with `y → 0`
  (`bg_recursive_nonbinding.py`): e.g. `j=40`, size 441, `ell = −0.0868`, `y = 0.0216`. That **exceeds** the
  simple broom-frontier value at small `y` (where brooms have `ell < −0.2`). So the simple-frontier
  induction is unsound beyond the sizes tested — the true `(y, ell)` frontier is **recursive/self-similar**,
  not the broom hull. (This is the same recursive-`B(5)` substructure that makes `mixed > B(k)` for
  `k ≥ 20`.)
- The Jensen relaxation of preservation (`j·Φ(Y/j) + L₀ ≤ Φ(y_c)`) already fails at `j = 24`
  (`bg_frontier_reduced_ineq.py`, gap `+0.003`) — a second symptom that the simple `Φ` is wrong for large
  hubs.

## The one genuinely useful structural fact

**The lemma is NON-binding for large branches.** The recursive-`B(5)` limit gives `ell + μ·y → −0.086 ≪ V`
(`V ≈ 0.005`), so large branches are far from the bound. The binding region is **small-to-medium** branches:
- size `≤ 14`: exhaustively verified (`Σ = 53 272` branches);
- the near-binding branches are the brooms `B(6), B(7)` (sizes 13, 15), `ell + μ·y ≈ +0.003 < V`;
- size `> 27`: brooms `ell < −0.03`, recursive structures `≈ −0.086`, all comfortably `< V`.

So the tail reduces to: **broom dominance on the finite size range `~15–27`** (max `ell` per size = broom,
each broom already `< V`) **plus a uniform `ell`-envelope for size `> 27`**. Both are the same
max-`ell`-per-size statement — i.e. **broom dominance / the Kelmans wall**.

## Honest conclusion

The frontier induction **does not close** the single-child lemma: the true frontier is recursive, so no
simple concave majorant is preserved. But it **localised the difficulty decisively** — the lemma is
non-binding for large branches, and its open tail is broom dominance on a *bounded* size range (plus a crude
large-size envelope). The irreducible core is unchanged: **broom dominance (max total/`ell` per size = broom)
= the rooted Kelmans exchange = the parallel Lean session's Obligation A.** That is the wall that keeps BG
open; this session localised it to a per-branch, finite-size-range statement and built the tangent /
unification machinery around it, but did not breach it. `conjecture1_proved = False`.

## For the next attempt

The most promising remaining angle is **finite-range broom dominance** (sizes `~11–27`): a bounded extremal
check where the exchange must show `total(B(c)) ≥ total(any size-2c+1 branch)`. The `(U, total, d)`-coupled
exchange (the `bg_broom_exchange` counterexamples) is the obstacle; a correct exchange must dominate in the
joint `(log T, y)` order, which the tangent prices — pairing the tangent method with a careful compression
move (the rooted analog of `pushInto`) is the natural line. Reusable: the equality-constrained
Positivstellensatz engine and the Bernstein box fast-path.
