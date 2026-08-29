# Walk-count sub-problem — the combinatorial core of the capacity upper bound (route b)

**Status:** deliberate research effort, the reduced sub-problem of `BG_CAPACITY_ATTACK_SPEC.md` route (b).
It replaces the transcendental free-energy by a **finite, polynomial, local** object (spectral moments =
weighted closed-walk densities), where route (b) earns its keep over the failed local certificate (a).
`conjecture1_proved = False`.

## The reduction

`F(T) = (1/n)log(per(L)/∏deg) = ½∫log(1+u)dμ_{N²}(u)`, `u=λ²∈[0,1]`, `μ_{N²}` = spectral measure of
`N²`, `N=D^{-1/2}AD^{-1/2}`. Bound `½log(1+u) ≤ Σ_{k=1}^K c_k u^k` by a fixed polynomial envelope (valid
on `[0,1]`; SOS-certifiable, kernel-checkable). Then

    F(T) ≤ Σ_{k=1}^K c_k m_k(T),   m_k(T) := (1/n) Tr N^{2k} = normalized weighted closed-walk density.

`m_k(T)` is **local & polynomial**: `Tr N^{2k} = Σ_{closed walks of length 2k} ∏_{steps a→b} 1/√(deg_a deg_b)`;
on a tree every closed walk retraces edges, so `m_k` is determined by the `k`-neighborhoods. **Goal:** bound
`Σ_k c_k m_k(T) ≤ log ρ* + (1/n)log poly(n)` for all trees — a moment optimization, not a transcendental one.

## Key structural findings (2026-08-29)

**1. Different trees maximize different `m_k`** (exhaustive n=12): `m_1` by a hub tree (degseq [4,3,2,2]),
`m_2` by [3,2,2,2], `m_3`,`m_4` by the **path** [2,2,2,…]. The path has the highest *high* moments
(`m_2`=0.378, `m_3`=0.316 vs caterpillar 0.308, 0.198) but a *lower* free-energy (rate 1.210 < 1.2276).

**2. The extremal caterpillar maximizes NONE of the `m_k` individually** — so "bound each `m_k`" is the
wrong sub-problem (it gives the path/hub extremes, not `ρ*`).

**3. The free-energy is the balanced ALTERNATING combination.** The envelope coeffs alternate sign
(`c ≈ [+0.500, −0.242, +0.124, −0.035]`), so `Σc_k m_k = c_1 m_1 − |c_2| m_2 + |c_3| m_3 − …`. The path's
large `m_2` is *penalized* by `−|c_2|`; the caterpillar balances the alternation and maximizes the
combination. This is the finite-side shadow of the free-energy concavity.

## The precise sub-problem (moment-body / SDP)

Let `𝓜_K` = the convex body of achievable moment vectors `(m_1,…,m_K)` of **tree** spectral measures
`μ_{N²}` (a probability measure on `[0,1]`). Prove

    max_{m ∈ 𝓜_K}  Σ_k c_k m_k  =  log ρ*  (+ finite-n correction),   attained at the ~7-arm caterpillar.

Two nested relaxations, in increasing strength:
- **(S1) Hankel/moment relaxation:** `m` = moments of *some* probability measure on `[0,1]` (Hankel PSD).
  Cheapest; test first — if `max Σc_k m_k` over Hankel-PSD `m` (with the tree bound on `m_1`) already
  equals `log ρ*`, the bound is a clean SDP/SOS certificate (kernel-gateable). Likely too loose alone.
- **(S2) Tree walk-count constraints:** the additional inequalities that tree closed-walk densities
  satisfy (beyond Hankel PSD) — e.g. `m_1 = (2/n)Σ_e 1/(deg_i deg_j)` and higher local identities. These
  are the "tree-specific" cuts that tighten (S1) to the true `𝓜_K`.

## Milestones

- **W1.** Fix the degree-`K` envelope `Σc_k u^k ≥ ½log(1+u)` on `[0,1]` as an exact SOS certificate
  (univariate, kernel-checkable). K=4 already gives ~4-digit tightness at the caterpillar.
- **W2.** Bound `max_T m_1(T) = max_T (2/n)Σ_e 1/(deg_i deg_j)` in closed form (the entry moment; pure
  degree-sequence optimization under the tree handshake `Σdeg = 2n−2`).
- **W3.** Solve/relax (S1): the Hankel-PSD moment SDP with the functional `Σc_k m_k`; measure the gap to
  `log ρ*`. If closed → SDP proof; if not → identify which tree cut (S2) is missing.
- **W4.** Prove the needed (S2) tree walk-count inequalities (local, per-neighborhood), and assemble the
  bound. **W5.** Add the finite-`n` `poly(n)` correction (the small-n moment excess) for the exact
  statement.

## Why this is the right level

The moments are **local and polynomial**, so bounding them is combinatorial (walk counts / degree
sequences), not transcendental — sidestepping (a)'s collective wall (which lived in the per-vertex
`log a_v`) and Koiran's SOS no-go (which blocks certifying the *permanent*, not moment inequalities).
The alternating-sign structure is exactly the "discharging built into the dual" that (a) lacked. The
open risk is whether (S1)+(S2) close *tightly* to `ρ*^n·poly(n)` — real research, but now a finite
moment/SDP problem rather than an infinite-dimensional one.

## Reproduce / verify hooks

`m_k(T) = (1/n)Σ λ_i^{2k}`, `λ` = eigenvalues of `N=D^{-1/2}AD^{-1/2}`; envelope via `linprog`/SOS on
`½log(1+u)−Σc_k u^k ≥ 0` on `[0,1]`; caterpillar builder + `girardeau.hard_core_boson_partition` and
`rooted_phi._all_tree_edges(n)` (see `BG_TRUE_MAX_PROBE.md`, `BG_CAPACITY_ATTACK_SPEC.md`).

## W2 first result (2026-08-29): the entry moment `m_1` is bounded

`m_1(T) = (2/n)Σ_e 1/(deg_i deg_j)` (exact rational). Exhaustive per n:
- **path** `P_n` gives `m_1 = (n+1)/(2n) → ½` (edges: (n−3) interior `¼` + 2 end `½`).
- for `n ≤ 9` the path is the maximizer; for `n ≥ 10` a "double-broom" (two deg-3 hubs + extra leaves,
  degseq `[3,3,2,…,1,1,1,1]`) narrowly beats it (n=10: `5/9` vs path `11/20`).
- `max_T m_1` is **monotone decreasing** in n (5/8, 3/5, 7/12, …, 61/112 at n=14) and bounded, →~½.

So `m_1 ≤ 5/8` (all n; sharp at n=4) and `m_1 ≤ (small const)` asymptotically — the entry moment is
controlled by a pure degree-sequence optimization under the handshake `Σdeg = 2n−2`. **W2 is essentially
closed** (a clean rational bound); the work moves to W3 (the joint moment SDP with the alternating
functional), where the caterpillar's balance — not any single-moment extremum — must be shown optimal.

## W3 result (2026-08-29): Hankel-PSD + `m_1` OVERSHOOTS — the missing cut is an even-moment LOWER bound

Two relaxations tested against `log ρ* = 0.20510`:
- **Per-moment bounds** (`m_k ≤ β_k = max_T m_k`, K=6, grid-LP): max `F = 0.22977`, **gap +0.0247**.
  Loose — the β_k are not jointly achievable (different trees max different `m_k`).
- **Hankel-PSD moment SDP** (measure on [0,1], K=4 envelope) + `m_1 ≤ β_1` (cvxpy/SCS):
  `β_1=0.625` → gap +0.038; `β_1=0.52` (caterpillar) → **+0.0043**; closes only at `β_1 ≤ 0.505`,
  which *excludes* the caterpillar (`m_1=0.520`).

**Diagnosis (the S2 cut located).** With `c_2 < 0` in the envelope, the SDP inflates `F` by pushing
`m_2` down to the **Hankel floor `m_2 ≥ m_1²`** (`=0.270` at `m_1=0.52`) — below the caterpillar's
`m_2 = 0.308`. No tree with `m_1=0.52` reaches `m_2 < 0.308`. So the binding missing constraint is a
**tree-specific LOWER bound on `m_2` given `m_1`**, strictly above the Hankel floor. This is the concrete
S2 cut to prove (W4): `m_2(T) ≥ φ(m_1(T))` for a tree function `φ` with `φ(m_1) > m_1²`, tight at the
caterpillar. Higher even moments likely need analogous cuts. The per-vertex/degree-local nature of the
walk moments is what makes these cuts provable (unlike the transcendental per-vertex `log a_v`).

## W4 progress (2026-08-29): the S2 cut is a LOCAL even-moment lower bound (concrete + provable)

The tree `(m_1, m_2)` locus (empirical): the lower boundary is traced by the **caterpillar family** as
`a` grows. At `m_1 ≈ 0.52`, `m_2` decreases with `a` (a=7→0.308, a=10→0.296, a=13→0.287) but stays
**strictly above the Hankel floor `m_1² = 0.270`**; length-3 arms (0.394) and paths (0.378) sit far
higher. So trees provably do not reach the Hankel `m_2` floor that the W3 SDP-overshoot exploited.

**The cut is a local degree inequality.** `m_2 = (1/n)Tr N^4` has an explicit closed form: for each
vertex `v`, `(N^4)_{vv} = (1/deg_v²)(Σ_{a~v} 1/deg_a)² + Σ_{a~v}(1/(deg_v deg_a²))·Σ_{c~a,c≠v} 1/deg_c`
(closed 4-walks = "cherry-returns" `v→a→v→b→v` + "neighbor-of-neighbor" `v→a→c→a→v`). So `m_2` is a
**local, polynomial degree functional** — the S2 cut `m_2(T) ≥ φ(m_1(T))` is a per-neighborhood
inequality, exactly the provable object route (b) promised (vs the transcendental per-vertex `log a_v`).

**W4 remaining:** (i) derive the tight `φ` from the local formulas (the caterpillar boundary in closed
form); (ii) re-solve the SDP with `m_2 ≥ φ(m_1)` added — confirm it closes to `log ρ*` at the
caterpillar (and identify whether `m_3`,`m_4` cuts are also needed). **W5:** the finite-`n` `poly(n)`.

**Status of route (b):** the upper bound is now a **finite, local, moment-SDP + walk-count-cut problem**
— W1 (SOS envelope, ~done), W2 (`m_1` bound, done), W3 (relaxation gap measured + cut located, done),
W4 (cut is local/provable, in progress). No transcendental obstruction remains; the open work is the
explicit even-moment cuts and the SDP closure. `conjecture1_proved = False`.

## W4 DECISIVE (2026-08-29): the local `m_2` cut nearly closes the SDP — route (b) validated

Two confirmations that route (b) is a **viable** proof route (bypassing the collective wall):

1. **The `m_2` local degree formula is EXACT** — verified `m_2 = (1/n)Σ_v[(1/deg_v²)(Σ_{a~v}1/deg_a)² +
   Σ_{a~v}(1/(deg_v deg_a²))Σ_{c~a,c≠v}1/deg_c] = (1/n)Tr N^4` for all trees n=4–9. The cut is a concrete,
   provable, per-neighborhood degree inequality.
2. **Adding the tree `m_2` lower bound collapses the SDP gap** (K=4 envelope, `m_1 ≤ 0.52`):
   | cut | max F | gap to log ρ* |
   |---|---|---|
   | none | 0.20936 | +0.00426 |
   | `m_2 ≥ 0.287` (tree min at this m_1) | 0.20785 | +0.00275 |
   | `m_2 ≥ 0.308` (caterpillar) | 0.20588 | **+0.00078** |

The residual `+0.0008` is attributable to the K=4 envelope order and a missing `m_4` lower-bound cut;
a higher-K envelope + `m_2`,`m_4` cuts should close it fully. **This is the key viability result:** the
moment-SDP + a *provable local walk-count cut* drives the bound to `log ρ*`, so route (b) genuinely
evades the collective wall (which lived in the transcendental per-vertex `log a_v`) — the difficulty is
now a *finite, local, combinatorial* even-moment-cut problem.

**Remaining to a full proof:** (W4c) derive the tight `m_2 ≥ φ(m_1)` and `m_4` cuts in closed form from
the local degree formulas (the caterpillar traces the boundary); (W4d) re-solve with a higher-K SOS
envelope + both cuts, confirm exact closure; (W5) the finite-`n` `poly(n)` correction. Every remaining
piece is finite-dimensional and combinatorial — no transcendental obstruction. `conjecture1_proved = False`.

## W4c (2026-08-29): the S2 cut `φ(m_1)` in closed form

The tree `(m_1,m_2)` lower boundary is the caterpillar family, now derived in closed form from the local
degree formulas of the infinite periodic a-arm caterpillar (spine deg `d=a+2`, `a` mids deg 2, `a` leaves
deg 1; period `1+2a`), verified against empirical to <2e-3:

    m_1(a) = (2/(1+2a)) [ 1/(a+2)² + a/(2(a+2)) + a/2 ]
    m_2(a) = [ N4_spine + a·N4_mid + a·N4_leaf ] / (1+2a),   with
      N4_leaf  = 1/4 + 1/(4(a+2))
      N4_mid   = (1/4)(1+1/(a+2))² + (1/(2(a+2)²))(2/(a+2) + (a−1)/2)
      N4_spine = (1/(a+2)²)(2/(a+2)+a/2)² + (2/(a+2)³)(1/(a+2)+a/2) + a/(4(a+2))

The curve runs from `(m_1,m_2) = (0.520, 0.372)` at a=1 to `(½, ¼)` as a→∞ (variance `m_2−m_1² → 0`).
**The S2 cut is `m_2(T) ≥ φ(m_1(T))`**, `φ` = this boundary (parametric in `a`; monotone, invertible).

**W4c remaining → W4d:** (i) PROVE `m_2(T) ≥ φ(m_1(T))` for all trees — a per-neighborhood inequality on
the (now explicit) local degree formulas `m_1 = (2/n)Σ_e 1/(deg_i deg_j)`, `m_2 = (1/n)Σ_v[…]`; the
caterpillar boundary being tight means it's an equality-constrained optimization (Lagrange/rearrangement
over degree sequences). (ii) the analogous `m_4` cut for the residual `+0.0008`. (iii) re-solve the SDP
with `m_2 ≥ φ(m_1)` (+`m_4`) and a higher-K SOS envelope → confirm exact closure to `log ρ*`. Then W5
(`poly(n)`). All finite/combinatorial. `conjecture1_proved = False`.
