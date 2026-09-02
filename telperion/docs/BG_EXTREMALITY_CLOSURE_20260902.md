# Closing the 6-piece extremality reduction: pieces #4 and #5 gated, residual is pure induction bookkeeping (2026-09-02)

Continuing the extremality dismantling (`BG_EXTREMALITY_REDUCTION_20260902`), this closes the two remaining
buildable certificates (#4 broom-vs-cherry, #5 leaf-exchange). Every analytic/rational leaf of the extremality is
now kernel-gated; the sole open input is the **structural SCL induction assembly** (well-founded recursion on
`|c|`), not a wall. `conjecture1_proved = False`.

## The two closures

Both collapsed to small, exact certificates — the same "clear F* through the 11th power" pattern.

### #5 Leaf-exchange — a single pure-rational atom

For a hub of degree `d >= 3`, replacing a bare **leaf** child (`y=1`) by a **cherry** child (`y=1/3`) changes ell by
`Delta = (log(3/2) - F*) + log((d+s-2/3)/(d+s))` (the cherry drops `s` by `2/3`). Then
```
Delta > 0  <=>  (d+s-2/3)/(d+s) > (2/3)(621/64)^{1/11}  <=>  [(d+s-2/3)/(d+s)]^11 > (2/3)^11 (621/64)
```
(both sides in `(0,1)`; the 11th power clears `F*` and preserves order). The bracket is increasing in `d+s`, and
`d >= 3` with a leaf present forces `s >= 1`, so `d+s >= 4`; the worst case `d+s=4` gives bracket `= 5/6`. A
**single** atom closes it for all such hubs:
```
(5/6)^11  >  (2/3)^11 (621/64)      [ 48828125/362797056 > 736/6561, margin +0.022 ]
```
`LeafExchangeCertificate` (1 atom). And leaf->cherry also raises `y_c` (s drops), so it raises `V_mu` too — bare
leaves never occur in the ell- or V-extremum. (The one d=2 exception is exactly the cherry base, which is excluded.)

### #4 Broom-vs-cherry — finite head + broom-optimum tail

`V_mu(B(k)) = ell(B(k)) + mu*y_{B(k)} <= V_mu(cherry)` for all `k >= 1` and `mu in I = [456/3703, 3/7]`
(`y_{B(k)} = 3/(4k+3)`). Linear in `mu`, so the two endpoints of `I` bound it. Split by `k`:
- **head `k = 1..4`** — cleared `x11`, frozen log-enclosures: `11 L(bt(k)) - 11 L(3/2) - (2k-1) L(621/64) <= 11 mu (1/3 - 3/(4k+3))`, `bt(k) = 7/4, 11/4, 135/32, 513/80`.
- **tail `k >= 5`** — `ell(B(k)) <= 0` (broom optimum, `= 0` at the `k=5` tie) and `y_{B(k)} <= 3/23`, so
  `V_mu(B(k)) <= mu*3/23`; the atom `mu*3/23 <= V_mu(cherry)` closes all `k >= 5` at once (tight at `k=5`).

`BroomVsCherryCertificate` (10 atoms: (k=1..4 + tail) × 2 endpoints). The tie `B(5)` only beats the cherry
*below* `I` (crossover `mu ~ 0.038 < A = 0.1231`) — which is exactly why `I` is the right interval.

## The 6 pieces — final status

| # | piece | status |
|---|---|---|
| 1 | price map keeps `I` invariant | **GATED** `ExtremalityPriceMapCertificate` (20 atoms) |
| 2 | tangent `V_mu(hub) <= V_mu(B(d-1))` | **LEMMA** (concavity of `Real.log`) |
| 3 | SCL for non-broom deg≥2 children | the induction *conclusion* (proved by the assembly) |
| 4 | broom-vs-cherry, all k | **GATED** `BroomVsCherryCertificate` (10 atoms) |
| 5 | leaf→cherry raises ell & y | **GATED** `LeafExchangeCertificate` (1 atom) |
| 6 | deg≥7 children | **GATED** `HighDegreeTailCertificate` |

## What remains: the assembly (structural, not analytic)

The sole open hypothesis (`2b-lo-extremality`) is now the **joint size-induction** that composes #1–6: by strong
induction on `|c|`, every child of a degree-`d ≤ 6` hub is a leaf (excluded, #5), a broom (#4), deg≥7 (#6), or a
non-broom deg≤6 branch (IH at price `mu'' in I` by #1) — so `V_{mu''}(child) <= V_{mu''}(cherry)`; the tangent
(#2) gives `ell(hub) <= ell(B(d-1))`, pinning the near-broom as the argmax. This is a Lean **well-founded
recursion** proof (shared with the parallel session's Obligation A), not a transcendental obstacle — all its
analytic and rational inputs are now kernel-gated.

## Ledger

`bg_upper_bound.py`: `gated = 9/9`, 2 LEMMA (branch-ceiling step, tangent), 1 HYPOTHESIS (the assembly).
Tests green (27). `conjecture1_proved = False` — and it stays there until the assembly is formalized. But the
full upper bound is now visible and gated end to end: base + boundary + slack + KKT brooms + high-degree tail +
M_d (near-broom unimodality) + extremality (price map + tangent + broom-vs-cherry + leaf-exchange) + broom
optimum — with only the extremality's induction bookkeeping left to write.
