# Taking the extremality apart: the single-child lemma on an invariant price interval (2026-09-02)

The sole remaining open input of the BG asymptotic upper bound (after the near-broom unimodality closed the tail)
was the **extremality**: the near-broom `(d−2) cherries + B(m)` is the argmax `ell` over ALL non-broom
root-degree-d branches. This note dismantles it into a **joint induction on `|c|` over an invariant price
interval**, verifies all pieces with margins, and gates the price-flow backbone. `conjecture1_proved = False`.

## The reduction

The extremality is the **single-child lemma** (SCL): for a degree-`d` hub, every child `c` satisfies
`V_μ(c) := ell(c) + μ·y_c ≤ V_μ(cherry)` at price `μ_d = 3/(4d−1)`. Given SCL, the concavity tangent of
`L(s) = log(1+s/d) − F*` at the all-cherry point `s* = (d−1)/3` yields `ell(hub) ≤ ell(B(d−1))` (verified exact,
worst gap 0), and the strict child gaps pin the argmax to the near-broom.

SCL is proved by **joint induction on `|c|`**. The obstacle that stalled every prior attempt was **price flow**:
the tangent linearization sends a hub's price `μ` to its children's price
`μ'' = 3[(4d−1) − 3μ]/(4d−1)²`. The resolution is a single invariant interval.

### The invariant interval `I = [456/3703, 3/7]`

- `μ'' ` is decreasing in `μ`; the map keeps `I` invariant for **every** hub-degree `d ∈ {2..6}` (exact rational —
  checked at both endpoints). Its floor `A = 456/3703` is exactly the **fixed point of the tightest (d=6) map**,
  `μ''(6, 3/7) = 456/3703`.
- All actual hub prices `μ_d = 3/(4d−1)` (d=2..6) lie in `I`.

This is gated: `ExtremalityPriceMapCertificate` (20 pure-rational `norm_num` atoms).

### Why `I` is exactly the right interval (the tie boundary)

At `μ = 0`, `V_0(c) = ell(c)`, and the broom `B(5)` — the k=5 tie, `ell = 0` — **beats** the cherry
(`ELL_CH = −0.0077`). So SCL is *false* below the crossover `μ ≈ 0.038`. The interval floor `A = 0.1231` sits
safely **above** that crossover, so on `I` the cherry dominates every child. `I` is the largest window that both
contains the hub prices and stays clear of the tie's low-price inversion — and the price map is exactly closed on
it. The tie's shadow is what sets the floor.

## The pieces (all verified; margins on `I`)

| # | piece | status | margin on `I` |
|---|---|---|---|
| 1 | price map keeps `I` invariant, prices ∈ `I` (d=2..6) | **GATED** (ExtremalityPriceMap, exact rational) | — |
| 2 | tangent step `V_μ(hub) ≤ V_μ(B(d−1))` (log-concavity) | verified exact (worst gap 0) | 0 (tight) |
| 3 | SCL for non-broom deg≥2 children | verified (enum ≤ size 15) | **+0.031** |
| 4 | broom-vs-cherry `V_μ(B(k)) ≤ V_μ(cherry)`, all k | verified (unimodal in k) | **+0.012** |
| 5 | leaf→cherry raises `ell` and `y_c` (hence `V_μ`), d≥3 | verified (only exception = the cherry base) | — |
| 6 | deg≥7 children | **GATED** (HighDegreeTailCertificate) | — |

Assembly: for a hub of degree `d ≤ 6`, every child is a leaf (excluded by #5 — leaves never occur in the
extremum), a broom (#4), a deg≥7 branch (#6), or a non-broom deg≤6 branch (#3 via IH at price `μ'' ∈ I` by #1).
So every child satisfies `V_{μ''}(c) ≤ V_{μ''}(cherry)`; the tangent (#2) gives `ell(hub) ≤ ell(B(d−1))`, and the
strict gaps pin the near-broom as the argmax. `⇒ EXTREMALITY.`

## Honest status

The extremality is no longer a monolithic frontier — it is a **6-piece reduction**, all pieces verified with
comfortable margins (≥ +0.012), with pieces 1 and 6 kernel-gated. What remains is: the certificates for the
broom-vs-cherry family (#4, a one-parameter unimodality — the same 11th-root technique as the near-broom) and the
leaf-exchange (#5, a per-degree finite inequality), plus the **induction assembly** itself (bookkeeping that #1–6
compose into the size-induction). None of these is a transcendental wall; the analytic obstacle (price flow) is
solved by the invariant interval. `conjecture1_proved = False`.
