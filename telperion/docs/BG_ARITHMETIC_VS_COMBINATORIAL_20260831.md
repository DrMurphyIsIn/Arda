# BG: the arithmetic is done, the residual is combinatorial (2026-08-31)

A structural synthesis. The Brualdi–Goldwasser upper bound `ell(B) <= 0` for rooted branches factors into two
independent poles — and after this campaign they sit in very different states. `conjecture1_proved = False`.

## The two poles

`ell(B) = log total(B) - |B| F*`. The branch ceiling `ell(B) <= 0` is equivalent to:

- **(A) BROOM DOMINANCE — combinatorial, OPEN.** The broom `B(c)` maximises `total(B)` among all rooted branches
  of size `2c+1`. Verified unique-max for every odd size `<= 13` (`broom_dominance_holds`). This is the rooted
  analog of the tree→hub / Kelmans reduction — the same core the parallel Lean session calls **Obligation A**. It
  is about *structure* (which shape packs the most weighted matchings), not arithmetic.
- **(B) BROOM OPTIMUM — arithmetic, GATED.** Among brooms, `ell(B(c)) <= 0` with equality iff `c = 5`. Closed for
  all `c` by the `broom_ratio` single-crossing; kernel-gated (`BroomOptimumCertificate`, `bg_broom_optimum`).

## The arithmetic pole is fully resolved — and it is all one prime

The `c = 5` optimum is pinned by the single prime **23**, appearing in three places
(`broom_optimum_prime`, all exact):

- `4·5 + 3 = 23` — the numerator of `total(B(5)) = 621/64 = 27·23/64`;
- `4·4 + 7 = 23` — the `broom_ratio` crossing factor `g(4) = (4·4+7)(4+1) = 23·5` at the integer boundary `s = 4|5`;
- `23² = 529` — the `broom_ratio` constant `529/486` (`486 = 2·3⁵`).

Since `4s+7 = 4(s+1)+3` identically, the *same* prime `23` at `c = 5` pins the optimum in the numerator, the
crossing, and the constant. This is why the value is the **exact rational** `621/64` — a crystal, not a
quasicrystal — and why the closing of (B) is arithmetic. The **integrality gap** (`bg_smooth_nogo`) proves the
complement: the continuous relaxation overshoots `F*`, so no smooth certificate can reach it. Both are gated.

## The self-similarity: the branch-induction residual (b) is a facet of (A)

The mixed-hub / concavity-KKT route reaches `ell(B) <= 0` by induction, needing the per-child envelope
`V(c) <= V(cherry)`, whose residual (b) is the small-degree non-broom case. The envelope's **extremal children
are brooms at every degree** — verified for the main envelope (`MixedHubKKTCertificate`) and for the `d=2`
sub-envelope, whose top children are `leaf → cherry → root→cherry → …` (the broom family again). So the
branch-induction route does *not* escape the combinatorial core; it relocates it. **(b) is a facet of broom
dominance (A)** — the same structural principle, in the branch-induction guise. Honest correction to the earlier
"bypasses Obligation A" framing: the arithmetic half was bypassable (and is gated); the combinatorial half is
shared.

## Why (A) is hard: the exchange obstruction

Broom dominance is not near-degenerate — at *fixed* size the broom wins by a clear margin (`0.24`–`0.72` in
`total` for sizes 7–13), unlike the flat *arm-count* landscape (the arithmetic pole). So the difficulty is not
delicacy. It is that the natural proof — a local **exchange** move driving any tree toward the broom — has **no
clean sign**. Concretely, for two hubs joined by an edge (`a` and `b` cherry-arms), moving a cherry from the
source hub to the target has

```
ΔZ > 0  ⟺  b > a + 1      (stable at b = a + 1, i.e. near-balanced),
ΔZ < 0  ⟺  b ≤ a          (concentrating onto an equal/bigger hub LOWERS Z).
```

So *within* a two-hub family the optimum is **near-balanced**, yet the **global** maximiser is the **single
hub** (the broom, `degseq = [c, 2×c, 1×c]`, verified the unrooted `per(L)/∏deg` max for `n ≤ 15`). The greedy
concentration move therefore goes *downhill* on the way from a balanced multi-hub to the single-hub broom — a
`Z`-barrier. A one-move exchange cannot prove (A); the proof needs a non-greedy / multi-move argument (GTS-style
coefficientwise domination, or a global potential). This is the precise structural reason Obligation A is open —
the combinatorial analog of the smooth no-go: the honest obstruction, isolated.

## Where this leaves the campaign

| pole | nature | state |
|---|---|---|
| broom optimum `c=5` | arithmetic (prime 23) | **GATED** (`bg_broom_optimum`) |
| no smooth proof exists | arithmetic (integrality gap) | **GATED** (`bg_smooth_nogo`) |
| mixed-hub / envelope reduction | analytic | **GATED** (`bg_mixed_kkt`, `bg_hi_degree_tail`, `bg_tie_slack`) |
| **broom dominance (A)** = residual (b) | **combinatorial** | **OPEN** (verified `<= size 13`; shared with Obligation A) |

The remaining work is a single combinatorial extremal lemma — brooms pack the most weighted matchings per size —
not more arithmetic and (by the no-go) not any smooth certificate. It is exactly the object the parallel Lean
session is attacking. `conjecture1_proved = False`. See `BG_INTEGRALITY_GAP_20260831.md`,
`BG_UPPER_BOUND_REDUCTION_20260831.md`, `BG_STAR_OF_BROOMS_HANDOFF.md`.
