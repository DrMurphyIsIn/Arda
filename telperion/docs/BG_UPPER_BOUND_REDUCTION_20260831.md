# BG asymptotic upper bound — the composed reduction (2026-08-31)

The honest capstone: the whole branch-induction upper-bound argument, assembled into one explicit chain with
every step tagged **GATED** (a kernel-gated certificate), **BASE** (finite exhaustive check), **BOUNDARY** (an
`O(1)` constant), **LEMMA** (proven elsewhere), or **HYPOTHESIS** (the single open analytic input).
Machine-checkable at the reduction level via `telperion.bg_upper_bound.UpperBoundReduction`
(`test_bg_upper_bound.py`). `conjecture1_proved = False`.

## Goal

`F(T) = (1/|T|)·log π(T) <= F* = log(621/64)/11` asymptotically, where `π(T) = per(L)/∏deg` — the
Brualdi–Goldwasser asymptotic maximum (extremal family: the star of `B(5)`-brooms, a novel result beating Pant
2026; the lower bound `F*` is achieved and **proven**).

## The chain

| tag | statement | status |
|---|---|---|
| **0** | `1 <= π(T)/branch_total(T,r) <= 4/3`, so `(1/n)log π <= F* + O(1/n) → F*` **given** the branch ceiling | BOUNDARY (`O(1)`) |
| **1a** | branch ceiling base: `ell(B) <= 0` for `|B| <= 11` | BASE (exhaustive) |
| **1b** | branch ceiling step: `ell(hub of c_i) <= ell(B(k)) <= 0`, induction on `|B|` | LEMMA |
| **2a** | `mixed <= B(k)`, `k >= 16`: `slack_g(k) <= F*` | **GATED** `TieSlackCertificate` |
| **2b-brooms** | `mixed <= B(k)`, `k <= 15`: per-child `V(B(j)) < V(cherry)`, `B(2..8)` | **GATED** `MixedHubKKTCertificate` |
| **2b-hi** | envelope tail, `d_c >= 7`: `V(c) < V(cherry)` via ceiling `ell <= 0` | **GATED** `HighDegreeTailCertificate` |
| **2b-lo** | envelope tail, `d_c <= 6` non-broom: `ell(c) < ell(cherry) + (d_c−3)/(d_c(4k+3))` (degree-dependent) | **HYPOTHESIS (b)** |
| **3** | broom optimum: `ell(B(k)) <= 0`, `= 0` iff `k=5` (the `23`-adic tie) | **GATED** `BroomOptimumCertificate` |

Step **2** proves the mixed-hub bound: for `k <= 15` by the log-concavity tangent + per-child KKT
`V(c) <= V(cherry)` (`V(c) = ell(c) + λ(k)·x_c`, `λ(k) = 3(k+1)/(4k+3)`), whose envelope splits into 2b-brooms /
2b-hi / 2b-lo; for `k >= 16` by the slack bound. Step **1** then runs the branch induction; step **0** converts
the branch ceiling to the asymptotic bound.

## The single open input

**HYPOTHESIS (b):** every small-degree (`d_c <= 6`) non-broom branch has
`ell(c) < ell(cherry) + (d_c−3)/(d_c(4k+3))` (the degree-dependent refined ceiling; higher `d_c` → higher
threshold → nearer the plain ceiling, so the binding cases are `d=2,3`). This is the *only* non-gated,
non-finite, non-`O(1)` step. Reduced from "all branches" by the three-case envelope split; its failure mode (a
large low-root-degree near-extremal branch with `ell ≈ 0`) was **tested and refuted** — such branches are diluted
by their low-degree root (`ell ≈ −0.27`), see `branch_ell_by_vertex` (the cavity deficit view). A rigorous (b)
reduces to a per-vertex deficit lower bound for the bounded-root-degree family. Verified over all branches
`<= size 16` at every `k in [2,15]` (zero `open` non-brooms), generalized brooms (to size 66), star-of-brooms
rooted at low-degree vertices (to size 101).

## Status

`UpperBoundReduction.build().status()` →
`gated=4/4 pass; steps: GATED=4, BASE=1, BOUNDARY=1, LEMMA=1, HYPOTHESIS=1; open hypotheses=1;
conjecture_proved=False`.

So the BG asymptotic upper bound is **machine-checkable modulo one clean, restricted, well-understood analytic
lemma (b)** (plus the `O(1)` boundary constant and the finite base). `conjecture1_proved = False` — the flag flips
only when (b) is discharged and the chain is assembled in Lean. See `BG_MIXED_KKT_20260831.md`,
`BG_BROOM_DOMINANCE_20260831.md`, `BG_STAR_OF_BROOMS_HANDOFF.md`.
