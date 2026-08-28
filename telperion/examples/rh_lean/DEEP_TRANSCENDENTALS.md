# Reaching the deep transcendentals in-kernel — roadmap (NOT a proof)

This document is a **formalization roadmap**, grounded in what was verified about
Mathlib and mpmath during this session. It contains **no proved theorems** — the
Lean snippets are sketches with `sorry`, kept out of the built `RH` library on
purpose, so nothing here is conflated with the kernel-proven line.

## The gap, precisely

Every RH-necessary certificate (`turan_xi`, `jensen_xi`, `toeplitz_xi`,
`newton_xi`) is **enclosure-conditional**: it takes `lo_k < a_k < hi_k` (with
`a_k = [z^{2k}] ξ(1/2+z)`) as *imported hypotheses*. To make them
**unconditional**, Lean must prove those enclosures itself. That requires
in-kernel numeric bounds on the deep transcendentals:

1. `ζ(1/2) ∈ [lo, hi]` (and `ζ^{(j)}(1/2)`),
2. `Γ(1/4)`, `Γ^{(j)}(1/2)` bounds,
3. the Stieltjes constants `γ_n` (for the ξ Taylor expansion),
4. and finally `a_k` assembled from 1–3 via `ξ = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)`.

## What Mathlib has vs. lacks (verified this session)

| Ingredient | Mathlib status |
|---|---|
| `Real.pi` decimal bounds | **HAS** (`Real.pi_gt_3141592`, …) — used in `pi_bracket` |
| `Real.exp` Taylor bound | **HAS** (`Real.sum_le_exp_of_nonneg`) — used in `exp_bracket` |
| `Real.log` convex bounds | **HAS** (`Real.log_le_sub_one_of_pos`) — used in `log_bound` |
| `Real.log 2` decimal bounds | **HAS** (`Real.log_two_lt_d9`, `_gt_d9`) — for tight log |
| `Γ(1/2) = √π` | **HAS** (`Real.Gamma_one_half_eq`) |
| `Γ` numeric bounds at rationals | partial (convexity/Bohr–Mollerup; no ready `Γ(1/4) ∈ [lo,hi]`) |
| `riemannZeta` defined, `ζ(2)=π²/6`, functional eq. | **HAS** |
| **`ζ(s) ∈ [lo,hi]` for general s (esp. 1/2)** | **LACKS** — the crux |
| `ζ` derivatives, Stieltjes constants | **LACKS** |
| Euler–Maclaurin with explicit remainder | partial / not in usable numeric form |
| Alternating series bounds | **HAS** (`tsum`/`Finset.sum` alternating estimates) |

mpmath cross-check: `iv.pi`, `iv.gamma` give **rigorous intervals** (usable as
the numeric targets); `iv.zeta` is **broken** (no Bernoulli in the interval
context), and the naive η-series for ζ(1/2) converges as `1/√N` — too slow. So
even the *Python* rigorous ζ(1/2) needs acceleration; this is genuinely hard on
both ends.

## Cleanest path for `ζ(1/2)` in-kernel

Avoid Euler–Maclaurin (Bernoulli remainder is painful to formalize). Use the
**globally convergent Hasse / Cohen–Villegas–Zagier alternating representation**,
whose tail is geometric (`~ 3^{-N}`), so a rigorous rational bracket needs only
`O(digits)` terms and elementary estimates:

```
η(s) = Σ_{n≥0} 1/2^{n+1} Σ_{k=0}^{n} (-1)^k C(n,k) (k+1)^{-s},   ζ(s) = η(s)/(1−2^{1−s}).
```

Formalization stages (each a real lemma):
1. `k^{-1/2}` rational bounds — a **`SqrtBracketCertificate`** (√ via `Real.le_sqrt`
   / `Real.sqrt_le'`), the missing transcendental primitive. *(buildable next.)*
2. The CVZ partial sum `S_N` as an exact rational combination of the `(k+1)^{-1/2}`
   brackets.
3. A rigorous geometric tail bound `|η(1/2) − S_N| ≤ C·d_N` (the CVZ error lemma) —
   the one genuinely new analytic lemma; Mathlib has the alternating-series
   scaffolding but not this specific bound.
4. `ζ(1/2) = η(1/2)/(1−√2)` with `√2` bracketed (stage 1) → the final
   `ζ(1/2) ∈ [lo,hi]`.

Sketch (with `sorry` at the genuine gaps — **not compiled, not in `RH`**):

```lean
-- SCAFFOLD ONLY -- sorries mark the real Mathlib gaps.
theorem zeta_half_bracket :
    (-1.46036 : ℝ) < riemannZeta (1/2) ∧ riemannZeta (1/2) < (-1.46035 : ℝ) := by
  -- 1. sqrt brackets for (k+1)^{-1/2}, k ≤ N            (SqrtBracketCertificate)
  -- 2. exact-rational CVZ partial sum S_N
  -- 3. geometric tail |η(1/2) - S_N| ≤ C·3^{-N}         ← NEW analytic lemma (sorry)
  -- 4. divide by (1 - √2), bracketed                     (sqrt 2)
  sorry
```

## From `ζ(1/2)` to `a_k` — a second, larger gap

`a_k` needs the **derivatives** `ζ^{(j)}(1/2)`, `Γ^{(j)}(1/4)`, plus the Stieltjes
constants, combined through Leibniz on the ξ product. Two sub-routes:
- **Coefficient route:** bracket each factor's Taylor coefficients and multiply
  (interval polynomial arithmetic in-kernel) — needs `ζ`/`Γ` derivative brackets,
  which need the CVZ representation *differentiated term-by-term* (uniform
  convergence justification — a further analytic lemma).
- **Cauchy-integral route:** `a_k = (2πi)^{-1} ∮ ξ(1/2+z) z^{-2k-1} dz`; bound by
  a rigorous in-kernel quadrature with contour error — needs formalized rigorous
  numerical integration, which Mathlib does not have.

Both are **substantial** (comparable to formalizing a published analytic-number-
theory computation). Honest estimate: the `ζ(1/2)` bracket is a focused
multi-week formalization on top of a new `SqrtBracket` + CVZ tail lemma; the full
`a_k` bracket is a research-scale effort (likely warranting an upstream Mathlib
contribution of ζ-numerics).

## The completable / blocked line

The deciding question is simply **whether Mathlib carries a closed form or a
computable-with-bounds representation** of the constant:

| Deep constant | Mathlib handle | In-kernel bracket |
|---|---|---|
| `√2`, `√q` | `Real.sqrt` monotone + `sqrt_sq` | **DONE** (`SqrtBracketCertificate`) |
| **`Γ(1/2)`** | **closed form** `Real.Gamma_one_half_eq : Γ(1/2)=√π` | **DONE** (`GammaHalfBracketCertificate`) — kernel-proven `1.772 ≤ Γ(1/2) ≤ 1.775` via π-bracket + √ |
| `Γ(1/4)` | none (lemniscate constant, no closed form) | **BLOCKED** |
| `ζ(1/2)` | none (Dirichlet series diverges; no numeric API) | **BLOCKED** — needs CVZ representation + tail lemma |
| `a_k` | needs `ζ`/`Γ` *derivatives* at 1/2 | **BLOCKED** (research-scale) |

So `Γ(1/2)` — one of the named deep transcendentals — **is now completed
in-kernel**, because it has a Mathlib closed form. That is the honest extent of
what "completing the deep formalization" reaches today.

## Honest bottom line

- **Done + kernel-proven:** the archimedean brackets (`exp`, `log`, `pi`, `sqrt`),
  the deep constant `Γ(1/2)`, and all enclosure-conditional RH-necessary certificates.
- **The genuine wall (verified, not asserted):** `ζ(1/2)` has no computable handle
  in Mathlib v4.32.0 (`mp.iv.zeta` broken; η-series `1/√N`-slow; no `ζ(s)∈[lo,hi]`
  lemma). Closing it is a focused formalization with one new analytic lemma (the
  CVZ tail bound); `a_k` additionally needs `ζ`/`Γ` derivative brackets and is
  research-scale — plausibly an upstream Mathlib ζ-numerics contribution.
- This repo ships **zero** proofs for the blocked constants
  (`conjecture1_proved=False`); this file is a plan, not a proof.
```
