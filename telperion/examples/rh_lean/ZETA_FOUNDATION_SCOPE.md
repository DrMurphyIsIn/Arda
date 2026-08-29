# Scoping the Mathlib analytic-zeta foundation: what's missing, what's buildable

> **Honest target.** This is NOT a plan to prove RH. It scopes where kernel-formalization work
> could make a *real* (if modest) contribution to the analytic machinery RH actually lives in --
> the zero-free-region line (category 1 in the frontier taxonomy), the one place a certificate-shaped
> tool honestly touches genuine RH progress. `conjecture1_proved` stays False.

## What Mathlib v4.32.0 already HAS (probed, not assumed)

The *foundation* is largely in place:

| Present | Constant / lemma |
|---|---|
| zeta + completed zeta | `riemannZeta`, `completedRiemannZeta`, `completedRiemannZeta₀` |
| functional equation | `completedRiemannZeta_one_sub`, `riemannZeta_one_sub` |
| analytic continuation | `differentiableAt_riemannZeta` (s ≠ 1) |
| **non-vanishing on Re >= 1** | `riemannZeta_ne_zero_of_one_le_re` |
| **pole / residue at s=1** | `riemannZeta_residue_one` : `(s-1)·zeta s -> 1` |
| trivial zeros | `riemannZeta_neg_two_mul_nat_add_one` |
| theta / prime-side | `jacobiTheta`, `ArithmeticFunction.vonMangoldt`, `Nat.primeCounting` |
| zeta-numerics (this session) | `zeta(2),(3),(4),(5),(6),(7)` two-sided bounds (Re>1 Dirichlet series) |

Beyond Mathlib, two external projects (not yet merged) cover more: Kontorovich-Tao's
**PrimeNumberTheoremAnd** (PNT via Wiener-Ikehara), and the **zeta/L-functions in Lean** project
(Dirichlet's theorem, non-vanishing on Re=1, a formal *statement* of RH). arXiv:2503.00959.

## What's MISSING (the actual frontier)

| Missing | Why it matters | Formalized anywhere? |
|---|---|---|
| **quantitative zero-free region** `zeta(s) != 0 for Re > 1 - c/log|t|` | the classical progress line toward RH | NO (Mathlib has only Re >= 1) |
| zeta growth bound `|zeta(σ+it)| << log|t|` near σ=1 | the analytic input to the region | NO (partial in PNT+?) |
| explicit formula (zeros <-> primes) | connects zeros to prime counting | NO |
| Vinogradov-Korobov region | the widest known region | NO |
| zero-density estimates `N(σ,T)` | category-2 frontier (Guth-Maynard 2024) | NO |
| de Bruijn-Newman `Λ`, `H_t` heat flow | category-4 frontier (RH <=> Λ<=0) | NO (Polymath15 used interval arithmetic, unformalized) |
| `hurwitzZeta`, Chebyshev `θ`,`ψ` | building blocks | NO (unknown in v4.32.0) |

## Triage: tractable vs research-scale

- **Research-scale (do NOT attempt now):** de Bruijn-Newman Λ bounds (needs a *verified interval-
  arithmetic framework for the H_t heat-flow evolution* -- an enormous formalization); zero-density
  estimates; the explicit formula. These are the deep frontiers; certificate emission has no purchase.
- **Foundation-adjacent but off-frontier:** more zeta-numerics on Re>1 (we already did ζ(2)..ζ(7));
  real but not on the RH-progress line.
- **TRACTABLE and certificate-shaped (the recommendation):** the **classical zero-free region via
  nonnegative trigonometric polynomials.**

## Recommended target: zero-free region via nonneg trig polynomials

The classical `zeta(s) != 0 for Re > 1 - c/log|t|` proof has a clean two-part structure:

1. **The certificate (our distinctive strength, LOW effort).** The Mertens inequality
   `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)^2 >= 0`. Applied to `Re[3 log zeta(σ) + 4 log zeta(σ+it) +
   log zeta(σ+2it)]` it gives `zeta(σ)^3 |zeta(σ+it)|^4 |zeta(σ+2it)| >= 1`. **Better** nonnegative
   trig polynomials (higher degree, optimized coeffs; a Fejér-Riesz / sum-of-squares object) give a
   **better constant c** -- and certifying nonnegativity of a trig polynomial is exactly a
   worst-corner / SOS certificate (arXiv:1410.3926). This is a genuine Telperion emitter.
2. **The analytic assembly (the BOTTLENECK, MEDIUM-HIGH effort).** Turning the pointwise inequality
   into a zero-free region needs the zeta growth bound `|zeta(σ+it)| << log|t|` near σ=1, plus the
   pole at s=1 (`riemannZeta_residue_one`, HAVE it) and non-vanishing on Re=1 (HAVE it). The growth
   bound is the missing analytic piece and likely overlaps the PNT+ project's in-progress work.

**Honest effort verdict.** The *certificate* is landable now and is the distinctive contribution; the
*full region* is medium-high and should be coordinated with (not duplicated against) PNT+. So the
realistic first deliverable is: (a) the nonneg-trig-poly certificate machinery (kernel-verified,
general, with the 3-4-1 Mertens polynomial as the seed and optimized higher-degree polynomials as the
value-add), and (b) a scoped statement of the region-assembly it feeds, flagging the growth-bound
dependency.

## Why this is a REAL step (and its honest ceiling)

A zero-free region `Re > 1 - c/log|t|` is genuine, unconditional progress about *where the zeros can
be* -- it is on the same century-long line (de la Vallée Poussin -> Vinogradov-Korobov) that RH sits at
the end of. That is categorically different from Robin/Jensen reformulations, which only relocate RH.
**But the ceiling is real:** the classical region is FAR from Re = 1/2, its constant `c` is small, and
improving it has been stuck since 1958; a formalized classical region is a contribution to the
*verified foundation*, not a narrowing of the true gap to RH. It does not prove RH, and does not claim
to. `conjecture1_proved = False`.
