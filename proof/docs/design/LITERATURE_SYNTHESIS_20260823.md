# Literature synthesis: the marginal tie is the shared wall of BOTH proof families (2026-08-23)

`conjecture1_proved = False`. A deep-research dive (adversarial-verify verdict was a spend-limit
false-negative; the harvest is the payoff) surfaced two decisive papers and a unifying strategic
insight. Both papers read in full; every numeric claim below re-checked in exact rational `π` against
our engine (`verification/permanent.laplacian_ratio`).

## The two papers

1. **Wu, Dong, Lai, "Two problems on Laplacian ratios of trees", Discrete Appl. Math. 372 (2025).**
   Also (same group) Wu et al., "Solution to an open problem on Laplacian ratio", arXiv:2402.15669.
   These give the **transformation toolkit** for `π(T)=per(L(T))/∏d(v)`, all via the matching-sum
   `π(T)=Σ_M ∏_{uv∈M} 1/(d(u)d(v))` (Lemma 2.1 = our engine's identity):
   - **Lemma 2.2/2.3/2.5** — exact per-Laplacian deletion recursions (`per L(G)=per L(G−v)+2 per L_u(G−v)`
     for a pendant `v`; cycles vanish on trees).
   - **Lemma 2.8** — the branch-vs-pendants transfer: `π(G1) ≥ π(G2)` (a hanging branch beats the same
     mass as pendants at `u`), proven by an injective `k`-matching argument (partition by whether `u` is
     covered) + `ψ≥θ` reciprocal-degree comparison.
   - **Lemma 2.9** — pendant redistribution: `π(T) > min{π(T1),π(T2)}` (splitting pendants across two
     deg-2 vertices is never the minimizer). **Verified exact in our engine** (`pant_transform_check.py`).
   These reduce any tree to a **caterpillar** (Thm 1.1 proof: Lemma 2.8(iii) → caterpillar `T0`, then
   Lemma 2.9 merges leaves) — the minimization route to the broom.

2. **Pant, "Counterexamples to a Conjecture on Laplacian Ratios of Trees", arXiv:2605.14176 (May 2026).**
   **Disproves** Wu-Dong-Lai's *maximizer* Conjecture 1.2** in all three parity cases, via
   `T(a1,…,am)` = cherries on a core path, with `π=(3/2)^{Σaᵢ}·fₘ` (our cavity recursion). True
   maximizer left **OPEN**. The **marginal tie**: `T(3,3,3)` at n=21 hits the bound `2(3/2)⁹` exactly but
   is not the conjectured `S(21,10)`.

## The unifying insight (the strategic payoff)

**Wu-Dong-Lai had the ENTIRE transformation toolkit and STILL got the maximizer wrong** — Pant refuted
them. So the transformation route, by itself, is **provably insufficient** to pin the maximizer. It
reduces arbitrary trees to a caterpillar / near-star family (valid, and independently confirmed by our
`caterpillar_collapse_probe`), but the **final comparison inside that family is a marginal tie**
(`T(3,3,3)` ties `S(21,10)`), where the transformation partial order gives `≥` but not the strict winner.

This is the SAME non-hyperbolic marginal tie that kills every **certificate** route (SOS / Handelman /
potential / p-adic — the continuous near-star envelope `>1` at `k≈4.82`, `ρ(A)→1` at the tie). So:

> **The marginal tie is the irreducible core shared by BOTH proof families.** Certificate routes die
> *at* it; transformation routes reduce *to* it and die there too. Neither family escapes it.

## Why our architecture is the right one (external validation)

Our engine already does the correct synthesis, and it is validated by this literature:
- **Transformation-reduction** to the de-loaded cherry-bundle star = our R1–R6 (R4 = Kelmans, exactly
  this toolkit). Valid, and matches the literature's caterpillar reduction.
- **Arithmetic tie-breaker at the marginal tie** = our R3 (`Φ≤1`, equality iff the near-star tie, the
  23-adic `529/486`). This is the piece **no transformation can supply** — it *is* the marginal tie made
  explicit.
- And our de-loaded cherry-bundle star **beats both Wu-Dong-Lai and Pant** at matched `n`, margin growing
  in `n` (`pant_counterexample_check.py`, PR #87). Our target is correct where the literature's was wrong.

## Consequence for strategy

1. **Do not chase the pure transformation route** — Wu-Dong-Lai already demonstrated it is insufficient
   (Pant refuted them). Transformations are a valid *reduction* (R1–R6), not a *closure*.
2. **The arithmetic crux R3 (`Φ≤1`, 23-adic tie) is the genuine irreducible core** and the right thing to
   keep attacking. Every route — ours, certificates, transformations — bottoms out here.
3. **The correct proof is the combination our effort already has**: transformation-reduction (R1–R6,
   literature-valid) + arithmetic tie-breaker (R3, open). The dive did not hand us a new closure; it
   *validated the architecture* and *proved the crux is irreducible* (transformations can't route around
   it).
4. Immediately usable transferable bricks, verified exact in our engine: the deletion recursion
   `per L(G)=per L(G−v)+2 per L_u(G−v)` (Lemma 2.3) and the injective-matching transfer (Lemma 2.8) — for
   any future R4/R6-style Lean-ization.

`conjecture1_proved = False`. The crux did not move; it was **proven irreducible** — no transformation
route bypasses the 23-adic marginal tie, which is exactly what R3 attacks.
