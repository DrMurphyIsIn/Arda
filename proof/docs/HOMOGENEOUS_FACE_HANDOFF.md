# Handoff: the homogeneous face of the master inequality

**Status: `conjecture1_proved = False`.** This records one session's arithmetic on the sharpest
attackable face of the Brualdi–Goldwasser master inequality. Every numeric claim below was
exact-verified in `Fraction` arithmetic (blocks = all rooted trees `n ≤ 12/13`). No layer of the
crux was closed. What moved is its *localization*. Read alongside `MASTER_INEQUALITY_FRONTIER.md`.

## The target

The near-star half of the single-hub inductive step reduces (verified, see caveat) to the
**homogeneous bound**: for every real rooted block `C` with cavity message `μ` and factor `F ≤ 1`,
```
max_j  H_C(j) := W (1 + jμ/(j+1))^11 · F^j  ≤  1 ,   W = 64/621,
```
tight **only** at the arm (`μ=1/3, F=486/529`, at `j=5` = the tie `N(0,5)`). Because the
`C`-broom (`j` copies of `C`) is a *real tree* whose factor is exactly `H_C(j)`, this bound **is
BG restricted to symmetric hubs** — a genuine 1-parameter, unimodal-in-`j` (crossing-once) face,
not a surrogate.

## What is proven (Lean-green)

- **Arm**: `H_arm(j) ≤ 1`, tight at `j=5`, is the near-star ratio-unimodality `R(s)` — `NearStar.lean`.
- **Near-star family** `N(0,k)`: `nearStar_family_le_zero`, unconditional, `0` sorry.

## Findings this session (all exact-verified, none a proof)

1. **Value-localization (the main gain).** Over 7803 distinct real blocks, the homogeneous bound
   is tight *only* at the arm (`H=1`). Every block with `H > 0.37` is the arm or a near-star
   `N(0,k)` — the already-proven families. **Every other real block has `H ≤ 0.3637`** — a `0.636`
   margin. So the entire *hard content* of this face lives in the Lean-green families; closing it
   reduces to certifying a wide-margin uniform bound on the non-near-star blocks.

2. **The achievable envelope `Ψ(μ)` has no clean closed form.** Computed as `max F` over real
   blocks per message: `3373/7508` upward kinks in `log Ψ` — a jagged discrete scatter, not a
   curve. This is *why* no analytic surrogate closes the bound: there is nothing smooth to bound
   against. (The mid-`μ` "integrality band" is exactly where the scatter curves below any surrogate.)

3. **The g-lemma is tight at the arm** (`γ/(1+μ/3)^11 = 486/529` exactly at `μ=1/3`) — but useless
   off it: at small `μ` it permits `F` up to `γ = W²(5/3)^11 ≈ 2.93 > 1`, so `H` blows up to `10^140`.
   Even `F ≤ min(1, γ/(1+μ/3)^11)` fails: at `μ≈0.307` the cap allows `F=1`, giving `W(1+μ)^11 ≈
   1.74 > 1` — but no real block has `(0.307, 1)`. Surrogates go slack precisely in the mid-`μ` band.

## Four would-be closures caught before shipping (the discipline working)

- **Reduction `F_hub ≤ max_child Hmax`** — verified `0/4000` random, `0/24300` adversarial no-arm
  mixes, *but its proof is broken*: "below-average removal → homogeneous" is **false** — removal has
  non-homogeneous fixed points (`μ=(1/5,2/5)`, `(1/4,7/20)` are fixed yet not homogeneous). VERIFIED,
  proof OBSTRUCTED.
- **g-lemma / cap surrogate** — blows up / goes slack in the mid-`μ` band (finding 3).
- **`j*≥2 ⟺ near-star` dichotomy** — would split the bound into {near-star, proven} ∪ {`j*=1`
  single-graft}. **False**: one counterexample at `n=12` (`μ=0.1594≠3/19`, `F=0.7657`, `j*=2`,
  harmless `H=0.18`). No clean structural split.
- (Earlier arc) the moment-SoS-on-measure and `∏env ≤ 1` routes — both dead (continuous `F_ns`
  exceeds 1 at `k≈4.82`).

## The open target for the next session

Prove `max_j H_C(j) ≤ 1` for **non-near-star** real blocks. Everything above `H=0.37` is a proven
family; the residual is a **0.63-margin uniform bound** on the rest. The obstruction is unchanged in
kind: it needs a *uniform* `(μ,F)` bound (the master inequality), and no proven surrogate supplies it
because `Ψ(μ)` is jagged. The crossing-once engine gives the unimodal *shape* for free; the *value*
`≤1` is the arithmetic core. The one encouraging structural fact: the tight set is now fully
accounted for (arm + near-stars, Lean-green), so a proof needs only a crude bound off that set.

*Every numeric/identity claim in this document was exact-verified in `Fraction` arithmetic.
`conjecture1_proved = False`.*

## Addendum: the homogeneous face is *downstream of the g-lemma* (a robust-gap reduction)

Taking the next step produced the session's strongest lead — and it consolidates rather than closes.

**Finding.** Define the g-lemma functional `g(C) = F·(1+μ/3)¹¹`; the g-lemma is `g(C) ≤ γ = W²(5/3)¹¹
= 2.92761`, **tight only at the arm** (the elementary `root+leaf` block, `n=2`; `μ=1/3` structurally
forces the arm, so it is isolated). Over **non-near-star** blocks, `max g(C) = 1.85241` — a strict
gap `γ−γ' = 1.075`. Under `F ≤ min(1, γ'/(1+μ/3)¹¹)` with `γ'=1.85`, the homogeneous max is
`H ≤ 0.588 < 1` (checked over all `μ∈(0,1/2]`). So:

> **homogeneous bound (non-near-star)  ⟸  [ g(C) ≤ γ'≈1.85  ∧  F ≤ 1 ]** — closes with 0.4 margin.

**The gap is robust** (unlike this session's other leads, which broke at `n=22–56`):
- Enumeration all trees `n ≤ 14`: max non-near-star `g` = `1.8524`, attained at the fixed `n=4` path;
  it *decreases* for larger `n`.
- Adversarial construction to `n=28` (defected near-stars `k≤40`, deep paths, arms+tie-branches):
  max `g` stays `1.8524`; every large construction falls below. `g` does **not** creep toward `γ`.
- Structural support: non-arm blocks near `μ=1/3` have `F≈0`; large defected near-stars have `g→0`
  (arm factor `486/529 < 1` to the `k`). The arm is the unique, isolated g-saturator.

**What this means (consolidation, not closure).** `γ' < γ` is the g-lemma *plus* its equality
characterization (arm is the unique near-saturator) — strictly a refinement of the g-lemma, which is
itself **open** (the R1 branching-induction residual, verified `n≤11`, see `PROOF_ASSEMBLY.md`). So the
homogeneous face is **not an independent easier target**: it is a *loose downstream consequence of the
g-lemma*, with a large stable margin. Both the near-star half (via {reduction}+{homogeneous}) and R1
single-hub extremality reduce to the **same** object — the g-lemma / master-inequality branching wiring.

**Redirected target for the next session.** Do not attack the homogeneous face in isolation; it falls
automatically (with margin) once the g-lemma's branching wiring closes. The single crux to attack is
`g(C) ≤ γ` with equality iff arm — the R1 branching residual. `conjecture1_proved = False`.
