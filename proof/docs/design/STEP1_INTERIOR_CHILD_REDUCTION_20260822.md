# STEP-1: the canonical family's interior child dissolves into log-convexity + the j=1 g-step

> **⚠ SUPERSEDED (2026-08-22, same day).** This doc pursued the *vertex/canonical-family* route to the
> g-step bound as if STEP-1 were open. It is **not** open: an audit of `main` found the g-step is already
> proven **unconditionally for every achievable config** — `CappedJointConfig.gstep_le_one_achievable`
> (`CappedJointClosure.lean`), whose core is the majorization `GArmExtAbstract.gCoreOff_le_replicate`
> ("any config ≤ all-children-at-the-knee", an elementary push-to-knee induction — the vertex lemma, done).
> Verified genuine: no `sorry`/`axiom`/vacuous hypothesis; `muStar_crossover` real; statement non-trivially
> true. So the vertex route below (and the `gs2`/`gs3`/`gs3_full` face bricks) is a **redundant parallel
> route** — mathematically valid and independently corroborating, but not needed. The real open frontier is
> **Gap 2 (the Branch→per(L) bridge)** + R7, per `PROOF_STATE_AND_PLAN.md` and memory
> `laplacian_crux_closed_bridge_open_2026-08-18`. The analysis below is retained for the record.

2026-08-22. `conjecture1_proved = False`. This ADVANCES the heterogeneous-reduction program
(`HETERO_REDUCTION_SCOPING_20260821.md`): it collapses that doc's obligation #3 (the interior
child of the canonical family — previously "Bernstein cells over `(a,b,ν)`") into a clean,
elementary split that reuses already-proven pieces. It does **not** close STEP-1: the vertex
lemma (obligation #1) remains. Scoping + exact micro-facts, not a Lean closure.

## Context: where STEP-1 sits after the face bricks

The g-step `GS = base(q+1,S)^11 · ∏ Bcap(μ_i) ≤ T` (`T = W(5/3)^11`, `W=64/621`,
`Bcap = min(master_ub, glemma, 1)`, knee `μ_c = 5W^{2/11}−3 ≈ 0.30774`) is tight ONLY at the
single arm (`q=1`, one leaf; `GS=T`). The scoping doc reduces the max to the **canonical family**
(bang-bang / vertex lemma): all children at region bounds except ≤1 interior child —

    cap children (μ ≤ μ_c, Bcap=1) · b children at ½ · c leaves (μ=1) · ONE interior ν ∈ (μ_c, ½].

The face bricks now on `main` (`GStepFullFace.gs3_full`, PR #60) certify the **ν-free** case
`{cap^b, ½^a, 1^c} ≤ T` for all counts. The one remaining piece of the *family certification* is
the single interior child `ν`.

## The canonical-family scan (validation)

Exhaustive scan over `(a,b,c) ∈ [0,10)×[0,8)×[0,8)` and `ν` on a 40-pt grid of `(μ_c, ½]`
(knee via `μ_c = 5W^{2/11}−3`), plus the ν-free sub-family:

- **Max `GS = 28.40695 = 1.00000·T`, attained at `(a,b,c)=(0,0,1)` (the single arm).**
- **Zero configs exceed `T`.** The whole route is validated.
- The interior child, at its own optimum, always lands at a **vertex** (`ν=μ_c` → a cap child, or
  `ν=½` → a half child) — never strictly interior. The vertex lemma, seen empirically.

## The interior-child reduction (the advance)

`GS(a,b,c,ν) = base(q+1,S)^11 · glemma(½)^b · W^c · glemma(ν)`, `q=a+b+c+1`,
`S = a·μ_c + b/2 + c + ν`, `glemma(ν)=γ/(1+ν/3)^11`, `γ=W²(5/3)^11`. As a function of `ν`:

    d²/dν² log GS = 11·[ 1/(3+ν)²  −  1/((q+1)·base)² ],   (q+1)·base = q + 1 + S + 1/3.

so **`log GS` is convex in `ν` ⟺ (q+1)·base > 3+ν ⟺ q + S > 5/3 + ν`**, and since
`q+S = a(1+μ_c) + (3/2)b + 2c + 1 + ν`, this is exactly

    q + S > 5/3 + ν  ⟺  a(1+μ_c) + (3/2)b + 2c > 2/3  ⟺  a+b+c ≥ 1.

Verified numerically (`log GS''` sign matches `a+b+c≥1` on every tested case; **0** endpoint-max
violations across all interior configs; min margin `T−GS = 7.86`). The obligation splits:

| case | `log GS(ν)` | closes by |
|---|---|---|
| **`a=b=c=0`** (interior child *alone*) | concave (interior max) | = the **proven `j=1` g-step**: `GS(0,0,0,ν)=base(1,ν)^11·glemma(ν) ≤ T` on `(0,½]` (`64·17^11 ≤ 621·14^11`; max `24.78` at `ν=½`) |
| **`a+b+c ≥ 1`** (interior child + ≥1 other) | **convex** | convexity ⟹ `GS(ν) ≤ max(GS(μ_c), GS(½))`; both endpoints are **vertex** configs (cap child / half child) ⟹ `≤ T` by `gs3_full` |

So the interior child needs **no new multivariable certificate** — only (a) the existing `j=1`
g-step, and (b) log-convexity in `ν` (exact condition derived above) feeding into the existing
`gs3_full` vertex bound. This replaces the scoping doc's Bernstein-cell obligation.

## The vertex-lemma exchange is elementary

The two-point spreading exchange (obligation #1's core) at fixed sum, both children above the knee,
reduces to the `glemma` product ratio: moving `μ₁ ≤ μ₂` apart by `δ` gives, with `x=μ₁/3, y=μ₂/3,
e=δ/3`,

    (1+x−e)(1+y+e) − (1+x)(1+y) = e(x−y) − e² = −[ e(y−x) + e² ] < 0,

so the `glemma` product strictly increases — `GS(spread) ≥ GS(merged)`. The exchange inequality is
a **quadratic**; the difficulty in obligation #1 is not analysis but the *combinatorial assembly*
(iterate to a vertex, handle the two-region knee structure, aggregate below-knee mass).

## Route ruled out: no polynomial per-child envelope (the vertex lemma is unavoidable)

A tempting shortcut would sidestep the vertex lemma entirely: find a **polynomial per-child
envelope** `φ ≥ Bcap` with `φ(0)=1` and `base^11 · ∏φ(μ_i) ≤ T` for all configs, closing the g-step
by a pure product bound (the 2026-08-20 capped-joint reframing floated this). **It cannot exist.**
Cap children can sit at any `p ∈ (0,μ_c]` with `Bcap=1`; a config of `a` cap children at `p` gives
`base^11·φ(p)^a`, and `base → 1+p` as `a→∞`, so `φ(p) > 1` makes the bound diverge (verified:
`φ(p)=1.01` at `p≈0.154`, `a=500` → `701 ≫ T`). Hence `φ ≤ 1` on `(0,μ_c]`; combined with
`φ ≥ Bcap = 1` there, `φ ≡ 1` on `(0,μ_c]` — and a polynomial equal to 1 on an interval is
identically 1, contradicting `φ(1)=W`. So no polynomial envelope closes the product bound; the cap's
piecewise flat-then-drop structure is essential, and the **vertex/bang-bang reduction is genuinely
necessary**. This confirms the scoping doc's route over the envelope shortcut.

## What remains (honest)

1. **Vertex lemma (obligation #1) — the real open core.** Reduce arbitrary realizable configs to the
   canonical family. The per-exchange step is elementary (above); the assembly (iteration +
   knee two-region bookkeeping + below-knee mass aggregation) is the genuine remaining work.
2. **Formalization.** The interior-child reduction above is analytically settled but not Lean.
   Route (b) needs `ν`-log-convexity in Lean (Mathlib `Convex`/`inner_le_nnorm`-style, heavier than
   the rational bricks), or a direct per-`(a,b,c)` rational interval bound on `[μ_c^{rat}, ½]`
   (Telperion `emit_bernstein`/interval bracket + integer tails) — the Bernstein route still works,
   just no longer *needed* for the mathematics.
3. **`s_low` monotone (obligation #2)** and **leaf splice (#4)** — minor, per scoping doc.

## Status

The g-step **face certification** (the downstream `≤T` obligation) is now, modulo formalization,
complete on the canonical family: `gs3_full` (vertex configs) + this doc's interior-child split.
STEP-1's remaining crux is squarely the **vertex lemma's combinatorial assembly** — the
achievability reduction proper. `conjecture1_proved = False`.

All figures Fraction/float-verified this session (scan, `log GS''` sign, endpoint-max, exchange
quadratic). Reproducible.
