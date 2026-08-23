# Brualdi–Goldwasser (a, b, ν) family certification

*2026-08-22 — companion to `examples/bg_family/` and
`proof/verification/hetero_family_scan.py`.*

## Where this sits in the proof

The Brualdi–Goldwasser extremality argument reduces, through the homogeneous
master inequality `GS(k, μ) ≤ T`, to a **heterogeneous** master inequality over
arbitrary child-message profiles. A vertex / majorization lemma (the sole open
brick — a Mathlib convex-analysis commitment, tracked in
`proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md`) collapses that
arbitrary problem to a **2-integer + 1-real canonical family**:

```
GS(a, b, ν) = base(a+b+1, a·μ_c + b/2 + ν)^11 · glemma(1/2)^b · glemma(ν)
```

* `a` below-knee children pinned at the rational knee `μ_c = 37/120` (there
  `Bcap = glemma(μ_c) = 0.99803 < 1` — 37/120 sits just **above** the true knee),
* `b` children at `1/2` (`Bcap = glemma(1/2) = 0.11106`),
* one interior child at `ν ∈ (μ_c, 1/2]`.

Constants match the kernel (`W = 64/621`, `Γ = W²·(5/3)¹¹`, `T = W·(5/3)¹¹`).

## The family bound is a 3-brick certificate

An exact `Fraction` scan (`hetero_family_scan.py`, re-run 2026-08-22) shows the
family max is **0.8722·T**, attained at the `k=1, μ=1/2` sector, with the tie
(`GS/T = 1`) isolated at the arm (`μ=1` leaf, outside this family). That collapses
`GS(a, b, ν) ≤ T ∀ a,b≥0, ν∈(μ_c,1/2]` into three independent bricks:

| brick | statement | status | witness |
|---|---|---|---|
| **base cell** | `GS(0,0,ν) ≤ T` on `[μ_c, 1/2]` | **certified (this repo)** | Bernstein, elevation 11 |
| **monotone-a** | `GS(a+1,b,ν) ≤ GS(a,b,ν)` | validated exactly (worst ratio **0.99955**) | ratio family, next layer |
| **monotone-b** | `GS(a,b+1,ν) ≤ GS(a,b,ν)` | validated exactly (worst ratio **0.87370**) | ratio family, next layer |

Then `GS(a,b,ν) ≤ GS(0,b,ν) ≤ GS(0,0,ν) ≤ 0.8722·T < T`. No finite grid is
assumed — the two monotonicities cover the full integer tails.

## The base cell (Telperion-native, kernel-checked)

Clearing the positive denominator `(1+ν/3)¹¹` turns `GS(0,0,ν) ≤ T` into a
degree-11 polynomial positivity on a rational interval:

```
0 ≤ T·(1+ν/3)¹¹ − Γ·((7+3ν)/6)¹¹      on [37/120, 1/2].
```

`examples/bg_family/generate.py` certifies this with Telperion's Bernstein
emitter: the target's Bernstein coefficients on `[37/120, 1/2]` are already
nonnegative at elevation 11 (no extra elevation needed), so the emitted Lean is
the search-free `ring` (the Bernstein identity) + `linarith` (sum of nonnegative
basis terms). The ~40-digit rational coefficients push the degree-11 `ring` past
Lean's default 200k-heartbeat cap, so the generator prepends
`set_option maxHeartbeats 4000000` as a local step (the shared emitter is
untouched). CI job: `bg-family-compiles`.

Certification is exact and refuses a false bound: claiming `GS(0,0,ν) ≤ 0.8·T`
(below the 0.8722·T max) yields a polynomial that dips negative on the interval,
so no nonnegative Bernstein certificate exists and `certify` raises
(`tests/test_bg_family.py::test_false_bound_is_refused`).

## Remaining commitment (the next layer)

1. **monotone-a / monotone-b as certificates.** Each is a ratio inequality
   `[base(j+1, S+δ)/base(j, S)]¹¹ · Bcap(δ) ≤ 1` — a **2-integer + 1-real**
   family (integers `a,b`; real `ν`). monotone-b has comfortable margin;
   monotone-a is tight (0.99955, the near-knee marginal case) and will need the
   base-ratio-≤1 sublemma made explicit before a `MonotoneRatioTailEmitter` /
   Bernstein-in-ν composition can discharge it. This is the natural next
   Telperion build and is fully in-scope for the existing emitter set.
2. **The vertex / majorization lemma.** The hetero→family reduction itself is a
   Mathlib convex-analysis theorem (max of a sum of convex `log Bcap` over a
   fixed-sum box slice is at a vertex). It is **not** a certificate brick — it is
   the one genuine formalization commitment, owned by the BG kernel work.

The empirical vertex-lemma check (`spreading never hurts`, worst
merged/spread ratio **1.0**) and the whole reduction are re-validated by the scan
on every run, so this base-cell brick lands against a green empirical backdrop.
