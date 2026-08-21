# Scoping the heterogeneous -> homogeneous reduction: why it broke, and the route that replaces it

2026-08-21. `conjecture1_proved = False`. This is a SCOPING document (exact micro-facts +
a proposed certifiable route), not a closure. Companion to the achievable homogeneous face
(HomogMaster.lean, PR #35) and the STEP-1 unification doc (7f52fb4).

## The residual crux (context)

The achievable homogeneous master bound `GS(k, mu) <= T` (equality only at the arm) is
closed per-piece kernel-green. The unification doc's remaining gap is the
heterogeneous -> homogeneous reduction, whose below-average-chain proof is BROKEN
(HANDOFF_MASTER_INEQUALITY_20260819.md item 2): the chain has non-homogeneous fixed
points, witness mu = (1/5, 2/5).

## Exact micro-facts (all Fraction-exact, this session)

With knee mu_c = 5*(64/621)^(2/11) - 3 ~ 0.30774 (where glemma = 1; Bcap = min(1, glemma)
on (0,1/2], master_ub never active there):

1. **Homogeneous is a fixed-S local MINIMUM in the convex region.** For a j=2 pair at
   fixed sum with both children above the knee, the spread pair strictly beats the merged
   pair: GS(m-d, m+d)/GS(m, m) = 1.000001 at m = 19/60, d = 1/1000, growing like d^2
   (1.000064 at d = 8/1000). Mechanism: log glemma = log GAMMA - 11*log(1+mu/3) is
   strictly CONVEX, so fixed-S Jensen goes the WRONG way for merging. **This is why every
   exchange-to-equal / below-average argument must fail** — the reduction target
   (homogeneous) is not even a local max on fixed-S slices above the knee.

2. **Yet the unconstrained per-arity max IS homogeneous — pinned at the knee kink.**
   Fine exact search (j=2, grid 1/1000): max at (77/250, 77/250), value 0.72320*T
   (the coarse-grid 19/60 figure 0.71644 was resolution-limited). At the kink, spreading
   strictly loses BOTH ways: the below-knee child gains no Bcap (capped at 1) while the
   pair loses base or the above-knee child pays the glemma penalty. **Kink-pinning, not
   exchange monotonicity, is the true mechanism** behind the empirical "maximizer is
   homogeneous".

3. The broken chain's fixed point (1/5, 2/5) — one child below the knee, one above —
   has GS/T = 0.51190: a stationary artifact of the chain's dynamics, far from maximal,
   and (see below) a member of the canonical family, not a counterexample to it.

## The route that replaces the reduction: bang-bang with one exception

Drop "reduce to homogeneous" entirely. The objective at fixed (arity j, sum S) is

    GS = base(j, S)^11 * prod_i Bcap(mu_i),   log Bcap = min(0, f),  f = log glemma convex

and maximizing a SUM OF CONVEX FUNCTIONS over the fixed-sum box slice
{0 < mu_i <= 1/2, sum = S} attains its max at a VERTEX of the slice — i.e. at
configurations with **all children at region bounds except at most one**:

    CANONICAL FAMILY C(a, s_low, b, nu):
      a children below the knee with total mass s_low (individually free — Bcap = 1,
        only s_low enters, through base),
      b children exactly at 1/2,
      at most ONE interior child at nu in (knee, 1/2),
      (+ leaf children mu = 1, already monotone-safe by the existing argument).

Two monotone cleanups shrink it further:
  - s_low pushes UP to its cap (a * knee, rationally relaxed to a * 74/240): base
    increases, Bcap unchanged — exact monotone lemma;
  - the below-knee child COUNT a trades off against base only (d = j+1 in the
    denominator) — a 1-integer-parameter monotonicity.

So the FULL heterogeneous achievable problem collapses to a 2-integer + 1-real family

    GS(a, b, nu) = base(a+b+1, a*mu_c + b/2 + nu)^11 * glemma(1/2)^b * glemma(nu)

(plus the boundary sub-families with no interior child / no half-children), which is the
SAME certifiable shape as the homogeneous probe: per-(small a, b) Bernstein cells in nu +
integer-parameter monotone tails (glemma(1/2)^b decays geometrically; base is bounded).
The homogeneous bound becomes a COROLLARY (the family contains the homogeneous points),
not a lemma.

## Proof obligations (each an existing machine shape)

1. **Vertex lemma** (the only new mathematics, and it is standard): max of
   sum-of-convex over a fixed-sum box slice is at a vertex (all-but-one coordinates at
   bounds). Provable by the two-point spreading exchange — which IS valid in this
   direction (convexity favors spreading; iterate until at most one interior coordinate).
   Note this is the same convexity that KILLED the merging argument, now used in its
   correct direction. Care at the knee: f is convex on (knee, 1/2] and the cap min(0, f)
   is flat below; the spreading exchange must respect the two-region structure (spread
   within the above-knee subset; below-knee children only carry mass).
2. **s_low monotone lemma** (exact algebra, one line of the d/dk-identity kind).
3. **Family certification**: Bernstein cells + tails over (a, b, nu) — the homog-master
   machinery re-run on a 3-parameter family. Margins unknown until scanned; the family
   max should be the known sector max 0.8722*T at (a=0, b=0... i.e. k=1, nu=1/2 — wait,
   nu-interior vs b: the sector max (k=1, mu=1/2) is the b=1, no-interior point). SCAN
   FIRST; the scan is cheap and will also re-check the vertex lemma empirically.
4. **Leaf splice**: leaves are monotone-safe by the existing argument; the arm equality
   (k=1, mu=1) stays the unique tight point (L4/armGS_le).

## What could break (honest risks)

- The vertex lemma's two-region bookkeeping (below-knee mass vs above-knee spread) has
  the same kink subtlety that produced the chain's fixed points; the exchange must be
  stated on the above-knee coordinates ONLY, with below-knee mass an aggregate variable.
- Achievability is coarser than "mu_i in (0, 1/2]": the true child messages are
  mu = 1/(j+1+S) values from the recursion. The family certification must stay a
  RELAXATION (any mu in the box), as the homogeneous probe's did — if the relaxed family
  max exceeded T anywhere off the known tight points, the finer achievable structure
  would need to enter (it did not for the homogeneous face; the scan will tell).
- The (a, b) integer tails need uniform-in-(a, b) bounds; base is bounded by
  1 + (S+1/3)/... — the sup-base relaxation from L3 should transfer.

## Status

Scoping doc. Micro-facts exact and reproducible (this doc's figures were computed with
Fraction arithmetic; the spread/merged witnesses and the 77/250 fine max are exact).
`conjecture1_proved = False`.

## LANDED (2026-08-21, kernel-clean, axioms = [propext, Classical.choice, Quot.sound])

Both proof obligations #1 (vertex lemma) and #3 (family certification) are now closed in
Lean over the canonical family. No `sorry`/`admit`/`native_decide`/added axioms.

**(1) THE FULL VERTEX LEMMA** — `proof/formalization/R3Cert/VertexLemmaFull.lean`
(imported into the `R3Cert` root, so covered by the `proof-lean` CI `lake build`):
  - `glemma_spread` — general sum-preserving two-point spread (the log-convexity engine,
    generalizing the exact-midpoint seed `VertexLemma.glemma_two_point_spread`):
    `a+b=c+d`, `c·d ≤ a·b` (more spread) ⇒ `glemma a · glemma b ≤ glemma c · glemma d`.
  - `glemma_push_to_bound` — the exchange pushing one coordinate to the bound `1/2`
    (valid for `a,b ∈ [0,1/2]` via `(1/2−a)(1/2−b) ≥ 0`).
  - `vertex_bound` / `vertex_bound_cons` — the vertex bound by list induction:
    `∏_{c∈a::l} glemma c ≤ glemma(1/2)^|l| · glemma(a + Σl − |l|/2)` for children in
    `[0,1/2]` and nonnegative residual. This is exactly the doc's "clean formalization"
    target (§Proof obligations #1). The two-region kink risk is handled by requiring the
    box `[0,1/2]` and keeping the running free coordinate in `[0,1/2]` with residual ≥ 0
    (below-knee children are simply not part of this above-knee `glemma` product — they
    enter only through `base`, in the family value below).

**(3) THE (a,b,nu) FAMILY CERTIFICATION** —
`telperion/examples/g1_floors/lean/HeteroFamily.lean` (built by a new
`telperion-production` CI step: `lake build HomogMaster HomogMasterAssembled HeteroFamily`):
  - `nu_cell` — the interior `nu`-cell `fam(0,0,nu) ≤ T` for `nu ∈ [37/120, 1/2]`,
    discharged by reusing the homogeneous Bernstein bridges `bridgeB` (`[37/120,1/3]`) and
    `bridgeC1` (`[1/3,1/2]`). `fam(0,0,nu)` is exactly the homogeneous `k=1` value
    `base(1,nu)^11 · glemma(nu)`; the family peak `fam(0,0,1/2) = GS 1 (1/2) = 0.872204·T`
    is recorded (`fam_peak_eq_GS1`).
  - `astep` / `bstep` — the two integer tails are monotone reductions:
    `fam(a+1,b,nu) ≤ fam(a,b,nu)` and `fam(a,b+1,nu) ≤ fam(a,b,nu)` for `nu ≥ 37/120`.
    Both reduce to `base`-ratio inequalities whose numerators, after `nu = 37/120 + t`,
    have ALL-NONNEGATIVE coefficients (a-step: `23b + 120t + 3 ≥ 0`; b-step: an
    all-nonneg-coeff polynomial), so they close by `nlinarith`/`positivity` with no huge-`T`
    cross-multiplication. The b-step's `glemma(1/2)` factor is accounted by the exact
    rational bound `Rb^11 · glemma(1/2) ≤ 1` with `Rb = 994/951` (`Rb_pow_glemma_half`).
  - `family_master` — assembled: `fam(a,b,nu) ≤ T` for ALL `a,b : ℕ` and `nu ∈ [37/120, 1/2]`.
    The integer tails collapse to the `nu`-cell (`fam_le_cell`), which is `≤ T`.

Empirical backing (`proof/verification/hetero_family_scan.py`, exact `Fraction`,
`certify()` passes): family max `0.872204·T` at `(0,0,1/2)`, 0 violations, adversarial
arbitrary-heterogeneous max = exactly `T` at the arm only.

**Scoped-open (honest).** The boundary sub-family with NO interior child
(`GS_family_noInterior`, all children at `1/2` or below the knee) is not separately
formalized; the scan shows its max coincides with `fam(0,0,1/2)` (the interior child sitting
at the bound), which `family_master` covers, so it is dominated but not independently
certified in Lean. The achievability relaxation (§What could break) is inherited from the
homogeneous face: the family is certified over the full box `nu ∈ [37/120,1/2]`, a superset
of the recursion-realizable messages, so no finer achievable structure is needed (the scan
confirms 0 box-relaxation violations). `conjecture1_proved = False`.
