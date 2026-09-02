# The extremality assembly: gating the SCL induction's arithmetic backbone (2026-09-02)

Follows `BG_EXTREMALITY_REDUCTION_20260902.md`. That note dismantled the extremality into a 6-piece
reduction over the invariant price interval `I = [456/3703, 3/7]`, with pieces #1 (price map) and #6
(deg≥7) gated and the rest verified-with-margins. This note **closes the two remaining arithmetic legs**
(#4 broom-vs-cherry, #5 leaf-exchange) as kernel-gated certificates, adds an assembly-consistency gate,
and Lean-emits + CI-compiles #4/#5. The one open input is thereby reduced from *"assemble + prove the
extremality"* to purely the **well-founded recursion on `|c|`** (all its arithmetic now gated).
`conjecture1_proved = False`.

## The two new arithmetic legs (both `.check()` exact; Lean-emitted, CI-compiled)

**Leg #4 — `BroomVsCherryOnICertificate`.** The reference broom beats the cherry in `V_μ` UNIFORMLY on `I`:
`V_μ(B(j)) ≤ V_μ(cherry)` for every broom child of degree `≤ 6` (`j = 1..5`; degree `≥ 7` is
`HighDegreeTailCertificate`) and every `μ ∈ I`. Since `V_μ(B(j)) − V_μ(cherry) = [ell(B(j)) − ell(cherry)]
+ μ(y_{B(j)} − 1/3)` is **linear in `μ`** (and `y_{B(j)} < 1/3`), the two endpoints `A, B` suffice. Cleared
(`×11`, `11 F* = log(621/64)`) with the exact-rational `μ`-term:

```
11 L(total B(j)) − 11 L(3/2) − (2j−1) L(621/64)  <  11 μ (1/3 − y_{B(j)}),   μ ∈ {A, B},
```

LHS upper-bounded by frozen log-enclosures (`_LOG`, adding `log(7/4)` for `B(1)`), RHS exact rational.
10 atoms (`j=1..5 × {A,B}`), margins `≥ +0.012` (the raw `V`-margin the reduction doc reported). This is the
all-cherry reference leg: the hub `B(d−1)` itself satisfies `V_μ ≤ V_μ(cherry)` on all of `I`.

**Leg #5 — `LeafExchangeCertificate`.** A bare leaf child never occurs in the `M_d` argmax: for hub degree
`d = 3..6`, replacing a leaf child by a cherry strictly raises `ell`. Exactly
`ell(B(d−1)) − ell((d−2)cherries + leaf) = log(3/2) − F* + log((4d−1)/(4d+1)) > 0`, which clears (`×11`) to
the **pure rational** (no enclosures)

```
(3(4d−1) / (2(4d+1)))^11  >  621/64,   d = 3..6.
```

4 atoms, `X^11 ∈ {13.8, 21.8, 28.8, 34.6} > 9.70`. So the `M_d` supremum (over all sizes) is attained
without leaf children, and the SCL induction's child-case split excludes them. (`d=2` is the base case.)

## The assembly gate — `SCLInductionCertificate`

Re-checks that **every arithmetic leg of the induction is mutually consistent** and that the **price map is
closed on `I`** (the well-foundedness precondition — every child price `μ'' = _price_map(d, μ)` lands in `I`
where the legs are proved). Components (all gated): price map (#1), broom-vs-cherry (#4), leaf-exchange (#5),
hi-degree (#6), near-broom unimodality, `MdStep`, `MonotoneTail`, `MixedHubKKT`. `.check()` = all components
pass ∧ `I` invariant under the price map for `d = 2..6`.

## What is now gated, and what remains

The SCL `V_μ(c) ≤ V_μ(cherry)` (all rooted branches, `μ ∈ I`) is proved by strong induction on `|c|`:
a degree-`d≤6` hub decouples (concave-log tangent at all-cherry, gap 0) into per-child inequalities at the
child price `μ'' ∈ I`; the child cases are **exhaustive** — leaf [#5, excluded], broom `B(m≤5)` [#4],
degree `≥7` [#6], non-broom degree `≤6` [IH]; the all-cherry reference `B(d−1)` closes via #4. Hence
`ell(hub) ≤ ell(B(d−1))`, the strict gaps pin the near-broom as the argmax, ⇒ EXTREMALITY ⇒ `mixed ≤ B(k)`
⇒ `ell(B) ≤ 0`.

`bg_upper_bound.py` now shows **10/10 GATED certificates pass**, and the sole HYPOTHESIS (`2b-lo-scl-induction`)
is the **well-founded recursion on `|c|` itself** — a Lean induction proof analogous to the branch-ceiling
induction (step `1b`, LEMMA). All of its arithmetic inputs are gated; the recursion Lean formalization is the
remaining follow-through. `conjecture_proved = False` (honest), and `conjecture1_proved = False`: the full
conjecture also needs the finite-`n` structural side (tree→hub / Hnorm–Hdom) and the matching lower bound
(`S(k,5)` achieves `F*`).

## Files

- `telperion/src/telperion/tie_regime.py` — `BroomVsCherryOnICertificate`, `LeafExchangeCertificate`,
  `SCLInductionCertificate` (+ the `log(7/4)` enclosure).
- `telperion/src/telperion/bg_upper_bound.py` — ledger: legs #4/#5/assembly GATED; the HYPOTHESIS narrowed to
  the recursion glue.
- `telperion/examples/bg_broom_vs_cherry/`, `telperion/examples/bg_leaf_exchange/` — dogfood generators +
  emitted Lean; CI jobs `bg-broom-vs-cherry-compiles`, `bg-leaf-exchange-compiles` in `telperion-lean-e2e.yml`.
- Tests: `test_tie_regime.py` (3 new), `test_bg_upper_bound.py` (updated counts: 14 steps, 10 gated).
