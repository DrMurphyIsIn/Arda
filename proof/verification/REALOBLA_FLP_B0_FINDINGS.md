# B0 de-risk: the FLP (leaf-path-extension) move for `StraightProgress_sized`

**Script:** `proof/verification/realobla_flp_derisk.py` (+ the 2x2 / characterization probes inline below).
Exact rational arithmetic; `Aobj` engine anchored in `telperion/scratch/a3_derisk.py` (matches unrooted
`per(L)/prod deg`, root-invariant, self-checked). Enumeration: all non-isomorphic unrooted trees `n = 2..14`.

## What was measured

The Lean-proven Type-L move (`aobj_flp_context_lift_crest`) is the leaf-onto-leaf **sibling** path-extension:
a node `u = node(leaf :: leaf :: crest)` (two BARE-LEAF children) becomes `node(stem :: crest)`,
`stem = node[leaf]` (one leaf stacked under the other). Vertex-preserving; drops `strDefect` by exactly 1
(when `u` flips non-piece->piece at its parent); `Aobj` non-decreasing with the closed-form increment
`P*(n^2 + n*Q + 4*Q)/(2(n+1)(n+2)) >= 0`.

**Population = the GENUINE hard core:** trees with `min strDefect over roots > 0` — the defect-minimal
rootings, where a mere re-root cannot discharge `StraightStep_sized` and a real structural move is required.
This is the correct load-bearing population (a re-root IS a valid `StraightStep_sized`, so non-minimal
rootings are trivial). 504 genuine trees for `n <= 14`.

## Decisive results (n <= 14, 504 genuine trees)

| Move | Coverage | Notes |
|------|----------|-------|
| **(A) sibling-leaf FLP** — the *actual Lean cert* | **394 / 504 = 78.2%** | drop always exactly 1; **0 Aobj violations**; closed-form increment == direct cavity increment on every witness |
| **(B) broad size-1** — any pendant leaf onto any vertex | **495 / 504 = 98.2%** | |
| true whole-hub **Type-W** (needs moved size >= 2) | **9 / 504 = 1.8%** | the genuine residual |

**The 78% -> 98% gap is MOVE-GENERALITY, not population** (verified on the *same* genuine set). The 101
"B-but-not-A" trees are ALL discharged by relocating a pendant leaf onto **another BARE LEAF** (target
degree = 1 in **101/101** cases) — just a **non-sibling / distant** one (parent->target distance 2..7),
not a sibling of `u`. So the Type-L family is UNIFORM — *leaf-onto-leaf path-extension* — and splits:

- **sibling** (both leaves children of one node): **78.2%** — covered by the current Lean cert.
- **distant** (target leaf elsewhere in the tree): lifts coverage to **98.2%** — needs an EXTENDED cert
  (remove a leaf from `par_w` + attach under a distant leaf `v`; two local cavity effects, both leaf ops).
- **whole-hub Type-W** (moved size >= 2): **1.8%** — the genuine open core (Case-B, k-star relocation).

## Reconciliation with the prior "92% / 8%" figure

The earlier `a7_taxonomy` sweep reports Type-L ~92% because it measures a DIFFERENT thing: (i) over the
FIXED-rooting population (all rooted trees with `strDefect(root) > 0`, most discharged by re-root), and
(ii) with the BROADER classifier `minsz == 1` (any size-1 leaf relocation anywhere in the deepest-defect
subtree, i.e. move (B), not the sibling cert). Neither "92%" nor "8%" describes the *currently-proven*
Lean move. On the genuine core the honest split is **78 / 20 / 2** (sibling-FLP / distant-leaf / whole-hub).

## Soundness gates (all PASS -> GO)

- Aobj-decrease violations on sibling-FLP witnesses: **0** (every witness raises or ties `Aobj`).
- Closed-form increment `!=` direct cavity increment: **0** (the three cone-cert quantities
  `F2_num = n^2+nQ+4Q`, `P`, `Q` reproduce the exact `Aobj(after)-Aobj(before)` on every witness).
- `strDefect` drop histogram on Type-L witnesses: `{1: 394}` — always exactly 1 (Nat-recursion friendly).

## UPDATE (deeper de-risk): the distant move is CONDITIONAL; the safe rule reconciles to 92/8

The first-pass "98% via broad leaf-onto-leaf" was over-optimistic: a RANDOM distant leaf-onto-leaf move is
NOT unconditionally Aobj-nondecreasing (60k-config sweep: 2117 DECREASE Aobj, worst ~ -17; 34 decrease Aobj
even while reducing defect). A naive `DistantLeafStepAt` mirroring `FlpStepAt` would therefore be FALSE.

The SAFE sub-family is the DEGREE-EQUALIZING leaf relocation (the a3_derisk premise): relocate the pendant
`w` from `par_w` onto a bare leaf `v` with **deg(par_w) > deg(par_v)**. Among defect-reducing moves obeying
this rule: **0 Aobj violations** (322/322); violating it: 35 negatives. Exhaustive genuine-core coverage
(n<=14, 504 trees) with the SAFE class:

| move class (safe, cone-certifiable) | coverage |
|---|---|
| sibling-FLP (`FlpStepAt`, DONE) | 78.2% |
| + degree-equalizing distant leaf | **91.5%** |
| true whole-hub Type-W (moved size >= 2) | **8.5%** (43 trees) |

**This RECONCILES with the plan's "92% Type-L / 8% Type-W"**: 92% = sibling + degree-equalizing distant
leaf moves (all cone-certifiable via the same leaf-path-extension G-machinery, gated by the degree rule);
8% = the genuine whole-hub (Case-B k-star) residual. The unqualified "98%" below counts UNSAFE distant
moves too and is NOT the certifiable figure.

## UPDATE 2 (closed-form de-risk): the degree-equalizing cert is NOT cleanly gateable — NO-GO

Derived the degree-equalizing distant-leaf increment SYMBOLICALLY (cavity factorization, adjacent case:
`par_v` a child of `par_w`), verified EXACT against real-tree Aobj (0/3000 mismatches):

    increment = PB * PO * N / [ 2 (nB+2)(nO+1)(nO+2) ]        (denominator: positive linear factors)
    N = QB*QO*nO + 4*QB*QO + QB*nO^2 + QB*nO + QO*nB*nO + 4*QO*nB + QO*nO + 8*QO
        + nB*nO^2 + nB*nO + nO^2 - 2*nO

where `(PB,QB,nB)` = par_v's OTHER children (Bv), `(PO,QO,nO)` = par_w's OTHER children, `QO<=nO`, `QB<=nB`
(each qContrib in (0,1]). **`N` is NOT sign-definite under the degree gate `deg(par_w) > deg(par_v)`**
(i.e. `nO > nB`): 839/300000 realizable draws give `N < 0`. The violation region is precise — at
`nB=0, nO=1, QB=0`: `N >= 0  <=>  QO >= 1/9`; for `nO >= 2` it is nonneg. So the increment DROPS when
`par_w` has a single HIGH-degree other child (`QO < 1/9`).

**VERDICT: NO clean cert.** The degree gate alone does NOT sign the increment; a correct gate must also
bound `par_w`'s other-children bushiness (`nO >= 2` OR `QO >= threshold`), i.e. couple to global structure
(or to defect-reduction, which is non-local — that is WHY the coverage sweep saw 0 violations among
defect-reducing moves: those instances avoid the `nO=1`-bushy region, but not by any LOCAL rule). The
adjacent case is the BEST case; the general (deeper `par_v`) distant move only adds path denominators and
is worse. So `DegEqLeafStepAt` is NOT an `nlinarith`-tractable analogue of `FlpStepAt`.

**Consequence for Problem B.** The clean, cone-certifiable coverage stalls at the sibling class
(`FlpStepAt`, 78.2%). The +13.5% to 91.5% requires either (a) a COMPOUND-gated distant cert (messy,
couples to `QO`/defect-reduction), or (b) a different move family for the residual. This is a genuine
research obstruction, not a mechanical packaging step — the de-risk (verify before Lean) prevented writing
a false or vacuously-narrow cert. The 8.5% whole-hub Type-W (Case-B k-star) remains the final residual.

## State of the Lean packaging (already done) and the true open residual

The local step is ALREADY packaged and kernel-clean in `R3Cert/BGSCLFlpStepAt.lean`:
- `FlpStepAt` — a depth-closed MULTI-flip sibling move class (completes `2m` sibling leaves -> `m` stems at
  one site in one composite step; `m=1` is the single sibling FLP).
- `FlpStepAt.props` / `FlpStepAt.straightStep` — every `FlpStepAt` step is a `StraightStep_sized`
  UNCONDITIONALLY (usize=, strDefect<, Aobj<=, all invariants), axiom-clean.
- `straightProgress_sized_of_coverage` / `hnorm_of_coverage` — reduce `StraightProgress_sized` (hence Hnorm)
  to a pure COVERAGE statement: exhibit `R` refining `StraightStep_sized` covering every positive-defect
  tree. (`FlpStepAt` refines it; the Lean comment measures its class at **52.4% of all trees, n<=12**.)

So **B1 (local step) is complete; the sole open piece of Hnorm is COVERAGE.** This B0 de-risk measures
exactly that coverage on the load-bearing genuine core and shows the path to close it:

1. `FlpStepAt` (sibling multi-flip) covers **78.2%** of the genuine core (n<=14).
2. **The next move class is the DEGREE-EQUALIZING distant leaf relocation** (safe under `deg(par_w) >
   deg(par_v)`) — same path-extension G-machinery, two-site increment. Union with `FlpStepAt` -> **91.5%**.
3. The genuine whole-hub **Type-W** residual is **8.5%** (43 trees, n<=14) — the Case-B k-star relocation,
   the parity-blocked open core.

Recommended sequencing: build a `DegEqLeafStepAt` move class (the degree-equalizing distant leaf move; its
Aobj cert must be gated by the degree hypothesis `deg(par_w) > deg(par_v)`, NOT unconditional) + its
coverage lemma -> union with `FlpStepAt` for `R` -> `hnorm_of_coverage` closes Hnorm to the **91.5%** Type-L
class. The 8.5% whole-hub Type-W (Case-B, moved size >= 2) is the residual to attack last. NOTE: unlike the
sibling `FlpStepAt`, the distant cert is CONDITIONAL — the two-site increment is sign-indefinite without the
degree gate (verified: 34 defect-reducing distant moves DECREASE Aobj when the gate is violated).
