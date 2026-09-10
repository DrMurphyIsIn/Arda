# B0 de-risk: Type-W (whole-hub / k-star relocation, Case-B) — the Hnorm coverage residual

**Script pattern:** exact-rational `Aobj` (anchored `a3_derisk.py`), all trees `n <= 14`, genuine hard core
(`min strDefect over roots > 0`, 504 trees). Continues `REALOBLA_FLP_B0_FINDINGS.md`.

## The move (Case-B)

Relocate a whole non-piece child `B` (a `k`-star `kstar k = node(replicate k leaf)`, size >= 2) onto a
bare leaf `v` elsewhere in the tree, extending it into a stem `node[kstar k]`. `BGSCLRealOblBSymBase.lean`
proves the ISOLATED base exactly Aobj-NEUTRAL: `node[kstar k, kstar k] -> afterB k`, both sides
`(4k+2)/(k+1)`, `dAobj = 0` for all `k` (and the asymmetric `node[j-star,k-star]` too).

## Coverage (genuine core, n <= 14)

| move class | coverage |
|---|---|
| sibling-FLP (`FlpStepAt`, clean/unconditional) | 78.2% (394) |
| whole-hub k-star relocation, alone | 93.7% (472) |
| **sibling OR whole-hub-kstar** | **99.6% (502)** |
| residual (neither) | **2 trees** — degseq `[4,4,4,3,1..]`, `[4,3,3,3,2,2,2,1..]` (symmetric multi-hubs) |

On the 43 Type-W trees (not covered by sibling or degree-equalizing distant leaf): **42/43** are covered by
a whole-hub relocation, moved-size {2:22, 3:16, 4:4}, **Aobj strictly POSITIVE in all 42** (the isolated
Case-B base is the neutral extreme; context makes it strict), `B` a literal k-star in 40/42.

**So the whole-hub (Case-B) family is the RIGHT residual move — 99.6% with sibling, far better than the
distant-leaf route (91.5%). The distant-leaf cert is unnecessary.**

## But the move is CONDITIONAL — and NOT cleanly gateable

Like the distant leaf move, the EMBEDDED whole-hub relocation is not unconditionally Aobj-safe:
- random embedded moves: 13940/40000 decrease Aobj; **2199 decrease Aobj even while reducing defect**.
- adding the degree gate `deg(par_B) > deg(par_v)` does NOT fix it: **1529 defect-reducing negatives
  remain** (vs the distant move, where the same gate gave 0). Degree-gated whole-hub covers only 87.5%
  with sibling.

So the whole-hub increment's sign couples to more than a local degree comparison (the base neutrality is
tight; embedding can push either way). No clean local gate certifies it.

## Verdict for Problem B (Hnorm coverage) — the whole map

- **Clean, unconditional coverage = sibling `FlpStepAt` = 78.2%** (done, kernel-clean).
- **Full coverage 99.6%** is achievable by per-tree move selection (sibling ∪ whole-hub-kstar), but **no
  clean move class certifies it**: every residual-covering SPR move (distant leaf, whole-hub k-star) is
  Aobj-CONDITIONAL, safe only in structural configs not captured by any local gate. The proven base cases
  (sibling FLP unconditional; Case-B symmetric/asymmetric neutrality) are the EXTREMAL certificates; lifting
  them to embedded contexts is the open difficulty.
- **2 symmetric multi-hub trees** (degseq `[4,4,4,3,..]`, `[4,3,3,3,2,2,2,..]`) resist even the union of all
  moves — the genuine parity-blocked core.

**This is a genuine research obstruction, not mechanical packaging.** The coverage reduction
(`hnorm_of_coverage`) is in hand; what is missing is a certifiable safe-move-SELECTION rule for the
conditional SPR moves — the sign of each embedded increment depends on global degree structure. `Hnorm`
stays open; `conjecture1_proved = False`.

## MECHANISTIC ROOT CAUSE (why the residual is hard): the G1 lift-gain fails

The `FlpStepAt` machinery lifts a move through ANY context UNCONDITIONALLY iff the acted node satisfies
BOTH cavity gains (`dtSub_gains_lift` + `Aobj_child_replace_of_gains`):
- **G1**: `Ztot(dtSub before) <= Ztot(dtSub after)`
- **G2**: `Zopen(dtSub before)/udeg(before) <= Zopen(dtSub after)/udeg(after)`

For the Case-B whole-hub move (acted node `node[star_j, star_k] -> node[node(replicate(j-1) leaf ++
[node[star_k]])]`), computed exactly over `j,k in 1..8`:
- **G1 FAILS in 55/64** cases — the move DECREASES the acted node's `Ztot(dtSub)`.
- G2 holds (0/64 violations).

So the whole-hub move CANNOT use the lift machinery: it lowers the acted node's total, so a parent sees a
weaker child and the embedded Aobj can drop. G1 is restored only in a tiny sub-region (`j >= 2k+2`:
relocate a SMALL star onto a MUCH larger one — `j=4->k<=1, j=6->k<=2, j=8->k<=3, j=10->k<=4`), which covers
**0.2%** of the genuine core (union with sibling stays 78.2%).

**Conclusion.** The existing lift machinery certifies EXACTLY the sibling-FLP class (**78.2%**). Every
residual-covering move (distant leaf, whole-hub k-star) FAILS G1 and therefore requires a fundamentally
NON-LOCAL certification (its Aobj sign depends on the global tree, not on the acted node alone). That is the
precise, mechanistic wall for the coverage route to `Hnorm` — the clean-liftable ceiling is 78.2%, and
closing the remaining 21.4% (to 99.6%) plus the final 2-tree symmetric core is genuine open research.

## The EXACT non-local safe condition, and the sharp open lemma

For an acted node that is a child of a degree-`k` parent whose OTHER children contribute `QO` to `qSum`,
the cavity factorization gives the parent-Aobj increment `∝ (1 + QO/k)·G1 + (1/k)·G2`. Hence the move is
Aobj-nondecreasing IFF

    G2  >=  (k + QO)·(-G1)          [ G1 <= 0 for the residual moves; G2 >= 0 ]

an explicit condition that couples the LOCAL gains `(G1,G2)` to the NON-LOCAL context `(k, QO)` (larger
parent degree / more siblings ⇒ harder). This is the precise certification target; there is no local-only
strengthening (deeper embeddings only add more context factors).

Empirically a satisfying site ALWAYS exists: greedy DEEPEST-DEFECT-FIRST, picking the Aobj-MAX
defect-reducing SPR move, straightens every genuine tree (n<=12: 30/30) with **0 Aobj decreases**. But this
is near-tautological — the max move is safe *because* a safe move exists. It reduces `Hnorm` coverage to
one crisp, genuinely-open lemma:

> **(Hnorm residual)** For every tree `t` with `strDefect t > 0`, there EXISTS an SPR move `t -> t'` with
> `strDefect t' < strDefect t` and `Aobj t <= Aobj t'`.

This "a straightening direction never costs `Aobj`" claim is a weak-but-genuine form of the BG extremality
principle. It is verified exhaustively (n<=12 via generic SPR, 100%) but has no local cavity certificate —
proving it is the open frontier (a global potential / amortized argument, or a direct `per(L)/prod deg`
bound). `conjecture1_proved = False`.
