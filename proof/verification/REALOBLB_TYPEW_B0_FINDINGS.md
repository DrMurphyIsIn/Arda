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
