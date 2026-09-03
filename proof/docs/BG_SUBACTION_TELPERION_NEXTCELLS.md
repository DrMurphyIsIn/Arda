# Telperion handoff — enclosure atoms for the next `IsSubaction ρwit` cells (2026-09-03)

**For the parallel Telperion session.** Branch `bg/scl-on-main` (GitHub `DrMurphyIsIn/Arda`).
Companion to `BG_CEILING_SUBACTION_HANDOFF.md`. `conjecture1_proved = False`.

## 0. What Telperion produces

The BG ceiling now rests on the single obligation `IsSubaction ρwit`, discharged cell-by-cell over a
finite per-node family. Each cell's proof (BG side) does: `log_tangent` decouple → node-ρ bound →
per-child ρ lower bounds → `linarith`. The **one analytic input Telperion supplies per cell is a scalar
enclosure atom** — a message-independent inequality of the form

```
Σ_i a_i · Real.log (r_i) − k · FSTAR  ≤  B          (a_i, k, B, r_i all rational)
```

emitted by `emit_log_combination`. Multiply by 11 (`11·FSTAR = log(621/64)`) to get the **fold**
`X = ∏_i r_i^(11 a_i) · (64/621)^k`, and the atom is exactly `log X ≤ 11·B`, i.e. `X ≤ exp(11·B)`.
Route by where `X` sits:

- **monotone** — `log x ≤ x − 1` at `X ≤ 1` with `11B = 0` (strictly requires `q = 0`). Cheapest.
- **tangent** — degree-1 `log x ≤ x − 1` folded through FSTAR, gated by `X − 1 ≤ 11B` (`11B = N·q`), any-sign `q`.
- **tight** (Q<0) — degree-3 exp Taylor (`Real.exp_bound'`, `n = 3`) for the **added-FSTAR** blocker shape
  (`log(7/9) + F* ≤ …`), where `11B < 0`. Shows `X · exp(−11B) ≤ 1`. HARD-REQUIRES `11B < 0`.
- **tight_hi** (Q>0) — degree-`n` exp **lower** bound for `11B > 0` with fold `X > 1`. Discharges `log X ≤ 11B`
  via `Real.log_le_iff_le_exp` + `Real.exp_bound` (`exp(11B) ≥ Sₙ − Eₙ`) then rational `X ≤ Sₙ − Eₙ`;
  auto-picks the smallest `n ≤ 8` that closes. This route DID NOT EXIST when the spec was first written — it was
  added by the Telperion session for atom (A) (branch `telperion/log-combination-tight-hi`).

Established examples in-repo (match this naming + shape): `log119_sub_fstar` (tangent),
`log79_add_fstar` (tight, `q = 11/24`), `log74_le_4fstar`, `log54_sub_fstar_le'`, `log53_enc`, `d2_deg5_enc`.

> **Route-label correction (2026-09-03, post-delivery).** The route tags in §2 below were WRONG in the first
> draft and are corrected here: (A) is **tight_hi** (not the existing tight route — that requires `Q<0`, atom A
> has `Q=+79/96`); (B) and (C) are **tangent** (not monotone — monotone strictly needs `q=0`, and the
> `X−1 ≤ N·q` gate quoted for them is the *tangent* gate). Atom A also folds cleanly `2·log(3/2)+log(4/3)=log 3`
> (fold `X = 3^11/(621/64)^5 ≈ 2.06`). All three were emitter-generated and delivered on
> `bg/scl-deg3-leaf-cells` (`R3Cert/BGSCLSubactionEnc2.lean`), axiom-clean.

## 1. State reconciliation (the §3/§5 cell table in the main handoff is slightly stale)

Already **landed** on `bg/scl-on-main` (verified present + axiom-clean via `AxiomGuard.lean`, commit `80e51d1`):

| node deg | children | cell theorem |
|---|---|---|
| 1 | — | `subaction_nil` |
| 2 | leaf | `subaction_cherry` |
| 2 | deg-2 | `subaction_deg2_deg2child` |
| 2 | deg≥3 | `subaction_deg2_highchild` |
| 2 | deg≥5 | `subaction_deg2_deg5child` |
| 3 | leaf,leaf | `subaction_broom_d3` |
| 3 | deg≥3,deg≥3 | `subaction_deg3_highchildren` |
| 4 | leaf,leaf,leaf | `subaction_cell_broom_d4` |
| 4 | deg-3 profile | `subaction_cell_d4_d3` |

So deg-1, deg-2 (all child types), and part of deg-3/deg-4 are done. Remaining below.

## 2. READY TO EMIT — three atoms, exact, verified numerically

These three cells close with a single tangent + independent per-child bounds; Telperion can generate the
atoms immediately. Constants verified against `F* = log(621/64)/11 ≈ 0.2065862`.

### (A) `subaction_deg3_deg2children` — deg-3 hub, two deg-2 children  [route: TIGHT_HI]
- BG assembly: `s0 = 1` (slope `1/(3+1) = 1/4` = ρwit(deg-2) slope ⇒ per-child bound message-independent);
  `log_tangent (d:=3)(s:=S)(s0:=1)`: `log(1+S/3) ≤ log(4/3) + (S−1)/4`. Node-ρ `ρwit(node)=1/(32(3+S)) ≤ 3/352` (`S ≥ 2/3`).
- **Atom:** `2·Real.log (3/2) + Real.log (4/3) − 5·FSTAR ≤ 79/1056`  (LHS folds to `log 3 − 5·FSTAR`).
- Fold `Y = 3^11/(621/64)^5 = (3/2)^22·(4/3)^11·(64/621)^5 ≈ 2.0596 > 1`; `11B = 79/96 ≈ 0.8229 > 0`. This needs the
  **tight_hi route** (Q>0, X>1) — the existing tight route requires `Q<0` and does NOT apply, and `x−1 ≈ 1.06 > 0.82`
  kills the tangent gate. `Real.exp_bound` degree-`n` lower bound, auto-picks `n = 4` (slack ≈ 0.17), `exp(79/96) ≈ 2.277 ≥ Y`.
- Delivered as `deg3_deg2children_enc` (multi-term ⇒ `_enc` suffix), cell margin **+0.00913**.

### (B) `subaction_deg3_leaf_deg2` — deg-3 hub, one leaf + one deg-2 child  [route: TANGENT]
- The leaf's `ρwit = F*` alone dominates the RHS (`F* ≤ ρwit(leaf)+ρwit(deg-2)`), so the cell reduces to
  `e_node + ρwit(node) ≤ F*` in the single variable `S = 1 + bY(deg-2) ∈ [4/3, 3/2]`. The LHS is increasing in `S`
  (derivative `1/(3+S) − 1/(32(3+S)²) > 0`), so evaluate at the endpoint `S = 3/2`.
- **Atom:** `Real.log (3/2) − 2·FSTAR ≤ −1/144`.
- Fold `X = (3/2)^11·(64/621)^2 ≈ 0.9188`; `11B = −11/144 ≈ −0.0764 < 0`; `X−1 ≈ −0.0812 ≤ 11B` → **tangent** OK
  (NOT monotone — monotone requires `11B = 0`; this passes the `X−1 ≤ 11B` tangent gate).
- Delivered as `log32_sub2fstar`, cell margin **+0.00076** (tight but valid).

### (C) `subaction_deg3_leaf_high` — deg-3 hub, one leaf + one deg≥3 child  [route: TANGENT]
- Same "leaf ρ = F* dominates" reduction; `S = 1 + bY(deg≥3) ∈ [1, 4/3]`, endpoint `S = 4/3`.
- **Atom:** `Real.log (13/9) − 2·FSTAR ≤ −3/416`.
- Fold `X = (13/9)^11·(64/621)^2 ≈ 0.6069`; `11B = −33/416 ≈ −0.0793 < 0`; `X−1 ≈ −0.393 ≤ 11B` → **tangent**, huge slack.
- Delivered as `log139_sub2fstar`, cell margin **+0.038** (comfortable).

## 3. CELL (D) — SOLVED (redesign landed); (E)/(F) still need BG-side design

### (D) `subaction_deg3_deg2_high` — deg-3 hub, one deg-2 + one deg≥3 child  [RESOLVED 2026-09-03]
The two-slope obstruction (deg-2 ρwit slope `1/4` vs deg≥3 per-child slope `3/11`; a single tangent can't
match both, overshoots ≈ **+0.0043** at the `(bY_d2,bY_h)=(1/3,0)` corner via the loose `rhowit_ge_perchild`
line) is **dissolved WITHOUT a two-slope decouple**. Key move: the high child's message is small (`bY_h ≤ 1/3`),
so bound it into a constant, **DROP its (nonnegative) `ρwit` entirely** (no per-child line ⇒ no slope to match),
and reduce to a single-variable inequality in the deg-2 child's message. Tangent at `s0 = 1` (slope-match the
deg-2 child), node-ρ `≤ 3/320`, and ONE new atom closes it. Proven + axiom-clean in
`R3Cert/BGSCLSubactionDeg3Mid.lean` (`subaction_deg3_deg2_high`), worst corner `(1/3,1/3)`, atom margin `+0.0006`.
- **New atom (delivered here, `log2_sub3fstar`) — route TIGHT_HI:** `Real.log (4/3) + Real.log (3/2) − 3·FSTAR ≤ 71/960`.
  Fold `X = (4/3)¹¹·(3/2)¹¹·(621/64)⁻³ = 536870912/239483061 ≈ 2.2418 > 1`, `Q = 781/960 > 0`. **Needs degree-5
  Taylor** (n=4 lower bound `≈ 2.2114 < X`; n=5 gives `exp Q ≥ 61122928451812033/27179089920000000 ≥ X`) — a data
  point that the tight_hi auto-`n` search must go past n=4. Dogfood note for the emitter: confirm it escalates n.

### (E) Remaining d=4 mixed profiles  [the (D) trick unblocks the two-slope cases]
`subaction_cell_broom_d4` (all-leaf) and `subaction_cell_d4_d3` (deg-3 children) are done. The mixed profiles
(leaf/deg-2/deg≥3 combinations across the 3 children) follow the same assembly with reference
`s0 = 3·(child max message)` per profile. Any profile mixing a deg-2 and a deg≥3 child previously hit the (D)
two-slope obstruction — **now dissolved by the same (D) recipe**: bound each deg≥3 child's message `≤ 1/3`,
drop its `ρwit ≥ 0`, and slope-match only the deg-2 child(ren). Each profile still needs its own scalar atom
(different constant/fold), but the *shape* is settled — no research left, just per-profile atom emits. Recommend
BG enumerate the d=4 profiles and hand Telperion the atom list; each is monotone/tangent or tight_hi by fold.

### (F) deg≥5 tail
`ρwit(node) = 0` for deg ≥ 5, so `(SUB)` is `e_node ≤ Σ_c ρwit(c)`. This is **not** a uniform `≤ 0` collapse:
leaf children push `S` up to `d − 1`, so `e_node = log(1 + S/d) − F*` can be positive and must be covered by
`Σ ρwit ≥ (#leaf children)·F*`. Needs the decouple with the bound `Σ_c ρwit(c) ≥ |leaf children|·F*`; the
residual atom is a family in `d` (parametric), not a single scalar — BG to state the parametric form first.

## 4. Verification protocol (per atom)

1. Telperion emits the atom lemma into `R3Cert/BGSCLSubactionEnc.lean` (or a new `…Enc*.lean`), route as
   specified, `import Mathlib` + `import R3Cert.BGSCLInduction`, namespace `R3Cert.BGSCL`.
2. `lake build R3Cert.BGSCLSubactionEnc` green; no bare `sorry`/`admit` (write "no \`sorry\`" in prose to
   avoid the CI grep-scan false positive).
3. Deliver on the branch; BG side merges + writes the cell theorem consuming it, then adds the cell theorem to
   `AxiomGuard.lean` (`#print axioms R3Cert.BGSCL.subaction_…`) so CI keeps the axiom-clean claim enforced.
4. Confirm `lake env lean AxiomGuard.lean` reports `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Local build works: `PATH=$HOME/.elan/bin; cd proof/formalization; lake exe cache get; lake build …`
(toolchain v4.32.0; the `R3Cert.+` glob self-builds every module).
