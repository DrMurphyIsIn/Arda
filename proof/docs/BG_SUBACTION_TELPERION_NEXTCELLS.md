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

## 3. NEEDS BG-SIDE DESIGN FIRST (do NOT emit an atom yet)

### (D) `subaction_deg3_deg2_high` — deg-3 hub, one deg-2 + one deg≥3 child  [TWO-SLOPE OBSTRUCTION]
A single tangent cannot slope-match both children: deg-2 ρwit has slope `1/4`, deg≥3 ρwit's per-child
lower-bound line (`rhowit_ge_perchild`) has slope `3/11`. Matching the deg-2 child (`s0 = 1`, slope `1/4`)
leaves the high child with an uncancelled term `(1/4 − 3/11)(bY_h − 1/3) = (3/44)(1/3 − bY_h) ≥ 0`, worst
`= 1/44 ≈ 0.0227` at `bY_h = 0`. Folding that into the scalar overshoots the RHS by ≈ **+0.0195** (fails).
Matching the high child (`s0 = 2/3`, slope `3/11`) makes a slope-`3/11` line lie *above* the deg-2 ρwit
(actual slope `1/4 < 3/11`) — not a valid lower bound. **Resolution is BG-side**: a two-region tangent, a
sharper deg≥3 per-child line whose slope varies with the child's own degree, or exploiting the deg≥3 child's
own subaction surplus (its `ρwit` is not the loose perchild line when `bY_h` is small). Only after the
decomposition is fixed will the residual scalar atom be well-defined — hand Telperion the atom then.

### (E) Remaining d=4 mixed profiles
`subaction_cell_broom_d4` (all-leaf) and `subaction_cell_d4_d3` (deg-3 children) are done. The mixed profiles
(leaf/deg-2/deg≥3 combinations across the 3 children) follow the same assembly with reference
`s0 = 3·(child max message)` per profile — **but any profile containing BOTH a deg-2 and a deg≥3 child hits
the same two-slope obstruction as (D)**. Pure-leaf-plus-one-type profiles are monotone endpoint atoms
(emittable once BG states them, analogous to (B)/(C)). Recommend BG enumerate the 3-child profiles and mark
which are single-slope (ready) vs two-slope (blocked on (D)).

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
