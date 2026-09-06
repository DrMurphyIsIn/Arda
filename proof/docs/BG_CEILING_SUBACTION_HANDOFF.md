# BG classical ceiling via additive SUBACTION — consolidated handoff (2026-09-03)

**Status: reduction chain kernel-complete; `IsSubaction ρwit` per-cell family in progress.
`conjecture1_proved = False`.** Branch `bg/scl-on-main` (GitHub `DrMurphyIsIn/Arda`).

## 1. The result and the reduction chain (all kernel-green, axiom-clean `[propext, Classical.choice, Quot.sound]`)

Goal: the BG classical branch ceiling `∀ b, bell b ≤ 0` (equivalently `Gf b := exp(11·bell b) ≤ 1`,
`Gf b = btotal(b)^11·(64/621)^|b|`), `bell b = log(btotal b) − |b|·F*`, `F* = log(621/64)/11`.

The ceiling telescopes per-vertex: `bell b = Σ_v e_v`, `e_v = log(1 + S_v/d_v) − F*`, `S_v = Σ_{child c} bY c`,
`d_v = deg v = bcc v + 1`.  An **additive subaction** `ρ : Branch → ℝ` with `ρ ≥ 0` and the per-vertex
inequality `(SUB)  e_v + ρ(v) ≤ Σ_c ρ(c)` telescopes to `bell b ≤ −ρ(root) ≤ 0`.

| theorem (`R3Cert.BGSCL`, file) | statement |
|---|---|
| `ceiling_of_subaction` (BGSCLSubaction) | `(∀b 0≤ρ b) → IsSubaction ρ → ∀b bell b ≤ 0` |
| `ρwit_nonneg` (BGSCLSubaction) | `∀b, 0 ≤ ρwit b` (nonneg leg DISCHARGED) |
| `ceiling_of_witness` (BGSCLSubaction) | `IsSubaction ρwit → ∀b bell b ≤ 0` |

So the **entire ceiling now rests on the single obligation `IsSubaction ρwit`.**

Why additive, not the earlier cap: the multiplicative capped-product step `Le1Step` is **FALSE**
(`proof/docs/BG_LE1STEP_REFUTED_20260902.md`, exact counterexample 3 children at message 13/42 → 1.006 > 1).
A *sum* of slightly-loose local terms telescopes; a *product* overshoots. The subaction cannot hit that.

## 2. The witness `ρwit` (validated, `R3Cert/BGSCLSubaction.lean`)

```
ρwit(leaf)   = F*
ρwit(deg 2,μ) = 2F* − log(3/2) + (1/4)(μ − 1/3)     -- μ = bY = 1/3 at the cherry (tie anchor)
ρwit(deg 3,μ) = μ/32
ρwit(deg 4,μ) = μ/384
ρwit(deg ≥5)  = 0
```
Keyed by `bcc b` (degree − 1) and `bY b`.  Only `F*` and `log(3/2)` are transcendental (deg 1,2);
deg 3,4 rational-linear; deg ≥5 vanishes (because `e_tail = log(1+1/d) − F* > 0` ONLY for `d = 2,3,4`).
**Validated exhaustively** (all 376k branches n≤16 + high-degree parents to deg-140 + spider family +
120k mixed high-degree trees), margin 0, tight only at the `27·23 = 621` tie.  NB: the earlier
`ρwit(deg≥4)=0` witness FAILED the high-degree-parent tail — this corrected witness is the valid one.

## 3. `IsSubaction ρwit` cell map — what's proven, what remains

`IsSubaction ρwit := ∀ cs, (log(1 + (cs.map bY).sum/((cs.length)+1)) − F*) + ρwit(node cs) ≤ (cs.map ρwit).sum`.
Finite per-node family: node degree `d = |cs|+1`.

| node deg | children | cell | status |
|---|---|---|---|
| 1 | — | `subaction_nil` | ✅ |
| 2 | leaf (cherry) | `subaction_cherry` (exact tie leg) | ✅ |
| 2 | deg-2 | `subaction_deg2_deg2child` (tangent@½ + secant + `log54_sub_fstar_le'`) | ✅ |
| 2 | deg≥3 (all) | `subaction_deg2_highchild` (uses `log79_add_fstar`, TIGHT route) | ✅ |
| 3 | leaf,leaf | `subaction_broom_d3` (fixed-point) | ✅ |
| 3 | deg≥3, deg≥3 | `subaction_deg3_highchildren` (DECOUPLE, `BGSCLSubactionDeg3.lean`) | ✅ |
| 3 | {leaf,deg-2}×{leaf,deg-2,deg≥3} | see §5 | ⏳ |
| 4 | multi-child | same assembly, d=4 reference | ⏳ |
| ≥5 | (ρ=0 tail) | multi-child decouple (leaf children give `S` up to `d−1`, covered by `Σρ = |leaves|·F*`) | ⏳ |
| tie | `27·23` | exact identity | ⏳ |

**Node degrees 1 and 2 COMPLETE; the single-child spine complete; first two multi-child (broom + first
decouple) done.**

## 4. The round-trip protocol (PROVEN end-to-end)

1. **BG side** specifies a cell: node degree `d`, child-degree profile, message intervals, tangent reference `s0`.
2. **Telperion side** (`emit_log_combination`) generates the enclosure atom, verifies green against `R3Cert.BGSCLInduction`, delivers on a branch.
3. **BG side** merges + assembles (`log_tangent` decouple + node-ρ bound + per-child ρ-lower-bound lemma + equal-distribution `linarith`) into the cell, verifies green + axiom-clean, merges to `bg/scl-on-main`.

Three enclosure regimes, all built + dogfooded: **monotone** (`≤0`, tie identity), **tangent** (degree-1
`log x≤x−1`, any-sign q), **tight** (degree-3 exp via `Real.exp_bound'` — needed when the fold `X` is near
`e^q`, or `X>1`).  Decouple = `RecursionClosureEmitter` shape; `log_tangent` is in the repo.

**KEY assembly trick:** choose `s0` so the tangent slope `1/(d+s0)` MATCHES `ρwit`'s slope on the heavy child
degree → the per-child bound becomes **message-independent** (collapses to one scalar log-combination atom).

## 5. Next cell specs (ready to generate)

**`subaction_deg3_deg2children` — deg-3 hub, two deg-2 children** (exercises TIGHT route inside the decouple):
- Profile `bcc c₁ = bcc c₂ = 1`, `bY cᵢ ∈ [1/3, 1/2]` (`bY_ge_third_of_bcc1` + `bY_le_inv_deg`).
- Reference **`s0 = 1`** (slope-matching: `1/(3+1) = 1/4 = ρwit(deg-2)` slope ⇒ per-child bound bY-independent).
  `log_tangent (d:=3)(s:=S)(s0:=1)`: `log(1+S/3) ≤ log(4/3) + (S−1)/4`.
- Node-ρ bound `ρwit(node) = (1/32)/(3+S) ≤ 3/352` (`S ≥ 2/3`).
- **Enclosure atom (TIGHT route needed):** `2·log(3/2) + log(4/3) − 5·F* ≤ 79/1056`.
  Fold `Y = (3/2)²²·(4/3)¹¹·(64/621)⁵ ≈ 2.06 > 1`, so `log x ≤ x−1` is loose (`x−1 ≈ 1.06 > 0.823` needed);
  degree-3 exp route closes it (`Y ≤ 1+q+q²/2+q³/6 ≤ exp q`, `q = 79/96`).
- Per-child bound (deg-2, bY-independent): `2F*−log(3/2)+1/24 ≥ C'/2`, `C' = log(4/3)−F*+3/352` — reduces to the atom.  Margin **+0.0091**.

**Remaining d=3 profiles:** `leaf+deg≥3` and `leaf+deg-2` close via `LHS ≤ F* ≤ RHS` (leaf's `ρ=F*` dominates;
monotone enclosure); `deg-2+deg≥3` = one deg-2 (tight atom) + one deg≥3 (§3 per-child bound).
**d=4:** same assembly, reference `s0 = 3·(child max message)` per profile.
**Tail (deg ≥5):** `ρwit(node)=0`, so `e_node ≤ Σρ(c)`; NOT a uniform `≤0` collapse (leaf children give
`S` up to `d−1`) — needs the same decouple, `Σρ ≥ |leaf children|·F*` covering `e_node`.

## 6. Files

- `R3Cert/BGSCLInduction.lean` — Branch model, `bell`, `bY`, `bell_node`, `log_tangent`, `bY_node`, `scl_of_child_step` (shared, on `main`).
- `R3Cert/BGSCLSubaction.lean` — `IsSubaction`, `ceiling_of_subaction`, `ρwit`, `ρwit_nonneg`, `ceiling_of_witness`, all §3 cells + helpers (`bY_le_one`, `bY_le_inv_deg`, `bY_ge_third_of_bcc1`, `cherry_anchor_nonneg`, `log54_sub_fstar_le'`, `log53_enc`, …).
- `R3Cert/BGSCLSubactionEnc.lean` — `log79_add_fstar` (Telperion tight-route enclosure).
- `R3Cert/BGSCLSubactionDeg3.lean` — `subaction_deg3_highchildren` + `log119_sub_fstar` + `rhowit_ge_perchild`.
- Telperion `emit_log_combination` (routes monotone/tangent/tight) — the enclosure generator.

## 7. Honest scope

Kernel-complete: the reduction `ceiling ⟸ IsSubaction ρwit`, the witness + its nonnegativity, and the
single-child + first multi-child cells.  Open: the rest of the `IsSubaction ρwit` per-cell family (d=3 mid
profiles, d=4, the deg≥5 tail) and the `27·23` tie identity.  The round-trip is proven, the tools built, the
pattern pinned — the remainder is finite, patterned generation, not new mathematics.  `conjecture1_proved = False`
until the whole family lands and the chain builds sorry-free.  Do NOT claim the ceiling closed before then.
