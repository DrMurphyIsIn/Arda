# BG subaction round-trip — handoff (2026-09-03)

Handoff for the cross-front effort that discharges the BG proof's one remaining
obligation, `IsSubaction ρwit`, by generating each per-cell analytic core with
Telperion emitters and assembling it against the live Lean proof. Written so either
session can pick up cold. `conjecture1_proved = False` — this is a WITNESS + a
finite per-cell family, not a closed ceiling; it stays False until the whole family
and the tie land and the chain builds `sorry`-free.

## The proven round-trip (this is the durable result)

The emitter→kernel pipeline is demonstrated end-to-end, axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

1. BG session specifies a cell: node degree `d`, child-degree profile, per-child
   message intervals, tangent reference `s0`.
2. Telperion generates the log-enclosure atom(s) with `emit_log_combination`
   (`route ∈ {monotone, tangent, tight}`), self-checked + negative-controlled.
3. The cell is assembled in Lean — `log_tangent` decouple over `S = Σ bY(c)` +
   the enclosure atom + a per-child ρ-lower-bound + equal-distribution `linarith`.
4. It is built GREEN against the real `R3Cert.BGSCLInduction` / `BGSCLSubaction`
   (worktree of `bg/scl-on-main`; `BGSCLInduction` is Mathlib-only → shallow dep,
   local `lake build` ~10s over the mathlib cache) and delivered on a branch.

## The BG genome (for anyone picking up cold)

`ρwit : Branch → ℝ` (the validated 5-case witness, `R3Cert.BGSCLSubaction`):
```
match bcc b with
| 0 => FSTAR                                   -- leaf (deg 1)
| 1 => (2*FSTAR - Real.log (3/2)) + (1/4)*(bY b - 1/3)  -- deg 2
| 2 => (1/32) * bY b                           -- deg 3
| 3 => (1/384) * bY b                          -- deg 4
| _ => 0                                       -- deg ≥ 5
```
`FSTAR = Real.log (621/64)/11`. Obligation: `IsSubaction ρwit`, i.e.
`∀ cs, (log(1 + (Σ bY c)/(|cs|+1)) − F*) + ρwit(node cs) ≤ Σ_c ρwit c`. Key helpers:
`bY_nonneg`, `bY_le_inv_deg` (`bY b ≤ 1/(bcc b + 1)`), `ρwit_nonneg`, `bY_node`
(`bY(node cs) = 1/((|cs|+1) + Σ bY)`), `log_tangent`
(`log(1+s/d) ≤ log(1+s0/d) + (s−s0)/(d+s0)`).

## Progress map (`IsSubaction ρwit`)

| node degree | status | where |
|---|---|---|
| 1 (leaf) | ✅ | `subaction_nil` (BGSCLSubaction) |
| 2 (leaf/cherry, deg-2, all deg≥3) | ✅ COMPLETE | `subaction_cherry`, `subaction_deg2_deg2child`, `subaction_deg2_highchild` |
| 3, two leaves (pinned) | ✅ | `subaction_broom_d3` |
| **3, two deg≥3 children (first decouple)** | ✅ | `subaction_deg3_highchildren` (branch `bg/scl-deg3-decouple`) |
| 3, profiles with a leaf/deg-2 child | ⏳ | needs tight enclosure / shifted `s0` inside the decouple |
| 4 (multi-child) | ⏳ | same assembly, different reference/distribution |
| ≥5 (ρ=0 tail) | ⏳ | NOT a freebie — high-degree parent with leaf children has positive excess; genuine decouple |

Node degrees 1 and 2 are fully closed; the single-child spine and the first genuine
two-child decouple are done. All three enclosure regimes are proven and emitter-backed.

## Emitter toolbox (all on `main`; see NEW_EMITTERS_SUMMARY.md, README shape table)

- **`log_combination`** — the F\*-folding log-combination `Σ cᵢ·log(rᵢ) ≤ q`. Three
  routes: **monotone** (`q=0`), **tangent** (`log x ≤ x−1`, any-sign `q`, any `k`,
  incl. negative `+F*`), **tight** (degree-3 exp via `Real.exp_bound'`, for when the
  tangent overshoots). This is the per-cell enclosure generator.
- **`recursion_closure`** — tangent-majorant + per-child ceiling → node ceiling (the
  decouple-assembly shape).
- **`curvature_boundary`** — concave-endpoint reduction (`f''` sign → boundary).
- Plus the wider suite (`tight_cap_enclosure`, `affine_param_endpoint`, …).

## Branch map (deliverables on origin — BG session merges into `bg/scl-on-main` as consumed)

- `bg/scl-corrected-cells` — the two deg-4 cells at the validated slopes.
- `bg/scl-tight-enclosure` — `log79_add_fstar` (tight route), merged into `bg/scl-on-main`.
- `bg/scl-deg3-decouple` — `subaction_deg3_highchildren` (first decouple cell).

## Next step (the recommended cell to specify next)

The **deg-3 profile with a deg-2 or leaf child** — it exercises the **tight enclosure
inside the decouple** (the composition `curvature_boundary`/`log_tangent` + tight
`log_combination` were both built for). Near `bY = 1/2` the per-child bound needs the
tight route or a shifted `s0`. After that, the remaining d=3 profiles + the d=4 family
+ the ≥5 tail are the same assembly with different reference/distribution. Hand the
spec (node degree, child-degree profile, message intervals, `s0`) and it turns the
same way.
