# BG additive-SUBACTION ceiling — consolidated handoff (2026-09-03)

**Status: the ceiling reduces to the single obligation `IsSubaction ρwit`; the deg-1/2/3 cell families are COMPLETE,
the full d=4 atom table is proven, all three deg≥5 uniform tail families + the 27·23 tie are proven, AND all three
reduce-to-uniform MESSAGE halves (deg-2/3/4) are proven. Remaining: the d=4 cell wiring (mechanical), the top-level
`IsSubaction` assembly + Branch list-lift (mechanical), and the counts→single-degree EXCHANGE for mixed-degree tail
configs (the one genuine research nub). `conjecture1_proved = False`.**

Branch `bg/scl-on-main` (GitHub `DrMurphyIsIn/Arda`). Everything below is `no sorry`, kernel-verified, axiom-clean
`[propext, Classical.choice, Quot.sound]` (CI-enforced by `AxiomGuard.lean`, **31 guarded theorems**), full
`lake build` green (BG-subaction build re-verified INDEPENDENTLY 2026-09-03: 8663 jobs, 8 modules, no sorry,
AxiomGuard clean). Supersedes the running notes in `BG_CEILING_SUBACTION_HANDOFF.md`,
`BG_SUBACTION_TELPERION_NEXTCELLS.md`, `BG_SUBACTION_D4_TAIL_TIE_SPEC.md` (kept for detail/derivations).

---

## 1. The reduction (kernel-green)

The classical branch ceiling `∀ b, bell b ≤ 0` (`bell b = log(btotal b) − |b|·F*`, `F* = log(621/64)/11`).
The earlier multiplicative capped-product step `Le1Step` is **FALSE** (`BG_LE1STEP_REFUTED_20260902.md`, exact
counterexample). The live line is the **additive subaction**: a `ρ ≥ 0` with the per-vertex inequality
`(SUB)  e_v + ρ(v) ≤ Σ_child ρ(c)` telescopes to `bell b ≤ −ρ(root) ≤ 0`.

| theorem (`R3Cert.BGSCL`) | statement |
|---|---|
| `ceiling_of_subaction` | `(∀b, 0≤ρ b) → IsSubaction ρ → ∀b, bell b ≤ 0` |
| `ρwit_nonneg` | `∀b, 0 ≤ ρwit b` (nonnegativity leg — DISCHARGED) |
| `ceiling_of_witness` | `IsSubaction ρwit → ∀b, bell b ≤ 0` |

The witness `ρwit` (keyed by degree `bcc+1` and message `bY`), validated exhaustively (376k branches n≤16 +
high-degree parents to deg-140 + spider + 120k mixed), margin 0 tight only at the 621 tie:
```
ρwit(leaf) = F*;  ρwit(deg-2,μ) = 2F*−log(3/2)+(μ−1/3)/4;  ρwit(deg-3,μ) = μ/32;  ρwit(deg-4,μ) = μ/384;  ρwit(deg≥5) = 0
```
So the **entire ceiling rests on `IsSubaction ρwit`** — a finite per-node cell family (`∀ cs, e_node + ρwit(node cs)
≤ Σ ρwit(c)`, node degree `d = |cs|+1`).

## 2. `IsSubaction ρwit` — what is proven

### Node degree 1, 2 — COMPLETE
`subaction_nil` (deg-1), `subaction_cherry` (deg-2/leaf), `subaction_deg2_deg2child`, `subaction_deg2_highchild`
(deg≥3 child, subsumes deg≥5), `subaction_deg2_deg5child`.

### Node degree 3 — COMPLETE (all six child profiles)
`subaction_broom_d3` (leaf,leaf), `subaction_deg3_highchildren` (deg≥3,deg≥3), `subaction_deg3_deg2children`
(deg-2,deg-2), `subaction_deg3_leaf_deg2` (leaf,deg-2), `subaction_deg3_leaf_high` (leaf,deg≥3), and the redesigned
two-slope **`subaction_deg3_deg2_high`** (deg-2,deg≥3). Cell (D) was the crux: the deg-2 slope 1/4 vs deg≥3 per-child
slope 3/11 can't both be slope-matched by a single tangent; dissolved by **bounding the high child's message ≤1/3,
DROPPING its (nonneg) ρwit, and slope-matching only the deg-2 child** — a recipe that also unblocks d=4 mixed profiles.
Enclosure atoms in `BGSCLSubactionEnc2.lean` (deg3_deg2children_enc, log32_sub2fstar, log139_sub2fstar) +
`log2_sub3fstar` (cell D).

### Node degree 4 — the full 35-atom table proven; cells are mechanical
All **35 d=4 child-profile enclosure atoms** are proven in `BGSCLSubactionD4.lean` via one reusable lemma
`tangent_atom` (the tangent-route enclosure generator, written with `zpow` so a single lemma covers every
`log(3/2)`-fold sign, incl. the 15 negative-`kL` (2,*) profiles). Each profile closes with a single `log_tangent` at
its binding corner (verified: no two-slope wall at d=4, since each binding corner puts all children at a common
message). The 35 `subaction_*` cells themselves (wiring each atom + tangent + `linarith` over the message box) are the
one mechanical remaining d=4 task — the atoms and the recipe are done. NB: the pre-existing `subaction_cell_broom_d4` /
`subaction_cell_d4_d3` use a SUPERSEDED witness (ρ3), not `ρwit`.

### Node degree ≥5 (the tail) — all three uniform families + the tie proven
`ρwit(node)=0`, so `(SUB)` is `log(1+S/d) − F* ≤ Σ ρwit(c)` (`S=Σ bY(c)`, `d−1` children). The naive
"`Σρ ≥ |leaves|·F*`" design is WRONG (fails at 4 deg-3 children, no leaves, e_node>0). The worst profile per d is
uniform-type. Proven families (`BGSCLSubactionTail.lean`):
- `tail_all_deg4` (∀d≥1): `log((5d−1)/(4d)) − F* ≤ (d−1)/1536` — the flattest (min slack +0.0057 @ d=18).
- `tail_all_deg3` (∀d≥1): `log((4d−1)/(3d)) − F* ≤ (d−1)/96`.
- `tail_all_deg2` (∀d≥5, ℕ, the **TIE family**, exact equality at d=6): `log((4d−1)/(3d)) ≤ (2d−1)F* − (d−1)log(3/2)`.
  Not closable by one concavity bound over ℝ (tight@d6) → ℕ-dispatch: d=5 (fold), d=6 (`tie_identity_d6`), d≥7
  (`tail_all_deg2_large`, concavity + a quadratic with negative discriminant, using `henc_deg2_qp7`/`henc_deg2_q7`).
- The 27·23 tie: `tie_identity_d6` (`(23/18)·(3/2)⁵ = 621/64`) + `subaction_tail_tie_d6` (deg-6, five cherry children,
  exact equality).

## 3. Remaining pieces (updated 2026-09-03 by review-owner)

The tail families cover uniform-degree configs. To cover ARBITRARY child multisets, the reduce-to-uniform argument.
Its structure is fully characterized; the message halves are now ALL proven:

1. **Within a degree, only count + message-sum matter** — `ρwit` is affine in the message, so the message
   *distribution* within a degree is irrelevant. (Established.)
2. **Message → worst endpoint** — the per-degree SUB-slack. **DONE for all three** (`BGSCLSubactionExch.lean`):
   `tail_deg2_sum` (deg-2, slope-monotone), `tail_deg3_sum` (`log(1+S/d)−F* ≤ S/32`, ∀d≥5, `0≤S≤(d−1)/3`),
   `tail_deg4_sum` (`log(1+S/d)−F* ≤ S/384`, ∀d≥5, `0≤S≤(d−1)/4`). So the message half of reduce-to-uniform is CLOSED
   for every degree.
3. **Counts → single-degree exchange** across degrees (worst counts all in one degree) — the discrete convexity crux.
   **OPEN — the one genuine research nub.** With the EXACT coupled `log(1+S/d)` the children do not separate, so the
   per-child/independence shortcut does NOT apply (see the subadditivity no-go in §5). Likely a discrete
   convexity/majorization argument.
4. **Branch-level list lift** — expressing `Σρ`/`ΣbY` over arbitrary child lists (mechanical list induction). OPEN.
5. **d=4 cell wiring** — the 35 `d4_*` enclosure atoms + `tangent_atom` recipe are done; the 35 node-level
   `subaction_deg4_*` cells (wire atom + `log_tangent` + `linarith` over the message box, per the d=3 templates in
   `BGSCLSubactionDeg3Mid.lean`) are unwritten. MECHANICAL. Completes node degree 4.

**Recommended next steps (in order of tractability):** (a) the d=4 cell wiring (mechanical, completes node deg 4);
(b) the Branch list-lift + top-level `IsSubaction` degree-dispatch for the finite (deg ≤4) part; (c) the counts
exchange — the genuine research nub. Steps (a),(b) are patterned repetition; (c) is the real remaining mathematics.

## 4. Tools & techniques (reusable)

- **`tangent_atom (A kL kF B)`** (`BGSCLSubactionD4.lean`) — one-line tangent-route enclosures; `zpow` handles any
  `log(3/2)`-fold sign; `hfold` is a `norm_num` fact (works even for ~120-digit folds, ~5s).
- **tight_hi route** — for folds `X>1`, `Q>0` (where tangent's `X−1≤11B` fails and the old `tight` route needs `Q<0`):
  `Real.log_le_iff_le_exp` + a degree-`n` Taylor LOWER bound on `exp Q` (`Real.exp_bound`), auto-`n`. Used by
  `log2_sub3fstar` (n=5), `tail_all_deg3`'s atom (n=5), `henc_deg2_q7` (n=4). Telperion shipped this as an emitter
  route (`telperion/log-combination-tight-hi`), incl. a 5th route `tangent_multi` for the negative-`kL` (2,*) atoms.
- **cell-(D) drop-the-high-child recipe** — dissolves two-slope obstructions (deg-3 mixed, d=4 mixed).
- **tail family recipe** — `log((·d−1)/(·d)) = log(·) + log(1−1/(·d)) ≤ log(·) − 1/(·d)` (concavity) + a tight_hi atom
  + a negative-discriminant quadratic `nlinarith [sq_nonneg (·)]`.
- **message-monotonicity** (`tail_deg2_sum`) — `g(S)=log(1+S/d)−S/4` monotone via `log((d+S)/(d+S0)) ≤ (S−S0)/(d+S0)`.

## 5. Footguns (this line)

- **NO-GO for the counts exchange (checked 2026-09-03): log-subadditivity is too lossy.** The tempting shortcut
  `log(1+S/d) ≤ Σ log(1+bY(cᵢ)/d)` decouples the children (then each child's `δ = log(1+bY/d) − ρwit` is independent,
  so the worst config is trivially uniform-at-argmax). But the subadditive bound loses too much: at d=18, all deg-4,
  it gives `Σρ`-requirement `≈ 0.0279` where the EXACT `tail_all_deg4` needs `≤ 0.0111` (slack +0.006) — i.e. it fails
  by 2.5×. So the counts exchange MUST use the exact coupled `log(1+S/d)`; the per-child/independence route is a dead
  end. This is why (3) is genuinely discrete-convexity, not a per-child bound.
- `(4/3)^11 ≈ 23.7` (not ~4.4): `log(4/3) − F*` folds to `X≈2.44 > 1` ⇒ **tight_hi, not tangent**. Sanity-check fold
  magnitudes before choosing a route.
- `field_simp` sometimes fully closes an identity ⇒ a trailing `ring` errors "no goals" (case-dependent; e.g. `hfact`
  needs bare `field_simp`, but `hid` needs `field_simp; ring`).
- List-length casts: `↑(0+1+1+1+1+1)` needs `Nat.reduceAdd` in the simp set to fold to 5.
- ℕ-degree dispatch: after `subst h` the goal carries `↑5` — `push_cast` BEFORE `rw [show (4*(5:ℝ)−1)/… = …]`.
- `positivity` won't use hypotheses for `set`-opaque terms — discharge `0 ≤ S0` / `0 < 1+S0/d` explicitly
  (`div_nonneg`, `div_pos`).
- `Real.log_zpow` + `positivity` handle signed folds uniformly; `norm_num` evaluates zpow of concrete rationals.

## 6. Honest scope

Proven: the reduction, the witness + nonnegativity, deg-1/2/3 cells complete, the full d=4 atom table, all three
uniform tail families, the tie, and the deg-2 message half of reduce-to-uniform. Open: the d=4 cell wiring
(mechanical), deg-3/deg-4 message halves (case-work), and the **counts→single-degree exchange** (the genuine research
remainder) + Branch list lift. Do NOT claim the ceiling closed until `IsSubaction ρwit` builds sorry-free end-to-end.
This ceiling line is distinct from the finite-n tree→hub Hnorm/Hdom work.
