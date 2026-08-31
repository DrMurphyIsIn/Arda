# Hnorm closure: the tree → hub-state reduction (2026-08-31)

## Where this sits

`conjecture1_of_layers` (and `..._fixedN`) reduce Brualdi–Goldwasser to two open Props,
`Hnorm` and `Hdom`. `Hnorm` asserts every tree is `Aobj`-dominated by some **Balanced+Capped
hub-backbone**:

```
Hnorm : ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧ Aobj t ≤ Aobj (backboneU s)
```

Every balancing/rate lemma built to date (`single_hub_Hnorm`, `Aobj_balance_le_deep`,
`armRate11_le_one`, …) operates on objects **already** of the form `backboneU s`. The missing
bottom of the stack is the reduction from an **arbitrary `UTree`** to that form. This doc
records the closure plan and the schema that isolates it.

## What landed (`R3Cert/R47R7TreeToHub.lean`, sorry-free, axiom-clean)

A reusable well-founded **reduction schema**, lifting one structural level up the exact pattern
that closed the single-hub arm-balancing case (`single_hub_reaches_balanced`):

- `IsHubForm t := ∃ s, t = backboneU s` — the normal form (stuck points of the rewrite).
- `treeToHub_of_rewrite (R) (mu) (hmono) (hmeas) (hprog)` — given an `Aobj`-non-decreasing
  rewrite `R` with a strictly-decreasing `ℕ`-measure `mu` whose only stuck points are hub-form
  trees, proves `∀ t, ∃ s, Aobj t ≤ Aobj (backboneU s)`. Fuel-bounded `induction n` on `mu`
  (robust vs WF-eliminator naming), `Aobj`-monotonicity accumulated by `le_trans`.
- `tree_to_hub_of_obligations` — the same, phrased over the three named Props
  `RewriteMonotone` / `RewriteDecreases` / `RewriteProgresses`.

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]`. `conjecture1_proved = False`.

This converts the historically "no theorem exists" gap (iii) into **three typed obligations**
for a concrete rewrite `R`.

### Pass 1 landed (`R3Cert/R47R7ChildMono.lean`, sorry-free, axiom-clean)

The `RewriteMonotone` obligation is now discharged generically:

- `Aobj_tail_child_replace_le` / `Aobj_child_replace_le` — replacing any root child by a
  degree-preserving subtree of not-smaller `(Ztot, Zopen)` never decreases `Aobj` (from
  `node_Ztot_child_mono` + `Aobj_node_perm`).
- `ChildReplace` — the child-replacement rewrite relation; every concrete Kelmans/leg-cherry
  move is a sub-relation of it.
- `childReplace_monotone : RewriteMonotone ChildReplace` — **obligation (R-mono) closed** for the
  generator. `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

So the concrete Kelmans rewrite inherits `Aobj`-monotonicity for free; only `RewriteDecreases`
and `RewriteProgresses` remain, plus exhibiting each Kelmans move's local `(Ztot, Zopen)` gain.

## The concrete rewrite `R` — a union of Aobj-monotone moves, each with a paper certificate

The key realization from `proof/verification/`: the closure is not one move but a **union of
Aobj-non-decreasing relations**, all already certified symbolically. Because equality implies
`≤`, the exact-preserving plainification move and the strictly-monotone Kelmans moves both
satisfy `RewriteMonotone`.

### The Aobj-monotone workhorse (verified during Pass 1)

The single reusable generator of `RewriteMonotone` is **child-replacement monotonicity**
(`R47R6SpineMono.node_Ztot_child_mono` / `node_Zopen_child_mono`): the cavity recursion
`Ztot(node) = C1·Ztot(dtSub child) + C2·Zopen(dtSub child)` is **linear with nonnegative
coefficients** in each child, so replacing a subtree `T` by `T'` with
`Ztot(dtSub T) ≤ Ztot(dtSub T')`, `Zopen(dtSub T) ≤ Zopen(dtSub T')` at **equal degree**
`udeg T = udeg T'` never decreases `Aobj`. Every concrete monotone move below reduces to
exhibiting that local `(Ztot, Zopen)` gain. `R47R7ChildMono.lean` (Pass 1) packages this as the
generator `Aobj_tail_child_replace_le`.

| Move | Relation | Aobj effect | Certificate | Status |
|---|---|---|---|---|
| **Kelmans topped-up merge** | hubward-merge a de-loadable hub into its neighbour, debris-free, lands as a canonical load-5 arm | **non-decreasing** at env cap `3/16` | `kelmans_unified_merge.py` | **PROVEN**, 36/36 cells at cap `3/16` |
| **Vertex-budget domination** | de-loaded multi-hub ⟶ single-hub template of the SAME `n` | **non-decreasing** (global, not local) | `kelmans_vertex_budget.py` | **two-hub PROVEN all sizes**; m-hub = named open lemma (margins grow in `m`) |
| **(L)/(B) small-structure normalization** | reshape sub-cap residual (arms load ≤ 3, small/low-load hubs) | non-decreasing | `kelmans_env_rules.py` boundary + LB layer | design/partial |

**CORRECTION vs the first draft of this doc — plainification is NOT a raw-`Aobj` move.**
`plainification_theorem.py`'s MOVE B (`(c,K) == (c-1, K+[ARM])`) is an equality of **cavity and
`logPhi`** (the rate-normalized potential Φ), not of raw `Aobj = Ztot∘dtRealize`. At the raw
`UTree` level a hub-cherry and the paper's `ARM = (0,[(0,[])])` are the *same* subtree
`cherryU = node[node[]]` (both `usize = 2`), so MOVE B is a `c`-block/`K`-list reinterpretation,
trivial on trees; and trading a hub-cherry for a genuine arm (`armU 1`, `usize = 3`) changes `n`
and does **not** preserve `Aobj` (checked against `singleHub_Aobj_formula`: the `armU 1` value
`7/4` leaves a residual `7/6` factor). Plainification therefore belongs to the Φ-model layer, not
the tree→hub `Aobj` rewrite. The genuine generators are the child-monotone Kelmans moves above.

Termination measure `mu` (for `RewriteDecreases`): a lexicographic tree measure that every move
lowers — Kelmans merge reduces hub-count; vertex-budget reduces hub-count; small-structure moves
reduce the non-cherry-leg count. Budget accounting in `kelmans_vertex_budget.py`.

Progress (`RewriteProgresses`): a non-`IsHubForm` tree always admits a plainification or Kelmans
move (structural); the stuck de-loaded multi-hub configs are themselves `IsHubForm` (multi-hub
backbones), so they satisfy the target already and their single-hub sharpening is the
vertex-budget step feeding the Balanced/Capped refinement.

## Scope correction vs the earlier plan

The tree → hub reduction target is `∃ s, Aobj t ≤ Aobj (backboneU s)` for **some** (possibly
multi-hub) backbone. The subsequent sharpening — multi-hub ⟶ single Balanced+Capped hub — is the
vertex-budget + arm-balance + cap + de-load work, which upgrades the witnessed `s` and completes
`Hnorm`. The vertex-budget domination is thus **also** an `Aobj`-monotone relation and can be
folded into the same schema by strengthening the normal-form predicate from `IsHubForm` (any
backbone) to "single Balanced+Capped hub".

## Sequenced closure work (each = a Lean file discharging one obligation piece)

1. **Plainification in Lean** (moderate). Port MOVE B: define the cherry→arm rewrite on `UTree`,
   prove `Aobj (plainify-step t) = Aobj t` from the exact cavity/logPhi identity. The `armU`/
   `cherryU` closed forms already exist (`R47HubState.lean`). Reduces general trees to plain.
2. **Kelmans topped-up merge in Lean** (hard — the historical R4/Kelmans node). Port the 36-cell
   cap-`3/16` certificate the way the g1-floors 3084-cell family was ported (bilinear-corner
   nonneg per cell). Yields `RewriteMonotone` for the merge move.
3. **Termination measure + progress** (mechanical once 1–2 exist). Define `mu`, prove each move
   lowers it and that non-normal trees admit a move.
4. **Assemble** via `treeToHub_of_rewrite` → unconditional `tree_to_hub`.
5. **Multi-hub vertex-budget**: port the two-hub theorem (proven, symbolic); the **m-hub general
   lemma remains genuinely open** (per-de-loaded-hub ~9% parking-cost argument; only evidence so
   far). This is the honest hard remainder shared with Hdom/R2.

## Honest remaining hardness

- The **Kelmans merge cert port** (step 2) is a large but bounded finite-cell formalization —
  the math is proven on paper.
- The **m-hub vertex-budget general lemma** (step 5) is **not** proven on paper (two-hub is;
  m-hub has growing-margin evidence only). This is the same multi-hub extremality (R2) obstruction
  that also blocks Hdom, and is the single deepest open node in the whole reduction.
- Everything else (plainification, measure, progress, assembly) is porting + mechanical.

This does not touch Hdom's sharp master inequality (the loose `(6/5)·rhoB^n` vs exact
`(26/23)/rhoB` gap), which remains a separate front.
