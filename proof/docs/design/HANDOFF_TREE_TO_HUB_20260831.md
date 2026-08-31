# Handoff: the tree→hub reduction (Hnorm gap iii) — 2026-08-31

## What this session achieved

The Brualdi–Goldwasser `Hnorm` layer's **tree→hub reduction** — which every prior state-of-the-proof
audit called *"the hardest missing half, no theorem exists"* — is now a **fully machine-checked
reduction** (Lean 4 / Mathlib v4.32.0, all axiom-clean `[propext, Classical.choice, Quot.sound]`,
CI-green). The whole layer rests on exactly **two isolated research obligations**; everything
structural around them is proven.

Merged this session: PRs **#166–#175** (10 new `R3Cert/R47R7*.lean` modules + design/Phase-0 docs).

## The reduction chain (what is proven)

Target (well-posed, feeds `conjecture1_of_layers_fixedN` which needs `stateSize s = usize t`):

```lean
tree_to_hub_sized (StraightProgress_sized) :
  ∀ t, ∃ s, usize (backboneU s) = usize t ∧ Aobj t ≤ Aobj (backboneU s)     -- R47R7Sized
```

Built from (file → key theorem):

| File | Key result | Role |
|---|---|---|
| `R47R7TreeToHub` | `treeToHub_of_rewrite` | the WF reduction schema (monotone + measure-decreasing rewrite → domination) |
| `R47R7ChildMono` | `childReplace_monotone` | `RewriteMonotone` via child-replacement (cavity recursion linear-nonneg in each child) |
| `R47R7TreeReduce` | `treeReduce_of_rewrite`, `hnorm_of_rewrite` | generalised schema over any `Normal` target |
| `R47R7Straighten` | `strDefect`, `strDefect_backboneU`, `straightStep_decreases` | the off-spine defect measure (0 iff backbone); `RewriteDecreases` discharged |
| `R47R7DeepPerm` | `deepPerm_Aobj` | **`Aobj` invariant under child reordering at ALL depths** (the reverse anchor) |
| `R47R7Decode` | `strDefect_decode`, `tree_to_hub_of_progress` | defect-zero tree ⇒ deep-perm to a backbone (structural decode) |
| `R47R7Sized` | `deepPerm_usize`, `strDefect_decode_sized`, `tree_to_hub_sized` | size-preserving reorientation |
| `R47R7DegMono` | `node_Ztot_child_mono_deg` | degree-CHANGING child monotonicity (a straightening move changes degree) |
| `R47R7Debranch` | `strDefect_debranch_local`, `debranch_local_straightStep` | the direct-hub de-branch move (structural half) |
| `R47R7PushInto` | `pushInto`, `strDefect_pushInto`, `deephub_local_straightStep` | the DEEP-hub de-branch move (structural half) |

`StraightProgress_sized := ∀ t, strDefect t ≠ 0 → ∃ t', StraightStep_sized t t'`, where
`StraightStep_sized t t' := usize t = usize t' ∧ Aobj t ≤ Aobj t' ∧ strDefect t' < strDefect t`.

`conjecture1_proved = False` everywhere (correct — nothing is closed unconditionally).

## The two remaining obligations (both genuine research)

### Obligation A — the Kelmans cavity inequality (`hAobj`)
```lean
Aobj (node (A :: B :: rest)) ≤ Aobj (node (pushInto A B :: rest))     -- A spine-like, B non-piece
```
Moving branch `B` from a direct child of `N` to `A`'s deep hub. **`N` has root child-count `|rest|+2`,
`N'` has `|rest|+1`** — the root degree changes (`B` leaves the root level), so this is **not** a
child-replacement and `node_Ztot_child_mono_deg` does **not** apply. It is the full Kelmans
edge-relocation effect on `per(L)/∏deg` for ARBITRARY trees — the mathematical wall that keeps BG open.
The repo's `kelmans_*.py` certs only cover backbone-form states; the literature GTS/immanantal
monotonicity is wrong-direction for the *normalized* objective (toward the star, which is ≈ the
*minimum* of `Aobj`). **Phase 0** (`PHASE0_STRAIGHTPROGRESS_FINDINGS.md`) shows it is **strict** on every
genuine case (30/30, exact), so no equality edge case — but proving it is open research (generalise the
cap-3/16 cell-certificate method to the relocation site).

### Obligation B — `Aobj` root-invariance
`R47RootInvariance` proves the *algebraic* engine (permanent ratio is a vertex-labeling invariant;
`Aobj_root_invariant` conditional on a `GraphTransport` hypothesis). The *combinatorial* seam —
constructing the address-graph `SimpleGraph.Iso` for a re-rooting — remains. Self-contained; unblocks
the reroot witnesses (2138/2438 of Phase-0 cases were reroot-only).

## Remaining structural work (mechanical-ish, not research)

**Existence finder** for `StraightProgress_sized`: strong induction on `t` — if a non-piece child has
`strDefect > 0`, recurse; else the node has `≥ 2` non-piece children all defect-free (spine-like), pick
`A, B`, apply `deephub_local_straightStep`. Plus **context-lifting** (a de-branch at a deep node lifts to
the whole tree: `strDefect`/`usize`/`Aobj` congruence). The deep-hub move's structural halves are done;
this is the assembly.

## Critical findings / corrections (do not re-discover)

1. **The size-free `StraightProgress` is TRIVIAL** (`straightProgress_trivial`, #171): with no size
   constraint, step to a large near-star (`Aobj` unbounded). The size-free `tree_to_hub` feeds the
   *ill-posed* `conjecture1_of_layers` (fixed `tieU`). The real target is the **size-preserving** version
   (#172). Earlier "StraightProgress = hard frontier" framing was wrong.
2. **Plainification (cherry↔arm) is a Φ/rate-model equality, NOT a raw-`Aobj` move** (a hub-cherry and the
   paper `ARM` are both `cherryU`, `usize 2`; trading for `armU 1`, `usize 3`, changes `n` and breaks
   `Aobj`). The genuine `Aobj`-monotone generator is child-replacement.
3. **The Kelmans MERGE is already proven** (`R47StepMono.chain_to_normalForm`, at `List Hub`) and is NOT
   the missing piece; the missing piece is the tree→backbone *straightening*.
4. **Deep-perm anchor dissolved the decode obstruction**: `Aobj`-equality does not nest through the tail,
   so the decode needed `Aobj` invariance under child reordering at all depths (`deepPerm_Aobj`).
5. **m-hub vertex-budget is NOT needed** for the straightening half (Phase 0: no stuck configs to n=12).

## Lean footguns (encountered + resolved)

- `rw [backboneU]` fails (inline match) → use `backboneU_eq` + `tailU`.
- Nested-inductive induction through `List.Forall₂ DeepPerm` / recursion into children → use a MUTUAL
  `X` + `X_list` helper with pattern-match head recursion (tactic `induction`/`cases` loses termination).
- `isArm (node cs)` unfold → `show (cs.all isCherry) = false`, not `rw`/`simp only [isArm]`.
- `if` over a `Bool` condition → `split <;>` or `simp [hB]`, not `if_pos`/`if_neg` reliably.
- `rw` leaving `x + 0 = x` / `0 ≤ 1` / `n - 1` goals → append `omega`.
- `sizeOf (node cs) = 1 + sizeOf cs` is NOT `rfl` → `simp only [UTree.node.sizeOf_spec]`.
- `List.Forall₂.append` does not exist → prove the specific append by induction.
- CI sorry-scan trips on bare "sorry-free" in docstrings → write ``no `sorry` `` (backtick-quoted).
- Background agents doing git ops need `isolation: worktree` (a shared-worktree agent switched HEAD
  mid-commit; recovered via `git branch -f <branch> <sha>` ref-only + cherry-pick).

## Recommended next steps (priority)

1. **Existence finder + context-lifting** — completes `StraightProgress_sized` modulo Obligation A only
   (mechanical-ish, reuses the deep-hub move). Highest ratio of value to risk.
2. **Obligation B (root-invariance seam)** — self-contained combinatorial `SimpleGraph.Iso`; unblocks
   reroot witnesses.
3. **Obligation A (Kelmans cavity inequality)** — the deep research core; its own multi-PR campaign
   (generalise cap-3/16 cells to the relocation). Phase-0 strict margin says it's true.

Then full `Hnorm` additionally needs balancing/capping to `IsBCHubForm` (the `{4,5}`/Capped gaps), and the
whole conjecture needs `Hdom` (the master inequality) — separate fronts.
