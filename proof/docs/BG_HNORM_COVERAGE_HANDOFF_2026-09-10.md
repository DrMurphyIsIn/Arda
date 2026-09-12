# BG conjecture1 — Hnorm coverage front: HANDOFF (2026-09-10)

**Branch:** `bg/multihub-hnorm` (GitHub `DrMurphyIsIn/Arda`).  **Worktree:** `~/repos/Arda-wt-armrate`.
**Build:** `cd proof/formalization && lake build R3Cert.<Module>`.  **Axiom check:** scratch file with
`#print axioms <lemma>` via `lake env lean` — must show only `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`).  **`conjecture1_proved = False`** (do NOT flip until a full sorry-free chain exists).

Predecessor: PR #435 (MERGED to `main`, commit `20c0609`) closed the entire `Hdom` side.  This branch has
continued past that with the `Hnorm` coverage work below (all pushed, kernel-clean).

---

## 1. Where the whole proof stands

The size-correct capstone `conjecture1_of_layers_fixedN` (`R47TopCapstoneFixedN.lean:48`) proves
`∀ t, Aobj t ≤ Aobj (tie (usize t))` from a per-size tie plus two obligations:
- **`Hnorm`** (tree→hub): every tree is dominated by a Balanced+Capped hub-state of its own size.
- **`Hdom`** (hub→tie): every hub-state is dominated by the tie at its size.

Status of each:

| layer | status |
|---|---|
| **`Hdom`** — single-hub, two-hub, m≥3 multi-hub, AND the tie-definition | **CLOSED** (kernel-clean). `pairCollapse6` (m≥3) is a theorem; `tieArgmax` (finite-argmax single hub) discharges the tie layer; `conjecture1_of_Hnorm` (`R47TieArgmax.lean:119`) gives Conjecture 1 conditional on **`Hnorm` alone**. |
| **`Hnorm`** | **OPEN**, and has TWO layers (correction 2026-09-11): (i) size-preserving tree→general-backbone coverage — reduced kernel-clean to `hcore`/whole-hub (§3); (ii) the Balanced+Capped size-preserving NORMALIZATION (general backbone → arms∈{4,5}, ≥5 arms/hub) — a SEPARATE open layer NOT fed by `tree_to_hub_sized`. `conjecture1_of_layers_fixedN` needs BOTH; `hnorm_of_coverR_coverage` supplies only (i)'s usize-shape. So Conjecture 1 rests on hcore AND the normalization layer, not hcore alone. |

So Conjecture 1 rests on `Hnorm`; `Hnorm` = layer (i) coverage (reduced to `hcore`) + layer (ii) the Balanced+Capped size-preserving normalization (separate open). See the correction in `proof/verification/COVER_RELATION_STATUS.md`.

---

## 2. What this session delivered (this branch, since #435)

All kernel-clean, wired into `AxiomGuard.lean` + `.github/workflows/proof-lean.yml`:

- **`R47AdjLeafStruct.lean`** — the structural core of crux (a): `strDefect_adjLeaf_nB0` (nB=0
  defect-neutrality) ⇒ a defect-reducing adjacent leaf move forces `nB ≥ 1`.
- **`R47AdjLeafGains.lean`** — the Aobj half (the substantial part): closed-form cavity stats of
  `par_v = node(flpLeaf::Bv)` / `par_v' = node(flpStem::Bv)`; the real-var inequalities `adj_G1_real`
  (`nlinarith`) and `adj_G2_real` (positivity); the tree→real equalities; the base gains `adjLeaf_G1`/`G2`;
  and `adjLeaf_Aobj_le` — the Aobj clause lifted through any context via `Aobj_child_replace_of_gains`.
  Key facts: the move **LIFTS** (both cavity gains hold for `nB≥1`), so no re-rooting is needed here; the
  cancellation `qContrib(par_v) = 1/(nB+3+QB)` is what makes the arithmetic close.
- **`R47AdjLeafStep.lean`** — **`adjLeaf_straightStep`**: the full `StraightStep_sized` for the adjacent
  leaf move (usize= via `usize_child_replace`; Aobj≤ via `adjLeaf_Aobj_le`; strDefect< via
  `strDefect_child_replace_lt`).  Firing condition: `Bv` a NONEMPTY cherry list (so `par_v'` is an arm/piece)
  and a non-piece sibling in `Other` (`1 ≤ npCount Other`).
- **`R47RootShift.lean`** — `Aobj_rootShift` (single-edge root-shift is Aobj-INVARIANT, proven directly in
  the cavity model as a real identity — NO graph-iso); `RerootStep1`/`RerootRel` (ReflTransGen, Aobj/usize
  invariant); `CompRerootStep` (composite reroot to any lower-defect rooting) + its `StraightStep`.
- **`R47CoverRelation.lean`** — `AdjLeafStep`, `CoverR := FlpStepAt ∨ AdjLeafStep ∨ CompRerootStep`,
  `CoverR.straightStep`, `hnorm_of_coverR_coverage`; `RerootMinimal`; `coverR_coverage_of_minimalCore`
  (reroot half discharged, no path construction); and **`hnorm_of_wholehub`** — the size-preserving Hnorm
  reduces to ONE explicit hypothesis: a `CoverR` move for reroot-minimal defective trees with NO `FlpStepAt`
  move (the whole-hub / adaptive de-branch residual).
- **`R47AlignedMinSize.lean`** — `no_capped_state_of_size_lt_46`: no Balanced+Capped hub-state has size
  `0 < n < 46`, so the capstone `Hnorm` is UNSATISFIABLE there (aligned-n scoping, kernel-formalized).

Plus the research map (in `proof/verification/`): the monomer-dimer reformulation, the mechanistic G1
analysis, the coverage measurement, and the CORRECTIONS (`COVER_RELATION_STATUS.md`): Hnorm has TWO open
layers (whole-hub coverage + Balanced+Capped normalization) and is aligned-n scoped; the whole-hub
straightening is the ADAPTIVE de-branch (Case-B / hub-attach / uniform-averaging all ruled out — no fixed or
local certificate; it is the BG open core, Pant 2026).

---

## 3. The frontier: `Hnorm` ⟸ `CoverR` coverage

`hnorm_of_coverR_coverage` reduces `Hnorm` to ONE obligation:

    ∀ t, strDefect t ≠ 0 → ∃ t', CoverR t t'          -- CoverR = FlpStepAt ∨ AdjLeafStep

**Measured coverage** (exact Lean move conditions, rooted `StraightProgress_sized` population, n≤12, 19,099
defective trees — `proof/verification/COVER_RELATION_STATUS.md`):

| | fraction |
|---|---|
| `CoverR` fires directly | **62.7%** |
| `CoverR` OR a reroot | **99.3%** |
| residual (neither) | **0.7%** (125 trees, symmetric two-`k`-star / Case-B whole-hub) |

### Two remaining pieces (priority order)

**(A) A `RerootStep` class: 62.7% → 99.3%.  ✅ DONE (2026-09-10).**  `CompRerootStep` (composite reroot,
`RerootRel := ReflTransGen{shift-to-front ∨ child-perm}`, `Aobj`/`usize` invariant by composition) is built
and folded into `CoverR := FlpStepAt ∨ AdjLeafStep ∨ CompRerootStep` (kernel-clean; reaches 99.3%).  Only the
coverage lemma for `CoverR` and the 0.7% whole-hub residual (piece B) remain.  Original plan retained below.
A reroot to a lower-`strDefect` rooting is a valid `StraightStep_sized` (same vertices ⇒ `usize` equal;
`Aobj` is a graph invariant ⇒ equal; `strDefect` lower).

DE-RISK (2026-09-10, `_reroot_derisk` over rooted trees n<12) — two findings that PIN the design:
- The single-edge **root-shift** `node(node ds :: rest) → node(ds ++ [node rest])` (new root = the adjacent
  child) is **Aobj-INVARIANT exactly** (0/23713 violations).  So Aobj-invariance for an ARBITRARY reroot
  follows by COMPOSING single-shift invariance — no `SimpleGraph.Iso` needed if the single-shift identity is
  proved directly in the cavity model.
- BUT a single shift **cannot always lower `strDefect`** (1143 cases have the global min below `d0` yet no
  adjacent shift drops it — sideways shifts at equal defect).  So `RerootStep` must be "reroot to ANY
  lower-defect rooting" (a COMPOSITE of shifts), taken as ONE `StraightStep` (the intermediate sideways
  shifts are absorbed into the composite; only the endpoint defect must be lower).

BUILD PLAN: (i) prove the single-shift Aobj identity `Aobj(node(ds ++ [node rest])) = Aobj(node(node ds ::
rest))` in the cavity model (this IS the root-invariance seam, Obligation B — either via
`BGSCLObligationB.Aobj_root_invariant_of_iso` + the concrete iso, or a direct `rooting_identity`-based
derivation; the de-risk confirms it holds exactly); (ii) define `reroot(t, v)` as the shift-composite to
vertex `v` and lift the identity to `Aobj(reroot(t,v)) = Aobj(t)`; (iii) `RerootStep t t' := ∃ v,
t' = reroot(t,v) ∧ strDefect t' < strDefect t`, with `usize` preserved and Aobj equal ⇒
`StraightStep_sized`; (iv) `CoverR := FlpStepAt ∨ AdjLeafStep ∨ RerootStep`, re-measure (expect ~99.3%).
The single-shift Aobj identity (i) is the crux and the substantial part.

**(B) The whole-hub (Case-B) 0.7% residual.  Genuine open research.**
The 125 residual trees are the symmetric/asymmetric two-`k`-star family.  Their straightening move fails
the local `G1` lift-gain (whole-hub relocation LOWERS the acted node's `Ztot(dtSub)`), so it cannot lift
context-independently — proven mechanistically (`REALOBLB_TYPEW_B0_FINDINGS.md`).  Closing it needs a
GLOBAL argument; the foundation is the reformulation **`Aobj(T) = Σ_{matchings M} ∏_{(u,v)∈M} 1/(d_u d_v)`**
(the monomer-dimer partition function, verified exhaustively — `AOBJ_MATCHING_POLYNOMIAL_REFORMULATION.md`),
which moves the problem into Heilmann-Lieb territory (real-rootedness / interlacing / edge-deletion
recursion).  `BGSCLRealOblBSymBase.lean` already proves the isolated symmetric base is Aobj-NEUTRAL
(`(4k+2)/(k+1)` both sides).

---

## 4. Key file reference

**Lean (`proof/formalization/R3Cert/`)** — the Hnorm-coverage chain, in dependency order:
- `R47TopCapstoneFixedN.lean` — `conjecture1_of_layers_fixedN` (the capstone).
- `R47TieArgmax.lean` — `tieArgmax`, `hdom_capstone`, `conjecture1_of_Hnorm` (Hdom side closed).
- `R47R7Sized.lean` — `StraightStep_sized`, `StraightProgress_sized`, `tree_to_hub_sized`.
- `BGSCLFlpStepAt.lean` — `FlpStepAt`, `FlpStepAt.straightStep`, `straightProgress_sized_of_coverage`,
  `hnorm_of_coverage`.
- `BGSCLFlpDeepLift.lean` — `Ztot_dtSub_node_eq`, `Zopen_dtSub_node_eq`, `dtSub_gains_lift`,
  `Aobj_child_replace_of_gains` (the lift machinery).
- `BGSCLHnormPort.lean` — `usize_child_replace`, `strDefect_child_replace_lt`.
- `R47AdjLeafStruct.lean`, `R47AdjLeafGains.lean`, `R47AdjLeafStep.lean`, `R47CoverRelation.lean` — this
  session's adjacent-leaf class + cover relation.
- `BGSCLObligationB.lean` + `R47RootInvariance.lean` — root-invariance (for the reroot class).
- `BGSCLRealOblBSymBase.lean` — Case-B symmetric-star base (neutral).

**De-risk / research (`proof/verification/`):**
- `COVER_RELATION_STATUS.md` — the coverage map + the two remaining pieces (READ FIRST).
- `AOBJ_MATCHING_POLYNOMIAL_REFORMULATION.md` — the monomer-dimer identity + crux(a) resolution + the
  Heilmann-Lieb approach for the residual.
- `REALOBLB_TYPEW_B0_FINDINGS.md` — the mechanistic G1-failure analysis + the sharp open lemma.
- `REALOBLA_FLP_B0_FINDINGS.md` — the sibling/distant/whole-hub coverage de-risk.
- `realobla_flp_derisk.py` — the exact-rational coverage harness.
- Engine: `telperion/scratch/a3_derisk.py` (`Aobj_node` exact, anchored vs brute permanent).

---

## 5. How to continue (concrete)

1. **Build the `RerootStep` class** (piece A) — the biggest single coverage jump (→99.3%).  Steps:
   define reroot on `UTree`; for a defective `t`, select a lower-`strDefect` rooting; build the
   `SimpleGraph.Iso` between the two realized addresses; apply `Aobj_root_invariant_of_iso` for the Aobj=
   clause; package `RerootStep.straightStep`; add to `CoverR`; re-measure coverage.  De-risk the
   defect-drop selection in Python first (over rooted trees) to confirm a deterministic rule.
2. **Prove `CoverR` coverage for the 99.3%** — i.e. `∀ t, strDefect t ≠ 0 → (FlpStepAt ∨ AdjLeafStep ∨
   RerootStep) fires`.  This is a structural induction on the tree / on `strDefect`; the residual is (B).
3. **Attack the whole-hub residual** (piece B) via the monomer-dimer / Heilmann-Lieb route.  The open lemma:
   the symmetric two-`k`-star straightening move is Aobj-nondecreasing in context — needs a global matching-
   partition inequality, not a local cavity cert.

**Discipline (non-negotiable, this program's edge):** verify every target numerically in exact
`fractions.Fraction` BEFORE writing Lean (this session it caught PairCollapse-v1, the unconditional distant
move, the clean degeq cert, and pinned the exact adjacent firing condition).  Never commit a `sorry`/broken
file.  Every new `R3Cert/*.lean` → `AxiomGuard.lean` + `proof-lean.yml` leaf list.  Never overclaim closure.
