# Lean tree→hub Closure — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **HANDOFF NOTE:** This plan is handed off to the parallel session that owns the `hnorm`/tree→hub Lean lane. That session has deeper live context on the `R47R7*` modules and Mathlib idioms than a from-scratch reader; where this plan gives a proof *strategy* rather than exact tactics, the lane owner fills the tactic detail. The task boundaries, theorem statements, reuse map, and go/no-go gates are the load-bearing content.

**Goal:** Make the BG tree→hub layer rest on exactly one clean `ObligationA` hypothesis (Stage 1, achievable), then attempt to discharge `ObligationA` itself with the cavity / invariant-price-interval machinery (Stage 2, gated research).

**Architecture:** New `R3Cert/R47R7{Lift,Finder,Closure}.lean` modules (self-building via the `R3Cert.+` glob, no edits to shared files) prove the existence finder `StraightProgress_sized` conditional on a finder-step `ObligationA` predicate, feeding the existing `tree_to_hub_sized`. Stage 2 first isolates the exact finder-move inequality in a Python harness, probes whether the cavity recursion reduces it to a gated rational inequality, then either formalizes it in Lean or ships a sharpened-obstruction doc.

**Tech Stack:** Lean 4 / Mathlib v4.32.0 (`proof/formalization/`, lake); Python 3.12 + `fractions`/`networkx` for the empirical harness (`proof/verification/`); CI-only Lean builds (warm Mathlib olean + incremental `.lake/build` cache; no local `lake build` — SoC-watchdog risk on the live-trading Mac).

**Spec:** `proof/docs/design/LEAN_TREE_TO_HUB_CLOSURE_20260902.md`

## Global Constraints

- **No local Lean builds.** Iterate via CI only (warm cache ~5–10 min/module) or the gated remote-build capability. Never run `lake build` on the local machine — it crashes the SoC watchdog and this Mac runs the live trading daemons.
- **New files only.** No edits to the parallel session's `R47R7*` files (avoids merge-conflict surface); the `R3Cert.+` glob compiles new modules automatically.
- **Axiom-clean.** Every capstone must pass the `AxiomGuard` (`[propext, Classical.choice, Quot.sound]` only) and the repo sorry-scan. No `sorry`, `admit`, `native_decide` in shipped theorems.
- **`conjecture1_proved = False`** stays False unless Stage 2c actually closes Obligation A with green CI. Stage 1 landing does NOT claim BG closed — only that the layer rests on one explicit hypothesis.
- **Anti-overclaim (Stage 2 Python):** every numerical "reduction" gets a held-out / larger-`n` stress test before belief; re-anchor `Aobj` against `kelmans_mixed_load.pi_literal` / brute-force permanent. The campaign has caught ~13 overclaims of the "verified-numerically" shape — model faithfully before trusting.

---

## Reuse map (existing, do NOT rebuild)

| Symbol | File | Role for this plan |
|---|---|---|
| `UTree`, `node`, `usize`, `usizeList`, `udeg` | `R3Cert/R47Tree.lean` | tree datatype + size |
| `Aobj t := Ztot (dtRealize t)` | `R3Cert/R47Tree.lean` | the objective (`= per(L)/∏deg`, via `pi_utree`) |
| `Zopen`,`Ztot`,`Popen`,`Matched`, `tree_cavity_recursion` | `R3Cert/CavityTree.lean` | cavity recursion `Zopen/Ztot = 1/(1+Σ w·h)` |
| `node_Ztot_child_mono` | `R3Cert/R47R6SpineMono.lean` | `Ztot` monotone in one child's `Ztot`/`Zopen` (the lifting engine) |
| `Aobj_balance_le_deep` | `R3Cert/R47R6SpineMono.lean` | proven backbone single-child lemma (Stage 2c template) |
| `isLeaf`,`isCherry`,`isArm`,`isPiece`,`strDefect`,`npCount`,`npDefectSum` | `R3Cert/R47R7Straighten.lean` | piece recognizers + defect measure |
| `pushInto`,`pushIntoList`,`usize_pushInto`,`isPiece_pushInto` | `R3Cert/R47R7PushInto.lean` | the relocation move |
| `strDefect_deephub_local`,`usize_deephub_local`,`deephub_local_straightStep` | `R3Cert/R47R7PushInto.lean` | the step (defect drops 1, size preserved, `StraightStep_sized` modulo `hAobj`) |
| `StraightStep_sized`,`StraightProgress_sized`,`tree_to_hub_sized` | `R3Cert/R47R7Sized.lean` | `StraightStep_sized t t' := usize t = usize t' ∧ Aobj t ≤ Aobj t' ∧ strDefect t' < strDefect t` |
| `phase0_straightprogress_sized.py`, `kelmans_mixed_load.pi_literal` | `proof/verification/` | exact `Aobj` harness + Phase-0 finder witness |

---

## Task 0: fast-lean-check CI workflow (accelerator)

**Files:**
- Create: `.github/workflows/fast-lean-check.yml`

**Interfaces:**
- Produces: a CI job that, on push to `bg/lean-tree-to-hub`, restores the warm Mathlib + `.lake/build` caches and runs `lake build R3Cert.R47R7Lift R3Cert.R47R7Finder R3Cert.R47R7Closure` only (skips axiom-guard/sorry-scan/full-suite). ~5 min feedback.

- [ ] **Step 1: Write the workflow** — copy the `elan` install + `lake exe cache get` + incremental-cache-restore steps from `.github/workflows/proof-lean.yml` (steps "Cache elan toolchain", "Install elan", "Fetch Mathlib olean cache", "Cache Lean project build"), then a single build step:

```yaml
      - name: Fast build (target modules only)
        working-directory: proof/formalization
        run: lake build R3Cert.R47R7Lift R3Cert.R47R7Finder R3Cert.R47R7Closure
```
Trigger: `on: push: branches: [bg/lean-tree-to-hub]`, `paths: ['proof/formalization/R3Cert/R47R7Lift.lean','proof/formalization/R3Cert/R47R7Finder.lean','proof/formalization/R3Cert/R47R7Closure.lean']`. `timeout-minutes: 30`.

- [ ] **Step 2: Commit + push; confirm it runs green on an empty target** (create the three files as `import Mathlib` stubs first so the build target resolves).

```bash
git add .github/workflows/fast-lean-check.yml proof/formalization/R3Cert/R47R7Lift.lean proof/formalization/R3Cert/R47R7Finder.lean proof/formalization/R3Cert/R47R7Closure.lean
git commit -m "ci(bg): fast-lean-check for tree->hub target modules"
```

---

## Task 1: `R47R7Lift.lean` — context lifting (`strDefect`/`usize`/`Aobj` congruence)

**Files:**
- Create: `proof/formalization/R3Cert/R47R7Lift.lean`

**Interfaces:**
- Consumes: `node_Ztot_child_mono` (R47R6SpineMono), `strDefect`/`usize` (R47R7Straighten/R47Tree).
- Produces:
  - `theorem strDefect_lift (pre post : List UTree) (s s' : UTree) (h : strDefect s' < strDefect s) (hpc : isPiece s = false) (hpc' : isPiece s' = false) : strDefect (node (pre ++ s' :: post)) < strDefect (node (pre ++ s :: post))` — off-spine defect strictly lifts.
  - `theorem usize_lift (pre post : List UTree) (s s' : UTree) (h : usize s = usize s') : usize (node (pre ++ s :: post)) = usize (node (pre ++ s' :: post))`.
  - `theorem Aobj_lift (pre post : List UTree) (s s' : UTree) (h : Aobj s ≤ Aobj s') (hdeg : udeg s = udeg s') : Aobj (node (pre ++ s :: post)) ≤ Aobj (node (pre ++ s' :: post))` — the monotone lift (the load-bearing one).

- [ ] **Step 1: Stub the three theorem statements with `sorry`; push; confirm the *types* compile** (fast-lean-check green with sorry — verifies the signatures are well-formed against the real defs). Expected: builds, sorry-scan would flag (that's fine pre-merge; keep off `main`).

- [ ] **Step 2: Prove `usize_lift`** — `simp only [usize_node, usizeList_append, usizeList_cons, h]`. Push; fast-lean-check green.

- [ ] **Step 3: Prove `strDefect_lift`** — unfold `strDefect`, `npCount_append`/`npDefectSum_append` (add these list lemmas if absent), use `npCount` unchanged (both `s`,`s'` non-piece) and `npDefectSum` strictly drops on the `s→s'` slot; `omega`. Push; green.

- [ ] **Step 4: Prove `Aobj_lift`** — `Aobj = Ztot ∘ dtRealize`; `dtRealize (node (pre++s::post))` places `s` at child-weight `1/(d·udeg s)`; apply `node_Ztot_child_mono` with `hzt : Ztot (dtSub s) ≤ Ztot (dtSub s')`, `hzo` similarly, `hu : udeg s = udeg s'`. Requires exposing `Aobj s ≤ Aobj s'` as `Ztot (dtSub s) ≤ Ztot (dtSub s')` (they coincide up to the sub-realization; state a bridging lemma `Aobj_eq_Ztot_dtSub` if needed). Push; green.

- [ ] **Step 5: Commit.**
```bash
git add proof/formalization/R3Cert/R47R7Lift.lean
git commit -m "feat(bg-lean): R47R7Lift -- strDefect/usize/Aobj context-lifting congruence"
```

**NOTE (lane owner):** `node_Ztot_child_mono` needs BOTH `Ztot` and `Zopen` monotone in the child. `Aobj_lift`'s `hdeg : udeg s = udeg s'` holds for the finder's move because `pushInto A B` and `A` differ only deep inside `A` (the *root* of the sub `s` keeps its degree). Confirm this is true for the finder's `s = A`, `s' = pushInto A B` — the deep-hub move does NOT change `A`'s root degree (B goes to a *descendant* hub). This is the key that makes lifting applicable where the *whole-tree* root-degree change does not.

---

## Task 2: `R47R7Finder.lean` — the existence finder (conditional on `ObligationA`)

**Files:**
- Create: `proof/formalization/R3Cert/R47R7Finder.lean`

**Interfaces:**
- Consumes: `deephub_local_straightStep`, `strDefect_deephub_local`, `usize_deephub_local` (R47R7PushInto); `R47R7Lift`; `StraightStep_sized`/`StraightProgress_sized` (R47R7Sized).
- Produces:
  - `def finderStep : (t : UTree) → strDefect t ≠ 0 → UTree` — constructs the witness.
  - `def ObligationA : Prop := ∀ (t : UTree) (h : strDefect t ≠ 0), Aobj t ≤ Aobj (finderStep t h)`.
  - `theorem finderStep_defect_lt (t) (h) : strDefect (finderStep t h) < strDefect t`.
  - `theorem finderStep_usize (t) (h) : usize t = usize (finderStep t h)`.
  - `theorem straightProgress_of_obligationA (hOA : ObligationA) : StraightProgress_sized`.

- [ ] **Step 1 (PREREQUISITE — 1a-prep, Python, no Lean): confirm reroot-free finder suffices.** In `proof/verification/`, exhaustively over `n ≤ 12` non-backbone rootings, check that a **deepest-defect-node de-branch** (choose deepest node with `npCount ≥ 2`, spine-`A` = a defect-0 non-piece child, `B` = another non-piece child, apply `pushInto A B` locally) always yields `strDefect` drop 1 AND `Aobj` non-decrease WITHOUT a reroot. If yes → `finderStep` needs no reroot (Obligation B not required here). If some tree needs a reroot → `ObligationA`/`finderStep` must incorporate it (add an `ObligationB` root-invariance hypothesis). RECORD the verdict in the module docstring. Expected (from Phase-0 histogram): reroot-free suffices for genuine cases; reroot-only ties are for already-backbone-reachable graphs the recursion handles by descending.

- [ ] **Step 2: Define `finderStep`** — well-founded recursion selecting the deepest defect node + (A,B) decomposition. Stub `finderStep_defect_lt`/`_usize`/`straightProgress_of_obligationA` with `sorry`. Push; confirm types compile.

- [ ] **Step 3: Prove `finderStep_defect_lt` and `finderStep_usize`** — from `strDefect_deephub_local` (drop exactly 1) + `usize_deephub_local`, lifted by `R47R7Lift` (`strDefect_lift`/`usize_lift`) through the context from the root to the chosen deep node. Push; green.

- [ ] **Step 4: Prove `straightProgress_of_obligationA`** — `intro t h; refine ⟨finderStep t h, ?_, ?_, ?_⟩`: usize half = `finderStep_usize`; Aobj half = `hOA t h`; defect half = `finderStep_defect_lt`. Push; green.

- [ ] **Step 5: Commit.**
```bash
git add proof/formalization/R3Cert/R47R7Finder.lean
git commit -m "feat(bg-lean): R47R7Finder -- existence finder, StraightProgress_sized given ObligationA"
```

**NOTE (lane owner):** the well-founded recursion for `finderStep` and the "deepest defect node with `npCount ≥ 2` exists when `strDefect t ≠ 0`" structural lemma are the two hard pieces. The existence: `strDefect t ≠ 0` ⟹ some node has `npCount ≥ 2` OR a non-piece child with `strDefect > 0`; descend to a deepest such ⟹ `npCount ≥ 2` with all non-piece children defect-0. This mirrors the handoff's "existence finder" note. Prove as `exists_deep_debranch_site`.

---

## Task 3: `R47R7Closure.lean` — the capstone

**Files:**
- Create: `proof/formalization/R3Cert/R47R7Closure.lean`

**Interfaces:**
- Consumes: `straightProgress_of_obligationA` (Task 2), `tree_to_hub_sized` (R47R7Sized), `ObligationA`.
- Produces: `theorem tree_to_hub_sized_of_obligationA (hOA : ObligationA) : <the tree_to_hub_sized conclusion type>`.

- [ ] **Step 1: State + prove** — `theorem tree_to_hub_sized_of_obligationA (hOA : ObligationA) := tree_to_hub_sized (straightProgress_of_obligationA hOA)`. Copy the exact conclusion type from `R47R7Sized.tree_to_hub_sized`. Push; fast-lean-check green.

- [ ] **Step 2: Axiom check** — add the capstone to `AxiomGuard.lean`'s guarded list (this is a shared-file edit — coordinate with lane owner, or add a local `#print axioms tree_to_hub_sized_of_obligationA` and confirm `[propext, Classical.choice, Quot.sound]` in the full `proof-lean` run).

- [ ] **Step 3: Full `proof-lean` gate** — push and let the full `proof-lean.yml` run (not just fast-check): confirms no-sorry, axiom-clean, orphan-module check passes. This is the Stage-1 merge gate.

- [ ] **Step 4: Commit + open PR** (Stage 1 deliverable).
```bash
git add proof/formalization/R3Cert/R47R7Closure.lean
git commit -m "feat(bg-lean): R47R7Closure -- tree_to_hub_sized rests on single ObligationA hypothesis"
```
PR body: "Stage 1 — the tree→hub layer now rests on exactly one clean `ObligationA` hypothesis; finder + lifting proven sorry-free/axiom-clean. `conjecture1_proved = False` (Obligation A still open)."

---

## Task 4 (Stage 2a): faithful model + isolate the exact finder-move inequality — Python

**Files:**
- Create: `proof/verification/obligationA_faithful_model.py`

- [ ] **Step 1: Port `finderStep` exactly** — replicate the Task-2 `finderStep` decomposition (deepest defect node, spine-`A`, off-spine-`B`, `pushInto`) in Python, `Aobj` via exact `Fraction` matching-sum re-anchored to `kelmans_mixed_load.pi_literal`.

- [ ] **Step 2: Reproduce Phase-0's 0-failures ON THE FINDER MOVE** — exhaustive `n ≤ 12`: for every non-backbone rooting, `Aobj(finderStep(t)) ≥ Aobj(t)`. MUST be 0 violations (unlike the naive fixed-decomposition, which had 285). If violations appear, the `finderStep` decomposition is wrong — fix it before any Lean (this is the model-faithfulness gate).

- [ ] **Step 3: Extract the exact local inequality** — for the finder's chosen `(A,B,rest)`, print the exact `Aobj(node(A::B::rest))` vs `Aobj(node(pushInto A B::rest))` as `Fraction`s, and the structural invariants (root degree before/after, `A`'s spine length, `B`'s shape). Tabulate the *tightest* cases. Deliverable: `OBLIGATION_A_TARGET_20260902.md` — the precise inequality Lean must prove.

- [ ] **Step 4: Commit.**

---

## Task 5 (Stage 2b): cavity / price-interval discharge probe — Python — **GO/NO-GO GATE**

**Files:**
- Create: `proof/verification/obligationA_cavity_probe.py`

- [ ] **Step 1: Decompose the Aobj change via the cavity recursion** — express `Aobj(after)/Aobj(before)` through `tree_cavity_recursion` (`Zopen/Ztot = 1/(1+Σ w·h)`) at the relocation site; isolate the root-degree-change term (root drops from `|rest|+2` to `|rest|+1`).

- [ ] **Step 2: Test the reduction to a gated per-child inequality** — check whether the change reduces to a single-child-lemma form `V_μ`-style inequality on the invariant price interval `I=[456/3703,3/7]` (the Telperion certs: `BroomVsCherryCertificate`, `LeafExchangeCertificate`, `ExtremalityPriceMapCertificate`, `NearBroomUnimodalityCertificate`). Concretely: does the root-degree-change term match the price-map `μ_d=3/(4d−1)` flow, and does the residual reduce to a `norm_num`-checkable rational inequality?

- [ ] **Step 3: GO/NO-GO.**
  - **GO** (clean reduction, stress-tested on held-out `n=13,14`): write `OBLIGATION_A_CAVITY_REDUCTION_20260902.md` (the reduction + the exact rational atoms) → proceed to Task 6.
  - **NO-GO** (no clean reduction): write `LEAN_OBLIGATION_A_OBSTRUCTION_20260902.md` — exactly where the cavity machinery stalls, the tightest partial (backbone case = `Aobj_balance_le_deep`), and the honest verdict. **STOP** — Stage 1 stands as the banked result. Do NOT force Task 6.

- [ ] **Step 4: Commit the verdict doc.**

---

## Task 6 (Stage 2c, ONLY if Task 5 = GO): formalize `ObligationA` in Lean

**Files:**
- Create: `proof/formalization/R3Cert/R47R7ObligationA.lean`

- [ ] **Step 1: Emit the rational atoms** — via the Telperion enclosure/`norm_num` pattern (like `MdStepCertificate`), generate the `norm_num` lemmas for the reduced inequality; freeze + `--check`.

- [ ] **Step 2: Prove `theorem obligationA : ObligationA`** — follow the `Aobj_balance_le_deep` / `node_Ztot_child_mono` proof shape: reduce to the child cavity inequality, discharge via the emitted `norm_num` atoms + monotonicity. Stub with `sorry`, push, iterate on fast-lean-check.

- [ ] **Step 3: Discharge the capstone** — `theorem tree_to_hub_sized_unconditional := tree_to_hub_sized_of_obligationA obligationA`. Full `proof-lean` gate: no-sorry, axiom-clean.

- [ ] **Step 4: Flip the ledger** — `Telperion bg_upper_bound.py` step for this layer → GATED; update `conjecture1_proved` reasoning honestly (this layer closed; the OTHER BG layers still gate the full conjecture — do NOT set `conjecture1_proved=True` unless the ENTIRE chain is closed).

- [ ] **Step 5: Commit + PR.**

---

## Self-review notes (author)

- **Spec coverage:** Stage 1 (Lift/Finder/Closure) = Tasks 1–3; Stage 2a = Task 4; 2b = Task 5 (gate); 2c = Task 6. Task 0 = the accelerator. All spec sections mapped.
- **Reroot/Obligation B:** handled by Task 2 Step 1 (empirical prereq) — if reroot-free suffices, `ObligationA` is self-contained; else `finderStep` takes an `ObligationB` hypothesis (documented, not silently dropped).
- **The false-universal trap:** `ObligationA` is defined via `finderStep`, NOT `∀ valid A,B` (which is false — 285/1320). Task 4 Step 2 is the model-faithfulness gate that catches any regression to the false form.
- **Honest terminal:** Task 5 can legitimately end at NO-GO with an obstruction doc; the plan does not pretend Obligation A must close. `conjecture1_proved = False` unless Task 6 fully lands.
