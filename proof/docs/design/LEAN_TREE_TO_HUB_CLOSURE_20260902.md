# Design spec: closing the Lean tree→hub layer (assembly + Obligation A attempt) — 2026-09-02

## Goal

Drive the BG upper-bound's **tree→hub reduction** (the `Hnorm` layer, PRs #166–#175, all sorry-free /
axiom-clean / CI-green) toward closure. The layer already proves `tree_to_hub_sized` *given* the hypothesis
`StraightProgress_sized`, and every structural step (`deephub_local_straightStep`, `usize`/`strDefect` halves) is
proven *modulo* one inequality — **Obligation A**, the Kelmans `Aobj` relocation. This effort:

1. **Stage 1 (achievable):** prove the existence-finder assembly, so the whole layer rests on exactly one clean
   `ObligationA` hypothesis — nothing else open.
2. **Stage 2 (research, gated):** attempt Obligation A itself using the rooted-branch cavity / invariant-price-
   interval machinery. May close it, or may terminate in a sharpened, documented obstruction.

`conjecture1_proved = False` throughout, and only flips if Stage 2c actually closes Obligation A with green CI.

## Background (what already exists — do not rebuild)

- `UTree := inductive | node : List UTree → UTree` (`R47Tree.lean`); `Aobj t := Ztot (dtRealize t)` = `per(L)/∏deg`
  (machine-checked equal via `pi_utree`); `usize`, `udeg`.
- Cavity recursion proven end-to-end: `tree_cavity_recursion` (`CavityTree.lean`): `Zopen/Ztot =
  1/(1 + Σ_child w·(Zopen/Ztot))`, `w = 1/(d·d')`. Child-monotonicity `node_Ztot_child_mono` (`R47R6SpineMono.lean`).
  A proven backbone single-child lemma `Aobj_balance_le_deep` (arm-balancing raises `Aobj`).
- Straightening scaffold (`R47R7*`): `isPiece = isArm||isCherry`, `strDefect`, `pushInto`/`pushIntoList`,
  `strDefect_deephub_local` (defect drops exactly 1), `usize_deephub_local` (size preserved),
  `deephub_local_straightStep (hAobj) : StraightStep_sized (node (A::B::rest)) (node (pushInto A B::rest))`.
- `tree_to_hub_sized (hprog : StraightProgress_sized)` (`R47R7Sized.lean`) — the reduction, done given the finder.
- `StraightProgress_sized := ∀ t, strDefect t ≠ 0 → ∃ t', StraightStep_sized t t'`; `StraightStep_sized t t' :=
  usize t = usize t' ∧ Aobj t ≤ Aobj t' ∧ strDefect t' < strDefect t`.

Phase-0 (`PHASE0_STRAIGHTPROGRESS_FINDINGS.md`): exhaustive `n ≤ 12`, **0 failures / 2438 non-backbone rootings**;
the witness always drops `strDefect` by exactly 1 (a clean Nat recursion); genuine (SPR-needed) cases raise `Aobj`
**strictly** (30/30). Correction learned this session: Obligation A is **not** "for all valid `A,B`" — a fixed
`(A=child₁,B=child₂)` choice decreases `Aobj` in 285/1320 cases — it is "for the finder's **chosen** move." Stage 1
must therefore choose the move; Stage 2 proves the inequality for that chosen family.

## Stage 1 — the structural assembly

Deliverable: `ObligationA → StraightProgress_sized`, hence `tree_to_hub_sized` conditional on a single clean
hypothesis; finder + lifting proven sorry-free / axiom-clean.

### Components (new files, self-building via the `R3Cert.+` glob — no edits to shared files)

- **`R3Cert/R47R7Lift.lean` — context lifting.** A de-branch at a deep node lifts to the whole tree: congruence of
  `strDefect`, `usize`, and (crucially) `Aobj` under `node (pre ++ [sub] ++ post)`. `strDefect`/`usize` congruence
  is structural (list induction). `Aobj` congruence reuses `node_Ztot_child_mono` (monotone in the one child's
  `Ztot`/`Zopen`), so `Aobj sub ≤ Aobj sub'` lifts to `Aobj (context sub) ≤ Aobj (context sub')`.
- **`R3Cert/R47R7Finder.lean` — the existence finder.** Define the finder's move constructively as
  `finderStep : (t : UTree) → strDefect t ≠ 0 → UTree` (locate a deepest defect-carrying node with ≥2 non-piece
  children; designate spine-like `A` — a non-piece child that is itself defect-0, which exists *because* the node
  is a deepest defect node — and relocatable `B`; the move is `pushInto A B` lifted back to `t` via `R47R7Lift`).
  Then prove
  `theorem straightProgress_of_obligationA (hOA : ObligationA) : StraightProgress_sized`
  by strong induction on `strDefect t` (well-founded on `ℕ`; `strDefect (finderStep t h) < strDefect t` by
  `strDefect_deephub_local` + lifting; the size half by `usize_deephub_local` + lifting).

  **`ObligationA` is tied to the finder's CHOSEN move, not all valid `A,B`** (the universal form is *false* — a
  fixed `(A=child₁,B=child₂)` decreases `Aobj` in 285/1320 cases). The clean predicate is exactly what each finder
  invocation needs:
  `ObligationA := ∀ (t : UTree) (h : strDefect t ≠ 0), Aobj t ≤ Aobj (finderStep t h)`.
  Discharging it reduces (via `R47R7Lift`'s `Aobj` monotone lifting) to the *local* inequality
  `Aobj (node (A::B::rest)) ≤ Aobj (node (pushInto A B::rest))` **only for the `(A,B,rest)` the finder actually
  selects** (deepest-defect node, spine-`A`, off-spine-`B`) — a strictly smaller family than all-valid, and the
  one Phase-0 verified 0-failures on. Characterizing that family exactly is the Stage-1/2a seam.
- **`R3Cert/R47R7Closure.lean` — the capstone.** `tree_to_hub_sized_of_obligationA (hOA : ObligationA) :
  <tree_to_hub_sized statement>` := `tree_to_hub_sized (straightProgress_of_obligationA hOA)`. Axiom-guarded.

### Risks / subtleties (Stage 1)

- **Deepest-defect-node existence + the ≥2-non-piece-child structure.** A `strDefect>0` node has `npCount ≥ 2` OR a
  non-piece child with `strDefect>0`; recursing to a *deepest* such node yields `npCount ≥ 2` with all non-piece
  children defect-0 — the spine-like `A` + relocatable `B` decomposition. Must be proven, not assumed.
- **Re-rooting (Obligation B).** Phase-0's ties are `reroot_only`. If the finder needs a re-root to expose the
  move, Obligation B (`Aobj` root-invariance) is also required. Stage 1 will first attempt a **reroot-free** finder
  (the SPR de-branch move directly); if some defect>0 tree provably needs a reroot, Stage 1 additionally takes an
  `ObligationB` hypothesis. Determined empirically in 1a-prep (does a deepest-defect de-branch always apply without
  reroot? — quick exhaustive check `n ≤ 12`).

## Stage 2 — the Obligation A attempt (gated research)

- **2a — faithful model + isolate the exact inequality.** Rebuild the Python harness to apply *exactly* the
  finder's chosen move (deepest-defect de-branch, `pushInto` onto the spine), reproduce Phase-0's 0-failures, and
  extract the precise scalar inequality `Aobj(node(A::B::rest)) ≤ Aobj(node(pushInto A B::rest))` for that chosen
  family. Confirms the target the Lean needs. (No Lean.)
- **2b — cavity/price-interval discharge (the probe).** Decompose the `Aobj` change under the chosen move via the
  cavity recursion; the root degree drops by 1 (B leaves the root level) — exactly what the price map
  `μ_d = 3/(4d−1)` and the invariant interval `I = [456/3703, 3/7]` track. Test whether the inequality reduces to a
  per-child / single-child-lemma rational inequality already gated in Telperion (broom-vs-cherry, leaf-exchange,
  price-map). **Go/no-go:** clean reduction → 2c Lean; otherwise → sharpened-obstruction doc.
- **2c — terminal.** *Closes:* formalize the discharged inequality in Lean following `Aobj_balance_le_deep` /
  `node_Ztot_child_mono` (cavity monotonicity + `norm_num` rational atoms via the frozen enclosure pattern), giving
  `theorem obligationA : ObligationA`; then `tree_to_hub_sized` is unconditional (this layer). *Does not close:*
  `LEAN_OBLIGATION_A_OBSTRUCTION_<date>.md` — exactly what the chosen move needs, where the cavity machinery stalls,
  and the tightest partial (e.g. the backbone case, already `Aobj_balance_le_deep`). Stage 1 stands as the result.

## Testing / verification

- **Lean:** each new module must `lake build` green on the warm-cache CI (Mathlib olean cache + incremental
  `.lake/build`); axiom-guard clean `[propext, Classical.choice, Quot.sound]`; the repo sorry-scan passes. A
  minimal `fast-lean-check` workflow (build only the target module, warm cache, ~5 min) accelerates iteration; the
  full `proof-lean` remains the merge gate.
- **Python (Stage 2a/2b):** exact-`Fraction` `Aobj` harness re-anchored against the existing
  `kelmans_mixed_load.pi_literal` / brute-force permanent; exhaustive `n ≤ 12` reproduction of Phase-0's 0-failures
  before trusting any reduction; every numerical "reduction" gets a held-out / larger-`n` stress test (the campaign's
  standing anti-overclaim discipline).
- **Honest gates:** `conjecture1_proved` stays `False` unless 2c closes with green CI. Stage 1 landing does **not**
  claim BG closed — it claims the layer rests on one explicit hypothesis.

## Out of scope

- The `Aobj` root-invariance combinatorial seam (Obligation B) beyond what Stage 1's finder strictly needs.
- The other BG layers (the branch-model `bg_upper_bound` Telperion reduction is separate and already gated).
- Any local Lean build (SoC-watchdog risk; this Mac runs the live trading daemons). CI/remote only.

## Coordination

This takes over the parallel session's `hnorm`/tree→hub Lean lane (per operator instruction). New files only
(no edits to their `R47R7*` files), self-building via the glob, so no merge-conflict surface with in-flight work.
