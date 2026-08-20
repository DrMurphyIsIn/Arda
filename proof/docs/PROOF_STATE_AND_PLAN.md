# Brualdi–Goldwasser proof effort: state, gaps, and completion plan

**`conjecture1_proved = False`.** This is a whole-campaign map for all sessions: what is proven,
the exact remaining gaps, and a completion plan per gap. Built from the authoritative
`proof/verification/conjecture1_status.py` (the R-ladder aggregator) and this arc's localization work.
Last synthesized 2026-08-19; updated 2026-08-20 (capped-joint g-step arc — see the dated
addendum under Gap 1).

## The reduction: the whole 1984 problem sits on one crux

Conjecture 1 (near-star `N(0,5)` maximizes `Φ`) reduces through a 7-rung ladder:

| Rung | Claim | Status |
|---|---|---|
| R1 | branching star beats spiders (rate) | **PROVEN** (`spiders.py`, N₀=412) |
| R2 | legs are cherries | **PROVEN** (`legs.py`, exact) |
| **R3** | **branches are cherry-arms ⟺ `Φ≤1`** | **CERTIFIED CANDIDATE — the crux** |
| R4 | backbone is a star (Kelmans) | **PROVEN** all N, incl. strictness |
| R5 | single hub tiebreak | **PROVEN** constant-order; `(26/23)¹¹<621/64` holds |
| R6 | cherry distribution (arms@5, hub de-load) | **PROVEN** |
| R7 | global assembly | **OPEN**, depends on R3 |

Everything except R3 and R7 is proven, and R7 depends on R3. The entire problem collapses to:
*make `Φ≤1` (R3) a formal theorem, then assemble (R7).*

**Two standards of "proven" — do not conflate them:**
- The R1/R2/R4/R5/R6 "PROVEN" verdicts have their **full analytic arguments as Python exact-certificates**
  (`spiders.py`, `legs.py`, `psi_close.py`, `rem_tie.py`, `distribution.py`) — rigorous *if the argument
  is complete*, machine-checkable in Python. **Formalization is partial, not zero** (an earlier draft
  here overstated it as "no Lean rung theorems"): individual crux inequalities and gadget-rate leaves
  ARE kernel-checked — e.g. `r5_crux`/`C1_lt_one` (R5), `ell1_rate`/`legs_rate_ge3`/`legs_are_cherries`
  (R2), and the extensive R3 scaffold (`node_le_omega`, `menuHull_cell_le`, `s_tail_ge_65`). What is
  **not** yet in Lean is the rung-level *reduction* theorems (tying the leaves to the tree-extremality
  statements) and R1/R4/R6's rate arguments; there the Python certificate is ground truth. So a fully
  *formal* proof still needs that rung-reduction Lean-ization (subsumed into R7/G7). "One theorem away"
  is the **mathematical** standard (R3 + accepting the exact certificates); the **formal** standard is
  that theorem *plus* the remaining Lean mountain (rung reductions, R1/R4/R6, Gap 2 bridge, Gap 3 G7).
- (Caveat: these verdicts are from the status file + spot-audits, not a fresh re-audit of every
  certificate.)

**R-numbering disambiguation.** This ladder (R1–R7) is the *Conjecture-1 reduction* per
`conjecture1_status.py` (authoritative). It is a **different axis** from the *R47 Lean
reduction-layer campaign* (also labelled R1–R7, the stage-wise assembly formalization, = G7).
E.g. "single-hub extremality / the master inequality" is **R3 here** but is called "R1" in some
`R47_*`/`R1_WIRING_*` docs. When a doc says "R1", check which axis it means.

## The four remaining gaps

**GAP 1 — R3 / `Φ≤1` branching tail (the mathematical crux).** The uniform per-node condition /
valid-potential existence (`Reach.ValidPotential`). This *is* the master inequality = the homogeneous
(C-broom) face = the downstream shadow of the **g-lemma** `g(C)=F(1+μ/3)¹¹ ≤ γ`, `γ=W²(5/3)¹¹=2.9276`,
equality iff arm. Currently an exact/interval **numeric certificate** (`ALL_INTERVAL_CERTIFIED`,
`gap_interval_certification.py`), **not a proof-assistant term**. Genuinely open new arithmetic:
the raw maximizer conjecture was *refuted* in 2026, every continuous certificate provably fails
(continuous `F_ns>1` at `k≈4.82`; deep-left accumulation boundary at cavity 0), so the proof must be
integer-tight / 23-adic.

**GAP 2 — the realization bridge (Full STEP 4).** `Branch.logPhi` is a standalone Lean *definition*;
nothing yet ties `logPhi B ≤ 0` back to `per(L(T))/∏deg`. Steps 1–3 + the Step-4 core (`hub_rho0_limit`)
are CI-green; the open piece is `logPhi≤0 → per(L(T))` via the amplitude ratio + uniform `O(1/p²)` —
"last + hardest bridge gap." A proven R3 is not a statement about the real Laplacian without this.

**GAP 3 — R7 global assembly (formal).** Stages I–IV discharged (I unconditional, II closed 36/36,
III/IV via G5/G6 + R5/R6). Named residuals: **G1** (symbolic hardening of interval-float floors),
**G7** (Lean formalization of R7 = the R47 campaign), independent review.

**GAP 4 — promote R3's interval certificate to a Lean term.** The Lean scaffold is far along:
`Structure.node_le_omega` is a *real conditional theorem* given {concave menu hull `H`, child-envelope
`ℓ_i ≤ H(μ_i)`, sweep bound `Qeq≤ω`}; the hull (`menuHull`/`menuHullRat`) is defined with
concavity/nonpos/tie proved; the s-tail (`s≥65`) is proved; the finite core (`s≤64`) is reduced to
machine-checked per-cell rational inequalities (`menuHull_cell_le`, hull-agnostic `Qeq_cell_le`). The
**one load-bearing open hypothesis is the child-envelope** — which *is* Gap 1. **So Gap 1 and Gap 4 are
the same object**, viewed from Python (interval cert) and Lean (open hypothesis).

## Completion plan per gap

### Gap 1 (+ Gap 4): the arithmetic crux — `Φ≤1` branching tail
**Tractability: genuinely open. No mechanical path.** Best available strategy (this arc): attack the
**g-lemma**, equality iff arm — upstream of the homogeneous face, with a robust `γ−γ'≈1.08` margin
(survives enumeration to n=14 and adversarial construction to n=28, no creep toward γ). Sub-targets:
1. Prove the **equality characterization**: the arm is the *unique* g-saturator (`μ=1/3` structurally
   forces the arm block; formalize that isolation).
2. Prove the **gap version** `g(C) ≤ γ' < γ` off the near-star family → closes the homogeneous face
   and the near-star half with margin (`H ≤ 0.588`).
3. Feed into the Lean child-envelope `ℓ_i ≤ H(μ_i)`, discharging `node_le_omega`'s last premise → Gap 4.

Steps 1–2 need a genuine integer-tight / 23-adic breakthrough. The scaffold is ready; the idea is not
in hand. **This is the one gap that cannot be scheduled.**

**Addendum 2026-08-20 (capped-joint g-step arc, landed on `main`).** The ≤-face of the g-lemma
attack moved substantially; the *strict/equality* content above remains the unschedulable part.
Landed, kernel-checked: (a) the achievability correction — the unconstrained `Case2Property` is
FALSE on `μ ∈ (1/2,1)` (exact witness `telperion/src/telperion/bg/g_step_margin.py`); non-leaf
cavity messages satisfy `μ ≤ 1/2`, and that hypothesis is the relocated integrality content;
(b) `R3Cert/CappedJointAchievable.lean` — `single_child_le_one`, `two_child_le_one`
(unconditional for two children: the integrality wall is a single-child phenomenon), and the
reduction `gstep_le_one_of_glemmaBound`; (c) the abstract g-lemma `gV_le` (≤-form, all blocks) is
kernel-proven over the `Blk` cavity model (`telperion/examples/g1_floors/lean/GLemma.lean`), and
the PR #20 branch (in review) carries both the `R3Cert` port and the **full closure**
`CappedJointClosure.lean:gstep_le_one_achievable` — the config g-step `≤ 1` at every arity,
unconditionally over achievable messages, kernel-clean. The mechanical seams are done pending
review + merge. Remaining *research* content of Gap 1: the equality characterization / strict gap
and the child-envelope feed into `node_le_omega`.

### Gap 2: realization bridge (Full STEP 4)
**Tractability: hard Lean formalization, not new mathematics** (the `p→∞` mechanism is already a
Mathlib `Tendsto` theorem). Plan: (a) formalize the amplitude-ratio identity `Branch.logPhi ↔ RTree.Ztot`
at finite p; (b) prove the uniform `O(1/p²)` remainder so the limit transfers `logPhi≤0` to the
matching-sum ratio; (c) compose with Steps 1–3 (green) to reach `per(L(T))/∏deg`. (b) is the crux.
**Independent of Gap 1 — can proceed in parallel now.**

### Gap 3: R7 assembly (G1, G7)
**Tractability: mechanical but large.**
- **G1** (symbolic hardening): replace interval-numeric floors in Stage II/III with exact-rational
  certificates — same cell-by-cell pattern already done for the finite core. Schedulable.
- **G7** (Lean formalization of R7 = R47 campaign): largest mechanical effort; the cell-reduction
  machinery is hull-agnostic and reusable. Long but decomposable.
- Then independent review. G1/G7 proceed in parallel with Gap 2; final assembly is **gated on Gap 1**.

## Critical path

```
Gap 1 (R3 arithmetic crux)  ───────────────┐  [the only unschedulable gap]
   └─ discharges Gap 4 (Lean child-envelope) │
Gap 2 (bridge Step 4)  ── parallel ──────────┼──► R7 final assembly ──► Conjecture 1 proved
Gap 3 G1/G7 (R7 Lean-ization) ── parallel ───┘
```

**Bottom line:** *mathematically*, the effort is one genuine theorem away from done — Gap 1
(`g(C) ≤ γ`, equality iff arm), real open arithmetic with a ready scaffold and a validated attack
direction, but no breakthrough in hand. *Formally* (a Lean-checked proof), "done" is that theorem
**plus** the Lean mountain: R1–R6 are not yet formalized, Gap 2 (bridge) and Gap 3/G7 (the R47
campaign) are substantial though *mechanical* and parallelizable. So: **one unschedulable arithmetic
gap, plus a large but schedulable formalization mountain.** `conjecture1_proved = False` is
load-bearing and stays until the arithmetic closes.
