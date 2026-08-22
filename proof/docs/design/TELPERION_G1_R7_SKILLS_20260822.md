# Telperion skills for G1 Stage-II + R7 assembly — coordination hand-off (2026-08-22)

`conjecture1_proved = False`. This is a **coordination doc** for the parallel proof
sessions: it maps the open G1 Stage-II lemmas and R7 named hypotheses to the exact
Telperion certificate shapes that discharge them, so work can be split without
collision. Source audits: `GSTEP_STEP1_IS_THE_CRUX.md`, `BRIDGE_AUDIT_20260822.md`,
`G1_STAGE2_AUDIT_20260822.md`, `R7_ASSEMBLY_DESIGN.md`.

## State in one paragraph

The Φ≤1 / g-step / master-inequality **crux is closed** (`phi_le_one`,
`gstep_le_one_achievable`, unconditional, no `sorry`/`axiom`). The
permanent↔matching↔Branch **bridge is substantially formalized** (`pi_litHub'`,
`amplitude_bridge_real'` unconditional). The **open distance to Conjecture 1** is (a)
**G1 Stage-II** — three single-variable/convexity lemmas underpinning the R7 class
floors — and (b) **R7 global assembly** — the honest-conditional capstone `R7'_of`
over six named `Hyp*` Props. Telperion is already the proof's certificate backend
(9,451 `positivity`, 1,331 `tangent`, 117 SOS, 7 Bernstein, 8 unimodal, 3 Handelman
sites); the remaining pieces are mostly *authoring families in existing shapes*.

## The map: open piece → Telperion shape → status

| Piece | Character | Telperion shape | Class |
|---|---|---|---|
| **G1 L2** context-free class floor ("inf at equal children") | Jensen on the **convex hinge** `φ(y)=C·(y−T0)₊`; per-class floors interval-numeric | `TangentSumEmitter` (tangent-line/Jensen) + `BernsteinEmitter` (box floors) | **HAVE — author** |
| **G1 L3** domination-ratio unimodality `r(qᵢ)` | single-crossing rational fn, one interior min | `UnimodalMaxEmitter` / `MonotoneRatioTailEmitter` | **HAVE — author** |
| **G1 L1** ledger monotone in chain depth `pL` | telescoping-sum monotonicity, **family-specific + knee-critical** (counterexamples near `cav≈T0`) | `TelescopingPotentialEmitter` **+ `DichotomyGlueEmitter` at the knee** (new composite) | **NEW COMPOSITE** |
| **R7 `HypFloors`** class floors, rational certs | rational-fn lower bounds | `DirectPolya` / `ConeFarkas` / `Handelman` | HAVE (started #36) |
| **R7 `HypAmortizedHub`** `ledger ≥ (47/2000)·#hubs` | linear amortized bound | `ConeFarkasEmitter` (linear Positivstellensatz) | HAVE — author |
| **R7 `HypDominationSweeps`** exact finite dominations | bounded finite dispatch | `FiniteDecideEmitter` / `CaseDispatchAssemblyEmitter` | HAVE — author |
| **R7 `HypRatePort` / `HypLedgerTelescope` / `HypStarSymbolic`** | rate/telescope/star capstones | already authored (#33 R47Rate, #34 HypStarSymbolic) | LANDED |
| (a,b,ν) hetero base cells (#66) | interval positivity on a box | `BernsteinEmitter` | LANDED |
| **Residual master inequality** general `base¹¹·Bcap(μ)^k ≤ T` | **non-monotone, integer-tight** max, tight only at arithmetic resonances | — (no smooth certificate exists; program no-go) | **NOT A TELPERION TARGET** |

## The three needed skills (priority order)

### #1 — Author G1 L2, L3 + R7 floor/hub/sweep families in EXISTING shapes (highest leverage)
No new emitter. Build the certifiable families and emit:
- **L2 floor**: the hinge `φ` is convex ⇒ Jensen "min at equal children" is the
  `tangent_sum_family` shape (tangent line at the class mean); per-class interval
  floors via `bernstein_family` box positivity. The G1_STAGE2 audit flags this as
  **structurally EASIER than the already-closed g-step** (clean convexity, no knee
  non-convexity) — lowest-risk win.
- **L3 unimodality**: `r(qᵢ)` single-crossing ⇒ `unimodal_max_family` /
  `monotone_tail_family` (successive-difference sign change, already verified exact
  in `depth3_rigorous.py`).
- **R7 hub bound**: `ledger ≥ (47/2000)·#hubs` ⇒ `cone_family` (Farkas).
- **R7 sweeps**: the exact finite dominations ⇒ `finite_decide_family`.
Deliverable: kernel-checked theorems discharging **G1 L2, L3** and R7
`HypFloors`/`HypAmortizedHub`/`HypDominationSweeps`.

### #2 — NEW composite: knee-telescope for G1 L1 (the one genuinely-missing shape)
G1 **lemma 1** (ledger monotone in depth) is the hardest *tractable* piece: a
telescoping-sum monotonicity that is **family-specific and knee-critical** — the clean
cavity-contraction was refuted (counterexamples near `cav≈T0`). Telperion's
`TelescopingPotential` proves `slack≥0` but not monotonicity *through* the non-smooth
knee `y=T0`. Needed: a first-class **chain-monotone telescope** emitter =
`TelescopingPotential` glued with a `Dichotomy` case-split at the knee (below-knee `φ=0`
branch trivial; above-knee `φ` linear). Reusable because the same hinge-knee recurs in
both the R3 crux and the R7 ledger. Deliverable: `KneeTelescopeEmitter` + G1 L1 as a
theorem on the `chain3p` family.

### #3 — The master-inequality crux is NOT a tooling problem
General non-monotone integer-tight `base¹¹·Bcap(μ)^k ≤ T`: the program's own no-go
(near-star asymptotics: continuum overshoots to 1.00046, must be arithmetic/23-adic)
means **no smooth certificate — hence no Telperion emitter — can close it**. Telperion's
role is bounded to certifying sub-families (near-star `R(s)` via `UnimodalMax`, done).
Leave to the math track; do not build a speculative "integer-tight max" emitter as if it
were a known win.

## Coordination notes (READ before authoring)

- Parallel sessions are very active in the proof lane this week (PRs #58–#70:
  face capstones, R7 collapse-tail, (a,b,ν) family, G1 audits). **Claim a piece before
  authoring.** Suggested split: whoever owns `slack_ledger_dichotomy.py` /
  `amortized_hub_bound.py` likely owns G1 L1 + the hub bound; the L2/L3 floors are
  self-contained and safe to pick up.
- New emitter files (e.g. `emit_knee_telescope.py`) are collision-safe (new files);
  authoring proof *families* under `telperion/examples/` + `proof/` needs a claim.
- Branch protection (2026-08-22): 9 required checks (6 unit + `toy`/`tangent`/
  `primality-compiles`), `enforce_admins: false`. The narrow-path production compiles
  (`g1/audit/bridge/telescope-compiles`) are **not required** (they only trigger on
  specific example paths) — don't re-add them to required or they block non-matching PRs.

## This session's plan

Starting **#1** (author L2/L3 + hub/sweep families) and **#2** (`KneeTelescopeEmitter`)
on branch `feat/telperion-bg-g1-stage2`. #3 stays with the math track.
