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
| ~~Residual master inequality general `base¹¹·Bcap(μ)^k ≤ T`~~ | ~~non-monotone integer-tight~~ | — | **CLOSED — see correction below (this row was STALE)** |

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

### #3 — CORRECTED: the master inequality is CLOSED, not open
**This section as first written was STALE** — it repeated the *pre-`phi_le_one`*
framing. The general `base¹¹·Bcap(μ)^k ≤ T` is **CLOSED**: `phi_le_one` proves
`logPhi b ≤ 0` unconditionally (= exactly this inequality), and the homogeneous case
is subsumed by `gstep_le_one_achievable`. The old "no smooth certificate / must be
arithmetic / 23-adic" no-go was **EVADED, not unmet** — by using a *non-smooth*
potential, the folded hinge `φ = c·(y − T0)₊`. That folded hinge is the same object
skill #1/#2 build on. So there is no residual arithmetic breakthrough here; do NOT
hand this off as open. (Telperion's near-star `UnimodalMax` sub-family work stands as
one supporting piece of the now-closed crux.)

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

---

## CORRECTION 2026-08-22 (post Session-B review) — this doc was main-based and STALE

Session B (owner of the floor layer) reviewed this doc against in-flight work and
caught a real staleness: the map above was built on `main`, but the floor PRs
**#69/#71/#72/#73** are OPEN/auto-merging (not yet on `main`), so this doc missed
them. Corrections, authoritative:

- **G1 L2 has TWO halves; this doc conflated them.**
  - **Interval floors** (the 1-var `slack(y) ≥ floor` per class, Bernstein/`norm_num`)
    are **DONE** in **#73** — the whole context-free taxonomy (chain (0,0,1),
    bare-leaf nl=1/nl=2, m=0 childless, m≥4 collapse, six tax-window + below-window
    shapes), all CI-green. **DO NOT re-author** — that would be a 4th collision.
  - **The Jensen "min at equal children" reduction** (multi-child profile → the
    equal-children 1-var problem, via convexity of the hinge `φ`) is the **genuinely
    OPEN, correctly-shaped, UNCLAIMED pickup** — the `TangentSum` half. Session B
    certified the *output* of the relaxation (#73); nobody has formalized the
    *relaxation itself*.
- **#2 `KneeTelescopeEmitter` (lemma 1) — ON HOLD, do not build yet.** Lemma 1's
  true statement is **not settled** (family-specific `chain3p`; the clean route is
  refuted with counterexamples near `cav≈T0`; Session B independently ran it to
  false-in-general). You cannot build an emitter to a statement that doesn't yet
  exist in true form. It is also **Session B's active lane** (they own
  `slack_ledger_dichotomy.py` / `amortized_hub_bound.py`; note lemma 1 is DISTINCT
  from their just-landed `slk_min_at_knee`). Build the emitter to Session B's
  eventual family-specific statement, **coordinated** — not speculatively.
## CONSOLIDATED, post BOTH reviews (crux/lemma-1 session + floor session) — FINAL de-conflicted plan

Two sessions reviewed this. Their combined ground truth supersedes the original
recommendation:

- **L2 is fully covered — the third session should NOT take L2 at all.** The
  interval floors are DONE (#69 chain, #71 bare-leaf + nl=2 = 102 cells, #72/#73
  m=0 / m≥4 / tax-window facets, all Bernstein/`norm_num`, CI-green). The remaining
  L2 piece is the **assembly** ("min-at-knee + point-floor ⟹ per-class
  `slack(y) ≥ floor`"), which is the crux-session's **active** thread — `g_mono`
  landed, `slk_min_at_knee` (the m≥4 min-at-`T0` reduction) pushed as G7 bricks. So
  even the "Jensen reduction" I flagged as open is being done there. **Coordinate,
  don't author.**
- **Genuinely-unstarted, existing-shape wins for the third session:**
  - **L3 domination-ratio unimodality** — `UnimodalMax` (math already exact in
    `depth3_rigorous.py`); clean author-and-emit, confirm unclaimed.
  - **R7 `HypDominationSweeps`** — `FiniteDecide`; plausibly unclaimed.
  - **R7 `HypAmortizedHub`** — `ConeFarkas`; unstarted existing-shape, but **may be
    the crux-session's** (`amortized_hub_bound.py`) — claim-first.
- **#2 `KneeTelescopeEmitter` — DO NOT BUILD to the clean form; it is FALSE.** Lemma
  1's clean/general "adding a bundle raises the ledger" is **verified false at the
  knee** (achievable counterexamples ≈ −0.00073 near `cav≈T0`, persist when buried,
  not rescued by ancestors). A general "telescope-through-a-knee dichotomy" cannot
  certify a monotonicity that is false in general — the truth is **family-specific
  to `chain3p`'s equal-`3/23`-bundle structure**, which a knee dichotomy doesn't
  capture. Downgrade from "hardest *tractable* piece" to **research-adjacent**. If
  prototyped, the emitter must be validated against `chain3p`'s actual arithmetic
  first and will be narrowly chain3p-specific (limited reuse) or will correctly
  refuse.
- **#3 master inequality — CLOSED** (corrected above; `phi_le_one`).

**What THIS session actually built** (`hinge.py`, commit ec97bce): the convex-hinge
**superadditivity** certificate `Σ(yᵢ−t0)₊ ≥ (Σyᵢ−k·t0)₊`. Honest status: a valid,
tested, general convex-hinge primitive — but given L2 floors are DONE and the L2
remainder is the crux-session's assembly thread, **it is NOT a needed BG L2 piece**;
treat it as a general Telperion primitive, not a BG deliverable. See
`telperion/docs/HINGE_EMITTER_DESIGN_2026-08-22.md`.

**Net corrected plan:** third session takes **L3 (UnimodalMax)** + **R7
`HypDominationSweeps` (FiniteDecide)**, claim-first on `HypAmortizedHub`; L2 stays
with the floor + crux sessions; #2 is research-adjacent, not routine; #3 is closed.
