# Missions migration: ANDÚRIL + MIRRORMERE → registry (draft, 2026-09-14)

Status: DRAFT PR. Branch `feat/missions-anduril-mirrormere`, base `main` @ `fcc0df15`.
`conjecture1_proved = False` throughout — both campaigns are instruments and
finite verification, not a route to RH; every RH-hard node is `draft` and says so.

## What this adds

Two new campaigns in `telperion/missions/`, following the bg/rh conventions
(design: `MISSIONS_DESIGN_2026-09-11.md`; verbatim-extract read-back precedent:
PR #528):

| Campaign | Goal node | Nodes | Open+linked | Open unlinked | Draft |
|---|---|---|---|---|---|
| `anduril` | `AND_ladder_1e13` (draft) | 9 | 5 | 1 | 3 |
| `mirrormere` | `MM_zeta_comb_membership` (draft) | 9 | 6 | 2 | 1 |

Sources of truth migrated: `PROGRAM_ANDURIL_2026-09-12.md`,
`ROADMAP_ANDURIL_MIRRORMERE_2026-09-14.md`, `QC_PROGRAM.md` (+ the QC memo
set). Those documents remain narrative; the registry becomes tracking truth
for these campaigns, per the design's stated intent.

## THE GATE THIS DRAFT CANNOT PASS (and why that's correct)

Every artifact of both programs lives on the `rh/million-turing` line, which
is **not merged into `main`** — the registry and the programs evolved on
different branches. The §9 fidelity rule ("a claim that cannot pass the §7
gate migrates as `open`, never as `proved`") therefore applies to *every*
kernel-checked result here: all such nodes enter as **`open` with the
artifact linked** and read-backs recorded; **no node is `proved`**. The
grant pass is a separate, mechanical follow-up:

1. Reconcile `rh/million-turing` → `main` (or land the islands by subtree).
2. Run `telperion mission verify anduril mirrormere --deep-lean`.
3. `telperion mission grant <slug>` per node; the gate checks artifact
   existence + normalized statement containment, home-island CI stays the
   kernel authority.

Special cases flagged in the node files themselves:

- `AND_ladder_h280000` — the artifact theorem carries ~280 per-segment
  `BandHyp` binders (`..._of_bands`); the registry statement is the
  hypothesis-free conclusion. Grant additionally needs the StripClear
  two-box capstone glue (an existing roadmap deliverable). Until then the
  node is open and *unlinked* — linking the `_of_bands` artifact against a
  hypothesis-free statement would fail containment honestly.
- `MM_bragg_defect_witness` — `closure_clean = false`: the off-line leg
  carries one Arb `e^(1/10)` enclosure hypothesis (per `QC_PROGRAM.md`,
  "kernel (+1 Arb exp hyp)").
- `MM_nt_brick_conditional` — `closure_clean = false`: carries the named
  residual `RvMUnboundedMeanDensity`, which is itself the open node
  `MM_rvm_unbounded_mean_density` (intended discharge: the v4.34 li-island
  effective-RvM machinery, cross-island per design §2).

## Statement-authoring queue (deliberately NOT registered)

Nodes whose authoritative formal statements ARE the work were not invented
for this draft — registering a guessed statement is exactly what read-back
auditing exists to prevent. Queued, in roadmap order:

- **W3b GW-finite** — fixed-rectangle explicit-formula identity with carried
  remainders (the ANDÚRIL⟷MIRRORMERE bridge; unblocked since the E-track
  landed). First candidate for the next registry pass.
- **A3 Riemann–Siegel era** — θ Stirling-branch, RS main sum, Gabcke C0
  remainder (first-of-kind; statements to be authored at A3 staffing;
  `AND_ladder_1e9` names this gate in its title).
- **R1 crystalline rigidity** — with the isolated temperedness clause
  (QC_RIGIDITY_MEMO); de Branges/Hermite–Biehler explicitly not attempted.
- **W3c infinite-torus FQ axioms** and the **W4 face probes** (Speiser,
  Báez-Duarte, Λ-bounds) — after their memo/emitter phases settle.

W3a (multiplicativity axiom) and W3d (recurrence dictionary) are doc+harness
deliverables, not Lean theorems; they stay in the mission `sources`.

## Statement packages

`missions/{anduril,mirrormere}/lean/` follow the rh shape: one `Statements`
package per campaign pinned to the islands' shared `leanprover/lean4:v4.32.0`
+ Mathlib `v4.32.0` pin, a `Defs` vocabulary mirror of VERBATIM-copied island
definitions (provenance-commented, to be regenerated/diffed by
`build_anddefs.py`/`build_mmdefs.py` in the grant pass), and one module per
node ending in `by sorry`. Read-backs on open+linked nodes follow the
verbatim-extract precedent and were finalized against a full extraction pass
over the artifacts (2026-09-14).

Deliberate deviations from verbatim, each flagged in-file for the blind
read-back audit:

- `MMDefs.zetaOrdinates` is **AUTHORED** (the island keeps `Ordinates : Set ℝ`
  free); it pins the two authored W2c statements
  (`MM_rvm_unbounded_mean_density`, `MM_zeta_ordinates_not_uniformly_discrete`).
- `MM_bragg_defect_witness` is the **conjunction** of the two artifact
  witnesses (`defect_witness_online` ∧ `defect_witness_offline`), each
  conjunct verbatim including the certified rational brackets.
- `MM_offline_pairs_le_defect` inlines the island's section variables as
  explicit binders.
- `MM_zeta_comb_membership` (goal, draft) carries a **placeholder** statement
  (Mathlib `RiemannHypothesis`, justified by the island's `zeta_FQ_iff_RH`
  dictionary); the concrete FQ membership statement is the W3c authoring item
  and must replace it before the node leaves draft.
- The four ladder-height statements (`280000`, `1e6`, `1e9`, `1e13`) use the
  island capstone's verbatim conclusion type with the height literal swapped.

Extraction-pass finding recorded here for the grant pass: **no hypothesis-free
capstone exists on the island at any height above 100** — StripClear's
`all_nontrivial_zeros_up_to_height_100_strip_cleared` discharges only the
55/16 height floor (hγ) at height 100; every `AllZeros_h*.lean` through
h320000 keeps the per-segment `BandHyp` binders + hγ. `AND_ladder_h280000`
open/unlinked is therefore forced, not conservative.

## Honesty checklist (self-audit against the design)

- [x] No node migrated as `proved` (fidelity rule §9).
- [x] Every conditional labeled, hypothesis named, `closure_clean` accurate.
- [x] RH-hard targets (`AND_ladder_1e13` is not RH-hard, merely enormous;
      `MM_zeta_comb_membership` IS RH-hard) are `draft`, titled as such.
- [x] `conjecture1_proved = False` in both mission manifests.
- [ ] Statement package CI build (blocked: needs the extraction pass
      finalized + a Mathlib cache for the new packages).
- [ ] Read-back blind audit cycle (the PR #521 pattern) before launch.
