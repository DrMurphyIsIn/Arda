# Design: Prepare the Arda / Telperion repository for the mathematics community

**Date:** 2026-09-05
**Status:** Draft for review
**Scope:** Phases 0–4 (repo credibility). Phase 5 (whitepaper) is deferred to its own spec.
**Target repo:** `DrMurphyIsIn/Arda` (public GitHub). Canonical public surface going forward.
**Working branch:** `docs/public-release-prep` off `origin/main`.

---

## 1. Purpose

Prepare the public GitHub repository `DrMurphyIsIn/Arda` — which holds three
formal-mathematics arcs (Brualdi–Goldwasser / Laplacian-ratio, Riemann-zeta
zero-free regions, and the Telperion certificate engine plus AXLE/AxiomMath
ported material) — for outward-facing viewing by the mathematics and
formal-methods communities.

The audit (2026-09-05) established that **the mathematics is honest and the
engineering is real**; the repository is already more rigorous than most public
math repos (no `sorry`, no added axioms, an untrusted-generator / trusted-kernel
trust model, an executable status file, and preserved failed-route no-go
modules). The work required is therefore **presentation, consolidation, claim
correctness, attribution, and CI health — not fixing the mathematics.**

## 2. Governing decisions (from maintainer, 2026-09-05)

1. **GitHub is primary and live.** `DrMurphyIsIn/Arda` is THE public home.
   Remove/neutralize the "GitLab is primary / repo frozen" notice and scrub any
   leaked private-monorepo references.
2. **Claim posture is per-arc, driven by verification reality.** Lead with what
   is kernel-verified and unconditional; label open conjectures OPEN. Never
   present a special case as the general conjecture. `conjecture1_proved = False`
   stays load-bearing.
3. **Attribution cites only what the code supports.** Cite arXiv:2609.02882
   (AxiomMath/ZetaZeros), arXiv:2606.26442 (AXLE), `openai/ten-proofs`,
   `leanprover/comparator`, `ammkrn/nanoda`. Keep AXLE (serving infra) and
   AxiomMath/ZetaZeros (the zeta proof) **distinct**. Do **not** publish the
   "Ken Ono / internal-Anthropic-result / >67.25% simple zeros" framing — it
   appears nowhere in the code and is unconfirmed.
4. **Telperion stays BUSL-1.1**, source-available; the dual-license split is to
   be documented clearly, not changed.
5. **Full tidy**, including consolidating stranded work (open PRs + the two
   active fronts) and organizing the local worktree/clone sprawl.
6. **Whitepaper** is a fresh narrative "system" paper, specced and executed
   separately (Phase 5, not in this spec).

## 3. Audit ground truth (verified 2026-09-05)

### 3.1 Repository topology
- `DrMurphyIsIn/Arda` is PUBLIC; honest topics/description; `conjecture1_proved =
  False` present.
- The canonical checkout `~/repos/Arda` is **not** authoritative: stale branch
  `docs/bg-capacity-attack-spec`, ~512 behind main, 32-file dirty tree. Do not
  publish from it.
- Authoritative state = `origin/main` (tip `5940f79`, 2026-09-05). Freshest clean
  mirror = `~/bg-research`.
- ~20 worktrees/clones; most are stale probes (600–700 behind). Two **active,
  stranded** fronts: `~/repos/Arda-wt-armrate` (`bg/conjecture1-attack`, +96,
  active today) and `~/arda-rh-wire` (`rh/jensen-hyperbolicity`, +11, active
  today). 4 open PRs: #154, #178, #197, #210. ~200 remote branches.
- Two "math" worktrees (`~/arda-pvsnp-ladder`, `~/arda-wt-lean-campaign`) are on
  the **GitLab `arda-trading`** repo — must NOT be conflated with or pushed to the
  public math repo.

### 3.2 CI is currently RED on main (release blocker)
On the latest push to `main` (`5940f79`):
- `telperion-casestudy` — **failure**: `MANIFEST INCOMPLETE — unlisted generate
  scripts: telperion/examples/dvp_atoms/generate.py` (new dVP example not added
  to `telperion.toml`).
- `telperion-test` — **failure** (13 failed / 1280 passed):
  - `test_certificate_sensitivity::test_every_emitter_is_classified` — 3 new RH
    emitters missing a sensitivity stance: `BCSplitEmitter`,
    `JensenZeroCountEmitter`, `SphereBoundEmitter`.
  - `test_mt_optimize` (×3) — `ValueError: invalid literal for int() … '-06)'`
    (scientific-notation parse bug).
  - `test_emit_spectral_factorization::test_spectral_factor_roundtrips` — numeric
    tolerance miss (`1.16e-4 < 1e-6` fails).
  - `test_negative_control`, `test_simplify`, `test_statement_match` (several),
    `test_verify` — `FileNotFoundError: 'lake'` / server-start assertion: tests
    that require a Lean toolchain do not skip when `lake` is absent.
- `proof-verify` — success. `telperion-lean-e2e` — queued.

These are **real, small regressions** from today's rapid dVP/RH merges, not
flakes. Greening main is Phase 0.

### 3.3 Per-arc verification state
- **BG / Laplacian:** Lean tree verified clean — 0 real `sorry`, 0 `admit`, 0
  `axiom`, 0 `Prop := True` stubs (the historical "misleading green build"
  failure mode is genuinely remediated). `phi_le_one` proved unconditionally on
  the abstract `Branch` cavity model; `gstep_le_one_achievable` proved
  unconditionally on achievable configs; `amplitude_bridge_real'` bridges the
  real-graph ratio limit. **OPEN:** R7 global structural assembly (Python/paper
  only) and the `Branch`→per(L)/∏deg tree-level identity (H2). The **classical BG
  conjecture is OPEN**. Overclaim risks to fix: the Φ¹¹-vs-classical subtlety
  (81/8 ≠ 621/64 at the tie) is not surfaced in sharp form; a stale
  `conjecture1_status.py` "R3 not a closed proof" line now contradicts the newer
  Lean g-step closure.
- **RH:** RH not claimed. Four kernel-verified, unconditional, CI axiom-guarded
  (`#print axioms`) results: `zeta_fract_repr` (#177), `|ζ(σ+it)| ≤ 6(1+log|t|)`
  (#185), zero-free region `Re s > 1 − c/|t|⁵` (#180), polylog region
  `Re s > 1 − c/(γ⁴(1+log 2γ))` (#188). Plausibly the first unconditional,
  Hadamard-free zero-free regions machine-checked in Lean — but **strictly weaker
  than de la Vallée-Poussin**; the value is the formal derivation. The
  Borel–Carathéodory theorem is proved but **DRAFT** (non-sharp 4R constant, not
  axiom-guarded, not wired in). The dVP region is conditional by design. Docs are
  scrupulously honest; keep the "weaker than dVP" and "BC is DRAFT" framing.
- **AXLE / AxiomMath / Ken Ono:** Three **distinct** external sources; the memory
  conflates them. The two ported emitters (`emit_curvature_boundary.py`,
  `emit_transcendental_enclosure.py`) are production, registered, kernel-checked,
  and serve **BG, not RH** (the AxiomMath-specific C₀/trig face is explicitly
  **deferred/unimplemented**). Attribution is good in prose (docstrings, README,
  `docs/COMPARATOR.md`) but **absent from emitted `.lean` headers**, with **no
  NOTICE/CREDITS/bib and no CHANGELOG entry**.
- **Telperion (tool):** Coherent, installable (`telperion` 0.1.6, sympy-only
  core), CLI + MCP server (15 tools) + Claude plugin, ~78 emitters, 1333 fast
  tests, real self-verification layer (non-vacuity, emitter-sensitivity registry,
  metacircular audit, comparator), 7 substantive CI workflows with real `lake
  build`. Gaps: BUSL-1.1 (document clearly), under-documented local Lean
  verification path, campaign-heavy docs with no GETTING_STARTED / ARCHITECTURE /
  CONTRIBUTING, `bg/` research lab entangled with the reusable engine, stale
  "shapes" count.

### 3.4 Presentation surfaces
- README honest and strong, but the module count is stated four ways (109 / 110 /
  90 / actual ~119). STATUS.md and PUBLICATION_LEDGER.md are exemplary — keep.
- `PRIMARY_REPO_NOTICE.md` **contradicts** the README (frozen/GitLab-primary vs
  live) and leaks the private trading-monorepo name + internal MR/pipeline IDs.
- No `paper/` directory exists (whitepaper is Phase 5).
- CI has no status badges; a path-trigger typo in `telperion-lean-e2e.yml`
  (`forge-lean-e2e.yml`); and the `sorry`/`axiom` scan in `proof-lean.yml` ends in
  `|| true`, so "no sorry" is asserted but not CI-enforced.
- ~39 internal `HANDOFF_*` / `SESSION_REPORT_*` docs under `proof/docs/` expose
  worktree paths, GitLab MR refs, and second-person campaign instructions.
- CITATION.cff well-formed; add `version` / `date-released`.

## 4. Phased plan

Work lands on `docs/public-release-prep` and merges to `main` via CI-gated PRs,
matching the README's stated workflow. Phases 2 and 3 may proceed in parallel
after Phase 0/1.

### Phase 0 — Green the main branch (blocking prerequisite)
Goal: `origin/main` CI is green so a visitor sees passing checks.
1. Register `telperion/examples/dvp_atoms/generate.py` in `telperion.toml`
   (correct group).
2. Declare sensitivity stances for `BCSplitEmitter`, `JensenZeroCountEmitter`,
   `SphereBoundEmitter` in the emitter-sensitivity registry (with `checked_in`
   wiring or an honest stance, per the registry's contract).
3. Fix the `mt_optimize` scientific-notation parse bug (`'-06)'`).
4. Fix or re-baseline the `test_emit_spectral_factorization` tolerance (determine
   whether it is a real regression or an over-tight tolerance).
5. Make Lean-requiring unit tests skip cleanly when `lake` is absent
   (`test_negative_control`, `test_simplify`, `test_statement_match`,
   `test_verify`) — a pytest skip guard, not a silent pass.
6. Confirm `telperion-lean-e2e` passes once queued.
Acceptance: all workflows green on the working branch; no test silently
downgraded (skips are explicit and logged).

### Phase 1 — Governance & hygiene
1. Delete `PRIMARY_REPO_NOTICE.md` (or replace with a neutral `CONTRIBUTING`-style
   "development happens here via CI-gated PRs" note). Remove the private
   `arda-trading` monorepo name and internal MR/pipeline IDs from all tracked
   public docs.
2. Quarantine internal campaign docs: move `HANDOFF_*` / `SESSION_REPORT_*` out of
   `proof/docs/` into an untracked/`internal/` path (or `.gitignore`), **keeping**
   the deliberately-included independent-review docs the README cites as an
   honesty artifact.
3. Prune stale/backup/`worktree-agent-*` remote branches so the GitHub branch view
   is not a maze. Keep active fronts and open-PR branches.
4. Reconcile the local workspace: label/retire the ~20 stale worktrees/clones
   (600–700 behind) so the maintainer's workspace is organized; keep the two
   active fronts and `~/bg-research` (main mirror). This is a workspace-hygiene
   task, not a public-repo change.
Acceptance: no private-repo leakage in tracked files; README and repo notices are
mutually consistent; branch list is curated.

### Phase 2 — Claim correctness (per-arc honesty)
1. Reconcile the module count to a single true source (~119; or "see
   `R3Cert.lean`"); fix README, `proof/README.md`, `PROVENANCE.md`.
2. BG: surface the Φ¹¹-vs-classical subtlety (81/8 ≠ 621/64 at the tie) in sharp
   numeric form in README/STATUS; reconcile the stale
   `conjecture1_status.py` "R3 not a closed proof" line against the newer Lean
   g-step closure so the repo does not contradict itself.
3. RH: ensure the README/STATUS RH section states the four verified results, the
   "weaker than dVP" framing, and that BC is a DRAFT not wired into the pipeline.
4. Make the `sorry`/`axiom` scan a **hard CI gate** in `proof-lean.yml` (drop
   `|| true`) so "no `sorry`, no added axioms" is enforced, not merely asserted.
5. Fix the `telperion-lean-e2e.yml` path-trigger typo (`forge-lean-e2e.yml` →
   `telperion-lean-e2e.yml`).
Acceptance: every headline claim in README/STATUS matches the Lean/CI reality;
no internal contradiction between status files; CI enforces the no-sorry claim.

### Phase 3 — Attribution & licensing
1. Add a top-level `NOTICE`/`CREDITS` (and/or `references.bib` entries) citing
   arXiv:2609.02882 (AxiomMath/ZetaZeros), arXiv:2606.26442 (AXLE),
   `openai/ten-proofs`, `leanprover/comparator`, `ammkrn/nanoda`, keeping AXLE and
   AxiomMath distinct. No unconfirmed "Ken Ono / internal-Anthropic / 67.25%"
   framing.
2. Add provenance headers to the emitted `CurvatureBoundary.lean` and
   `TranscendentalEnclosure.lean` files naming AxiomMath/ZetaZeros + arXiv:2609.02882.
3. Add CHANGELOG entries for the two ported emitters naming the source.
4. Verbatim-copy compliance check: confirm no source text was copied from the
   external repos without honoring their licenses (the emitters appear
   independently written in the Telperion idiom — verify and record).
5. Make the dual-license split crystal clear in `LICENSING.md` (Apache math /
   BUSL engine / emitted-certs-are-yours). Add `version` + `date-released` to
   `CITATION.cff`.
Acceptance: every external dependency and ported idea is credited in a formal,
machine-and-human-readable place; emitted artifacts carry provenance; licensing
is unambiguous for academic reuse.

### Phase 4 — Presentation & navigation
1. README: add CI status badges (`proof-lean`, `telperion-lean-e2e`); add a short
   TL;DR at the top; corrected counts; a clean README → STATUS → per-arc entry →
   "how to verify" path. Do not imply a paper exists (Phase 5).
2. Telperion tool docs: `GETTING_STARTED.md` (install → generate → **build the
   emitted Lean locally** with the pinned `leanprover/lean4:v4.32.0` toolchain +
   Mathlib olean cache), `ARCHITECTURE.md` (engine vs `bg/` research-lab
   boundary), `CONTRIBUTING.md`. Reconcile the "shapes" count and clarify that
   "skill" is (in code) a synonym for emitter/certificate technique, not a
   subsystem.
3. Per-arc entry docs so a mathematician can go straight to the BG, RH, or
   Telperion arc and find the verified-vs-open boundary and the one-command
   verification recipe.
Acceptance: a first-time visitor can, within a few minutes, understand what the
project is, what is proven vs open per arc, and how to independently verify the
kernel checks.

## 5. Out of scope (this spec)
- Phase 5 whitepaper (separate spec).
- Any change to the mathematics or the Lean proofs' content.
- Relicensing the Telperion engine (decision: keep BUSL-1.1).
- The GitLab `arda-trading` repo and its math experiment worktrees.
- Landing/closing the individual open PRs is coordinated but their *content* is
  owned by their authors; this effort ensures main reflects the true latest state
  and does not strand credible public-facing work.

## 6. Risks & mitigations
- **Overclaiming to a math audience is unrecoverable.** Mitigation: Phase 2 gates
  every claim against Lean/CI; the audit already mapped verified-vs-open per arc.
- **Attribution error (misciting or conflating AXLE vs AxiomMath, or importing the
  unconfirmed Ono framing).** Mitigation: Phase 3 cites only code-supported
  sources; explicit AXLE≠AxiomMath separation.
- **Editing a live public repo mid-flight.** Mitigation: all work on
  `docs/public-release-prep`, CI-gated PRs, no force-pushes to main.
- **Deleting/moving something load-bearing (e.g. an independent-review doc that is
  an intentional honesty artifact).** Mitigation: Phase 1 keeps the cited review
  docs; only campaign/handoff logistics move.
- **The stale canonical checkout (`~/repos/Arda`) being mistaken for source of
  truth.** Mitigation: all work off verified `origin/main` in a fresh worktree.

## 7. Acceptance (whole effort)
A mathematician landing on `github.com/DrMurphyIsIn/Arda` sees: green CI badges;
a concise, honest README; a per-arc verified-vs-open map that matches the Lean
reality; correct, formal attribution of all external work; a clear path to
independently verify the kernel checks; and no internal/operational cruft or
private-repo leakage. Telperion is documented well enough to install, run, and
locally verify one emitted certificate end-to-end.
