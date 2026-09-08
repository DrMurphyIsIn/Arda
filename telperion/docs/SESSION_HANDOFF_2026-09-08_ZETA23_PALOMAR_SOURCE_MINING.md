# Session handoff — zeta-23 distillation + Palomar/source mining (2026-09-08)

For parallel Arda sessions. This session distilled the Anthropic **zeta-23-lean**
result into Telperion emitters + a reusable prelude, then built a **Palomar
certificate-mining module** and generalized it into a **multi-source monitoring
subsystem** (arXiv/GitHub/Zulip). Three PRs open; a weekly local poll installed.
`conjecture1_proved = False` throughout — this is positive-proportion / reduction
/ frontier-tracking tooling, NOT a path to RH.

## TL;DR status

| PR | Branch / worktree | What | CI |
|----|-------------------|------|----|
| **#326** | `feat/hermitian-moment-emitters` / `~/arda-hermitian-emitters` | HermitianMomentInertia emitters (`two_moment_count`, `rank_trace_scalar`) + RHLinalg Lean prelude + axiom guard | `hermitian-moment-compiles` **PASS**; `unit`/`g1`/`r47` fail (see CI note) |
| **#327** | `feat/palomar-mining` / `~/arda-palomar-mining` | Palomar registry miner + recurring `poll` + RSS reader + RH/BG source docs | inherits main red |
| **#328** | `feat/source-mining` / `~/arda-source-mining` | Source-monitoring subsystem (arXiv+GitHub+Zulip adapters over the miner) — **stacks on #327** | inherits main red |

**None are merge-ready yet — but the red is a PRE-EXISTING broken `main`, not this work.**

## CI reality (READ THIS before merging anything)

`main` HEAD (`42395ba`) is **already red**: `telperion-test` (all `unit` matrix legs)
and `telperion-production` (`g1-compiles`, `r47-regen-diff`) both FAIL on `main`.
All three PRs inherit that baseline. Evidence it's not ours: `g1-compiles` /
`r47-regen-diff` fail fast (12–23s) identically on the pure-Python miner branches
(#327/#328) that touch no Lean and no emitter — impossible for a docs+miner change
to break a Lean compile job. **Someone's parallel session broke `main`; that blocks
everyone.** Triage that first. (A full local-suite triage was running at handoff to
enumerate the exact failing tests; append results here.)

What is genuinely GREEN and ours:
- #326 `hermitian-moment-compiles` **passes** → the RHLinalg port compiles clean under
  Mathlib **v4.32.0** (retires the v4.33→v4.32 drift risk in `PORT_NOTES.md`).
- All new Python tests pass locally (10 hermitian_moment, 13 palomar_mine, 20 source_mining).

### Full-suite local triage (2026-09-08, `feat/source-mining`): 13 failed / 1595 passed / 106 skipped
**None of the 13 are in this session's new test files** — this work adds zero failures in
its own surface. Categorized:
- **6 x Python-3.9-ONLY artifact (pass on CI 3.11+):** `test_rhinbox` x4, `test_winding_count`,
  `test_dvp_box` all die at `examples/zeta_zero_localization/generate.py:305: TypeError:
  unsupported operand type(s) for |: 'type' and 'NoneType'` — a PEP-604 `X | None` used at
  RUNTIME (not a string annotation), which only works on Python >=3.10. The local system
  interpreter is Python **3.9**; CI uses 3.11-3.13, so these are NOT CI failures. (Still a
  latent portability bug in that RH-box generate.py worth a `from __future__ import
  annotations` fix — NOT this session's file.)
- **1 x inherited, FIXED in #326:** `test_certificate_sensitivity::test_every_emitter_is_classified`
  (EndpointGeomCap). Fails on #327/#328 (they lack the fix), green once #326 lands.
- **6 x pre-existing regen/idempotency/byte-stability** in untouched modules: `test_bg_family`,
  `test_bg_floor` (+families, +r7_facets), `test_bernoulli_external` (byte-stable-vs-frozen),
  `rh_jensen/test_end_to_end_d2` (needs a Lean toolchain). Several are likely also local-env
  (frozen artifacts generated under a different Python/sympy than local 3.9); the remainder
  are part of `main`'s pre-existing red. **TODO for whoever fixes main: re-run on CI 3.11+ /
  clean-main to split env-artifact from genuine breakage.**

Net: merge-blocked ONLY by `main`'s pre-existing red + the `EndpointGeomCap` fix living in #326.
This session introduces no new test failure.

**Recommended merge order once `main` is green:** #326 → #327 → #328.

## FOOTGUNS for parallel sessions

- **`EndpointGeomCapEmitter` classification.** #326 classifies the pre-existing
  unclassified `EndpointGeomCapEmitter` in `emitter_sensitivity.REGISTRY` (to green
  `test_every_emitter_is_classified`). If another session also classifies it →
  trivial merge conflict on one dict entry. Coordinate: let #326 own that fix.
- **`MiningCandidate` gained fields** `source_name` + `lead_type` (defaults preserve
  Palomar behavior). #328 depends on these; they live in `palomar_mine.py` (shared).
- **New launchd agent** `com.telperion.palomar-poll` (deliberately NOT `com.arda.*`
  so it stays clear of `arda-drift`/collision-guard). See "Weekly poll" below.
- **Worktrees added this session:** `~/arda-hermitian-emitters`, `~/arda-palomar-mining`,
  `~/arda-source-mining`. All off `github.com/DrMurphyIsIn/Arda`.

## 1. zeta-23-lean distillation (#326)

Source: `github.com/anthropics/zeta-23-lean` (arXiv:2608.13637, "≥2/3 of ζ zeros
simple + on the critical line", author a Claude model). Uses comparator + nanoda +
landrun (same stack as `reference_comparator_integration`).

- **Emitters** (`emit_hermitian_moment.py`): `TwoMomentCountEmitter` (§6 count cert
  `(2−κ)N−err ≤ count`, κ=1/λ+λ/3; λ=1→2/3, c=3→5/6; nlinarith off `Real.sqrt_le_sqrt`)
  and `RankTraceScalarEmitter` (integrality atom `2c·x−c² ≤ x²`). Wired into
  `_SPECIAL_KINDS` + `_SPECIAL_DISPATCH` + sensitivity `REGISTRY`.
- **RHLinalg prelude** (`examples/hermitian_moment/lean/`, 8 files, v4.32.0,
  `AxiomGuardRHLinalg.lean`): the §3 matrix core (Sylvester inertia, von Neumann trace,
  rank-trace, Inertia). **SCOPING CORRECTION:** these matrix lemmas are a PRELUDE
  library, NOT emitters (can't hand a concrete matrix's rank/posIndex to the kernel
  cheaply). Generator-shaped emitters = scalar/count/enclosure only.
- **Honesty seam:** emitters certify the linear-algebra half; the two moment bounds
  enter as theorem HYPOTHESES (analytic trust seam), like RH-in-a-box's Arb inputs.
- **Second-pass catalog** (`SECOND_PASS_EMITTER_CATALOG.md`): 8 more shapes; top =
  `EnclosureIntervalFold` (NumericCert/RowCert), `ArgumentVariationCount` (RvM/Backlund),
  `ReflectionHalving` (RvM/Halving, NEW generic symmetry-orbit count).

## 2. Palomar mining (#327) + 3. source subsystem (#328)

- `palomar_mine.py`: pure `classify_entry`/`mine`/`mining_report` (topic lexicons
  rh/bg/pvsnp × shape rules → existing `kind` or NEW candidate) + `poll` (seen-state
  diff) + `fetch_registry`/`fetch_feed`/`parse_feed` (recent.json + RSS; CDN needs a
  User-Agent, 403s the default).
- `source_mining.py`: `Source` adapter interface + `lead_type` (FORMALIZED=already
  Lean-verified→port lead; RAW=unformalized→formalize-first) + `poll_source` +
  `build_source` + arXiv adapter. Adapters: `source_mining_github.py` (mathlib4/
  formal-conjectures/PrimeNumberTheoremAnd/compfiles commits, formalized),
  `source_mining_zulip.py` (Lean Zulip REST, raw, env-cred-gated graceful no-op).
- CLI: `telperion source-mine --source all|palomar|arxiv|github|zulip [--poll --state-dir …]`.
- Palomar has **no push webhook**; RSS + JSON are pull-only → weekly cadence.

### Top LEADS the miner surfaced (curated in PALOMAR_RH_SOURCES.md / PALOMAR_BG_SOURCES.md)
- **Li's criterion is ALREADY formalized** upstream: `nicholasbulka/li-criterion-rh-equivalence-lean`
  (RH ⟺ all Li–Keiper coeffs of ξ have Re≥0). → build a **Li positivity-ladder emitter**
  ONTO this reduction (highest-value next build; RH-roadmap Track 2).
- `teal-sea/zeta-lab`: Farmer–Gonek–Lee pair-corr form factor (κ-optimization for
  TwoMomentCount) + **Davenport–Heilbronn** = the negative control for these emitters.
- `savarin/lean-spectral-theory`: unbounded self-adjoint spectral thm → unlocks a
  Hilbert–Pólya statement (Track 4).
- BG: permanent entries (`sun-cotangent-permanent`, `beyond-bethe`), König–Egerváry
  matching, Bollobás–Nikiforov (Laplacian eigenvalue PSD).

## Weekly poll (installed locally, needs your activation)

- `~/Library/LaunchAgents/com.telperion.palomar-poll.plist` (Mon 09:00 local) →
  `~/.telperion/source_poll.py` → `source-mine --poll --source all --min-score 3`,
  per-source state `~/.telperion/source-seen/`, reports `~/.telperion/reports/`.
- **NOT auto-loaded** (launchctl bootstrap failed from the non-GUI agent shell, err 125).
  Activate from a login shell: `launchctl bootstrap gui/$(id -u) ~/Library/LaunchAgents/com.telperion.palomar-poll.plist`
  (else it loads at next login). Verified working manually: 44 leads run 1, 0 on re-poll.
- **Zulip** contributes nothing until `ZULIP_EMAIL`/`ZULIP_API_KEY` are set (bot key needed).

## Next steps (priority)
1. **Triage + fix `main`'s pre-existing red** (unit + g1-compiles + r47-regen-diff) — blocks all merges.
2. Merge #326 → #327 → #328 once main is green.
3. Build the **Li positivity-ladder emitter** on `li-criterion-rh-equivalence-lean` (Track 2).
4. Wire **Davenport–Heilbronn as the negative control** for the HermitianMomentInertia family.
5. Provision a Zulip bot key to activate that source.

Memory: `reference_palomar_zeta23_telperion.md` (+ MEMORY.md index line).
Roadmap context: RH-reductions 5-track roadmap (Jensen-Pólya / Li / Weil positivity /
Hilbert-Pólya spectral / function-field-F1); see `project_rh_zero_free_formalization`.
