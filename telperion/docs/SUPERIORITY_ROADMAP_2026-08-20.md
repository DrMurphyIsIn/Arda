# Telperion superiority roadmap — sequential implementation plan (2026-08-20)

Derived from the frontier comparison
([COMPARISON_ALPHAPROOF_DEEPSEEK_PROVER_V2](COMPARISON_ALPHAPROOF_DEEPSEEK_PROVER_V2_2026-08-20.md)).

## The strategic frame (why this ordering)

Telperion cannot out-discover LLM+RL provers on open-ended olympiad proving —
that is a compute race against DeepMind/ByteDance/Harmonic. The defensible path
to "superior to all" is to **own the axis the frontier is vacating** as it scales
toward bigger/slower/stochastic/closed: soundness-by-construction, determinism,
byte-reproducibility, laptop-cost, family-scale, and — via a tactic — becoming the
certificate backend those systems are *incomplete without*. Every frontier prover
now runs a Lean-verifier-in-the-loop; none has a deterministic certificate backend;
the niche is empty. This roadmap makes Telperion #1 on that axis and indispensable
on theirs.

## Dependency structure

```
Phase 0  atomic prove_goal()  ─────────┬──> Phase 1 (Lean tactic + backend lift)
  (single-goal certify→emit│triage)    ├──> Phase 2 (certifiable-fragment benchmark)
                                        └──> Phase 5 (LLM statement front-door)
Phase 3 (proof-auditor mode) ── mostly independent (builds on lint-lean + nonvacuity)
Phase 4 (combinatorics emitters) ── independent research track
Phase 6 (evolve → real discovery) ── builds on telperion.evolve
```

Phase 0 is the keystone: bets #1, #2, #5 all need a single-goal atomic op that
does not exist today (everything is family/project-scoped). Build it first.

---

## Phase 0 — Atomic `prove_goal()` (FOUNDATION) — START HERE

**Why first.** An external prover loop, a benchmark harness, and an
autoformalization front-door all need the same primitive: *give me one goal, get
back a self-contained Lean proof term or a triage (FALSE + counterexample /
NOT_POLYA + hints / CERTIFIABLE-but-unemitted)*. Telperion today only exposes
`certify(family)` + `emit(...)` over grids and scaffolded projects.

**Deliverable.**
- `telperion.prove.prove_goal(target, symbols, ...) -> ProofResult` — wraps a
  single scalar inequality `0 ≤ target` in a 1-instance family, runs
  certify→emit through an emitter ladder, returns Lean text + emitter name +
  reported axioms; on refusal, runs `diagnose` and returns the triage.
- `ProofResult` dataclass: `proved`, `lean`, `emitter`, `verdict`,
  `counterexample`, `detail`.
- CLI: `telperion prove "<expr>" --symbols u,v` (Lean to stdout, triage to
  stderr, exit code encodes proved/false/not-polya).
- MCP tool: `prove_goal(expression, symbols)` — the backend socket for agents.
- Tests: proved case (known-good rational inequality), FALSE case (returns
  rational counterexample), NOT_POLYA case (returns hints). No Lean build in the
  unit test — emitted text checked structurally + soundness-linted; CI compiles.

**Definition of done.** `prove_goal` green on all three triage branches, CLI +
MCP wired, soundness-lint clean on emitted output, no regression in existing tests.

**Scope note.** v1 targets the rational-inequality → DirectPolya path (the most
common competition/benchmark leaf) with an SOS fallback; the full ~30-emitter
auto-router (kind detection → Putinar/Handelman/WZ/CG/...) is Phase 0.1.

---

## Phase 1 — Lean tactic + backend-lift measurement (BET #1, highest leverage)

**Why.** The empty niche + the publishable result. Prove that an LLM prover +
Telperion backend beats the prover alone on certificate-shaped subgoals.

**Deliverable.**
- A Lean `telperion` tactic shim: from inside a Lean proof, serialize the goal,
  call `prove_goal` (via CLI/MCP), splice back the returned proof term. Ships as
  a small Lean file + Python bridge; degrades to `diagnose` triage on refusal.
- An integration harness against an *open* prover (Goedel-Prover-V2, Apache-2.0)
  on the inequality subset: measure problems solved by prover-alone vs
  prover+Telperion-backend, and the cost delta (Telperion is CPU-seconds vs
  pass@N sampling).
- Writeup: the first published certificate-backend-in-LLM-loop integration.

**Blocked-on.** The prover run needs GPU/cloud (no local GPU; local Lean builds
crash this machine — use cloud CI). The tactic shim + harness *scaffold* are
local; the measured run is cloud.

**Definition of done.** Reproducible harness + a real lift number on the
inequality subset, with cost accounting.

---

## Phase 2 — Own the certifiable-fragment benchmark (BET #2)

**Why.** Convert "narrow" into "dominant on this slice." Be deterministically #1
where stochastic provers burn pass@thousands.

**Deliverable.**
- Curate the certificate-shaped subset of PutnamBench + inequality-heavy
  competition problems into a named benchmark (`bench/certifiable_fragment/`).
- Run `prove_goal` over it; report deterministic solve rate + wall-clock, next
  to published stochastic-prover numbers on the same items.
- Honest labeling of coverage (what is out-of-shape and why — `diagnose` triage
  distribution).

**Definition of done.** A table: Telperion (deterministic, CPU-s) vs frontier
provers (pass@N, GPU) on the same certifiable items.

---

## Phase 3 — Proof-auditor mode (BET #4, parallelizable early)

**Why.** As the field ships confident informal/self-verified proofs
(DeepSeekMath-V2), a machine-checkable vacuity/soundness auditor for *anyone's*
Lean output is an axis no one occupies. Wedge: audit their output.

**Deliverable.**
- `telperion audit <file.lean>` — runs the existing soundness lint
  (`lean_lint`) + non-vacuity + certificate-load-bearing checks over
  externally-authored Lean (not just Telperion-emitted), reporting
  sorry/axiom/`Prop := True`/reflexive-statement/unused-hypothesis findings.
- Extend `nonvacuity` to accept arbitrary theorem statements, not only
  Telperion's own emissions.

**Definition of done.** Runs on a third-party Lean proof and flags a seeded
vacuity defect; clean on a known-good proof.

---

## Phase 4 — Combinatorics certificate emitters (BET #3, research track)

**Why.** Compete where the frontier is *weakest*, not strongest — combinatorics
(IMO 2024 P3/P5 unsolved by every system). A deterministic combinatorial-bound
certificate is superiority on the axis LLM provers fail.

**Deliverable (staged).**
- Survey which combinatorial bound families reduce to existing shapes
  (lattice-box / CG / WZ already cover integer-linear + hypergeometric).
- New emitters for the gaps: double-counting/injection bounds, symmetric-
  inequality certificates (Schur/SOS-Schur, tangent-line trick), and a
  finite-structure exhaustion emitter.
- Each: certify→emit→freeze, per the standard pipeline (inherits enforcement).

**Definition of done.** ≥1 new combinatorial family CI-green end-to-end.

---

## Phase 5 — LLM statement front-door (BET #5)

**Why.** Close the one genuine gap (natural-language → formal statement) without
becoming a stochastic prover. LLM proposes statement + certificate *guess*;
deterministic core certifies or rejects; kernel checks. Trust model untouched.

**Deliverable.**
- `telperion formalize "<informal statement>"` — local-LLM (Ollama, reusing the
  evolve arm) emits a candidate formal `target` + symbols; hands to `prove_goal`.
  The LLM never touches the proof; a wrong formalization is rejected by
  certification or produces a checkable (possibly vacuous → caught) theorem.
- Faithfulness gate: the emitted statement must pass `faithfulness_check`
  against the informal intent's numeric instances.

**Definition of done.** End-to-end on a handful of informal inequalities;
LLM-free core path unchanged and still default.

---

## Phase 6 — Evolve → real certificate discovery (BET #6)

**Why.** Make "search strategy" a strength: hybrid local-LLM-proposes-shape +
exact-core-scores is a cheaper, reproducible alternative to 671B tactic search
for the certifiable class. Today the evolve layer is measured but has never
frozen a proof.

**Deliverable.**
- Drive the evolve loop end-to-end on a real open sub-certificate until it
  produces a champion that passes the *kernel* gate (not just the certify tier)
  and gets frozen into CI — the missing milestone from `EVOLVE_RESULTS`.
- Wire the LLM mutator arm (currently unmeasured) and report novel-ratio rate.

**Definition of done.** ≥1 evolve-discovered certificate frozen + CI-green.

---

## Honest caveats on the whole program

- This does **not** produce an IMO-gold headline and should not try to. Success =
  dominant-and-indispensable on the soundness/determinism/cost/family axis.
- Phases 1, 4, 6 have real research risk (a measured lift, a combinatorial
  emitter, a kernel-frozen evolve champion may each prove harder than scoped).
  Phases 0, 2, 3, 5 are mostly engineering.
- GPU/cloud is required for the *measured* prover integration (Phase 1) and any
  local Lean compilation — this machine builds Lean only in cloud CI.
- `conjecture1_proved` discipline applies throughout: no phase claims done until
  its definition-of-done is met with evidence, not assertion.

## Execution order

**0 → (1 ‖ 2 ‖ 5) → 3 (anytime) → 4 (research) → 6 (research).**
Start: Phase 0, `prove_goal`.
