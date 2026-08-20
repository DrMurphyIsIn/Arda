# Telperion vs AlphaProof vs DeepSeek-Prover-V2 — head-to-head (2026-08-20)

A comparative research dive. External facts below were gathered by a multi-agent
deep-research pass (20 sources fetched, 99 claims extracted, 25 top claims
adversarially verified 3-0 each, 0 refuted). Telperion facts come from the local
repo (README, CHANGELOG, `docs/EVOLVE_RESULTS_2026-08-18.md`) — they are
first-party ground truth, not third-party audited.

## Executive verdict

All three systems rest on the **same trusted base — the Lean 4 kernel** — so none
can emit a false theorem. Everything upstream differs radically:

- **AlphaProof** (DeepMind, Nature 2025) is a closed 3B-parameter AlphaZero-style
  RL agent that reached IMO 2024 silver (P1, P2, P6) at a cost of ~180K TPU-days
  of training and 2–3 days of test-time RL per hard problem. State of the art on
  open-ended olympiad proof discovery; unavailable and irreproducible by design.
- **DeepSeek-Prover-V2** is the open-weights counterpoint: a 671B MoE (+7B
  distill) that hits 88.9% on MiniF2F-test (pass@8192) but only ~7.4% on
  PutnamBench — strong on routine competition problems, an order-of-magnitude
  cliff on hard ones.
- **Telperion** occupies a different niche: a deterministic, LLM-free-by-default
  **certificate compiler** that proves *families* of statements reducible to
  ~30 certificate shapes, at CPU-seconds cost, byte-reproducibly, with a
  soundness/vacuity discipline neither competitor has. It cannot autoformalize
  and would score near zero on general MiniF2F/IMO problems outside its shapes.

Honest bottom line: **outclassed** on open-ended search and autoformalization;
**genuinely differentiated** on determinism, cost, auditability, family-scale
certification, and vacuity defense; **best positioned as a backend, not a
competitor** — the certificate-shaped subgoals that LLM decomposition produces
are exactly what Telperion discharges.

---

## System snapshots

### AlphaProof (Google DeepMind — Nature, 2025)

- **Architecture**: AlphaZero-inspired RL agent; 3B-parameter encoder-decoder
  transformer coupled to AND/OR tree search inside Lean 4 (product nodes
  back-propagate the value of the *hardest* branch). Every found proof is
  kernel-verified and reinforces the model. [Nature s41586-025-09833-y;
  DeepMind blog; Schrittwieser blog]
- **Training corpus**: a fine-tuned Gemini autoformalizer translated ~1M
  natural-language problems into ~80M formal Lean statements (stochastic
  formalization → many variants per problem). ~80,000 TPU-days for the main RL
  run + ~100,000 TPU-days for autoformalization.
- **Test-time RL (TTRL)**: at the contest, generates a bespoke curriculum of
  synthetic variants (simplifications/generalizations) around each target and
  trains on them until the original falls. Each hard IMO solution took 2–3 days
  vs humans' two 4.5-hour sessions.
- **Results**: IMO 2024 combined AlphaProof + AlphaGeometry 2 score 28/42
  (silver band, 1 point below gold), graded by Gowers and Myers. AlphaProof
  proved P1, P2, P6 (all algebra + number theory; P6 fully solved by only 5 of
  609 humans). Both combinatorics problems (P3, P5) unsolved.
- **Openness**: closed. No weights or code; an interactive exploration tool for
  select mathematicians; the `alphaproof-nexus-results` repo contains only
  generated proofs. The paper itself concedes training is "likely beyond the
  reach of most academic research groups", TTRL inference is multi-day, and
  successes are "primarily within… competition mathematics", not
  research/theory-building.
- Note: DeepMind's IMO **2025 gold** was a *different* system (Gemini DeepThink,
  informal/natural-language) — not AlphaProof.

### DeepSeek-Prover-V2 (April 2025)

- **Architecture**: 671B MoE prover (on DeepSeek-V3-Base; 685B params in
  BF16/F8) + 7B distill (on Prover-V1.5-Base, 32K context). Cold start:
  DeepSeek-V3 recursively decomposes theorems into subgoals, a 7B prover
  resolves them, and resolved-subgoal proofs are synthesized with V3's
  reasoning into chain-of-thought data. Then GRPO-family RL on binary
  Lean-verification reward. CoT and non-CoT generation modes.
- **Results**: 88.9% on MiniF2F-test — **at pass@8192** — and 49/658 (~7.4%) on
  PutnamBench (the 7B distill solved 13 Putnam problems the 671B missed; 62/658
  combined). SOTA in open neural proving at release; since exceeded by
  Goedel-Prover-V2, Seed-Prover, Kimina-Prover (2025-26).
- **Openness**: genuinely downloadable — both sizes on Hugging Face; code MIT;
  weights under a permissive custom model license (open-weights, not strictly
  OSI open-source).
- **Caveat on the benchmark itself**: arXiv 2511.03108 documents misformalized
  statements inside MiniF2F — a reminder that autoformalization risk lives in
  the *statement*, which the kernel cannot check.

### Telperion (local; v0.1.x)

- **Architecture**: exact-arithmetic certificate compiler → Lean 4 emitter,
  ~13K lines of Python, sympy the only core dependency. Untrusted generator /
  trusted kernel: a wrong certificate is a compile error, never a false theorem.
- **~30 emitter shapes**: Pólya positivity, exact rational SOS (PSD Gram),
  Putinar/Handelman (with automatic SDP-based certificate *finding* rounded to
  exact rationals), Nullstellensatz ideal-membership / infeasibility /
  consequence via Gröbner cofactors, real Nullstellensatz, SOS refutation,
  Wilf-Zeilberger identities, Chvátal-Gomory integer rounding (VIPR-style,
  discharged by `omega`), p-adic valuations, `exp` interval brackets,
  unimodal/log-concave max localization, telescoping tree potentials, finite
  case dispatch, `∀ K ≥ K₀` tails, lattice-box integer Positivstellensatz,
  assembly/glue emitters.
- **Enforced workflow**: certify → validate → emit → lake build → freeze; SHA-256
  provenance hashing and byte-level drift detection; soundness lint refusing
  `sorry`/`axiom`/`Prop := True`; non-vacuity + certificate-load-bearing checks
  (a corrupted certificate must break the claim).
- **Search layer** (`telperion.evolve`): AlphaEvolve/OpenEvolve-style genome
  evolution scored by the exact certify→build cascade; optional local-LLM
  (Ollama) mutator, LLM-free by default. Measured 2026-08-18 (structured arm,
  laptop CPU): 5/5 trials climb from a failing seed to a certifying champion,
  median 344 sympy evaluations, ~22.5 s/trial. Honest caveats: certify-tier
  only (not kernel-verified per trial), champions came from the supplied ratio
  pool (no novel ratio without the LLM arm, which is unmeasured), and nothing
  evolve-found has been frozen into CI yet.
- **Track record**: the Brualdi-Goldwasser Laplacian-ratio campaign — 200+
  CI-green Mathlib theorems across the original batches (36-cell bilinear
  table, 36 adapters, 72 vee/mirror branches, 42 leg + 55 shedding
  certificates), with the largest frozen family (`g1_floors`: 3,084 theorems)
  compiled against pinned Mathlib in the `telperion-production` CI gate.
- **Agent surfaces**: CLI, MCP server, Claude Code plugin — all on the same
  enforced pipeline; no API path to Lean that skips certification.
- **Honest scope**: certificate compiler, not an autoformalizer; will not invent
  structural inductions; `diagnose` triages refusals into FALSE (exact rational
  counterexample) / NOT_POLYA / CERTIFIABLE rather than emitting a
  plausible-but-wrong proof.

---

## Axis-by-axis

| Axis | AlphaProof | DeepSeek-Prover-V2 | Telperion |
|---|---|---|---|
| **Problem scope** | Open-ended olympiad algebra/NT (incl. functional equations); combinatorics resisted it | Routine competition formalization; collapses on hard problems (7.4% Putnam) | Families reducible to ~30 certificate shapes: inequalities, identities, valuations, brackets, integer LP, case analysis |
| **Search strategy** | AlphaZero RL + AND/OR tree search + test-time RL curriculum | LLM subgoal decomposition + GRPO RL + massive sampling (pass@8192) | Deterministic certificate finding (Pólya lift, SDP→exact rounding, Gröbner) + optional evolutionary search |
| **Trust model** | Kernel-checked proofs; *statement* trust depends on (stochastic Gemini) autoformalization | Kernel-checked proofs; statement trust depends on benchmark formalization (MiniF2F has documented misformalizations) | Kernel-checked; statements authored by the user; adds vacuity/load-bearing lint the others lack |
| **Determinism / reproducibility** | Non-deterministic; closed, irreproducible by construction | Non-deterministic sampling; weights public so *re-runnable*, not deterministic | Byte-reproducible; SHA-256 provenance + drift net; same input → same Lean bytes |
| **Compute / cost per theorem** | ~180K TPU-days training; 2–3 TPU-days *per hard problem* at inference | 671B-scale inference × up to 8192 samples per goal | CPU-seconds to minutes on a laptop; evolve layer ~22 s/trial |
| **Openness** | Closed (results repo + limited tool only) | Open weights (custom license), MIT code | Local source, ~13K lines, auditable by a referee |
| **Autoformalization** | Yes — its central enabler (Gemini fine-tune) | Partial — informal→formal via V3 decomposition | None by design |
| **Verification guarantee** | Lean kernel | Lean kernel | Lean kernel + soundness lint + non-vacuity + certificate-sensitivity |
| **Extensibility** | Not extensible (closed) | Fine-tuning/prompting only | New emitter class inherits the whole pipeline (enforcement, provenance, lint, agent surfaces) |
| **Track record** | IMO 2024 silver (28/42), Nature paper | MiniF2F 88.9% (pass@8192), PutnamBench 49/658 | 3,000+ CI-green Mathlib theorems in one research campaign (narrow domain) |
| **Where it fails** | Combinatorics; multi-day latency; anything outside competition math; access | Genuinely hard problems; no cost/determinism guarantees | Anything outside certificate shapes; no statement invention; no induction synthesis |

## Contrast in one sentence each

- AlphaProof asks: *can RL + search discover a proof no one wrote down?* — yes,
  at nation-state compute, behind closed doors.
- DeepSeek-Prover-V2 asks: *can an open LLM write Lean tactic proofs at scale?*
  — yes for the easy 90%, no for the hard 10%.
- Telperion asks: *given a true concrete statement, can we compile a
  machine-checked proof deterministically and audit every byte?* — yes, when it
  reduces to a certificate, and it says so honestly when it doesn't.

## Where Telperion is genuinely differentiated

1. **Family scale.** Both LLM provers prove one theorem per (expensive) search
   episode. Telperion's unit of work is a *parameterized family* — 3,084
   theorems in one frozen artifact is a mode of operation neither competitor
   has any analogue for.
2. **The vacuity defense.** The kernel rejects false theorems but compiles
   true-but-vacuous ones green. Telperion's non-vacuity + load-bearing checks
   target exactly the failure class that actually bit this research program
   (the `Prop := True` R3Cert episode). Neither AlphaProof nor DeepSeek has —
   or needs, given their benchmarks — such a gate; but for *research* use it is
   load-bearing.
3. **Cost and locality.** CPU-seconds on a laptop vs TPU-days/GPU-clusters.
   Roughly 6–7 orders of magnitude in compute per theorem for in-scope targets.
4. **Provenance.** SHA-256 input hashing + byte-diff drift detection means a
   referee can verify that what CI checked is what the paper claims. Stochastic
   provers cannot offer this even in principle.
5. **A third search paradigm.** `telperion.evolve` (evolutionary search over
   certificate genomes with an exact certify→build fitness) is distinct from
   both RL and pure SDP rounding — though it is early: measured working
   end-to-end, not yet a producer of frozen proofs.

## Where Telperion is outclassed

1. **Open-ended proof discovery.** It will never solve IMO P6. No structural
   induction, no clever-lemma invention, no functional-equation reasoning.
2. **Autoformalization.** AlphaProof's ~80M-statement corpus construction is a
   capability class Telperion doesn't attempt; the user must author every
   statement.
3. **Breadth benchmarks.** On MiniF2F/PutnamBench as given, Telperion would
   score near zero — most items are not certificate-shaped as stated.
4. **Third-party validation.** AlphaProof has a Nature paper and independent
   grading by Gowers/Myers; DeepSeek has public weights anyone can re-run.
   Telperion's record is first-party, on one (hard) research domain.

## Complementarity — the real conclusion

The systems are not actually competitors; they sit at different layers:

- DeepSeek's own pipeline *already* decomposes hard theorems into subgoals, and
  many decomposed leaves are precisely Telperion-shaped: polynomial
  nonnegativity, rational inequalities, integer bounds, exact identities.
- AlphaProof's search already leans on Lean's tactic ecosystem; a deterministic
  certificate tactic is just a very strong tactic.
- Telperion's MCP/CLI surfaces mean an LLM prover could dispatch
  certificate-shaped subgoals to it today as a **sound, deterministic, cheap
  backend** — the LLM handles statement invention and proof architecture, the
  certificate compiler handles the arithmetic leaves, the kernel checks both.

Verified research found **no published system yet wiring a certificate compiler
into an LLM prover's loop as a sub-tactic** — the niche appears open.

## Caveats (from the adversarial-verification pass)

1. No claims about the broader symbolic landscape (polyrith, positivity, VIPR,
   CoqInterval, Lean SOS) survived verification, and no published head-to-head
   of certificate compilers vs LLM provers on inequality problems was found —
   the landscape/complementarity sections are reasoned synthesis, not
   measurement.
2. Per-category (inequality vs combinatorics) benchmark breakdowns for
   AlphaProof/DeepSeek were not confirmed — the most decision-relevant slice is
   unmeasured.
3. All AlphaProof claims trace to DeepMind-affiliated sources by construction
   (the system is closed).
4. Field moves fast: Goedel-Prover-V2, Seed-Prover, Kimina-Prover exceed
   DeepSeek-V2's numbers as of 2026-08; DeepSeekMath-V2 (Nov 2025, informal,
   118/120 on Putnam 2024) is a separate line from the Lean prover.
5. Telperion's side of every comparison is first-party ground truth, unaudited
   by third parties.

## Open questions worth pursuing

- Measure AlphaProof/DeepSeek-class provers on the *Telperion-overlap class*
  (certificate-shaped inequalities) specifically.
- Prototype the backend thesis: expose `telperion certify`/`diagnose` as a Lean
  sub-tactic or MCP tool inside an LLM prover loop and measure the lift.
- Track DeepSeek prover follow-ups through 2026 (does anything close the
  MiniF2F→Putnam cliff?).
- A dollar-denominated cost-per-theorem comparison (TPU-days vs pass@8192 GPU
  sampling vs CPU-minutes) — no source quantifies this in comparable units.

---

# FRONTIER EXTENSION — the 2025-2026 field (added 2026-08-20)

The sections above benchmark Telperion against AlphaProof (2024) and
DeepSeek-Prover-V2 (April 2025). Both are now behind the frontier. This
extension covers the systems that have since passed DeepSeek-V2 and re-scores
Telperion against them. **Verification note:** the deep-research pass that
gathered these facts had its 3-vote verifier abstain under a spend limit
(logged as "refuted 0-0", a false negative, not a real refutation). Every
load-bearing number below was therefore **cross-checked by hand** against the
primary source (arXiv abstract, GitHub README, HuggingFace card, or vendor
blog) — citations inline. Treat these as operator-verified, not workflow-verified.

## The two headline updates since the first report

1. **MiniF2F is effectively saturated at the frontier.** The "88.9%" that anchored
   the DeepSeek-V2 section is no longer a discriminating number. Seed-Prover
   "saturates MiniF2F"; Goedel-Prover-V2-32B hits 90.4% (self-correction, pass@32);
   Kimina-Prover-72B reaches 92.2% with test-time RL. The benchmark has stopped
   separating the top systems.

2. **The PutnamBench "hard cliff" is closing — fast.** The first report called
   DeepSeek's 49/658 (~7.4%) "the clearest quantitative evidence LLM provers still
   fail on genuinely hard formal mathematics." That claim has substantially
   eroded in ~8 months:
   - Goedel-Prover-V2-32B: **86/658 (~13%)** at pass@192 — nearly double DeepSeek's
     count at ~1/20 the model size and ~1/5 the sample budget.
   - Seed-Prover (base): **>50% of PutnamBench**.
   - Seed-Prover 1.5 (Dec 2025): **88% of PutnamBench**, plus 11/12 on Putnam 2025
     in a 9-hour run.
   The single biggest correction to the first report: the "hard formal math breaks
   LLM provers" thesis is now largely a 2024-early-2025 artifact at the very
   frontier. It still holds for *small/open, small-budget* provers.

## Frontier system snapshots (all numbers operator-cross-verified)

### Goedel-Prover-V2 (Princeton et al., Aug 2025) — the open efficiency win
- **8B and 32B**, weights on HuggingFace under **Apache 2.0** (the most permissive
  license in the field). Method: scaffolded synthetic-data curriculum +
  verifier-guided self-correction (Lean compiler feedback) + checkpoint model
  averaging. Pure LLM+search+verifier; no symbolic backend.
- MiniF2F-test: 32B **88.0%** pass@32 standard, **90.4%** self-correction; the **8B
  matches DeepSeek-Prover-V2-671B (~100x larger)** at 84.6%.
- PutnamBench: 32B solves **57 at pass@32, 86 at pass@192**, vs DeepSeek-671B's
  22/47 — first place among open models.
- [github.com/Goedel-LM/Goedel-Prover-V2]; paper arXiv 2508.03613.

### Seed-Prover / Seed-Prover 1.5 (ByteDance Seed) — the hard-math frontier
- **Closed** (report + some materials on GitHub, no open weights). Lemma-style
  whole-proof reasoning, iterative Lean-feedback refinement, three test-time
  search tiers (deep + broad), Seed-Geometry companion. Agentic RL.
- Base (Jul 2025): saturates MiniF2F, **>50% PutnamBench**, **78.1% of past IMO
  problems**, and **formally proved 5/6 IMO 2025 problems in Lean** (P1 solved
  post-competition; graded silver-equivalent under contest timing).
- 1.5 (Dec 2025): **88% PutnamBench**, 80% Fate-H (graduate), 33% Fate-X (PhD),
  **11/12 Putnam 2025 in 9 hours**. Trained by large-scale agentic RL + test-time
  scaling.
- arXiv 2507.23726 (base), 2512.17260 (1.5); seed.bytedance.com blog.

### Kimina-Prover-72B (Numina + Moonshot/Kimi) — open RL reasoning
- **Qwen2.5-72B** base, multi-stage RL (Kimi k1.5 pipeline), a learned "formal
  reasoning pattern" that interleaves informal sketch with Lean rather than pure
  tactic tree-search. Preview open-sourced 1.5B/7B distills; **72B later released
  on HuggingFace under MIT**.
- MiniF2F-test: **84.0%** pass@32, **87.7%** pass@1024, **92.2%** with test-time RL
  lemma search — beating the ~9x larger DeepSeek-671B at every matched budget.
- arXiv 2504.11354; huggingface.co/AI-MO/Kimina-Prover-72B + AI-MO blog.

### Harmonic Aristotle (commercial) — formal IMO 2025 gold
- **Closed / commercial** (API product; ~$295M raised total, $120M Series C Nov
  2025 at $1.45B valuation). Three-part system: Lean proof search + an informal
  reasoning engine that *generates and formalizes lemmas* + a dedicated geometry
  solver.
- **IMO 2025: formally verified Lean 4 proofs for 5/6 problems** (gold-equivalent),
  failing only P6 (unsolved by every gold-level AI). Solutions required to be
  complete Lean 4 + Mathlib, **no `sorryAx`, no unsound axioms** — the same
  kernel-soundness bar Telperion enforces.
- arXiv 2510.01346; Harmonic announcements.

### The informal track — a category distinction that matters
- **Gemini DeepThink** (DeepMind) reached **IMO 2025 gold, but *informally*** —
  natural-language solutions graded by humans, not kernel-checked Lean. Not an
  AlphaProof successor.
- **DeepSeekMath-V2** (Nov 2025): self-*verifying* informal math, 118/120 on
  Putnam 2024 — but "self-verified" is an LLM checking an LLM, **not a kernel
  guarantee**. A wrong self-verification produces a wrong-but-confident proof, the
  exact failure mode formal systems exist to preclude.
- Also new: **Aleph** (Logical Intelligence) reporting strong PutnamBench results;
  **ProofOptimizer** (proof simplification); ongoing Erdős-problem formalization.

## Re-scoring Telperion against the 2026 frontier

### Newly outclassed (the gap widened)
- **Raw capability on hard formal math.** The differentiator the first report
  leaned on — "these provers collapse on Putnam" — is mostly gone at the frontier
  (Seed-Prover 1.5 at 88%). Telperion proves *none* of PutnamBench as stated; on
  the breadth axis it is further behind than it was 8 months ago.
- **Formal IMO gold is now table stakes**, achieved by ≥2 systems (Aristotle,
  Seed-Prover) in kernel-checked Lean with the same no-`sorry`/no-axiom bar
  Telperion advertises. "We emit sound Lean" no longer distinguishes anyone.

### Still genuinely differentiated (and the gap *widened in Telperion's favor*)
- **Determinism, reproducibility, provenance.** Every frontier system is
  stochastic test-time search; none offers byte-reproducibility, SHA-256 input
  hashing, or drift detection. As the field scales *up* in nondeterminism,
  Telperion's audit story becomes *more* unusual, not less.
- **Cost and hardware.** The frontier is moving the opposite direction from
  Telperion: Seed-Prover 1.5 spent **9 hours** on Putnam 2025; Goedel needs
  pass@192; Aristotle/Seed are GPU-cluster systems. Telperion is CPU-seconds on a
  laptop, no GPU. The compute gap per in-scope theorem is now larger, in
  Telperion's favor.
- **Family scale.** Still no analogue anywhere — frontier provers are one-theorem-
  per-search-episode. Telperion's 3,084-theorem frozen family is a different unit
  of work.
- **Vacuity / load-bearing defense.** DeepSeekMath-V2's self-verification track
  makes this *more* relevant: "the checker can be fooled" is precisely the risk
  Telperion's non-vacuity + certificate-sensitivity lint targets. Kernel-checked
  systems (Aristotle, Seed, Goedel) close the false-theorem hole but none of them
  publishes a vacuity gate.
- **Auditable small artifact.** ~13K lines, sympy-only, referee-readable — versus
  72B–671B weights or closed APIs.

### Answers to the three critical questions
1. **Is the easy/hard cliff closing?** Yes, decisively at the closed/large frontier
   (Seed-Prover 1.5 88% Putnam), partially at the open/efficient frontier (Goedel
   13%). MiniF2F is saturated and has stopped being informative.
2. **Has anyone occupied the certificate/symbolic-backend niche?** **No.** Every
   system surveyed — Goedel, Seed, Kimina, Aristotle — is LLM+RL+search with a Lean
   *verifier* in the loop. None uses deterministic certificate compilation (SOS,
   Positivstellensatz, Nullstellensatz, WZ, CG). The Telperion niche is still
   empty. Crucially, they *all* now have a verifier-in-the-loop architecture —
   which is exactly the socket a certificate tactic plugs into.
3. **Does informal self-verification devalue kernel-checked proving?** No — it
   *revalues* it. DeepSeekMath-V2 and DeepThink show impressive informal results,
   but "self-verified" is not "kernel-verified"; the value of a machine-checked
   proof (and of a vacuity gate on top) is higher, not lower, once the field starts
   shipping confident-but-unchecked informal proofs.

### The complementarity thesis is stronger than in the first report
Two frontier developments turn the "Telperion as backend" idea from speculation
into an obvious integration:
- **Aristotle already has an "informal reasoning engine that generates and
  formalizes lemmas."** Those lemmas are frequently certificate-shaped
  (inequalities, positivity, identities) — exactly Telperion's discharge class. A
  certificate backend would let such a system *prove* the lemma deterministically
  instead of searching for a tactic proof.
- **Every frontier prover now runs a Lean-compiler-feedback loop.** A deterministic
  `telperion certify`/`diagnose` exposed as a Lean tactic or MCP tool is a drop-in
  strong tactic for that loop — cheap, sound, and it returns a *rational
  counterexample* on failure (FALSE triage) that a stochastic prover cannot.
- Still no published integration of a certificate/SOS backend into an LLM prover
  loop was found — the niche remains open and now has more, and more capable,
  hosts to plug into.

## Bottom line vs the 2026 frontier
Telperion is **more outclassed on breadth** (hard formal math is no longer a moat)
and **more differentiated on discipline** (determinism, cost, provenance, vacuity,
auditability) than it was against the 2024-25 baselines — the frontier moved toward
bigger, slower, more stochastic, more closed, while Telperion's value is small,
fast, reproducible, open, auditable. It is not, and should not try to be, an
olympiad prover. Its defensible 2026 position is a **deterministic certificate
backend and family-scale compiler** that the very systems now saturating MiniF2F
would benefit from calling — the integration case is stronger today than at the
first report.

## Frontier extension — sources (operator-cross-verified, not workflow-verified)

- Goedel-Prover-V2: https://github.com/Goedel-LM/Goedel-Prover-V2 · https://arxiv.org/abs/2508.03613 · https://huggingface.co/Goedel-LM/Goedel-Prover-V2-32B
- Seed-Prover: https://arxiv.org/abs/2507.23726 · https://seed.bytedance.com/en/blog/bytedance-seed-prover-achieves-silver-medal-score-in-imo-2025 · https://github.com/ByteDance-Seed/Seed-Prover
- Seed-Prover 1.5: https://arxiv.org/abs/2512.17260 · https://seed.bytedance.com/en/blog/seed-prover-1-5-advanced-mathematical-reasoning-through-a-novel-agentic-architecture
- Kimina-Prover: https://arxiv.org/abs/2504.11354 · https://huggingface.co/AI-MO/Kimina-Prover-72B · https://huggingface.co/blog/AI-MO/kimina-prover
- Harmonic Aristotle: https://arxiv.org/abs/2510.01346 · https://cryptobriefing.com/harmonic-aristotle-ai-imo-gold-medal/
- Gemini DeepThink (informal IMO 2025 gold): https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/
- Aleph / PutnamBench: https://logicalintelligence.com/blog/aleph-solves-putnambench

---

## Key sources — first report (all claims 3-0 verified)

- AlphaProof Nature paper: https://www.nature.com/articles/s41586-025-09833-y
- DeepMind IMO-silver blog: https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/
- Schrittwieser (co-author) paper walkthrough: https://www.julian.ac/blog/2025/11/13/alphaproof-paper/
- Zahavy (co-author) project page: https://www.tomzahavy.com/projects/alphaproof
- DeepSeek-Prover-V2 paper: https://arxiv.org/abs/2504.21801
- DeepSeek-Prover-V2-671B weights: https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-671B
- DeepSeek-Prover-V2 repo: https://github.com/deepseek-ai/DeepSeek-Prover-V2
- MiniF2F misformalization audit: https://arxiv.org/abs/2511.03108
- AlphaProof results repo (proofs only, not the system): https://github.com/google-deepmind/alphaproof-nexus-results
