# Telperion Whitepaper Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Write a compilable, arXiv-ready LaTeX preprint presenting Telperion as a system, with honestly-scoped BG / RH / proof-complexity case studies.

**Architecture:** A modular LaTeX document under a new top-level `paper/`: `main.tex` inputs `sections/*.tex`; `references.bib` holds citations. The paper is kept **compilable from the first task** (the writing analogue of "tests pass") and every factual claim is pinned in this plan to a named Lean theorem or executable check so prose stays accurate and never overclaims.

**Tech Stack:** LaTeX (article class), `latexmk -pdf`, BibTeX/`references.bib`. No code.

**Spec:** `docs/superpowers/specs/2026-09-05-whitepaper-design.md`

## Global Constraints

- **Tone (every section):** conversational and approachable AND exact. Motivate before formalizing; active voice / first-person plural; plain-language gloss beside every precise statement; explain jargon on first use; honesty reads as confidence. Verbatim from spec §4.
- **Honesty guardrails (every section):** every "verified" claim traces to a named Lean theorem or executable check; `conjecture1_proved = False` stated plainly; special cases never presented as the general conjecture; novelty marked provisional/un-lit-checked.
- **Forbidden vocabulary (hard gate, grep-checked):** the words `resolution`, `fully machine-checked`, `solved`, `breakthrough` (case-insensitive) must not appear as claims about this work.
- **Compile-green invariant:** `cd paper && latexmk -pdf main.tex` must succeed with no undefined-reference or undefined-citation warnings after every task.
- **RH is not claimed; the classical BG conjecture is open.** Both stated explicitly in their case studies.
- **Toolchain fact:** every Lean result cited was checked against pinned `leanprover/lean4:v4.32.0` + Mathlib v4.32.0.
- **Attribution:** AXLE (arXiv:2606.26442) and AxiomMath/ZetaZeros (arXiv:2609.02882) are distinct; cite exactly as in the repo's `NOTICE.md`.

---

### Task 1: Compilable paper skeleton

**Files:**
- Create: `paper/main.tex`, `paper/sections/{01-intro,02-system,03-vacuity,04-bg,05-rh,06-proofcomplexity,07-evaluation,08-related,09-conclusion}.tex`, `paper/Makefile`, `paper/README.md`
- Create (empty for now): `paper/references.bib`

**Interfaces:**
- Produces: `main.tex` with `\input{sections/NN-name}` for each section; each section file contains only its `\section{...}` heading and a one-line placeholder sentence; `paper/Makefile` with a `pdf` target running `latexmk -pdf main.tex`.

- [ ] **Step 1: Write `main.tex`** — `\documentclass[11pt]{article}`, `amsmath,amsthm,amssymb,hyperref,cleveref,booktabs`, a `\title{Telperion: certificate compilation for Lean 4, and three case studies}`, author placeholder `\author{Peter W. Murphy}`, `\begin{document}\maketitle\begin{abstract}TODO abstract\end{abstract}`, then the nine `\input` lines, then `\bibliographystyle{plain}\bibliography{references}\end{document}`.
- [ ] **Step 2: Write the nine section stubs** — each file: `\section{<title>}` + one placeholder sentence so the build has content.
- [ ] **Step 3: Write `paper/Makefile`** — `pdf:\n\tlatexmk -pdf main.tex` and `clean:\n\tlatexmk -C`.
- [ ] **Step 4: Compile** — Run `cd paper && latexmk -pdf main.tex`. Expected: `main.pdf` produced, exit 0. (If `latexmk` is absent, use `pdflatex main.tex` twice.)
- [ ] **Step 5: Commit**

```bash
git add paper/
git commit -m "docs(paper): compilable LaTeX skeleton"
```

---

### Task 2: Bibliography (`references.bib`)

**Files:** Modify: `paper/references.bib`

**Interfaces:** Produces the citation keys used by later tasks: `brualdi1984`, `dlvp1896`, `lean4`, `mathlib`, `axiommath_zetazeros` (arXiv:2609.02882), `axle` (arXiv:2606.26442), `tenproofs`, `comparator`, `nanoda`, `positivstellensatz` (a standard Putinar/Handelman reference), `lasserre_sos`.

- [ ] **Step 1: Add entries** — one BibTeX entry per key above. For the arXiv items use `@misc` with `eprint`/`archivePrefix`. Copy the arXiv numbers and repo URLs verbatim from `../NOTICE.md` (`2609.02882`, `2606.26442`, `github.com/openai/ten-proofs`, `leanprover/comparator`, `ammkrn/nanoda_lib`). For `brualdi1984` cite Brualdi & Goldwasser, *Permanent of the Laplacian matrix of trees and bipartite graphs* (Discrete Math., 1984).
- [ ] **Step 2: Reference-check** — add a temporary `\cite{}` of every key in `main.tex`, run `latexmk -pdf main.tex`, confirm no "undefined citation" warnings, then remove the temporary cites.
- [ ] **Step 3: Commit** — `git add paper/references.bib && git commit -m "docs(paper): references.bib"`

---

### Task 3: §2 The Telperion system

**Files:** Modify: `paper/sections/02-system.tex`

**Content requirements (pin every claim):**
- The `certify → validate → emit → freeze` pipeline; the parameterized-`InequalityFamily` model; certification in exact `fractions.Fraction`/sympy (no floats on the certificate path); emitted Lean re-checked by Mathlib v4.32.0's kernel.
- The trust inversion: **the generator is untrusted**; a wrong certificate is a compile error, never a false theorem.
- Scale: ~78 certificate emitters spanning general/textbook, analytic, BG, and proof-complexity shapes (present a *representative* grouped table, not all 78).
- Reproducibility: byte-stable regeneration (the `--check` drift gate) and CI (`telperion-lean-e2e` builds emitted Lean against pinned Mathlib).
- Walk ONE small example end-to-end (Bernoulli's inequality `(1+x)^k − 1 − kx ≥ 0`, `examples/bernoulli/`).

- [ ] **Step 1: Write the section** to the content requirements, in the mandated tone (motivate → show the pipeline → the Bernoulli walkthrough → the shape table → reproducibility). Cite `lean4`, `mathlib`, `lasserre_sos`/`positivstellensatz` where SOS shapes are mentioned.
- [ ] **Step 2: Compile** — `cd paper && latexmk -pdf main.tex`; expected exit 0, no undefined refs.
- [ ] **Step 3: Guardrail grep** — `grep -niE "resolution|fully machine-checked|solved|breakthrough" sections/02-system.tex`; expected: no output.
- [ ] **Step 4: Commit** — `git add paper/sections/02-system.tex && git commit -m "docs(paper): section 2 — the Telperion system"`

---

### Task 4: §3 The vacuity gap and self-verification

**Files:** Modify: `paper/sections/03-vacuity.tex`

**Content requirements:**
- The kernel catches *false* theorems but not *true-but-vacuous* ones — the central limitation the system is designed around.
- The emitter-sensitivity registry: every emitter declares `CERTIFICATE_SENSITIVE` (corruptible witness → needs a kernel-gated negative-control adapter) vs `STRUCTURALLY_NONVACUOUS` (positivity/decidable/hypothesis-gated glue). A new emitter that declares neither fails the test suite.
- Negative-control adapters (forge the witness → the kernel must reject); the Comparator (independent second kernel — `leanprover/comparator` + `nanoda` — whitelisted axioms only).
- **The irreducible trusted floor, stated honestly:** whether a formal statement *means* the informal claim is undecidable (Löb/Gödel) — the paper's own limitation.

- [ ] **Step 1: Write the section** to the content requirements and tone. Cite `comparator`, `tenproofs`, `nanoda`.
- [ ] **Step 2: Compile** — `latexmk -pdf main.tex`, exit 0.
- [ ] **Step 3: Guardrail grep** — forbidden-words grep on the file; no output.
- [ ] **Step 4: Commit** — `git commit -am "docs(paper): section 3 — vacuity gap and self-verification"`

---

### Task 5: §4 Case study I — Brualdi–Goldwasser

**Files:** Modify: `paper/sections/04-bg.tex`

**Content requirements (exact claims — do not embellish):**
- The 1984 question: among trees on `n` vertices, which maximizes `π(T) = per(L(T))/∏_v deg(v)`? Why hard: the determinantal shadow `det(I−P) ≡ 0`, so determinant-based tools see nothing. Cite `brualdi1984`.
- The conjectured maximizer: a near-star; equality at six 11-vertex trees where a normalized invariant `Φ¹¹ = 1`, via the integer identity `64·243·23 = 621·576`; growth rate `ρ_B = 621/64`.
- **Verified in Lean (unconditional, no sorry):** the Branch-model `Φ ≤ 1` (`PotentialFinal.lean:phi_le_one`); the arm-extremality g-step at every arity on achievable configs (`CappedJointClosure.lean:gstep_le_one_achievable`); the real-graph ratio/amplitude bridge (`BridgeStep4j`, `amplitude_bridge_real'`) resting on `per(L) =` matching-sum for acyclic graphs and the tree cavity recursion.
- **Honest scope / OPEN:** `Φ¹¹` is a *rooted-branch amplitude* invariant; identifying the Branch model with the classical `per(L)/∏deg` tree quantity (the H2 bridge) and the R7 global structural assembly are **open**; therefore the **classical BG conjecture is open** (`conjecture1_proved = False`). Present a small verified-vs-open table.
- **DEFERRED (do not invent):** the sharp rooted-branch-vs-classical numeral ("81/8 vs 621/64 at the tie") is maintainer-gated (spec §8). State the *qualitative* distinction (Branch-model Φ ≠ classical ratio) but leave a clearly-marked LaTeX comment `% TODO(maintainer): confirm sharp tie numeral before inclusion` where the numeral would go — do NOT write the number.

- [ ] **Step 1: Write the section** to the content requirements and tone; motivate the problem, state what is verified with the exact theorem names, then the open pieces and the verified-vs-open table.
- [ ] **Step 2: Compile** — `latexmk -pdf main.tex`, exit 0.
- [ ] **Step 3: Guardrails** — forbidden-words grep (no output) AND confirm the strings `conjecture1_proved = False` (or an explicit "the conjecture is open" sentence) and the `% TODO(maintainer)` marker are present.
- [ ] **Step 4: Commit** — `git commit -am "docs(paper): section 4 — Brualdi–Goldwasser case study"`

---

### Task 6: §5 Case study II — RH zero-free regions

**Files:** Modify: `paper/sections/05-rh.tex`

**Content requirements (exact claims):**
- Four kernel-verified, **unconditional**, CI-axiom-guarded (`#print axioms`, no `sorryAx`) results:
  1. `zeta_fract_repr` — the fractional-part strip representation of ζ on `{0<Re s}\{1}` (PR #177).
  2. `zeta_log_bound` — `‖ζ(σ+it)‖ ≤ 6(1+log|t|)` on `1≤σ≤2, |t|≥2`, explicit constant (PR #185).
  3. `riemannZeta_zero_free_poly` — unconditional Hadamard-free region `Re s > 1 − c/|t|⁵` (PR #180).
  4. `riemannZeta_zero_free_polylog` — unconditional region `Re s > 1 − c/(γ⁴(1+log 2γ))` (PR #188).
- **Honest framing (mandatory):** these are, to our knowledge, the first unconditional, Hadamard-free zero-free regions machine-checked in Lean, BUT the rate is **strictly weaker than de la Vallée-Poussin** (`Re s > 1 − c/log|t|`, cite `dlvp1896`); the contribution is the *formal derivation*, not a new analytic bound. **RH is not claimed.**
- The Borel–Carathéodory theorem is present but **DRAFT** (non-sharp constant, not axiom-guarded, not wired into the region) — say so; the dVP region core is conditional by design.

- [ ] **Step 1: Write the section** to the content requirements and tone. State each theorem with its exact hypotheses/constant, then the "weaker than dVP / value is the formal derivation / RH not claimed" framing.
- [ ] **Step 2: Compile** — `latexmk -pdf main.tex`, exit 0.
- [ ] **Step 3: Guardrails** — forbidden-words grep (no output) AND confirm the phrases "weaker than de la Vallée" and "RH is not claimed" (or equivalents) are present.
- [ ] **Step 4: Commit** — `git commit -am "docs(paper): section 5 — RH zero-free regions case study"`

---

### Task 7: §6 Case study III — proof complexity

**Files:** Modify: `paper/sections/06-proofcomplexity.tex`
**Read first:** `telperion/examples/knapsack_sos/WRITEUP.md` and the `knapsack_sos` / 3-XOR example dirs.

**Content requirements:**
- Extract the exact claims from `knapsack_sos/WRITEUP.md`: what statement is certified (knapsack / 3-XOR SOS refutation or pseudo-expectation), the certificate shape used, and its verified state. Do NOT state a result the writeup does not support; hold to the same verified-vs-open honesty as the other case studies.
- Frame it as evidence of generality: a *different* certificate shape (SOS refutation / pseudo-expectation duality) than the analytic and combinatorial arcs, same untrusted-generator/trusted-kernel discipline.

- [ ] **Step 1: Read** `telperion/examples/knapsack_sos/WRITEUP.md` (and the example's `generate.py` + emitted `lean/`), and list the exact certified claims + their status.
- [ ] **Step 2: Write the section** from those claims, in the mandated tone, with the verified-vs-open framing.
- [ ] **Step 3: Compile** — `latexmk -pdf main.tex`, exit 0.
- [ ] **Step 4: Guardrail grep** — forbidden-words grep; no output.
- [ ] **Step 5: Commit** — `git commit -am "docs(paper): section 6 — proof-complexity case study"`

---

### Task 8: §1 Introduction + abstract

**Files:** Modify: `paper/sections/01-intro.tex`, `paper/main.tex` (abstract)

**Content requirements (written AFTER §§2–6 so contributions are concrete):**
- Open with the trust problem in machine-assisted proof (heuristic/LLM provers give plausible-but-possibly-wrong arguments); the inversion (check the witness, don't trust the author).
- A crisp contributions list: (1) Telperion, the certificate compiler + its self-verification layer; (2–4) the three case studies with their honest one-line status (BG: Branch-model Φ≤1 verified, classical conjecture open; RH: four unconditional zero-free results, weaker than dVP, RH not claimed; proof complexity: the SOS result from Task 7).
- A one-paragraph forward map to the case studies.
- Abstract (≤ ~200 words): same content, compressed, honest.

- [ ] **Step 1: Write** `01-intro.tex` and replace the `main.tex` abstract placeholder.
- [ ] **Step 2: Compile** — `latexmk -pdf main.tex`, exit 0.
- [ ] **Step 3: Guardrail grep** — forbidden-words grep on both; no output.
- [ ] **Step 4: Commit** — `git commit -am "docs(paper): section 1 — introduction and abstract"`

---

### Task 9: §7 Evaluation & limitations, §8 Related work, §9 Conclusion

**Files:** Modify: `paper/sections/07-evaluation.tex`, `08-related.tex`, `09-conclusion.tex`

**Content requirements:**
- §7: provisional/un-lit-checked novelty (carry the `PUBLICATION_LEDGER` honesty forward); the scope discipline; what the tool does NOT do (does not choose the family/problem; the trusted floor of §3); a short "what would falsify our claims" paragraph.
- §8: Lean 4 / Mathlib (`lean4`, `mathlib`); certificate/reflection tactics and SOS/Positivstellensatz (`lasserre_sos`, `positivstellensatz`); **AXLE** (`axle`, arXiv:2606.26442) and **AxiomMath/ZetaZeros** (`axiommath_zetazeros`, arXiv:2609.02882) — explicitly distinct, attributed as in `NOTICE.md`; the Comparator lineage (`comparator`, `tenproofs`, `nanoda`).
- §9: what the system is, honestly what the case studies show, and the open fronts — no hype.

- [ ] **Step 1: Write** the three sections to requirements and tone.
- [ ] **Step 2: Compile** — `latexmk -pdf main.tex`, exit 0.
- [ ] **Step 3: Guardrail grep** — forbidden-words grep across all three; no output.
- [ ] **Step 4: Commit** — `git commit -am "docs(paper): sections 7–9 — evaluation, related work, conclusion"`

---

### Task 10: Reproducibility appendix + paper README

**Files:** Create: `paper/sections/A-reproducibility.tex`; Modify: `paper/main.tex` (`\appendix` + input), `paper/README.md`

**Content requirements:**
- Appendix A: how a reviewer regenerates and re-checks a certificate end-to-end (mirror `telperion/docs/GETTING_STARTED.md`: `pip install -e telperion`, `python examples/<x>/generate.py`, then `cd examples/<x>/lean && lake exe cache get && lake build`). Point at the CI badges as standing evidence.
- `paper/README.md`: one paragraph — what the paper is, how to build it (`make pdf`), and that it is a preprint (not yet submitted).

- [ ] **Step 1: Write** the appendix and `paper/README.md`; add `\appendix\input{sections/A-reproducibility}` before the bibliography in `main.tex`.
- [ ] **Step 2: Compile** — `latexmk -pdf main.tex`, exit 0.
- [ ] **Step 3: Commit** — `git commit -am "docs(paper): reproducibility appendix + paper README"`

---

### Task 11: Full honesty-guardrail review pass + PR

**Files:** none (review) then a PR.

- [ ] **Step 1: Full-document forbidden-words gate** — Run `grep -rniE "resolution|fully machine-checked|solved|breakthrough" paper/sections paper/main.tex`. Expected: no output (or, if a legitimate non-claim use exists, confirm it is not a claim about this work).
- [ ] **Step 2: Claim-traceability read-through** — read the compiled `main.pdf`; for every "verified"/"proven" claim, confirm it names a Lean theorem or executable check from this plan. Fix any that don't.
- [ ] **Step 3: Open-state check** — confirm the paper states, in words, that the classical BG conjecture is open and that RH is not claimed; and that the `% TODO(maintainer)` BG-numeral marker is still present (not silently filled).
- [ ] **Step 4: Final compile** — `cd paper && latexmk -C && latexmk -pdf main.tex`; expected clean build, no undefined refs/cites.
- [ ] **Step 5: Push + PR**

```bash
git push -u origin docs/phase5-whitepaper
gh pr create --repo DrMurphyIsIn/Arda --base main --head docs/phase5-whitepaper \
  --title "docs(paper): Telperion system whitepaper (arXiv preprint draft)" \
  --body "Phase 5. A compilable, arXiv-ready LaTeX preprint under paper/ presenting Telperion as a system with honestly-scoped BG/RH/proof-complexity case studies. Conversational tone; every verified claim traces to a named Lean theorem; conjecture1_proved=False throughout; RH not claimed; the sharp BG tie numeral is left as a maintainer TODO. No mathematics changed.

🤖 Generated with [Claude Code](https://claude.com/claude-code)"
```

---

## Self-Review

**Spec coverage:** §1 purpose → whole paper. Spec §4 tone → Global Constraints + every section step. Spec §5 structure → Tasks 3–10 (one per section, intro written last per spec). Spec §6 build → Tasks 1–2, 10, compile-green invariant. Spec §7 guardrails → Global Constraints + per-section grep steps + Task 11. Spec §8 flagged items → Task 5 (BG numeral = `% TODO(maintainer)`), Task 7 (proof-complexity extracted from writeup). Spec §9 out-of-scope (submission) → not a task (correct). No gaps.

**Placeholder scan:** The only intentional deferrals are the maintainer-gated BG numeral (Task 5, explicit `% TODO(maintainer)` marker, not a vague placeholder) and the proof-complexity claims (Task 7, gated on reading the actual writeup with an explicit read step) — both are genuine external dependencies, flagged per the spec, not lazy TODOs. No "add appropriate X" placeholders.

**Consistency:** citation keys defined in Task 2 (`brualdi1984`, `dlvp1896`, `lean4`, `mathlib`, `axiommath_zetazeros`, `axle`, `tenproofs`, `comparator`, `nanoda`, `positivstellensatz`, `lasserre_sos`) are the exact keys used in Tasks 3–9. Section file names (`01-intro`…`09-conclusion`, `A-reproducibility`) are consistent between Task 1's `\input` list and each section task. The compile command (`cd paper && latexmk -pdf main.tex`) and forbidden-words grep are identical across tasks.
