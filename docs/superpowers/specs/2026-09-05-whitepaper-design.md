# Design: The Telperion system whitepaper (arXiv preprint)

**Date:** 2026-09-05
**Status:** Draft for review
**Scope:** Phase 5 of the public-release-prep program — a standalone deliverable with its own implementation plan.
**Target repo:** `DrMurphyIsIn/Arda`; the paper lives in a new top-level `paper/`.
**Working branch:** `docs/phase5-whitepaper` off `origin/main`.

---

## 1. Purpose

Write a citable arXiv preprint that presents **Telperion** — an
untrusted-generator / trusted-kernel certificate compiler for Lean 4 — as a
reusable system, with three case studies (Brualdi–Goldwasser, Riemann-zeta
zero-free regions, and proof complexity) demonstrating its generality. The paper
is the outward-facing narrative artifact the repository currently lacks (there is
no `paper/` yet; the in-revision BG paper was deliberately held out of the
import).

The contribution is the **system and its methodology**, which is publishable on
its own merits without any conjecture being solved. The case studies are
evidence of generality and honesty, not the load-bearing claim.

## 2. Governing decisions (from maintainer, 2026-09-05)

- **Venue:** arXiv preprint, cross-listed **math.CO + cs.LO** (the exact category
  set is an open item, §9).
- **Center of gravity:** Telperion as a system; BG / RH / proof-complexity are
  case studies.
- **Scope:** all three arcs + the engine.
- **Format:** LaTeX, arXiv-ready, with `references.bib`.
- **Structure:** Approach A (classic system paper) — see §5.
- **Tone (first-class requirement):** *conversational and approachable, while
  maintaining clarity and correctness.* See §4.

## 3. Audience

Two overlapping readerships: (a) mathematicians (extremal combinatorics, analytic
number theory) who care about the results and their honest status, and (b) the
formal-methods / Lean-Mathlib community who care about the system and its trust
model. The paper must be readable and motivating for both without talking down to
either.

## 4. Tone & style (a hard requirement, not a nicety)

The paper is **conversational and approachable** *and* **precise and correct**.
These are not in tension; the discipline is:

- **Motivate before you formalize.** Every formal statement is preceded by a
  plain-language reason it matters and an intuition for why it is true or hard.
- **Active voice, first person plural, short sentences.** "We check each
  instance in exact arithmetic" — not "each instance is checked."
- **Plain-language gloss alongside precise statements.** State theorems exactly
  (exact hypotheses, exact constants), then immediately say what they mean in
  words. Never sacrifice a hypothesis or a caveat for readability.
- **Explain jargon on first use;** prefer a concrete example to a definition
  where one will do.
- **Honesty reads as confidence, not hedging.** "The conjecture is open; here is
  precisely what we *have* verified" is a strength — write it that way.
- **No hype vocabulary.** Never "resolution", "fully machine-checked",
  "breakthrough", "solved". The claims speak for themselves.
- Use the `elements-of-style:writing-clearly-and-concisely` skill if available
  during drafting.

A useful north star: a curious graduate student in either field should be able to
read the introduction and the case-study intros and come away understanding what
was built, what is proven, and what is open — without the paper ever having
overstated anything.

## 5. Structure (Approach A) and per-section content

1. **Introduction.** The trust problem in machine-assisted proof (heuristic and
   LLM provers produce plausible-but-possibly-wrong arguments). The inversion:
   don't trust the author, *check the witness* — an untrusted generator emits a
   certificate the Lean kernel re-proves from scratch. Contributions list. A
   forward map of the three case studies.
2. **The Telperion system.** The `certify → validate → emit → freeze` pipeline;
   the parameterized-family model; the ~78 certificate shapes (grouped, with a
   representative table, not exhaustive); exact-rational certification; emitted
   Lean re-checked against pinned Mathlib v4.32.0; reproducibility (byte-stable
   regeneration, CI). Keep it concrete — walk one small example (Bernoulli)
   end-to-end.
3. **The vacuity gap and self-verification.** The kernel catches *false*
   theorems but not *true-but-vacuous* ones. Telperion's answer: the
   emitter-sensitivity registry (every emitter declares CERTIFICATE_SENSITIVE vs
   STRUCTURALLY_NONVACUOUS), negative-control adapters (forge the witness →
   kernel must reject), and the Comparator (independent second kernel, whitelisted
   axioms). State the **irreducible trusted floor** honestly: whether a formal
   statement *means* the informal claim is undecidable (Löb/Gödel) — the paper's
   own limitation, stated up front.
4. **Case study I — Brualdi–Goldwasser.** The 1984 question (`per(L(T))/∏deg`
   over trees); why it is hard (the determinantal shadow is identically zero).
   What Telperion helped verify: the Branch-model `Φ ≤ 1` (`phi_le_one`, Lean,
   unconditional, no sorry), `gstep_le_one_achievable`, the real-graph
   ratio/amplitude bridge. The **honest scope**: `Φ¹¹` is a *rooted-branch*
   amplitude invariant, and identifying the Branch model with the classical
   `per(L)/∏deg` tree quantity (the H2 bridge) plus the R7 global structural
   assembly are **open**; therefore the **classical BG conjecture is open**
   (`conjecture1_proved = False`). *(The sharp rooted-branch-vs-classical
   numerical framing — the "81/8 vs 621/64 at the tie" point — is flagged for
   maintainer confirmation before it goes in; see §8.)*
5. **Case study II — RH zero-free regions.** The four kernel-verified,
   unconditional, CI-axiom-guarded results: the fractional-part strip
   representation `zeta_fract_repr`; the sharp bound `|ζ(σ+it)| ≤ 6(1+log|t|)`;
   the elementary Hadamard-free region `Re s > 1 − c/|t|⁵`; and the polylog region
   `Re s > 1 − c/(γ⁴(1+log 2γ))`. **Honest framing:** these are (to our knowledge)
   the first unconditional, Hadamard-free zero-free regions machine-checked in
   Lean, but the rate is **strictly weaker than de la Vallée-Poussin** — the
   contribution is the *formal derivation*, not a new analytic bound; **RH is not
   claimed**. The Borel–Carathéodory theorem is present but DRAFT (non-sharp
   constant, not wired in) — say so.
6. **Case study III — proof complexity.** The knapsack / 3-XOR SOS results
   (`telperion/examples/knapsack_sos/`, `WRITEUP.md`). *Content to be gathered
   during drafting from that writeup; the exact claims are an implementation-plan
   task, held to the same verified-vs-open honesty.*
7. **Evaluation & limitations.** Provisional novelty (the `PUBLICATION_LEDGER`
   already states novelty is un-lit-checked — carry that honesty forward); the
   scope discipline; what the tool does *not* do (it does not choose the family or
   the problem; the trusted floor of §3). A short "what would falsify our claims"
   paragraph.
8. **Related work.** Lean 4 / Mathlib; certificate-producing / reflection tactics;
   Positivstellensatz and SOS certification; **AXLE** (arXiv:2606.26442) and
   **AxiomMath/ZetaZeros** (arXiv:2609.02882) — kept distinct, attributed exactly
   as in `NOTICE.md`; `openai/ten-proofs` / `leanprover/comparator` / `nanoda`.
9. **Conclusion.**

Appendices as needed: the certificate-shape catalog; a reproducibility appendix
(how a reviewer regenerates and re-checks — mirrors `telperion/docs/GETTING_STARTED.md`).

## 6. Artifact & build

- New top-level `paper/` in the Arda repo: `main.tex`, `references.bib`, section
  files (`sections/*.tex`) so the document is modular, a `Makefile` (or latexmk
  invocation), and a short `paper/README.md`.
- `references.bib` seeded from `NOTICE.md`'s citations (2609.02882, 2606.26442,
  ten-proofs, comparator, nanoda) plus Brualdi–Goldwasser (1984), de la
  Vallée-Poussin, Lean/Mathlib, and the standard SOS/Positivstellensatz references.
- **Compilable from day one:** the implementation plan builds the skeleton first
  and keeps `latexmk -pdf main.tex` green as sections land (the paper's analogue
  of "tests pass").
- Optional CI: a `paper-build` workflow that compiles the PDF on PR (decide in the
  plan; not required for a first draft).

## 7. Honesty guardrails (claim-safety — non-negotiable)

- Every quantitative or "verified" claim traces to a named Lean theorem or an
  executable check; if it cannot be traced, it does not go in.
- `conjecture1_proved = False` is stated plainly; no arc is presented as more
  finished than the audit established.
- No "Resolution / fully machine-checked / solved / breakthrough" language.
- Special cases are never presented as the general conjecture (BG, RH both).
- Novelty claims are marked provisional and un-lit-checked, per the ledger.
- The verified-vs-open state is stated explicitly per arc, ideally as a small
  table.

## 8. Open items to resolve during planning/drafting (flagged, not defaulted)

- **BG Φ¹¹-vs-classical sharp framing** — needs maintainer confirmation of the
  exact rooted-branch value at the tie and the preferred description of the H2
  bridge (this is the same item flagged in PR #234). The paper states the
  qualitative distinction regardless; the sharp numeral only goes in once confirmed.
- **Proof-complexity claims** — to be extracted from `knapsack_sos/WRITEUP.md`
  during drafting and stated to the same honesty standard.
- **Author list / acknowledgements**, **arXiv category set** (math.CO + cs.LO
  primary; possibly math.NT for the RH case study), and **whether to submit or
  keep as a repo preprint first** — maintainer decisions before submission (not
  before drafting).

## 9. Out of scope (this spec)

- Actual submission to arXiv (a maintainer action after the draft is reviewed).
- Changing any mathematics or Lean proof.
- The Phases 0–4 repo work (separate, already in PRs #231/#233/#234/#235/#237).

## 10. Acceptance

A complete, self-contained LaTeX preprint in `paper/` that compiles to PDF; is
conversational and approachable yet exact; presents Telperion as the contribution
with three honestly-scoped case studies; traces every verified claim to an
artifact; contains no overclaim or hype; and could be read by a curious graduate
student in either community and understood without being misled. Every §7
guardrail holds on a final read-through.
