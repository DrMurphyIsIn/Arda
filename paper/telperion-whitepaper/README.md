# Telperion whitepaper (draft)

Source for the standalone Telperion paper — an arXiv-style preprint introducing
Telperion (untrusted exact-arithmetic certificate compiler → kernel-checked Lean 4)
with the openai/ten-proofs Comparator independent-verification layer, and the
Brualdi–Goldwasser formalization as an **honestly-scoped, in-progress** case study.

> **Status: first draft.** Every `\todo{...}` is a placeholder needing the author's
> input or a fact to verify before submission — see the checklist below. The paper
> is deliberately explicit that the BG conjecture is **not** proved.

## Build

```sh
latexmk -pdf main.tex        # or: pdflatex main; bibtex main; pdflatex main; pdflatex main
```

## Layout

| file | contents |
|---|---|
| `main.tex` | preamble, title, abstract, disclosure, `\input`s |
| `sections/01-intro.tex` | the two problems, the integrated-system contribution |
| `sections/02-trust-model.tex` | untrusted generator, sole-trusted kernel, non-vacuity |
| `sections/03-emitters.tex` | pipeline, ~30 certificate shapes, worked example |
| `sections/04-independent-verification.tex` | Comparator: identity, axiom whitelist, 2nd kernel |
| `sections/05-bg-casestudy.tex` | BG flagship + the **Proved/Open ledger** |
| `sections/06-related-work.tex` | Lean/Mathlib, learned provers, VIPR, Comparator |
| `sections/07-limitations.tex` | scope, vacuity, self-check limits, scale |
| `sections/08-conclusion.tex` | recap, availability, licensing |
| `sections/99-appendix.tex` | emitter catalog, verified anchors, reproduction |
| `refs.bib` | bibliography (software URLs solid; academic entries flagged to verify) |

## Author checklist (the `\todo`s)

1. **Authorship & affiliation** — listed authors, affiliation, email, ORCID.
2. **AI-assistance disclosure** — finalize the wording (front matter). The paper's
   thesis actually leans into this: the generator is untrusted by construction.
3. **BG conjecture statement** — paste the exact published Brualdi–Goldwasser
   statement + citation (`sections/05`, `refs.bib`); confirm §5 does not overstate it.
4. **Exact anchor signatures + `#print axioms` output** — from a CI run (`sections/99`).
5. **Bibliography** — verify every academic entry (AlphaProof, DeepSeek-Prover,
   VIPR, de Bruijn, Positivstellensatz, Brualdi–Goldwasser, Lean/Mathlib).
6. **License & availability** — repository URL, release tag/DOI, confirm BSL-1.1 /
   Apache-2.0 terms and any CLA.
7. **Emitter catalog** — reconcile the table against the released version's exact list.
