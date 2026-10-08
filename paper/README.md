# Telperion whitepaper

An arXiv-style preprint presenting **Telperion** — an untrusted-generator /
trusted-kernel certificate compiler for Lean 4 — as a system, with three
honestly-scoped case studies (Brualdi–Goldwasser, Riemann-zeta zero-free
regions, and proof complexity).

Build the PDF:

```bash
make pdf        # uses latexmk if present, else two pdflatex passes + bibtex
```

Status: **draft preprint, not yet submitted.** `conjecture1_proved = False` —
nothing here is presented as more finished than the repository's `STATUS.md`
establishes.

> **Note (2026-10-07): the Brualdi–Goldwasser section is out of date.**
> `sections/04-bg.tex` was written while the problem was open and still calls
> the classical conjecture open. The problem has since been solved: the
> maximizer for every `n ≥ 4` is kernel-checked in Lean 4 / Mathlib (not yet
> refereed), released at [DrMurphyIsIn/brualdi-goldwasser](https://github.com/DrMurphyIsIn/brualdi-goldwasser)
> (doi:10.5281/zenodo.22983412). The flag `conjecture1_proved = False` in the
> draft refers to the campaign's first, conditional route (and, in the RH
> sections, to that campaign's goal), not to the 1984 problem. The section
> needs revising before submission.
