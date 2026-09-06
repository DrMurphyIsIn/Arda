# Notice & Credits

This repository builds on, ports ideas from, and cross-checks against several
external projects. This file records that provenance. Licensing terms for this
repository's own contents are in [`LICENSING.md`](LICENSING.md); this file is
about *attribution* of prior and external work.

For each item below we state precisely **what was taken**. Where an idea was
ported, it was **re-implemented independently** in this project's idiom (exact
sympy → kernel-checked Lean); no source code was copied verbatim from these
projects (see "Verbatim-copy statement" below).

## Foundations

- **Lean 4** and **Mathlib** (`leanprover-community/mathlib4`). Every theorem in
  this repository is checked by the Lean 4 kernel against a pinned Mathlib; the
  formalization is written in terms of Mathlib's library. Lean is Apache-2.0;
  Mathlib is Apache-2.0.

## Ported proof ideas — AxiomMath / ZetaZeros (arXiv:2609.02882)

Two Telperion certificate emitters port *proof ideas* (not code) from the Lean
formalization associated with **arXiv:2609.02882** and the
**`AxiomMath/ZetaZeros`** repository (the Montgomery–Taylor extremal-kernel
material, `extremalG_const`):

- **`CurvatureBoundaryEmitter`** (`telperion/examples/curvature_boundary/`)
  generalizes the `extremalG_const` move — a function with sign-definite second
  derivative attains its interval extremum at a boundary point (`G'' = 0 ⟹ G`
  affine ⟹ constant, evaluated at the endpoints) — to the general
  curvature-sign setting.
- **`TranscendentalEnclosureEmitter`** (`telperion/examples/transcendental_enclosure/`)
  ships a rational log-enclosure atom kin to the Montgomery–Taylor
  transcendental-constant enclosure; the trigonometric / `C₀` face of that
  construction is **not** implemented here (it is deferred and refused at
  certificate time).

These emitters serve this project's own Brualdi–Goldwasser cells; they are
credited in their generators' docstrings and in the emitted `.lean` headers.

## Engineering patterns — AXLE (arXiv:2606.26442)

Telperion's verify / gap-fill / repair / negative-control / bundle / normalize
tooling took **engineering patterns** (not code) from **AXLE**, Axiom Math's
cloud Lean-verification utility (**arXiv:2606.26442**, `axle.axiommath.ai`).
AXLE is a distinct project from AxiomMath/ZetaZeros above: AXLE is a
verification *utility*, ZetaZeros is a *proof*; they should not be conflated.

## Independent verification — the Comparator

For an independent second check that an emitted Lean proof proves *exactly* the
stated theorem using only whitelisted axioms, Telperion integrates:

- **`leanprover/comparator`** (from OpenAI's **`openai/ten-proofs`**), and
- **`ammkrn/nanoda_lib`**, an independent Rust re-implementation of the Lean
  kernel used as a second checker.

## Verbatim-copy statement

The ported emitters above are **independently written** in Telperion's Python
idiom (parameterized inequality families → exact sympy certification → emitted
Lean re-proved from scratch by Mathlib's kernel). No Lean, Python, or other
source files were copied verbatim from AxiomMath/ZetaZeros, AXLE, ten-proofs,
comparator, or nanoda. What is shared is the *mathematical idea*, credited
above.

## A note on scope

`conjecture1_proved = False`. Nothing in this file's attributions implies a
completed proof of the Brualdi–Goldwasser conjecture or of the Riemann
Hypothesis; see [`STATUS.md`](STATUS.md) for the honest, per-result state.
