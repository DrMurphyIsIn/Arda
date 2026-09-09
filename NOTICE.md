# Notice & Credits

This repository builds on, ports ideas from, and cross-checks against several
external projects. This file records that provenance. Licensing terms for this
repository's own contents are in [`LICENSING.md`](LICENSING.md); this file is
about *attribution* of prior and external work.

For each item below we state precisely **what was taken**. Where an idea was
ported, it was **re-implemented independently** in this project's idiom (exact
sympy → kernel-checked Lean). With one explicitly-flagged exception (the
`RHLinalg` prelude ported verbatim from `anthropics/zeta-23-lean`, Apache-2.0,
below), no source code was copied verbatim from these projects (see
"Verbatim-copy statement" below).

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

## Ported code + proof shapes — anthropics/zeta-23-lean (arXiv:2608.13637)

A growing family of Telperion certificate emitters (beginning with
`hermitian_moment`; the authoritative, current list is
`telperion/docs/SECOND_PASS_EMITTER_CATALOG.md`) builds on the Anthropic
**zeta-23-lean** development (**arXiv:2608.13637**, *"More than two thirds of
the zeros of ζ lie on the critical line"*; public repo
`anthropics/zeta-23-lean`, **Apache-2.0**). Two distinct things were taken,
stated precisely:

- **Verbatim code port** — the self-contained linear-algebra core of the
  paper's §3 (the Hermitian-inertia spine): eight Lean files from
  `zeta23/Zeta23/LinAlg/`, ported as
  `telperion/examples/hermitian_moment/lean/RHLinalg/` (namespace `RHLinalg`).
  This is the **one verbatim copy in this repository**; it is permitted and
  attributed under the source's Apache-2.0 license. Port details, the toolchain
  re-pin, and flagged risks are in
  `telperion/examples/hermitian_moment/lean/PORT_NOTES.md`.
- **Proof shapes** — the generator-shaped emitters of the family (the
  two-moment count certificate, the rank-trace integrality atom, and kin) port
  the paper's *certificate shapes* into Telperion's independent Python idiom,
  as with the other emitter attributions in this file.

The λ=1 headline constants reproduced by these emitters (H = 2/3, H_d = 5/6)
are **the paper's results**, credited to its authors; the emitters emit
faithful specializations as certificate atoms for this project's Weil-positivity
tooling track.

## Mined proof shapes — openai/NavierStokesAndEuler

A growing family of Telperion emitter kinds (beginning with `affine_ledger`,
`quadratic_irrational`, and `gevrey_majorant`; the authoritative, current list
is `telperion/NS_EULER_EMITTER_CATALOG.md`, which names each kind's source
file) was distilled in waves from a certificate-mining pass over OpenAI's
**`openai/NavierStokesAndEuler`** finite-time-blowup formalization
(Apache-2.0). What was taken is **certificate shapes only** — the
generator-shaped, kernel-cheap arithmetic atoms recurring in that development —
re-implemented independently in Telperion's Python idiom, exactly as with the
AxiomMath/ZetaZeros emitters above. No Lean or other source files were copied;
the PDE/matrix/ODE machinery of the source was treated as out-of-scope prelude,
and its analytic facts enter Telperion certificates only as explicit
hypotheses.

## Certified onto an upstream formalization — li-criterion-rh-equivalence-lean

The `li_positivity` emitter certifies finite rungs of Li's criterion \emph{onto}
an external Lean formalization surfaced by the Palomar miner:
**`nicholasbulka/li-criterion-rh-equivalence-lean`** (Apache-2.0), which proves
the upstream reduction `RiemannHypothesis ↔ ∀ n, 0 ≤ (taylorCoeff riemannXi n).re`.
What is taken is the **statement interface** (the emitter's theorems target that
formalization's positivity ladder); no code was copied, and the numeric lower
bounds the emitter certifies are documented external Arb/mpmath hypotheses
(see `telperion/docs/LI_POSITIVITY_LADDER.md`, including its honest ceiling:
finitely many rungs never decide RH).

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
comparator, nanoda, or openai/NavierStokesAndEuler. What is shared is the
*mathematical idea*, credited above. The **single exception** in this repository is the `RHLinalg` prelude
(`telperion/examples/hermitian_moment/lean/RHLinalg/`), a flagged verbatim port
of eight Apache-2.0 Lean files from `anthropics/zeta-23-lean`, attributed in
its own section above and in `PORT_NOTES.md` alongside the files.

## A note on scope

`conjecture1_proved = False`. Nothing in this file's attributions implies a
completed proof of the Brualdi–Goldwasser conjecture or of the Riemann
Hypothesis; see [`STATUS.md`](STATUS.md) for the honest, per-result state.
