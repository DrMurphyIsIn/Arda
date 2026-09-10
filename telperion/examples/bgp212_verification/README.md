# bgp212 kernel verification — the published exact surface of H₁ ≤ 212

Kernel-verification of the **published exact-rational content** of
*"A New Bound for Small Gaps Between Primes"* (Charton, Hong, Lau, Ono, Remy, Siu,
Swaminathan, Thorner, Xie — Axiom Math, Sept 3 2026, `primegaps.axiommath.ai/bgp212.pdf`),
which proves `H₁ = liminf(p_{n+1} − p_n) ≤ 212`, plus a ready-to-consume pipeline for the
one certificate the paper does NOT publish. `conjecture1_proved = False`; this is
prime-gaps mathematics, not RH.

## Kernel-verified here (locally, 2026-09-09)

1. **`lean/H45Admissible.lean`** — the paper's actual 45-tuple H₄₅ (Section 12, printed in
   full) is admissible with diameter 212, by `decide` over the derived primes ≤ 43.
   Emitted by `AdmissibleTupleEmitter`; the paper's 14 omitted-residue witnesses (Lemma
   12.1) independently re-verified pre-emission. **Core Lean, no Mathlib; compiles
   standalone in ~2 s.** This is the tuple side of `DHL[45,2] ⟹ H₁ ≤ 212`.
2. **`lean/AppendixBLedger.lean`** — the complete Appendix B "exact analytic and
   combinatorial slack ledger" (Table 6): all **21 rows** of the arithmetic-side parameter
   inequalities, with the paper's exact fractions (slacks down to `163/2000000000000`),
   re-decided by `norm_num` over ℚ. Every slack independently re-verified in exact
   arithmetic pre-emission. **Compiles clean under Mathlib v4.32.0.**

Together these kernel-check every exact-rational verification surface the paper publishes.

## The gap this example is built to close (the collaboration ask)

The paper's **Appendix A** states that AxiomProver's Lean deduction of Theorem 1.1 takes
the **variational certificate of Theorem 11.1 as a hypothesis**: *"The exact rational
verification of the variational certificate is presently performed separately and supplied
to the formal development as a hypothesis."*

That certificate is: `P⋆ ∈ B₂₁` (the 846-dimensional space
`span{(L−P₁)ᵃ·P_λ : a+|λ| ≤ 21, λ even}` in 45 variables), with rational Gram matrices
`I_T`, `J_T` (Prop 10.2 — every entry a rational polytope moment via the simplex identity
(10.1)) and `J_T(F⋆) − 4·I_T(F⋆) > 0` (quotient ≈ 4.00438…). **The 846-entry coefficient
vector and the Gram matrices are not published in the paper.**

Telperion's emitters are wired to consume exactly this data:
- **`rayleigh_gram`** kernel-verifies `cᵀJc − 4·cᵀIc > 0` with the full Gram contraction
  re-done in-kernel (`norm_num`), given `(J, I, c)`.
- **`polytope_moment`** kernel-verifies the exact-rational simplex-moment computations
  behind each Gram entry (in-Lean `simplexMoment` closed form).

**Ask to Axiom Math:** publish (or share) the exact rational data — the 846-entry
coefficient vector of `P⋆` and the Gram matrices `I_T`, `J_T` (or the per-entry
simplex-moment decompositions) — and the hypothesis in your Appendix A becomes a
kernel-verified theorem.

## Honest engineering caveats
- `rayleigh_gram` currently caps the contraction dimension at 25 (norm_num cost); the
  846-dim contraction needs a scaling pass (blocked/sparse emission or `native_decide`) —
  a known, tractable engineering step, flagged rather than hidden.
- The analytic inputs (Type I/II/III equidistribution, Bombieri–Vinogradov, Harman
  decomposition) remain literature hypotheses in both their development and any
  verification built on this example — same seam, honestly shared.

## Regeneration
Both certs are produced by the registered emitters (`admissible_tuple`) and a small
ledger script; the H₄₅ list and all 21 ledger rows are transcribed from the paper and
exactly re-verified before emission (a transcription error is a refusal/assert, never a
wrong theorem).
