# Review: Axiom Math "A New Bound for Small Gaps Between Primes" (bgp212, 2026-09-09)

Paper: **Charton, Hong, Lau, Ono, Remy, Siu, Swaminathan, Thorner, Xie** (Axiom Math),
preliminary draft Sept 3 2026, `primegaps.axiommath.ai/bgp212.pdf`.
**Theorem 1.1: H₁ = liminf(p_{n+1} − p_n) ≤ 212** — beating Stadlmann's 240 [Sta26] and
Polymath8b's decade-old 246. Method: Stadlmann's mixed-support Maynard–Tao sieve +
Polymath8a/Baker–Irving equidistribution, optimized by distributed-cluster experimentation,
with three sharpenings (divisor-level estimate statements; whole-range factorization
verification; explicit four-range treatment of moduli near x^{1/2}).

## Why this matters to Telperion: the proof is certificate-shaped

The proof separates into independently-proved statements, each in a shape we emit:

1. **Arithmetic side** — support datum (δ, A, B, ε) of FIXED RATIONALS (Table 3);
   factor-extraction reduces to "a finite family of exact rational polyhedral implications"
   verified EXACTLY (Table 4 lists the six principal reserves with exact slacks, e.g.
   499999/5000000000; complete list in their Appendix B). → our cone/Handelman/
   `finite_decide` shapes.
2. **Variational side** — Lemma 10.1/Prop 10.2: `I_T(F)`, `J_T(F)` ∈ ℚ for rational F
   (rational-polytope moments via the simplex identity (10.1): ∫ Π zᵢ^{eᵢ} over a simplex =
   R^{m+Σe}·Πeᵢ!/(m+Σeᵢ)!). Theorem 11.1: a symmetric rational polynomial F⋆ with
   **J_T(F⋆) − 4·I_T(F⋆) > 0** — rational GRAM matrices where "any explicit rational
   coefficient vector gives a rigorous lower bound for the largest generalized eigenvalue."
   → exactly our `psd_form`/Rayleigh-quotient shape.
3. **Admissible tuple** — Lemma 12.1: the 45-tuple is admissible, diameter 212. → `decide`.

## The flagged gap (Appendix A) — Telperion's opening

"**AxiomProver**, an AI system under development by Axiom Math, autonomously generated from
natural-language specifications a Lean certificate of the deduction of Theorem 1.1" — taking
the five Type I/II/III estimates + bilinear BV + Harman decomposition **and the variational
certificate as hypotheses**. Verbatim: "**The exact rational verification of the variational
certificate is presently performed separately and supplied to the formal development as a
hypothesis.**"

That is precisely the class of exact-rational Gram verification Telperion does IN-KERNEL.
Kernel-verifying their Theorem 11.1 certificate (+ the Appendix B polyhedral table) would
close their explicitly-named trust gap — a concrete, well-scoped collaboration/contribution.

## Honest scope
H₁ ≤ 212 is real unconditional mathematics (its analytic inputs are published:
Polymath8a, Baker–Irving 2017, Stadlmann 2025/2026). The Lean artifact is a *conditional
deduction* on those inputs. The certificate parts are category-(b) finite verifications.
Nothing here touches RH. Their hypothesis-seam honesty pattern mirrors ours independently.

## Action leads (ranked)
1. **`rayleigh_gram` extension of `psd_form`**: given rational Gram matrices I, J and a
   rational vector c, kernel-verify cᵀJc − 4·cᵀIc > 0 — their Theorem 11.1 shape; offer to
   close their hypothesis gap.
2. **New `polytope_moment` emitter** — Lemma 10.1's shape: exact ∫_P G over a rational
   polytope via triangulation + simplex moments; generator finds the triangulation, kernel
   checks the rational algebra. Broadly reusable for sieve-variational computations.
3. **New `admissible_tuple` emitter** — admissibility + diameter by `decide`.
4. **Mine the Axiom Math corpus** (axiommath.ai/research/publications: ~12 papers
   Jun–Aug 2026, AxiomProver-formalized): Nekrasov–Okounkov dominant zeros (→ interlacing),
   Han–Xiong Gaussian-binomial inequalities (→ SOS), formalized q-series (→ WZ), Thakur
   𝔽_q[t] power sums (→ Track-5-adjacent). NOTE: we already ported AxiomMath/ZetaZeros
   (arXiv:2609.02882) → `curvature_boundary` + `transcendental_enclosure`.
