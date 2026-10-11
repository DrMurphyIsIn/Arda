# What a proof of RH would have to look like, from this project's results (2026-10-11)

A thinking note, written at the user's request after the Newman, Selberg-class and sextic-bottleneck work.
It contains no result. `conjecture1_proved = False`; nothing here is progress on RH.

## 1. Two constraints the project has established

**The Euler product must be load-bearing.** The Davenport-Heilbronn function has a functional equation, the
right growth, membership in the extended Selberg class, and zeros off the line. Dobner's proof, now
formalized for the whole class (`selberg_newman_sharp`), never uses the Euler product, which is exactly why it
proves `Lambda_F >= 0` for every `F` and `Lambda_F = 0` for none. Any argument that would also work for
Davenport-Heilbronn is wrong before it starts. In OpenAI's 7/8 method the arithmetic enters once, at Mobius
inversion; that single entry bought a fixed strip and, as the thread-C sweep showed, nothing more.

**It cannot be a march of strips.** The 7/8 architecture is a two-sided vertex (optimum = Liu's 0.874957);
the obstruction is structural (the cubic theta is the only metaplectic form with known Gauss-sum
coefficients; the sextic order is forced; higher orders have worse sparsity), so a sequence of strips
converging to 1/2 would need inputs that improve with the twist order while every known input degrades.
Zero-free regions that narrow toward `Re s = 1` do not converge to the line either.

So the proof must be a global statement about all zeros at once, with the primes on one side of an identity
and a positivity on the other. The one classical object of that shape is Weil's explicit formula, and Weil's
criterion (RH iff `W(f * f~) >= 0` for all test functions) is the equivalence. The equivalence is a coordinate
change (Mirrormere wall map); the content would be a REASON the arithmetic side is positive.

## 2. What the reason would have to look like

In the function-field case the reason is geometric: the explicit formula is a Lefschetz trace formula on
`C x C` and positivity is the Hodge index theorem on intersection numbers. Weil did not estimate; he found a
space in which the sum IS an intersection number and inherited positivity. Every serious attempt on RH proper
(Connes-Consani's scaling site and semi-local trace formula, Deninger, de Branges) is an attempt to build that
space for `Spec Z`; all have reproduced the equivalence without the inequality. The dual shape is a
Hilbert-Polya operator: if the Weil form is a sum of squares there is an operator with the zeros as spectrum.
Neither the squares nor the operator has been exhibited.

## 3. Three bounded searches the project's tools fit

1. **Finite compressions of Weil's form, certified.** arXiv:2608.13637 (Aug 2026) proves more than two thirds
   of the zeros are simple and on the line by a rank-trace inequality on a finite compression of Weil's
   Hermitian form (Sylvester's law of inertia replaces Montgomery's RH assumption). Exact Gram matrices and
   positivity certificates are Telperion's native objects; improving the constants is certifiable work on the
   proportion of zeros on the line, not their location up to a height.
2. **Structure in the Gram matrices.** Compute the Weil form on natural bases in exact arithmetic and look for
   a factorization PATTERN as the dimension grows (SOS / Positivstellensatz tooling), compared against the
   prolate spheroidal operator (Connes-Consani 2022-23) and against Toeplitz-plus-Hankel and Jacobi shapes.
   Likely outcome: noise. If not noise, it points at the operator. DONE 2026-10-11:
   `telperion/research/weil_positivity/` (Gram matrices; zeros recovered from the prime side in `prony/`; the
   one-prime window in `one_prime/`). Positivity is real, sharp, and an exact cancellation between the archimedean
   side and the primes, tight at the pole; controls fail where they should; no Hilbert-Polya structure.
3. **An arithmetic Lyapunov function for the heat flow.** Rodgers-Tao's energy uses the zeros alone and so,
   by the Davenport-Heilbronn test, cannot reach `Lambda <= 0`. Whether a prime-weighted functional of the
   zeros of `H_t` is monotone along the flow is testable numerically on the island. Caveat found at design
   time: `H_t` for `t > 0` has no Euler product, so the "prime side" of such a functional is not canonical;
   the experiment needs a definition before it needs a computation. DONE 2026-10-11 in Dyson's quasicrystal form
   (`telperion/research/heat_flow_diffraction/`): the monotone log-prime Bragg weight is universal log-gas damping
   (also on GUE and Davenport-Heilbronn combs), diverges at t = 0+ as T grows, and is blind to collisions and
   off-line pairs. NEGATIVE.

## 4. What not to do

Do not start another formalization of a known theorem about zeta in the hope that rigor substitutes for the
idea. Do not search the 7/8 geometry again (closed, section 7 of SEXTIC_BOTTLENECK_2026-10-11.md). Do not add
equivalences. The honest summary: the shape is known (Weil positivity with the primes inside it), the missing
piece is the construction that makes the positivity visible, and a verification-first project can look for its
footprints without pretending to have it.
