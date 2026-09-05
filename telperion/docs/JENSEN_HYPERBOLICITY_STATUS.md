# Jensen-Polya Hyperbolicity: Status Document

**conjecture1_proved = False.** This document is an honest accounting of what
has been formally proved, what trust boundaries exist, and what has not been
done. Nothing here is a proof of the Riemann Hypothesis.

---

## What Is Proven

### Kernel-verified box-hyperbolicity for J^{2,n}, n = 0, 1, 2, 3

The Lean 4 kernel (via `lake build`) has accepted, sorry-free, four theorems:

| Theorem | Jensen polynomial | Discriminant margin |
|---|---|---|
| `jensen_box_hyperbolic_deg2_0` | J^{2,0}(x) | approx 2.82e-04 |
| `jensen_box_hyperbolic_deg2_1` | J^{2,1}(x) | approx 2.27e-08 |
| `jensen_box_hyperbolic_deg2_2` | J^{2,2}(x) | approx 8.00e-13 |
| `jensen_box_hyperbolic_deg2_3` | J^{2,3}(x) | approx 1.51e-17 |

Each theorem states: for every triple (c0, c1, c2) of real numbers lying in the
certified rational coefficient box, the degree-2 polynomial
`c2 * X^2 + c1 * X + c0` has exactly 2 real roots (counting multiplicity), i.e.,
`(Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0).roots.card = 2`.

The Jensen polynomial J^{d,n}(x) = sum_{k=0}^{d} C(d,k) * alpha(n+k) * x^k, where
alpha(m) is the coefficient of t^{2m} in Xi(t) = xi(1/2 + it). For d=2:
c0 = alpha(n), c1 = 2*alpha(n+1), c2 = alpha(n+2).

**Axioms.** Each theorem depends on exactly: `{propext, Classical.choice, Quot.sound}`.
No `native_decide`, no `sorry`, no `ofReduceBool`. Confirmed by `#print axioms`
in the emitted file, kernel-checked at build time.

**AXLE statement-match gate.** Each theorem is followed by a kernel-checked
`example` that closes the AXLE gate: the example compiles only if the emitted
Prop literally matches the intended box-hyperbolicity statement. A type mismatch
or proof of a weaker statement would cause a build failure.

**Proof structure.** The proof chains two steps:
1. A `nlinarith` box-positivity argument establishes `0 <= c1^2 - 4*c2*c0`
   (the discriminant lower bound) from the rational box constraints.
2. The Task-4 bridge lemma `hyperbolic_deg2_of_discrim_nonneg` (in
   `JensenBridge.lean`) concludes `.roots.card = 2` from the nonzero leading
   coefficient and nonnegative discriminant.

**This is the first formally kernel-verified Jensen-polynomial hyperbolicity
result for the Riemann zeta function** (to the authors' knowledge as of 2026-09-05).

---

## The Trust Boundary

The one non-kernel link in the chain is the **coefficient-membership claim**:
the assertion that the true value alpha(m) lies within the rational box [lo, hi].

This claim is certified by **Arb ball arithmetic** (python-flint), not by the
Lean kernel:

- For n = 0, 1, 2 (needing alpha(0..4)): the `acb_series` path evaluates Xi(t)
  as a truncated power series in t using Arb's ball arithmetic (every operation
  carries a rigorous, directed-rounded error ball). The ball's outward rational
  endpoints give the certified [lo, hi].

- For n = 3 (needing alpha(5)): the `acb_series` path is limited to 10 series
  terms by python-flint's zeta implementation (alpha(5) is at index 10). A
  three-point Vandermonde approach is used instead: Xi(t) is evaluated at
  t = 0.10, 0.15, 0.20 via certified `acb` ball arithmetic (direct gamma/zeta),
  the known contributions of alpha(0..4) are subtracted (using their acb_series
  certified boxes), and a 3x3 linear system for (alpha(5), alpha(6), alpha(7))
  is solved via Cramer's rule over acb balls. The residual (alpha(8)+) at these
  t values is bounded below 1e-28, well under the ball radius.

In both cases the enclosure is **Arb-certified, not kernel-certified**. This
is the plan's one documented non-kernel input, analogous to the inputs R and B
in other Telperion certificate families. Everything downstream of the rational
box (the nlinarith discriminant argument and the bridge lemma invocation) IS
kernel-verified.

---

## What Is Not Done / Deferred

### (a) Degrees d >= 3: deferred to Phase 2

Cubic (d=3) and higher-degree hyperbolicity certificates require a theorem of
the form "PSD Hermite-Bezoutian matrix implies all roots real." Mathlib (as of
2026-09-05) lacks the discriminant-to-real-roots bridges over R for degrees >= 3.

Phase 2 will implement a general **Hermite-Bezoutian PSD engine** that handles
all degrees d <= 8 uniformly via a single kernel-verified theorem. At that point,
the grid can be extended to (d, n) in {2,3,4,...} x {0,1,2,...}.

### (b) Uniform-in-d effective threshold N(d)

The actual RH-closing piece of the Jensen-Polya program requires showing that
J^{d,n} is hyperbolic for ALL n >= N(d) and all d (or for all n, d
simultaneously). This uniform threshold is a deep analytic result
(Griffin-Ono-Rolen-Zagier 2019 for existence; sharp bounds are open) and is
entirely out of scope for certificate-based formal verification with finite
rational boxes. The four certs here cover concrete small-n instances only.

### (c) Emitter framework integration

The current emitter (`JensenPolynomialHyperbolicityEmitter`) exposes only
`render_box` and is not yet registered as a first-class Telperion emitter with
`emit_body`/`certify.py` integration. This is a deferred capability follow-up.

---

## Summary Table

| Claim | Status |
|---|---|
| J^{2,n} hyperbolic for n=0,1,2,3 | KERNEL-VERIFIED (sorry-free, axioms clean) |
| Coefficient boxes certified | ARB-CERTIFIED (non-kernel, documented boundary) |
| d >= 3 hyperbolicity | DEFERRED to Phase 2 |
| Uniform threshold N(d) | OUT OF SCOPE |
| Proof of RH | FALSE (conjecture1_proved = False) |
