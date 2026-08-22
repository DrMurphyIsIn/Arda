# Telperion coverage gaps — certificate shapes & mathematics not yet covered (2026-08-21)

A literature + artifact dive (real algebraic geometry, computer algebra, ITP
ecosystems) for EXACT-certificate-emittable techniques missing from Telperion's
35 current emitters. Scope filter: a candidate must reduce a class of true
statements to an **exact, finite, kernel-checkable** certificate (untrusted
finder / trusted Lean kernel). Numeric-only / undecidable / trusted-float
techniques are flagged OUT OF SCOPE.

**Method note.** The deep-research workflow was degraded by a server-side rate
limit (only 6 sources fetched; all verification votes abstained — a false
"refuted", not a real refutation). Every candidate below was therefore
**hand-verified against its primary source** (arXiv / Mathlib docs / repos),
cited inline. Treat as operator-verified leads, not workflow-verified.

---

## Ranked candidates (fit × breadth × finder availability)

### 1. Primality certificates (Pratt / Lucas, then Pocklington–BLS) — TOP PICK
- **Proves:** `Nat.Prime p` for specific large `p` — an entire domain (number
  theory) Telperion does not touch.
- **Certificate:** Pratt's recursive witness — a primitive root `a` mod `p` plus
  the factorization of `p−1` with a Pratt certificate for each prime factor
  (recursion bottoms at 2). Finite, exact integer, compact.
- **Kernel-checkable / Mathlib precedent:** **already in Mathlib** —
  `Mathlib.NumberTheory.LucasPrimality.lucas_primality`. A machine-checked Pratt
  certificate for the BN254 scalar prime exists (Verified-zkEVM `CompPoly`); AFP
  has `Pratt_Certificate`. So the load-bearing lemma is done.
- **Finder:** trivial to strong — factor `p−1` offline (the expensive part),
  emit the recursion. Pocklington/BLS variants need only *partial* factorization
  of `p−1` (easier finder, larger reach).
- **Emitter difficulty:** LOW — Mathlib lemma exists; the emitter builds the
  recursive tree and discharges each node via `lucas_primality`.
- **Overlap:** none — new domain.
- **First probe:** emit a Pratt certificate for a 20–40 digit prime; verify it
  compiles with axioms `[propext, Quot.sound]`.
- Sources: leanprover-community mathlib4_docs LucasPrimality; blog.zksecurity.xyz
  poseidon-clean (CompPoly BN254); isa-afp.org Pratt_Certificate.

### 2. Matrix PSD via exact LDLᵀ + Schur-complement / Loewner-order certificates — HIGH
- **Proves:** `A ≽ 0` (positive semidefinite), `A ≻ 0`, Loewner comparisons
  `A ≼ B`, block-PSD, and quadratic constraints recast as LMIs — matrix
  inequalities Telperion's scalar-polynomial emitters cannot state.
- **Certificate:** an exact rational **LDLᵀ** (square-root-free Cholesky):
  `A = L D Lᵀ` with unit-lower-triangular `L` and diagonal `D`; `A ≽ 0 ⇔ Dᵢᵢ ≥ 0`.
  The identity `A = L D Lᵀ` is a polynomial matrix equality the kernel checks by
  `ring`/`decide`; the diagonal signs by `norm_num`. Schur complement reduces
  block-PSD to a smaller PSD + one rational Schur complement.
- **Kernel-checkable / Mathlib precedent:** Mathlib has `Matrix.PosDef`,
  `Matrix.PosSemidef`, and an `LDL` decomposition; the `LDLᵀ ≽ 0 ⇔ D ≥ 0`
  characterization is standard.
- **Finder:** deterministic exact rational LDLᵀ (no SDP, no rounding) — cheaper
  and more exact than the SOS SDP path.
- **Emitter difficulty:** LOW–MEDIUM (Mathlib support present).
- **Overlap:** complements SOS — SOS proves scalar-polynomial nonnegativity via
  a PSD Gram *found by SDP*; this directly certifies *matrix* PSD by exact
  factorization and unlocks LMI-shaped goals.
- **First probe:** certify a 3×3 rational PSD matrix by LDLᵀ; then a Schur-
  complement block reduction.
- Sources: mathlib4_docs Matrix/PosDef; cis.upenn.edu/~jean/schur-comp.pdf;
  Higham eprints.maths.manchester.ac.uk/1193 (pivoted Cholesky rank).

### 3. SONC — sums of nonnegative circuit polynomials — HIGH
- **Proves:** `0 ≤ p` for **sparse** polynomials where SOS/Pólya fail or blow up;
  independent of SOS (reaches nonneg-not-SOS polys, e.g. Motzkin-type, with
  sparsity preserved).
- **Certificate:** a decomposition into nonnegative *circuit* polynomials; each
  circuit's nonnegativity is decided by an **AM–GM inequality reduced to a linear
  system** in the exponent data — exact and rational. Dual SONC membership is an
  LP.
- **Kernel-checkable:** the per-circuit witness is `weighted-AM–GM`; needs a
  reusable Lean AM–GM lemma, then each circuit closes by `positivity`/`nlinarith`
  on the exact weights.
- **Finder:** exists — `sageopt` / POEM (relative-entropy / LP); the circuit
  step is LP, exact-rational-friendly.
- **Emitter difficulty:** MEDIUM (new AM–GM-of-monomials Lean lemma; no Mathlib
  circuit precedent).
- **Overlap:** extends the RationalSOS/SOS rungs into the sparse regime they
  scale badly on.
- **First probe:** a sparse nonneg-not-SOS polynomial `sageopt` certifies;
  emit the circuit + AM–GM witnesses.
- Sources: arXiv 1607.06010 (SONC Positivstellensatz); arXiv 1903.08966
  (SAGE/SONC duality); rileyjmurray.github.io/sageopt.

### 4. Fejér–Riesz / nonnegative trigonometric-polynomial positivity — MEDIUM-HIGH
- **Proves:** `0 ≤ q(θ)` for a trigonometric polynomial (Fourier positivity) — a
  domain Telperion lacks; also the circle-Positivstellensatz.
- **Certificate:** Fejér–Riesz factorization `q(ζ) = |p(ζ)|²`; over the reals a
  strictly-positive trig polynomial has an exact-rational SOS in `cos/sin`
  (a bounded-degree `A² + B²`). The factor / SOS pair is the witness, checked by
  `ring` after the `cos²+sin²=1` rewrite.
- **Finder:** spectral factorization (root-based) or an SOS-on-the-circle SDP
  rounded to exact rationals.
- **Emitter difficulty:** MEDIUM (trig normal-form + `cos²+sin²=1` handling).
- **Overlap:** none in the trig domain; conceptually a circle-restricted SOS.
- **Caveat:** an *exact rational* factor is not guaranteed for a merely-nonneg
  (tie-touching) polynomial; the exact-SOS form works for strictly-positive
  targets (Putinar on the circle). Flag ties as the boundary.
- Sources: arXiv 2005.11920, arXiv 0903.3639 (operator Fejér–Riesz).

### 5. Validated Taylor-model enclosures for log / arctan / sin / cos — MEDIUM
- **Proves:** two-sided rational brackets `lo ≤ f(x) ≤ hi` for transcendental `f`
  **beyond exp** — directly generalizes the existing `IntervalBracket` (exp-only).
- **Certificate:** a Taylor model `(P, I)`: rational Taylor polynomial `P` plus a
  rational remainder interval `I` with `f − P ∈ I` on the domain — a certified
  polynomial approximation, checked by the existing bracket machinery.
- **Finder:** classical (Taylor + Lagrange/Cauchy remainder); slow-converging
  functions (arctan) use faster polynomial families (Medina).
- **Emitter difficulty:** MEDIUM, incremental on `IntervalBracket`.
- **Overlap:** extends one existing emitter to a family of functions.
- **Precedent:** Taylor models formalized in Coq (`CoqApprox`) and PVS.
- Sources: inria.hal-00845791 (certified univariate Taylor models); Springer
  10.1007/978-3-642-28891-3_9 (Taylor models in Coq); arXiv 1406.1561 (Medina).

### 6. SAGE — signomial / exponential-polynomial positivity — MEDIUM (partial fit)
- **Proves:** nonnegativity of **signomials** `Σ cᵢ exp(aᵢ·x)` (arbitrary real
  exponents) — genuinely beyond Telperion's polynomial/rational scope; the
  exp-domain analogue of SONC.
- **Certificate:** AM–GM (X-SAGE) witnesses; membership is a relative-entropy
  program.
- **Emitter difficulty / caveat:** MEDIUM–HARD and **partially out of scope** —
  the relative-entropy optimum can be irrational, so a general exact-rational
  certificate is not guaranteed; the *monomial* AM–GM witnesses (rational
  exponents/weights) are exact and emittable. Pursue the exact sub-cone only.
- Sources: arXiv 2107.00345 (algebraic signomial optimization); sageopt docs.

---

## Finder-quality upgrade (not new expressivity)

### DSOS / SDSOS — LP/SOCP alternatives to the SOS SDP
Diagonally-dominant / scaled-diagonally-dominant SOS replace the PSD-Gram
condition with **linear (LP) / second-order-cone** conditions — which are
exact-rational-native (no SDP rounding). This does **not** add expressivity over
the existing exact SOS emitter (it certifies a *sub-cone*), but it is a cheaper,
rounding-free **finder** for the cases it covers, and "any even PD form is
r-dsos for some r". Worth adopting as an alternate finder behind the SOS rung.
Sources: arXiv 1706.02586 (Ahmadi–Majumdar).

---

## OUT OF SCOPE (flagged with reason)

- **Cylindrical Algebraic Decomposition / full real quantifier elimination** —
  procedural and doubly-exponential; produces a decision, not a compact reusable
  certificate. The ∃-**witness** direction (a sample point + sign conditions) IS
  exactly checkable and already reachable via `FiniteDecide`/case dispatch; the
  ∀-elimination side is not certificate-shaped.
- **LLL / lattice reduction as a prover** — the *output* (a short vector /
  integer relation) is an exact checkable ∃-witness (verify the relation + norm
  bound) and is worth a thin "integer-relation witness" emitter; but LLL proving
  *non-existence* is not a certificate.
- **General SDP/moment (Lasserre) beyond Putinar** — already covered by
  ConstrainedSOS; higher levels are the same shape at higher degree, not a new
  emitter.
- **ECPP primality** — checkable but heavy (elliptic-curve point-order data);
  Pratt/Pocklington give the same conclusion with a far simpler exact witness —
  prefer those first.

---

## Recommended sequence (in Telperion's lane, exact + Mathlib-backed first)

1. **Pratt/Lucas primality emitter** — Mathlib lemma already exists; highest
   fit, opens number theory, lowest emitter risk.
2. **Exact LDLᵀ matrix-PSD + Schur-complement emitter** — Mathlib PosDef/LDL
   present; opens matrix/LMI inequalities; deterministic exact finder.
3. **SONC emitter** — biggest expressivity gain on sparse positivity; needs one
   new AM–GM Lean lemma + an existing finder (sageopt).
4. **Taylor-model enclosures for log/arctan/sin/cos** — incremental on
   IntervalBracket; broad analytic-inequality reach.
5. **Fejér–Riesz trig positivity** — new Fourier domain (strict-positive first).
6. **DSOS/SDSOS** as a rounding-free alternate SOS finder.

All six preserve the untrusted-generator / trusted-kernel model: each emits an
exact witness the Lean kernel re-checks; a wrong certificate is a compile error.
Primality (#1) and matrix-PSD (#2) are the fastest wins because Mathlib already
carries the load-bearing lemmas.
