# Literature push 2026-08-20: new certificate capabilities for the three walls

Deep-research run (5 angles, 22 primary sources fetched, 109 claims extracted, 25 adversarially
verified 3-vote: 22 confirmed / 3 killed). Question: which published techniques could become NEW
exact Telperion emitters or proof strategies for the three wall layers left by the campaign —
(W1) tight master inequality / 23-gate strictness with the 1.000459 lattice-overshoot obstruction,
(W2) the R7 interpolation lemma (unimodal ratio, interior minimum ~q=34), (W3) the DirectPolya
g-step (Handelman/Putinar-shaped per-child envelope). Prior survey
`DISCRETE_ARITHMETIC_GAUSSIAN_LIT_2026-08-17.md` (matching polynomial / Lorentzian / M-convex) was
excluded as already internalized. `conjecture1_proved = False`.

**Headline.** Three genuinely new, EXACT, emitter-implementable certificate families survived
adversarial verification, one per wall — and the two directions that did NOT survive are recorded
as explicit coverage gaps, not silently dropped.

---

## Ranked emitter priority

1. **Ibrahim–Salvy contracted-cone positivity certificates for P-finite recurrences** (W2)
2. **VIPR-style Chvatal–Gomory rounding rule composed with Handelman lifting** (W1 overshoot)
3. **Kronecker-delta SONC lattice-vertex certificates** (W1, small-width windows only)
4. **Baker / p-adic linear-forms-in-logs** (W1 23-gate strictness — only after a unit-part
   reformulation; raw application FAILS, see the refuted probe)

---

## W2 — Ibrahim–Salvy positivity certificates for arbitrary-order P-finite sequences (STRONGEST FIND)

**What it certifies.** Positivity of a P-finite (holonomic) sequence of ARBITRARY order d — a
decisive advance over Kauers–Pillwein (termination only for order 2 and a subclass of order 3).
SODA 2024 (arXiv:2306.05930) + JSC 2025/26 (arXiv:2412.08576).

**The certificate object (exact, emitter-shaped).** A quadruple `(T, r, N, m)` with
`T in GL_d(Q)`, rational `r > 1`, integers `N, m`. Verification = sign checks of finitely many
polynomials in `Q(lambda)[n]` for `n >= N` (Sturm sequences over the algebraic dominant
eigenvalue) + finitely many initial-term checks. The polyhedral-cone variant (Prop 7 of
2412.08576) makes the final checkable object a RATIONAL POLYHEDRAL CONE with a
rational-perturbation stability guarantee — kernel-checkable in principle, directly analogous to
the existing Handelman/Putinar emitters. Maple implementation, 286 benchmarks.

**Fit against W2 (verified 3-0 on all constituent claims).**
- COLLECTIVE: the inductive invariant proves d(d-1) linear inequalities SIMULTANEOUSLY via cone
  contraction `A(n) C_r(v) subset C_r(v)` — non-separable by construction.
- INTERIOR-DIP TOLERANT: terms `n < N` are checked individually, so the q~34 interior minimum of
  r(q) is absorbed into the finite initial segment.
- REDUCTION-COMPLETE: P-finite closure properties reduce monotonicity, convexity, log-convexity,
  and comparison `u_n >= v_n` to positivity runs — so unimodality of r(q) (sign pattern of first
  differences, tail-shifted past the sign change) is in scope.

**The single genuine obstruction:** `best_template` is a max-over-family with no closed form and
is NOT known P-finite. Application requires first constructing a P-finite majorant/minorant
sandwich (or replacing the max by finitely many P-finite competitor families). Secondary risks:
the genericity hyperplane (`W^T U0 != 0`) is explicit but NOT effectively computable in general;
near-degenerate dominant eigenvalues near the q~34 resonance could violate unique-dominance;
hypotheses are Poincare-type recurrence + unique simple dominant eigenvalue.

**First probe.** Take the flatness config family from `g34_deep.py`; derive (or empirically fit +
then prove) a P-finite recurrence for pi_star(cfg(q)) (product structure suggests hypergeometric-
times-C-finite); sandwich best_template between two P-finite competitor-family sequences; run the
cone-certificate search on the difference sequences.

**Telperion emitter:** `emit_holonomic_positivity` — input: recurrence matrix A(n) over Q(n),
initial terms; output: (T, r, N, m) + Lean obligations = finite initial checks + Sturm-style
polynomial sign facts + the cone-contraction inclusion (linear algebra over Q). Feasible; the
finder is the hard half (mirror the checker->searcher pattern used for Handelman).

## W1 overshoot — Chvatal–Gomory rounding, VIPR certificate format (TOP-RANKED for the lattice gate)

**What it certifies.** Inequalities valid on INTEGER points but FALSE on the continuous
relaxation — exactly the 1.000459 overshoot shape that killed every smooth/SOS/convex certificate.
VIPR (Cheung–Gleixner–Steffy, arXiv:1611.08832; IPCO 2017 / Math. Prog. Computation): flat
sequential deduction lists with four rules — linear combination, integer ROUNDING
(`c^T x >= v` to `c^T x >= ceil(v)` when the c-support is integer variables), assumption
introduction, unsplit discharge. Verified entirely in exact rational (GMP) arithmetic by
`viprchk`; rational multipliers provably sufficient for rational data; proof-assistant conversion
explicitly flagged feasible by the authors. Format still the maintained standard through
2024–2026 (certified propagation, SMT verification of VIPR certificates).

**The uncharted composition step (not in any cited paper):** the W1 envelope is POLYNOMIAL, so a
Handelman-product LINEARIZATION over the arm-count polytope must precede the rounding step before
the integrality gain applies. This is the open question: does
`emit_handelman -> linearize -> emit_cg_round` close on the concrete near-star window around
k~4.82?

**Telperion emitter:** `emit_cg_round` — a new deduction rule layered on the existing Handelman
machinery; Lean side is `Int.ceil` monotonicity + a linear-combination fold (all existing
tactic shapes). HIGH feasibility as a checker; the Handelman-lift composition is research.

## W1 overshoot — two positivity-side backups

**Mastrolilli high-degree-basis SoS (arXiv:1709.07966; SIAM J. Opt.).** The SOS obstruction is
the STANDARD LOW-DEGREE MONOMIAL BASIS, not positivity certification per se: a custom
polynomial-size spanning set of HIGH-degree polynomials recovers Bienstock–Zuckerberg and
satisfies all constant-pitch valid inequalities of 0/1 covering polytopes; for pitch-bounded
inequalities the relaxation COLLAPSES TO AN EXACT LP (generalized Sherali–Adams over the custom
basis) — rational, Farkas-certificate-shaped, kernel-checkable. Caveats: 0/1 setting (arm counts
need binarization), polynomial size only for fixed pitch, covering-form applicability to the W1
envelope is an open fit question.

**Kronecker-delta SONC (Dressler–Kurpisz–de Wolff, arXiv:1802.10004; MFCS 2018 / FoCM 2022).**
Exact representation theorem (iff) for polynomials nonnegative ONLY at feasible vertices of the
constrained Boolean hypercube, allowed NEGATIVE between them: f = sum of vertex Kronecker-deltas
(products of the linear box constraints) + violated-constraint multiplier terms; degree bound
n+d, exact rational coefficients. Precisely the overshoot shape — but worst-case 2^n delta
terms, so emitter-feasible only for SMALL-WIDTH slices (the finite arm-count window around the
dip), not the whole family.

**Degree calibration (Kurpisz–Leppanen–Mastrolilli lower bound TIGHT vs
Sakaue–Takeda–Kim–Ito upper bound, ACM ToCT).** Exact hypercube Lasserre certificates exist at
level `(n+2d-1)/2` — sharp. Positive: a priori termination bound for any finder. Negative: level
~n/2 grows with tree size, so no fixed-degree hypercube-SoS emitter covers the whole family —
finite windows only. (Two stronger framings of this phenomenon were REFUTED in verification; rely
only on this tight-level statement.)

## W1 23-gate strictness — Baker theory has the right SHAPE, wrong immediate domain

**Archimedean side (Levesque–Waldschmidt, arXiv:1312.7203) — confidence MEDIUM.** Theorem 4.1:
effective lower bound `|eps*alpha - p/q| >= (log(eps-bar+2))^(-kappa3 log max{|p|,q,2})` via
linear forms in logarithms; the paper REMARKS (not proves — 2-1 vote) it generalizes from unit
groups to ANY finitely generated subgroup of Q-times of a fixed number field — exactly the
23-gate's algebraic setting (amplitude products lie in a f.g. multiplicative subgroup; the target
(621/64)^(n/11) lies in a fixed degree-11 field). Bugeaud two-log bounds are stronger but need
`a` close to `b` — fails for 621/64 ~ 9.7. Baker constants are log-power with large kappa growing
in the number of generators: uniform strictness over growing amplitude alphabets NOT automatic.

**23-adic side (Palojarvi–Seppala, arXiv:2107.00971; IJNT 2023).** Fully explicit p-adic lower
bounds for linear forms in p-adic logs of rationals via Pade approximations; every constant in
closed form. Two hard gates: (i) arguments must be p-adic 1-UNITS — 621/64 has v23 = 1 and NO
23-adic logarithm, forcing a 22nd-power/unit-part maneuver first; (ii) worked explicit thresholds
are astronomical (m=1, p=11 example needs H >= 3*10^1672), likely above the n <= 4401 regime
entirely.

**REFUTED probe (0-3, do not retry):** the Bugeaud p-adic route on the raw target — it requires a
large p-power dividing a-b, and 621 - 64 = 557 is PRIME, not divisible by 23.

**Verdict:** rank behind CG-rounding and holonomic routes; probe only after reformulating the tie
ratio `prod a_v * (64/621)^(n/11)` multiplicatively into the 1-unit log domain.

---

## Refuted claims (adversarial verification — do not rely on)

1. Degree ~n-L SOS lower bound for CG cuts on `{sum x_i <= L+eps}` (1-2).
2. "No fixed-degree SoS certificate exists; level ~n/2 NECESSARY for all such problems" — only
   the tight-level statement above survived (0-3).
3. The 23-adic Bugeaud probe on the raw target (0-3; 621-64 = 557 prime).

## Coverage gaps — NOT assessed by this round (honest holes, next search targets)

- **Direction (d): effective Handelman/Polya degree bounds** (Powers–Reznick, Averkov,
  post-2020) produced NO confirmed claims — so whether `find_handelman_certificate`'s enumeration
  is guaranteed to terminate at feasible degree on the real DirectPolya target (W3) remains
  UNANSWERED. This was the most directly actionable question and needs a dedicated follow-up.
- **Direction (e): 2020–2026 formalized positivity tooling** (Lean SOS tactics, Magron–Safey El
  Din exact SDP rounding, arithmetic-circuit certificates) produced NO confirmed claims — the
  porting landscape is unassessed.

## Open questions carried forward

1. Does `emit_handelman -> linearize -> emit_cg_round` close on the near-star window (the
   1.000459 dip at k~4.82)?
2. Is r(q) (or a P-finite sandwich around best_template) holonomic of Poincare type with a unique
   simple dominant eigenvalue near the q~34 resonance?
3. Can the 23-gate target be moved into the 23-adic 1-unit log domain (unit parts / 22nd powers),
   and do explicit thresholds ever descend to n <= 4401 — or is only the ineffective-but-uniform
   archimedean route viable?
4. (Gap d) Do effective Handelman degree bounds certify the W3 finder's termination?

## Primary sources (all peer-reviewed, verified by fetch)

- arXiv:1611.08832 — Cheung, Gleixner, Steffy: VIPR verifying-integer-programming-results format
- arXiv:1709.07966 — Mastrolilli: high-degree-basis SoS / Bienstock–Zuckerberg via SA
- arXiv:1802.10004 — Dressler, Kurpisz, de Wolff: SONC over the constrained hypercube
- ACM ToCT 10.1145/3626106 + Sakaue et al. SIOPT 27(1) — tight (n+2d-1)/2 Lasserre level
- arXiv:2306.05930 (SODA 2024) + arXiv:2412.08576 (JSC) — Ibrahim, Salvy: positivity
  certificates for P-finite sequences
- arXiv:1312.7203 — Levesque, Waldschmidt: effective linear forms in logs / f.g. subgroups
- arXiv:1602.05463 — Bugeaud: two-log effective irrationality measures
- arXiv:2107.00971 — Palojarvi, Seppala: fully explicit p-adic linear-form bounds

*Full verification transcript: deep-research run wf_2d687a14-2c2 (104 agents, 22 sources, 25
claims 3-vote verified). `conjecture1_proved = False`.*
