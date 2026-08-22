# Literature push 2026-08-20 (round 2): effective Handelman/Polya degree bounds (gap D)

Follow-up deep-research run on the two zero-coverage gaps from WALL_CAPABILITIES_LIT_2026-08-20.md
(23 sources fetched, 112 claims extracted, 25 verified 3-vote: 24 confirmed / 1 killed).
GAP D (degree bounds) is now WELL-COVERED with explicit formulas; GAP E (formal tooling)
produced zero surviving claims AGAIN and remains open. `conjecture1_proved = False`.

## The practical answer for find_handelman_certificate

For a degree-d polynomial in n <= 4 variables, positive with margin lambda:

1. **Simplex, LP/Handelman (Powers-Reznick 2001, JPAA 164:221-229).** Polya exponent
   `k > d(d-1)/2 * L(p)/lambda - d` suffices (L(p) = max normalized coefficient), so
   enumeration degree `D = d + k` is GUARANTEED. Linear in 1/lambda, quadratic in d.
   Localized version (CPR 2011 Prop 2) restricts to closed subsets with the same formula.
   Transfers to general rational polytopes via the defining linear forms.
2. **Box [-1,1]^n, LP/Handelman (de Klerk-Laurent 2010 via arXiv:2605.15821 Thm 7).**
   Level r*n with `r >= 60^d * d^3 * n^d * (f_max/f_min)`. Linear in 1/lambda but the
   60^d n^d prefactor is astronomical (~2.1e11 at d=n=4): treat published bounds as
   EXISTENCE GUARANTEES, not search caps. (General-sets version Thm 8 is a single
   unrefereed May-2026 preprint — confidence medium; box case inherits peer review.)
3. **SOS/Putinar fallback (Baldi-Mourrain, Math. Prog. 2023).** First general POLYNOMIAL
   Putinar bound; under constraint qualification (holds on box/simplex) degree
   ~ eps^(-2.5n) <= eps^(-10) for n <= 4. Baldi-Slot (SIAGA 2024): O(f_max/f_min) on the
   hypercube — linear in inverse margin — with an Omega((f_max/f_min)^(1/8)) LOWER bound.

## The load-bearing negative result — and its cure

**Degree blow-up as lambda -> 0 is a PROVEN lower bound, not an upper-bound artifact:**
Stengle 1996 (N ~ margin^(-1/2), two-sided), Baldi-Slot's hypercube lower bound, and the
Castle-Powers-Reznick family p_a whose minimal Polya exponent grows like 4/(2-a) — and at
the exact tie a=2 NO exponent exists at all, even though p_2 >= 0. Consequence: a
degree-capped Handelman finder MUST fail at or arbitrarily near tight inequalities — and
every BG target is tight at the tie/arm. (Killed claim, do not cite: "the O(1/sqrt(eta))
upper bound itself implies fixed-degree failure at eta=0" — necessity comes ONLY from the
separate lower bounds.)

**The cure is facial: Castle-Powers-Reznick 2011, "Polya's theorem with zeros" (JSC
46(9):1039-1048).** (i) Theorem 2: complete IFF characterization of nonnegative forms WITH
ZEROS on the simplex admitting Polya-type certificates — the zero set must be a union of
faces, negative-support exponents dominated on each zero face, and every facially-minimal
residual subform q(alpha, F) strictly positive on the relative interior of F. (ii) Theorem 3:
explicit degree bound `N > d(d-1)/2 * L(p) * max(1/lambda, 1/theta)` governed by the RESIDUAL
FACIAL MARGINS — which do not vanish at the tie — not the global minimum. Their worked
example's Theorem-3 bound (24/(2-a)) asymptotically matches the true minimal exponent
(4/(2-a)).

This mirrors what the g-lemma work already does implicitly (arm = unique gamma-saturator,
strictness local off the tie, equality by rfl at the arm) — but CPR makes it a REUSABLE
CERTIFICATE SHAPE: check Theorem 2's facial conditions, get Theorem 3's finite degree.

## Telperion consequences

- `find_handelman_certificate` should keep its small default degree and treat misses as
  expected near tight cells — escalating degree is provably hopeless AT the tie.
- New emitter candidate: **facial Handelman** (`emit_polya_with_zeros`) — input: the zero
  face(s) + residual subforms; certificate: CPR Theorem 2 conditions (each an existing
  emitter shape: face containment = linear, residual positivity = ordinary Handelman on a
  smaller face with NONVANISHING margin) + Theorem 3 degree bound for termination.
- Open fit question (carried forward): do the g-step/Bcap tight cells, mapped to simplex
  coordinates, satisfy Theorem 2's conditions (zero set = union of faces)? If yes, the
  DirectPolya g-step gets a guaranteed-terminating finder.

## Gap E: still zero coverage (2 rounds)

leanprover/sos status, Coq micromega/psatz certificate internals, RealCertify exact SOS
rounding, HOL Light REAL_SOS, VIPR 2.0 / verified MILP beyond 1.0 — no surviving verified
claims in either round (sources were fetched but claims did not survive verification or were
budget-dropped). A dedicated, narrower follow-up (fetch the micromega docs and leanprover/sos
repo DIRECTLY rather than via search fan-out) is the right next attempt.

## Primary sources (verified)

- Powers, Reznick, JPAA 164 (2001) 221-229 (via arXiv:2103.02924 Thm 4, arXiv:1802.02752)
- Castle, Powers, Reznick, J. Symbolic Comput. 46(9) (2011) 1039-1048 (full PDF verified)
- Baldi, Mourrain, Math. Programming Ser. A (2023), arXiv:2111.11258 (Thm 1.7, Cor 3.9)
- Baldi, Slot, SIAGA 8(1) (2024), arXiv:2302.12558; Laurent, Slot, Optim. Lett. 17 (2023),
  arXiv:2109.09528
- Stengle, J. Complexity 12 (1996) 167-174
- Heijmans-Kuryatnikova, Vera, Zuluaga, arXiv:2605.15821 (2026 preprint; Thm 7 = de
  Klerk-Laurent SIOPT 20:3104-3124 (2010))

*Run wf_5e201cf1-76e (105 agents). Open questions carried forward: standard-description
Handelman LOWER bounds (explicitly open per Laurent-Slot); refined Polya constants
(C_3 = 3/2, C_4 = 4232/2505, arXiv:1802.02752) for small d; CPR facial conditions on the
actual tie cells. `conjecture1_proved = False`.*

---

# ADDENDUM (same day): Gap E closed by DIRECT FETCH (not search fan-out)

After two zero-coverage search rounds, direct fetches of the four primary targets answered
everything. Lesson recorded: for tooling/status questions, fetch the repo/docs directly.

## 1. leanprover/sos — the missing SOS finder backend EXISTS and is ACTIVE (highest value)

Lean 4 `by sos` tactic (Apache 2.0, ~104 commits, CI, maintained by the Lean org):
reify goal -> encode SDP -> CSDP -> round float Gram matrices to RATIONALS (LDL^T +
Lagrange four-square; facial reduction for rank-deficient cases) -> kernel-decidable
`Certificate.checks` predicate INDEPENDENT of CSDP correctness. Certificates are (c, p)
pairs, c in Q>=0, rational-only throughout. Handles constrained goals, strict
inequalities, equalities, and power refutation for non-SOS nonnegative polynomials
(Motzkin). **`by sos?` reports the witness as a frozen `sos_witness` invocation — the
exact freeze discipline Telperion already uses.** Deps: Mathlib4, hex-mv-poly
(Mathlib-free kernel-decidable polynomial substrate), csdp-ffi, BLAS/LAPACK.

TELPERION CONSEQUENCE: this closes the "certifier not discoverer" gap for the SOS side
(Putinar / SOSRefutation emitters currently require user-supplied certificates). Two port
routes: (a) emit goals that `by sos?` freezes into `sos_witness` terms (fastest); (b) port
the CSDP-plus-exact-rounding pipeline into telperion's sos_sdp.py as the finder, keeping
our own certifier (cleanest fit with the untrusted-by-design pattern).

## 2. Coq micromega/psatz internals — the shipped production analogue, fully documented

Certificate format: Positivstellensatz cone refutations (-1 in Cone(S)); cone expressions
built from input polynomials, squares, sums, products; proof-term constructors PsatzAdd /
PsatzMulE / PsatzIn. Witness discovery: lra/lia search LinCone (positive-constant
combinations); nra/nia/psatz use an EXTERNAL ORACLE (CSDP, depth-bounded cone search, may
miss refutations; proof cache). Checking is REFLEXIVE and kernel-level: the cone witness
is normalized by ring and checked to be -1. **Key structural note: Coq's `lia` = linear
arithmetic + CUTTING PLANES + case splits — a shipped, kernel-checked Chvatal-Gomory
implementation.** Lean's `omega` (which emit_cg_round already emits) is the analogous
engine, confirming the CG emitter's Lean side rests on production-grade integrality
machinery.

## 3. VIPR status — v1.1 (2024), no proof-assistant integration exists yet

Repo (Zuse Institute, C++, active): spec v1.0 (2017) + v1.1 (2024, incomplete derivations
for Gomory cuts); tools viprchk (+ parallel variant), viprttn (certificate tightening),
viprcomp (completes incomplete certificates via SoPlex), vipr2html. NO v2.0, NO certified
presolve, NO proof-assistant or SMT integration in the repo. CONSEQUENCE: telperion's
emit_cg_round (VIPR-style rules -> kernel-checked Lean via omega) appears to be genuinely
novel territory — nobody has shipped a Lean-emitting CG certificate checker.

## 4. RealCertify (Magron-Safey El Din, arXiv:1805.02201) — superseded for our purposes

Maple package, hybrid symbolic-numeric SDP with rational SOS output. Correct shape but a
Maple dependency; leanprover/sos delivers the same capability natively in our target
ecosystem. Deprioritized.

*Gap E status: CLOSED. Priority port: leanprover/sos as the Putinar-finder backend.
conjecture1_proved = False.*
