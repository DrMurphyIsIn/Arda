# Tier-C research targets: a discrete / arithmetic Gaussian invariant for Brualdi–Goldwasser

The frontier (from the eleven-module arc): a certifying invariant must be simultaneously **non-separable
across siblings** AND **integral / discrete** (the tie is an integer resonance; smooth invariants overshoot to
`Φ¹¹ = 1.00046 > 1` between integer arm-counts). This file ranks candidate mechanisms from the 2026-08-17
literature push (five threads, ultra-wide + verified; full report + citations in
`docs/DISCRETE_ARITHMETIC_GAUSSIAN_LIT_2026-08-17.md`), each with an exact telperion first-probe. Ranked by
fit against five criteria: (1) non-separable, (2) integral, (3) recursion-compatible, (4) tight at the tie,
(5) exact-buildable. `conjecture1_proved = False`.

**Headline (validated this session).** All five threads converge on ONE object: the tree's **matching
polynomial** / its integer matching counts `m_k`. For a tree, `char poly = matching poly` (Godsil–Gutman), so
`Φ¹¹`'s base `per(L)/∏deg = ∏(1+λ²)` is a fixed polynomial in the integer `m_k`; it is real-stable
(Heilmann–Lieb) hence **Lorentzian** (Brändén–Huh) — the canonical "discrete Gaussian" (non-separable
Hodge–Riemann Hessian + integral M-convex support). Exact check: for N(0,s) the tie N(0,5) (`m_k=[1,10,30,40,
25,6]`, `∏(1+λ²)=112`) is where `(64/621)^n` balances the integer object to `Φ¹¹=1`. Non-separability = sibling
edge-competition; integrality = `m_k ∈ ℤ`.

---

## 1. Matching polynomial as the discrete Gaussian — Lorentzian + integer `m_k` (STRONGEST; unifies T5-M1, T2-M2, T1)

**Mechanism.** `Φ¹¹`'s base `per(L)/∏deg = ∏_{λ>0}(1+λ²) = |det(I+iN)|` (Girardeau) equals the tree matching
polynomial on the imaginary axis, a polynomial in the integer matching counts `m_k`. The multivariate matching
polynomial is real-stable (Heilmann–Lieb) ⇒ Lorentzian (Brändén–Huh Prop 2.2): Hessian with ≤ one positive
eigenvalue (non-separable Hodge–Riemann) AND M-convex support (integral). The tie sits on the **boundary** of
the Lorentzian cone (Hessian drops rank — matching the `(99/529)·J` rank-1 sibling Hessian in
`gaussian_invariant.py`); the smooth `Φ¹¹=1.00046` overshoot is Eur's `(HR0)`-holds-`(HR1)`-signature-fails
boundary degeneration (i.e. leaving the integer `m_k` lattice). **Fit ~9/10** (1:2, 2:2, 3:1, 4:2, 5:2).
**Open bridge:** is the BG update (`a_v=1+S/(j+1)`, exponent 11, 64/621) Lorentzian-cone-preserving? (crit 3).

**First probe.** Build the multivariate matching polynomial of N(0,5) and near-neighbors in sympy (exact);
verify Lorentzian via the Brändén–Huh criterion (M-convex support + Hessian ≤ one positive eigenvalue on the
positive orthant); confirm the tie gives exactly one-positive-plus-a-zero (cone boundary) while an off-tie
integer neighbor is interior (`Φ<1`); reconstruct `Φ¹¹` from the integer `m_k` and show the smooth arm-count
interpolation leaves the `m_k` lattice (the overshoot). Reuses `girardeau.py`, `graphlimit.matching_polynomial`,
`lorentzian.py`, `mconvex.py`.

## 2. M-convex arm-count exchange certificate — integrality where BG needs it (T2-M3 + T3-continuant + Murota)

**Mechanism.** Encode a tree's shape as an integer arm-count / child-multiplicity vector `ν`; the claim is
`Φ¹¹(T) ≤ 1` tracks whether `ν` lies in an M-convex set with the tie an exposed point. Murota's local-exchange
⇒ global-optimality theorem is the "local certifies a global bound" engine, and the exchange axiom
`ν(α)+ν(β) ≥ ν(α−e_i+e_j)+ν(β−e_j+e_i)` is a **discrete, non-smooth barrier**: it can hold at integer arm-counts
and be violated at the interpolated non-integer count where the smooth energy overshoots. This is the crispest
formalization of "integral fixes the continuum overshoot," and the best recursion fit. **Fit ~9/10** (1:1, 2:2,
3:2, 4:2, 5:2). **Open bridge:** M-convexity is a set-condition (weaker non-separability than a Hessian).

**First probe.** Enumerate arm-count vectors for small near-star trees; set `ν(arm-vector)=log Φ¹¹` (exact
Fraction); test the M-concave exchange inequality; verify the tie is the unique maximizer, and that the smooth
interpolation between integer arm-counts VIOLATES the exchange inequality (that violation IS the overshoot).

## 3. Tree resolvent / branching continuant / Conway–Coxeter frieze (T1 + T3-A)

**Mechanism.** The cavity recursion `μ_v = 1/(j+1+Σμ_c)` is a tree resolvent `g_v=1/(z−Σg_c)` with **integer
diagonal `z=j+1`** (degree), equivalently a branching **continuant** (a determinant — non-separable) /
Conway–Coxeter frieze. Frieze integrality (Conway–Coxeter theorem) is *equivalent* to a discrete triangulation
resonance — the integer-arm-count phenomenon. Glide period `(n+3)/2` is a candidate home for the `11|n` gate.
**Fit ~9/10** (1:2, 2:2, 3:2, 4:1, 5:2). **Open:** the exponent-11 amplitude coupling to the frieze integrality
locus is unproven; the *message* continuant is solid classical theory.

**First probe.** Build the branching continuant over the tree (exact Fraction; on a path check
`K(n)=a_n K(n−1)+K(n−2)`); form the associated frieze and test the diamond-rule `det=1` / integrality along a
family sweeping arm-count; check whether the integrality locus hits exactly N(0,5) and fails on 12-vertex
non-tie neighbors.

## 4. Multivariate Krawtchouk diagonalization of the sibling operator (T4-C1)

**Mechanism.** Diaconis–Griffiths multivariate Krawtchouk polynomials — orthogonal for the multinomial,
realized (Genest–Vinet–Zhedanov) as matrix elements of an SO(d) rotation of independent binomials — diagonalize
a **composition (multi-type) birth–death process** on the integer simplex. The sibling set at a vertex is an
integer composition; the multivariate Krawtchouk basis diagonalizes the *joint* sibling operator: non-separable
(the rotation mixes coordinates) + integral (integer simplex). **Fit ~9/10** (1:2, 2:2, 3:2, 4:1, 5:2).
**Open:** that the `F_v` sibling operator is *exactly* the composition-BDP operator these diagonalize.

**First probe.** For the tie hub (5 arms), build the multinomial measure over child compositions with the tie's
exact `μ_c` weights; construct the multivariate Krawtchouk basis via the explicit rotation-matrix-element
formula (small `d`, rational angle); apply the sibling operator of the `F_v` recursion and test whether these
are its eigenfunctions and whether the tie is a distinguished integer eigen-degree.

## 5. Atomic-measure / heat-kernel-regularization FRAME (why only integral certifies) — T5-M3, T1

**Mechanism (explanatory, not the certificate).** The heat trace `Θ(t)=Σ_i e^{−tλ_i}` is a Laplace–Stieltjes
transform against a **step function** (atomic spectral measure; jumps = integer multiplicities); Hardy–Littlewood
/ Karamata Tauberian theory is the rigorous discrete-sum-vs-smooth-asymptotics boundary — the smooth Weyl term
is the leading Tauberian term, the discreteness is the step correction. This is the *reason* only an
atomic/integral invariant can certify (the tie lives in the jump part, not the smooth part) — it justifies
targets 1–4 rather than competing with them. Cross-check demonstrator: `exp(−ζ'_L(0)) = n·τ(G) = n` for trees
(Kirchhoff), integral but blind to siblings (wrong operator `D−A`). **Fit ~6/10** (frame).

**First probe.** Compute the heat trace / step-function spectral measure of `D+iA` on near-stars (mpmath),
exhibit the atomic jumps, and show the smooth Weyl interpolation is what overshoots — an independent
re-derivation of the continuum-overshoot pathology from the spectral side.

## 6. Long shots (conceptual bridges; do NOT gate results on these)

- **Theta / Poisson-summation self-duality → the 23-gate (T4-C4).** The theta discrete Gaussian
  (Agostini–Améndola) is the max-entropy discrete Gaussian; lattice-theta self-duality ties the analytic
  Gaussian to modular/cyclotomic structure — the natural bridge to the `resonance_carrier` 23-adic gate
  (`11|n`). Explains arithmetic rigidity, not tightness. Fit ~4–5/10.
- **Arakelov arithmetic-Hilbert–Samuel / height positivity (T5-M4).** Recast `Φ¹¹≤1` as an arithmetic-degree
  inequality: analytic torsion (Ray–Singer/Quillen, Bismut–Gillet–Soulé) = archimedean functional determinant,
  finite places = integer intersection numbers — the ideal integral+analytic split. But no established
  tree→arithmetic-surface functor; not buildable now. Fit ~4/10.

---

## The unifying meta-target

Every strong candidate (1–4) is a facet of one object: the tree's **matching polynomial** / integer matching
counts `m_k` — real-stable ⇒ Lorentzian (the discrete Gaussian), the Girardeau functional determinant, a
resolvent/continuant with integer diagonal, diagonalized by multivariate Krawtchouk on the integer simplex.
Non-separability = sibling edge-competition; integrality = `m_k ∈ ℤ`; the smooth overshoot = leaving the `m_k`
lattice / the Lorentzian-cone boundary. **The two bridges to close are (crit 3) that the BG amplitude update is
Lorentzian/matching-polynomial-native, and (crit 4) that arm-count integrality equals the support/`m_k`
integrality.** Each is a concrete, exact telperion probe (targets 1–4). Any that survives its probe becomes its
own module in a later session (brainstorm → plan → build). `conjecture1_proved = False`.
