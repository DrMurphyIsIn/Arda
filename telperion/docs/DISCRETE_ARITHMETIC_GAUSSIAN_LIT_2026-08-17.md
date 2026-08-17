# Discrete / arithmetic Gaussian invariant for Brualdi–Goldwasser — literature research report (2026-08-17)

**A cited, adversarially-verified idea inventory.** Five parallel research threads, scored against five fit
criteria, seeded by the discrete heat kernel on ℤ and extended (per session direction) to spectral zeta /
functional determinants / Arakelov and to heat-kernel regularization. `conjecture1_proved = False`; this is
idea generation, not a proof.

## The target

The eleven-module telperion arc closed every standard avenue on BG with a reason, converging on one frontier:
a certifying invariant must be simultaneously **(A) non-separable across siblings** (the recursion
`F_v = (64/621) a_v^11 ∏_c F_c`, `a_v = 1 + S/(j+1)`, `μ_v = 1/(j+1+S)`, `S = Σμ_c` couples children through
the symmetric mode; single-variable bounds `x ≥ φ(μ)` are LP-infeasible) **and (B) integral / discrete** (the
tie N(0,5) is an *integer* resonance — the smooth energy `x(s) = −log Φ¹¹(N(0,s))` has `x(5)=0` but `x'(5)≠0`
and overshoots to `Φ¹¹ = 1.00046 > 1` at non-integer `s≈4.82`). The 23-adic carrier gives integral-but-
separable; the smooth Lewis–Riesenfeld Gaussian gives non-separable-but-smooth. BG needs their intersection.

**Fit criteria** (0/1/2 each): (1) non-separable, (2) integral/discrete, (3) recursion-compatible, (4) tight
at the tie, (5) exact telperion-buildable. The filter is **(1) AND (2) together**.

---

## Central finding: the discrete/arithmetic Gaussian is (very plausibly) the tree's MATCHING POLYNOMIAL

The five threads, run independently, converge on one object — the tree's **matching polynomial** / its
sequence of **integer matching counts `m_k`** (`m_k` = number of k-matchings) — as the carrier that is
non-separable AND integral *by construction*:

- **It is the Girardeau functional determinant.** For a tree/forest, `char poly = matching poly`
  (Godsil–Gutman 1981), so `Φ¹¹`'s base `per(L)/∏deg = ∏_{λ>0}(1+λ²) = |det(I+iN)|` is a fixed polynomial in
  the integer `m_k`. Integrality (criterion 2) is intrinsic — no zeta-regularization needed — and any smooth
  interpolation over arm-counts leaves the integer `m_k` lattice, which **is** the `Φ¹¹=1.00046` overshoot.
- **It is a Lorentzian polynomial** — literally the "discrete Gaussian" of the Brändén–Huh theory. The
  multivariate matching polynomial of any graph is real-stable (Heilmann–Lieb 1972), and real-stable ⇒
  Lorentzian (Brändén–Huh Prop 2.2). Lorentzian = **(A)** Hessian with ≤ one positive eigenvalue
  (Hodge–Riemann, non-separable) **AND (B)** M-convex support (discrete-convex, integral) — the meta-target's
  native home. The tie sits on the **boundary** of the Lorentzian cone (Hessian drops rank), matching the
  rank-1 `(99/529)·J` sibling Hessian computed in `gaussian_invariant.py`; the smooth overshoot is exactly
  Eur's `(HR0)`-positivity-survives-while-`(HR1)`-signature-degenerates boundary phenomenon.
- **It is a tree resolvent / continuant.** The cavity recursion `μ_v = 1/(j+1+Σμ_c)` is a resolvent /
  Green's-function recursion `g_v = 1/(z − Σg_c)` with **integer diagonal `z = j+1`** (the degree) — the
  matching/characteristic polynomial is its denominator — and equally a branching **continuant** /
  Conway–Coxeter frieze, whose integrality is a discrete (triangulation) resonance.
- **Its coupled sibling operator is diagonalized by multivariate Krawtchouk polynomials** (Diaconis–Griffiths;
  Genest–Vinet–Zhedanov as SO(d) rotations of binomials), living on the integer simplex — the discrete-Hermite
  eigenfunctions of the discrete Gaussian.

**Non-separability = sibling edge-competition; integrality = `m_k ∈ ℤ`.** **Precision (T2 capstone correction —
load-bearing).** The non-separability is carried by the **multivariate, per-edge** matching polynomial
(`Σ_M ∏_{e∈M} w_e`, one variable per edge; Heilmann–Lieb stable ⇒ Lorentzian), whose Hessian couples *distinct
edges* — that is the sibling-edge competition. It is **NOT** carried by the scalar sequence `m_k`: real-rootedness
gives `m_k` ultra-log-concave (Newton), but that is a *separable* one-variable statement, i.e. exactly the kind
of single-variable bound the arc PROVED fails. So the invariant is "the tree's **multivariate** matching
polynomial is Lorentzian, and `= tie` iff it sits on the **boundary** of the Lorentzian cone (Hessian drops rank
— the `(99/529)·J` degeneration)" — not "`m_k` is log-concave" (true generically, does not isolate the tie).
The scalar `m_k` are the *integral shadow* (criterion 2); non-separability must be taken from the multivariate
object and then specialized. Favourable note: the integrality-location gap is *smaller* here than feared — the
matching number `k` is itself an integer tree invariant, closer to BG's arm-count resonance than a generic
exponent-lattice support.

**Exact validation (this session).** For near-stars N(0,s): the `m_k` are integers, `∏(1+λ²)=per(L)/∏deg` is
a fixed polynomial in them (values 20, 48, **112**, 256, 576 for s=3..7 — identical to the monomer-dimer
partition function in `frustration_free.py`), and the tie N(0,5) (`m_k=[1,10,30,40,25,6]`, `∏(1+λ²)=112`) is
exactly where `(64/621)^n` balances the integer object to `Φ¹¹=1`. The matching polynomial localizes the tie
in the integer `m_k` lattice.

**Two open bridges** (the precise next targets, each a buildable probe; both were flagged honestly by threads):
1. **Recursion-compatibility (criterion 3).** Is the specific BG update (`a_v = 1+S/(j+1)`, exponent 11,
   constant 64/621) a Lorentzian-cone-preserving / matching-polynomial-native operation? Lorentzian is closed
   under products, differentiation, and some contractions, and the matching polynomial has a native tree leaf
   recursion `M_T = x·M_{T−v} − M_{T−v−u}` — but tying these to the BG-specific normalization is unproven.
2. **Arm-count vs support integrality (criterion 4).** In the literature the M-convex/integral structure lives
   in the polynomial's *support* (exponent lattice); BG's resonance is in the *arm-count*. Nobody has bridged
   these; the M-convex arm-count exchange certificate (below) is the candidate that puts integrality where BG
   needs it.

---

## Thread findings (candidates, fit-scores, verified citations)

### T1 — Discrete heat kernel / Bessel on trees → the stationary RESOLVENT
Top (9/10): the cavity recursion is literally a tree resolvent `g_v=1/(z−Σg_c)`, integer diagonal `z=j+1`;
the identity `a_v = 1/((j+1)μ_v)` converts `∏a_v^11` into an additive resolvent functional with an integer-
degree term. **Honest caveat (thread's own):** the *heat kernel* is a red herring — the load-bearing object is
its Laplace transform, the *stationary resolvent* `G(z)`, which drops the smooth `t` that criterion (2)
disqualifies. Weak: heat-mass/moment conservation (preserves the wrong linear symmetric mode).
Cites (verified): arXiv:2409.14344 (discrete Gaussian `K_ℤ=e^{−2t}I_x(2t)`); Chinta–Jorgenson–Karlsson,
Monatsh. Math. 178 (2015) 171–190, arXiv:1302.4644; Karlsson spectral-zeta arXiv:1907.01832.

### T2 — Lorentzian polynomials / discrete Hodge–Riemann / M-convexity (the structural twin)
- **M1 (9/10)** tie on the Lorentzian cone **boundary**; discrete HR (`M`-convex support) catches the smooth
  overshoot — Eur's `(HR0)`-holds-`(HR1)`-fails boundary exercise is the exact mechanism of the prior smooth
  failure.
- **M2 (8/10)** the multivariate matching polynomial of a tree is Lorentzian *for free* (Heilmann–Lieb
  real-stable ⇒ Brändén–Huh Prop 2.2); capacity/normalization (Schweitzer) is the candidate conserved quantity
  `=1` at the tie. Most self-contained probe.
- **M3 (9/10)** M-convexity of the arm-count vector as the integrality certificate; Murota local-exchange ⇒
  global-optimality; the exchange inequality holds at integer arm-counts and is violated at the interpolated
  overshoot.
- **M4 (control)** raw-tree independence polynomials are *not* known Lorentzian (Alavi–Malde–Schwenk–Erdős
  unimodality open; Bendjeddou–Hardiman need an `R_{W_4}` subdivision) — a control that should FAIL, steering
  toward the matching polynomial not the independence polynomial.
Cites (verified): Brändén–Huh, Ann. of Math. 192(3) 2020, arXiv:1902.03719 (Thm 2.16, 3.10, 3.14, Prop 2.2);
Eur expository notes (CMU); Heilmann–Lieb, CMP 25 (1972) 190–232; Bendjeddou–Hardiman, arXiv:2405.00511;
Anari–Liu–Oveis Gharan–Vinzant, arXiv:1811.01600; Schweitzer, arXiv:2011.14406; Murota, *Discrete Convex
Analysis*, SIAM 2003.

### T3 — Y-systems / cluster / Laurent phenomenon → continuant / frieze
- **A (9/10)** Conway–Coxeter frieze / branching **continuant**: the message recursion is a tree continued
  fraction = determinant (non-separable); frieze integrality (Conway–Coxeter theorem) = triangulation
  resonance (discrete). Glide period `(n+3)/2` a candidate home for the `11|n` gate.
- **B (8/10)** Laurent-Phenomenon-Algebra (Lam–Pylyavskyy) tree recursion; Caterpillar-Lemma integer-Laurent
  coefficients.
- **C (8/10)** Q-system conserved quantity = hard-particle/perfect-matching partition function (Di Francesco–
  Kedem) — non-separable + integer-valued.
- **D (framing)** Zamolodchikov periodicity = integer resonance (license, not the invariant).
**Honest caveat (thread's own):** the exponent-11/64-621 amplitude is BG-specific, *not* root-system Cartan
data, so the exact cavity map is probably **not** a literal cluster/Y-mutation and is likely **not**
Zamolodchikov-periodic — the robust part is the **continuant** (classical, verified).
Cites (verified): Conway–Coxeter, Math. Gazette 57 (1973); Fomin–Zelevinsky "Y-systems and generalized
associahedra," Ann. of Math. 158 (2003), arXiv:hep-th/0111053; Fomin–Zelevinsky "Laurent phenomenon,"
arXiv:math/0104241; Keller, Ann. of Math. 177 (2013); Lam–Pylyavskyy arXiv:1206.2611/1206.2612;
Di Francesco–Kedem, CMP 293 (2010), arXiv:0811.3027; Galashin–Pylyavskyy arXiv:1603.03942.

### T4 — Discrete Ermakov-LR + discrete orthogonal polys + theta
- **C1 (9/10)** multivariate Krawtchouk polynomials as eigenfunctions of composition birth–death processes /
  SO(d)-rotated binomials — genuinely non-separable (the rotation mixes coordinates) + integral (integer
  simplex). The strongest match in this thread.
- **C2 (7/10)** Karlin–McGregor univariate birth–death backbone (fails non-separability alone).
- **C3 (6–7/10)** difference-Ermakov (Hone exact discretization) — exact but inherently one-variable (fails
  criterion 1 alone; supplies the per-arm radial invariant).
- **C4 (4–5/10)** theta discrete Gaussian (Agostini–Améndola) — the 23-gate/cyclotomic arithmetic bridge, not
  a tightness certificate.
Cites (verified): Diaconis–Griffiths, arXiv:1309.0112 (JSPI 2014); Genest–Vinet–Zhedanov, J. Phys. A 46 (2013)
505203, arXiv:1306.4256; Griffiths arXiv:1603.00196; Karlin–McGregor, Trans. AMS 85 (1957); Hone, Phys. Lett.
A 263 (1999) 347–354; Common–Musette, Phys. Lett. A 235 (1997); Agostini–Améndola, SIAGA 3 (2019),
arXiv:1801.02373.

### T5 — Spectral zeta / functional determinants / heat-kernel regularization / Arakelov
- **M1 (9/10)** matching polynomial on the imaginary axis (the unifier): `char poly = matching poly` for trees
  (Godsil–Gutman) ⇒ the functional determinant is a polynomial in integer `m_k`; non-separable (sibling edge
  competition) + integral (`m_k∈ℤ`), and it explains the overshoot (smooth leaves the `m_k` lattice).
- **M3 (6/10, frame)** CJK tree heat trace = I-Bessel; heat-kernel regularization is a Laplace–Stieltjes
  transform against a **step function** (atomic spectral measure); Hardy–Littlewood Tauberian is the rigorous
  discrete-sum-vs-smooth-asymptotics boundary the tie sits on — the *reason* only an atomic/integral invariant
  can certify.
- **M2 (5/10, demonstrator)** `exp(−ζ'_L(0)) = ` pseudo-determinant of the Kirchhoff Laplacian `= n·τ(G)`;
  `τ=1` for trees, so integral but blind to sibling structure (wrong operator: `D−A`, not `D+iA`).
- **M4 (4/10, long shot)** Arakelov arithmetic-Hilbert–Samuel / height positivity — analytic torsion
  (Ray–Singer/Quillen, Bismut–Gillet–Soulé) + integer intersection numbers is the ideal integral+analytic
  split, but there is no established tree→arithmetic-surface functor; not buildable now.
Cites (verified): Godsil–Gutman, J. Graph Theory 5 (1981) 137–144; Chinta–Jorgenson–Karlsson arXiv:1302.4644;
Friedli–Karlsson, Tôhoku Math. J. 69 (2017), arXiv:1410.8010; Kirchhoff matrix-tree theorem; Faltings, Ann. of
Math. 119 (1984) 387–424; Bismut–Gillet–Soulé, CMP 115 (1988) 301–351.

---

## Cross-cutting hypothesis (confirmed by the convergence)

The discreteness/integrality enters through an **atomic (step-function) object** and the invariant is a
**functional of it**: the integer matching-count sequence `m_k` (equivalently the atomic spectral measure of
`D+iA`, equivalently the Lorentzian polynomial's M-convex support). T1 (resolvent), T2 (Lorentzian =
volume/capacity of a discrete measure), T3 (continuant integrality), T4 (Krawtchouk on the simplex), T5
(matching poly = integer `m_k`) are five faces of this one object.

## Honest scope

No proof, no new theorem about BG. The push identifies a concrete, well-founded candidate — the tree's
matching polynomial as the discrete/arithmetic Gaussian (real-stable/Lorentzian, integer `m_k`, the Girardeau
determinant, tie on the cone boundary) — and pins the two open bridges (recursion-compatibility; arm-count vs
support integrality) as the exact next targets. Citations independently re-verified this session:
Godsil–Gutman, Diaconis–Griffiths, Brändén–Huh, Chinta–Jorgenson–Karlsson, Heilmann–Lieb. The remainder were
thread-verified against ≥2 sources with confidence flags recorded above. `conjecture1_proved = False`.

See `TIER_C_TARGETS.md` for the ranked candidate mechanisms with concrete telperion first-probes.
