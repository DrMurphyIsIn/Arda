# Class P: what a positive von Mangoldt function buys you (and what it doesn't)

*Build of the literature scout "RH for class P (degree-1 FE + positive Lambda_F). With integer
frequencies class P is just {zeta}; the Beurling version is open". 2026-09-23.*

**`conjecture1_proved = False`.** Nothing here moves the Riemann Hypothesis or conjecture1.
Every claim below carries one of four tags: THEOREM-kernel-checked, THEOREM-paper-proof,
CONJECTURE-with-evidence, or HEURISTIC. Arb interval certificates are labelled as their own
trust class. They are rigorous computations, but they are not Lean kernel proofs.

---

## The story in one page

The scout asked a clean question. Take the functions that look like zeta from both ends:

* **P1.** A degree-1 functional equation. In the strict version this is Riemann's own shape,
  pi^{-s/2} Gamma(s/2), with a pole only at s = 1.
* **P2.** A nonnegative von Mangoldt function: -F'/F = sum Lambda_F(n) n^{-s} with every
  Lambda_F(n) >= 0.

Does every such F satisfy RH?

The scout's answer is that with integer frequencies the question is empty. P1 by itself
already forces F = zeta (Hamburger 1921). In the twisted degree-1 world of Kaczorowski and
Perelli (any conductor, any gamma shift, Euler product or not), P2 still forces F = zeta, by
a new argument that runs through a mixture-of-Euler-products lemma. So "every F in class P
satisfies RH" is literally RH. Positivity rules out every Davenport-Heilbronn-type witness.
It rules out everything else too, so it gives no leverage beyond zeta itself. The only
genuinely open version is the Beurling one, with general frequencies.

This build does three things with that answer.

1. **It kernel-checks the negative controls that show which hypotheses are load-bearing.**
   The star is F(s) = zeta(s)(1 + 4*2^{-s} + 2*4^{-s}). Its coefficients are 1, 5, 7 and
   multiplicative, which gives a formal Euler product. It has a zeta-shape functional
   equation with conductor 4 and root number +1. It also has exact zeros at
   Re s = log_2(2 + sqrt 2) > 1 (numerically 1.7716).
   * All of this is proved in Lean, including the vanishing of the absolutely convergent
     Dirichlet series at the zero. The Euler product is proved in the form "the coefficients
     are multiplicative"; the decimal 1.7716 is numerical.
   * In the degree-1 frame of S^#_1 (conductor free), F fails only P2, and it fails it at
     n = 4: Lambda_F(4) = -11 log 2. This is proved both from the Dirichlet-ring identity
     and from the analytic -F'/F.
   * Under the strict conductor-1 reading of P1, F also fails P1: its gamma factor is
     zeta's, Gamma(s/2), but its conductor is 4.
2. **It certifies the other two controls, partly in the kernel and partly in Arb.**
   * The Davenport-Heilbronn-type mixture a*zeta(s)(1 + sqrt5*5^{-s}) + b*L(s, chi_5) has
     nonnegative coefficients exactly when a >= |b|. For every such mixture P2 fails, and
     earlier than the scout said (kernel). The mixture also has zeros off the critical line
     (Arb).
   * The E8 Epstein zeta, renormalized to frequencies sqrt n, has an Euler product and a
     degree-1 FE with root number +1, and it has no zero at all on Re s = 1/2 (all three
     kernel). It also satisfies P2 (exact computation to n = 2000, plus a two-line paper
     proof).
3. **It records the collapse theorem as a design note** (below). It separates the parts
   that are proved elsewhere, the parts that are sketched, and the elementary fragments that
   are now kernel-checked.

It also turned up one rigor gap in an existing repo tool. The node-sampling winding count
in `telperion/src/telperion/arb_dh.py` does not by itself exclude extra turning between its
boundary nodes (details in "Corrections"). The DH crown zero box that tool certified is
re-certified here with whole-segment enclosures, and the count is still 1.

---

## Where the artifacts are

| Artifact | What it is | Trust class |
|---|---|---|
| `telperion/examples/li_positivity/lean/Crux/Crux_axiso_literature.lean` | 40 theorems and 27 supporting lemmas in 4 sections (A to D). No `sorry`, no `admit`, no `native_decide`, no new axioms. `#print axioms` on each of the 40 theorems gives `[propext, Classical.choice, Quot.sound]` or fewer | Lean kernel (v4.34.0-rc1, Mathlib de5ce8a9) |
| `neg_control_check.py` / `.json` | Exact Lambda_F(n) for n <= 4096 as integer vectors over log p, the closed form, growth exponent, mpmath FE residuals | exact integers + mpmath |
| `e8_arb_certificate.py` / `.json` | Certified first zeta zero; whole-boundary zero counts for G; FE samples; exact P2 identity for n <= 2000 | Arb + exact integers |
| `dh_mixture_check.py` / `.json` | FE samples; Lambda scans for n <= 3000; certified off-line zeros of the mixture; DH crown re-certification | Arb + mpmath |
| `hermite_theta_check.py` / `.json` | Theta identity enclosure; Hermite eigen-relations; positivity threshold | Arb + mpmath quadrature |
| `integer_case_stress.py` / `.json` | Optimization stress test of the integer-frequency collapse, q <= 24, N = 3000 | floating point (evidence only) |
| `arb_winding.py` | The rigorous argument-principle counter used above | Arb |

To reproduce:

```
cd telperion/examples/li_positivity/lean && lake env lean Crux/Crux_axiso_literature.lean
cd telperion/research/axiso_literature && for f in neg_control_check e8_arb_certificate \
    dh_mixture_check hermite_theta_check integer_case_stress; do /usr/bin/python3 $f.py; done
```

(In the build session the Lean check ran under the machine-slot wrapper `leanlock.sh`. The
Python stack was python-flint 0.6.0, mpmath 1.3.0, numpy 1.23.5, scipy 1.13.1 and
sympy 1.14.0, on the system Python 3.9.)

---

## Claim-by-claim ledger

The scout filed eleven claims. Here is where each one stands after this build.

### 1. Hamburger: zeta-shape FE with integer frequencies forces F = c*zeta

**THEOREM-paper-proof (classical), not rebuilt here.** Hamburger, Math. Z. 10 (1921). Nothing
in this build touches it. It is the base case that makes the integer-frequency question
empty.

### 2. The collapse: S^#_1 + a(1) = 1 + Lambda_F >= 0 forces F = zeta

**THEOREM-paper-proof (sketch; new as far as the scout found).** The design note below
records the argument, its five steps and its dependencies. Kernel-checked here:

* **The elementary half of step (1)** (`theta_eq_zero_of_nonneg_twist`,
  THEOREM-kernel-checked). Suppose n^{-i theta} is a nonnegative real for every n = 1 mod q.
  Then theta = 0. Only n = q + 1 and n = 2q + 1 are needed: they are coprime, so no
  nontrivial power relation links them. The non-elementary input, KP's periodicity of
  a(n) n^{i theta}, stays a black box.
* **Load-bearing status of P2.** The negative control F = zeta*P lies in S^#_1 (conductor 4,
  root number +1). It has a(1) = 1 and multiplicative coefficients a(n) >= 1, yet F is not
  zeta. So "a(n) >= 0" cannot replace "Lambda_F(n) >= 0" in the theorem. That is exactly
  `LSeries_coefF` + `coefFA_isMultiplicative` + `completedF_fe` + `vonMangoldtF_two_pow`
  (THEOREM-kernel-checked).

Numerical evidence: `integer_case_stress.py` optimizes over the admissible periodic f (see
"The integer-frequency stress test"). The scout's own check drew random samples. This one
maximizes.

### 3. With an Euler product: S_1 = {zeta, L(s + i theta, chi)} and P2 picks out zeta

**THEOREM-paper-proof (classical classification + one line), not rebuilt.** The one line
("chi(p) p^{-i theta} = 1 for all good p") is the same mechanism as
`theta_eq_zero_of_nonneg_twist`.

### 4. Negative controls: positivity of coefficients is not enough

**Upgraded to THEOREM-kernel-checked** for every load-bearing fact of the Euler-product
control, and for the P2 failure of the non-Euler (DH-type) control. The details are in
Section A and Section B below. There are two refinements to what the scout wrote:

* The DH-type mixture fails P2 **earlier** than the scout's cumulant witnesses 42 and 546.
  Kernel-checked (`vonMangoldtDH_36`, `dhMixture_P2_fails`): Lambda is negative
  * at n = 12 when 0 < b < a,
  * at n = 36 when a = b,
  * at n = 6 when b < 0, and also at n = 4 once (a - b)^2 > 2.

  That these are the *first* failures is only a numerical observation, from the scans at
  the tested parameters. The scout's own values at 42 and 546 are also kernel-checked
  (`vonMangoldtDH_42`, `vonMangoldtDH_546`, `dhMixture_P2_fails_squarefree`). The formula
  kappa_3 = -8ab(a - b) presumes the normalization a + b = 1. Without it the value is
  -8ab(a - b)/(a + b)^3.
* The scout says the mixture has **zeros in sigma > 1** (Bohr-type argument). That is **not
  certified here, and stays THEOREM-paper-proof (sketch)**. Such zeros need many prime
  phases aligned at once, and they sit far too high to find. What is certified instead
  (Arb) is a zero **off the critical line in 1/2 < sigma < 1** at height about 61, for
  (a, b) = (1/2, 1/2) and for (3/5, 2/5). That suffices for the negative-control point:
  FE + nonnegative coefficients do not give RH.

### 5. Beurling reduction: FE as a self-dual positive crystalline measure; epsilon = +1; c_0 formula

**THEOREM-paper-proof (sketch) + numerics re-verified, not kernel-checked.** In
`hermite_theta_check.py`:

* The theta identity sum_{n>=1} (8 pi n^2 - 2) e^{-pi n^2} = 1 is enclosed in Arb as
  1 +/- 2e-76, with an explicit tail bound. This is the (-1)-eigenfunction pairing for the
  Dirac comb. The exact identity follows from differentiating theta(1/t) = sqrt(t) theta(t)
  at t = 1.
* The Hermite eigen-relations hold to about 1e-29 by quadrature.
* The (+1)-eigenfunction f_plus = 16 y^2 (y^2 - 3) e^{-pi x^2} is positive exactly for
  |x| > sqrt(3/(2 pi)) = 0.690988, so the scout's "> 0 for |x| > 0.691" is right.
* The pairing of f_plus with the Dirac comb is 28.5886 > 0.

The equivalence "FE <=> M^ = eps M" (Bochner-Chandrasekharan, Kahane-Mandelbrojt) was not
re-derived.

### 6. Uniformly discrete g-integers force zeta

**THEOREM-paper-proof (sketch), not re-derived here.** It depends on Lev-Olevskii 2015 as a
black box. Kernel-checked: the last algebraic step
(`den_eq_one_of_bounded_denominators`, THEOREM-kernel-checked). If every power of a rational
g has denominator dividing a fixed D, then g is an integer. The pigeonhole step G in Q is
elementary but was not formalized.

One note for readers of the sketch. Once G is inside N, the finish is Hamburger (claim 1),
because P1 there is the zeta-shape FE. It does not need claim 2.

### 7. Kahane-Mandelbrojt finite basis: g-integers generate an order in a real number field

**THEOREM-paper-proof, CONDITIONAL on the KM hypothesis H_0.** The build does not verify
that H_0 follows from P1 + P2. Kernel-checked: only the K = Q branch
(`rat_integral_is_int`), which says a rational algebraic integer is an integer. This is a
Mathlib wrapper recorded for completeness. The Cayley-Hamilton step is
`IsIntegral.of_mem_of_fg` in Mathlib.

### 8. Normalization is load-bearing: the renormalized E8 Epstein zeta

**Upgraded to THEOREM-kernel-checked**, with two exceptions. The existence of a zeta zero is
Arb-certified. P2 for G is an exact computation to n = 2000 plus a two-line paper proof.
Section C below has the details. One correction to the wording: the scout
says G is excluded from P1 "only because its pole sits at s = 9/2".

* In the strict zeta-shape reading of P1 (pi^{-s/2} Gamma(s/2)), G is also excluded by its
  gamma factor. It has (2 pi)^{-s/2} Gamma(s/2 + 7/4), a shift mu = 7/4.
* "Only because of the pole" is right in the general degree-1 frame (free Q, free mu with
  Re mu >= 0), where G's abscissa and pole at 9/2 are the only violations.

### 9. Positivity alone is capped at de la Vallee Poussin

**THEOREM-paper-proof (dlVP part, standard); HEURISTIC (the claim that beating dlVP needs
arithmetic). Not built.**

### 10. A Beurling class-P RH counterexample would be a Hilberdink [alpha, 0]-system with alpha > 1/2

**THEOREM-paper-proof (reduction) + literature fact. Not built.**

### 11. Novelty: RH for Beurling zetas with a zeta-type FE is not addressed in the literature

**CONJECTURE-with-evidence (literature absence). This build did not re-run the literature
search.**

---

## What the Lean file proves

File: `telperion/examples/li_positivity/lean/Crux/Crux_axiso_literature.lean`, namespace
`CruxAxisoLiterature`. Every theorem below is THEOREM-kernel-checked.

### Section A: the Euler-product negative control F(s) = zeta(s)(1 + 4*2^{-s} + 2*4^{-s})

* `LSeries_coefF`: for Re s > 1, F(s) = sum a(n) n^{-s} with a(n) = 1 + 4[2|n] + 2[4|n].
  The proof goes through Mathlib's `LSeries_convolution'` and `LSeries_one_eq_riemannZeta`.
  `coefF_eq` gives a(n) = 1, 5, 7 according as v_2(n) = 0, 1, >= 2.
* `coefFA_isMultiplicative`: a is multiplicative. This is the Euler product, with local
  factor (1 + 4x + 2x^2)/(1 - x) at 2.
* `Pfac_fe`: 2^s P(s) = 2^{1-s} P(1-s), the degree-0 FE of the factor.
* `LambdaF_one_sub`, `LambdaF_eq`, `completedF_fe`: (4/pi)^{s/2} Gamma(s/2) F(s) is
  invariant under s -> 1 - s, away from the poles of Gamma_R. That is the zeta-shape FE with
  conductor 4 and root number +1.
* `negControl_zeros` (the certificate). Take any k in Z and set
  s_k = log_2(2 + sqrt 2) + i(2k+1) pi / log 2. `two_cpow_neg_sZero` gives
  2^{-s_k} = -1 + sqrt2/2, and the theorem gives all of the following:
  * F(s_k) = 0, zeta(s_k) != 0, Re s_k > 1 and Im s_k != 0;
  * the Dirichlet series with coefficients in {1, 5, 7} vanishes at s_k;
  * Lambda_F(s_k) = Lambda_F(1 - s_k) = 0 and F(1 - s_k) = 0, with Re(1 - s_k) < 0.
* `vonMangoldtF_two_pow` (ring form). Any L with sum_{d|n} L(d) a(n/d) = a(n) log n at
  n = 1, 2, 4, 8, 16 has L(2^k) / log 2 = 5, -11, 41, -135.
  `vonMangoldtF_two_pow_consistent` shows the hypothesis is satisfiable.
* `vonMangoldtF_of_logDeriv` (analytic form). Take any Lambda whose L-series converges
  somewhere and equals -F'/F at all large real x. Then Lambda(1) = 0,
  Lambda(2) = 5 log 2 and Lambda(4) = -11 log 2. The proof uses Mathlib's `LSeries_deriv`
  and the uniqueness theorem `LSeries.eq_of_LSeries_eventually_eq`. The theorem does not
  construct Lambda_F; its existence is classical.

### Section B: the DH-type mixture a*zeta(s)(1 + sqrt5*5^{-s}) + b*L(s, chi_5), with a + b = 1

* `chi5_eq_jacobiSym`, `chi5D_apply`: chi_5 is the Legendre symbol mod 5. `chi5D` is
  Mathlib's `DirichletCharacter` built from `quadraticChar (ZMod 5)`.
* `LSeries_coefDH`: for Re s > 1 the coefficient sequence `coefDH a b` is exactly that of
  a*zeta(s)(1 + sqrt5*5^{-s}) + b*`DirichletCharacter.LFunction chi5D s`.
* `coefDH_nonneg`: every coefficient is >= 0 when |b| <= a.
* `vonMangoldtDH_36`:
  * Lambda(4) = (2 - (a-b)^2) log 2
  * Lambda(6) = 4ab log 6
  * Lambda(12) = -4ab(a-b) log 12
  * Lambda(36) = -4ab(1 - 3(a-b)^2) log 6
* `vonMangoldtDH_42`: Lambda(42) = -8ab(a-b) log 42. `vonMangoldtDH_546`: at a = b = 1/2,
  Lambda(546) = -2 log 546.
* `dhMixture_P2_fails`: for every a >= |b| > 0, one of Lambda(6), Lambda(12), Lambda(36) is
  negative. `dhMixture_P2_fails_squarefree` proves the same with the scout's witnesses
  6, 42, 546.
* `cumulant_pm_one`: the ring identities kappa_2 = 4ab, kappa_3 = -8ab(a-b) and
  kappa_4 = -2 + 8 mu^2 - 6 mu^4 for a +-1 variable with mean mu = a - b.

### Section C: the E8 witness G(s) = zeta(s/2 + 7/4) zeta(s/2 - 5/4)

* `key_identity`: Gamma_C(w) zeta(w) zeta(w-3) = (w-3)(w-1)/(4 pi^2) Lambda(w) Lambda(w-3)
  for w not an integer. `LambdaG_one_sub`: Gamma_C(s/2 + 7/4) G(s) is invariant under
  s -> 1 - s. `Gammaℂ_shift`: that factor is the scout's (2 pi)^{-s/2} Gamma(s/2 + 7/4) up to
  the constant 2(2 pi)^{-7/4}.
* `GE8_ne_zero_on_critical_line`: G(1/2 + it) != 0 for every real t. On that line the first
  factor sits at Re 2 and the second at Re -1, where zeta has no zeros
  (`riemannZeta_ne_zero_of_re_eq_neg_one`, via the FE).
* `GE8_zero_of_zeta_zero`: take any zeta zero rho with 0 < Re rho < 1. Then G vanishes at
  2 rho + 5/2, which has 5/2 < Re < 9/2, and at the mirror point 1 - (2 rho + 5/2), which has
  Re < -3/2.
* `GE8_eulerProduct`: for Re s > 9/2, G is the product of two Euler products.

### Section D: fragments of the paper sketches

`theta_eq_zero_of_nonneg_twist`, `den_eq_one_of_bounded_denominators` and
`rat_integral_is_int`, as described under claims 2, 6 and 7.

---

## What the computations certify

**Negative control** (`neg_control_check.json`).
* Lambda_F(n) is computed exactly for n <= 4096, with logs as integer vectors over the
  primes. It matches the closed form with no mismatches:
  * Lambda_F(p^k) = log p for odd p;
  * Lambda_F(2^k) = (1 - p_k) log 2, where p_k = (-2 + sqrt2)^k + (-2 - sqrt2)^k;
  * Lambda_F(n) = 0 off prime powers.
* Lambda_F(4^j) < 0 for every j >= 1. The computation checks this exactly for
  4^j <= 4096. For all j there is a two-line argument: for even k >= 2 both
  (-2 + sqrt2)^k and (-2 - sqrt2)^k are positive, and the second is at least
  (2 + sqrt2)^2 > 11, so 1 - p_k < 0.
* The effective exponent log|Lambda_F(2^k)| / log 2^k tends to log_2(2 + sqrt2) = 1.7716.
  So Selberg's Euler-product axiom (theta < 1/2) fails badly, while the coefficients a(n)
  stay bounded (Ramanujan holds).
* At 40 digits, |F(s_0)| = 1.9e-41 and the FE residuals are below 3e-41.

**E8 witness** (`e8_arb_certificate.json`).
* `acb.zeta_zero(1)` encloses rho_1 = 1/2 + 14.134725141734693790457...i with radius 3e-46.
  Independently, Lambda_zeta(1/2 + it) changes sign on [14.1347, 14.1348].
* Whole-boundary zero counts for G:
  * exactly one zero in [3.3, 3.7] x [28.1, 28.4] (Re 7/2, off the line);
  * exactly one in the mirror box [-2.7, -2.3] x [-28.4, -28.1];
  * none in [0.3, 0.7] x [28.1, 28.4], the box straddling the critical line at the same
    height.
* All four FE samples contain 0.
* The P2 identity Lambda_{zeta(w) zeta(w-3)}(n) = Lambda(n)(1 + n^3) >= 0 holds exactly for
  n <= 2000. In the Beurling variable s the log-coefficient at the g-prime power p^{k/2} is
  (p^{-7k/4} + p^{5k/4})/k > 0. Positivity does not see the rescaling.

**DH-type mixture** (`dh_mixture_check.json`).
* FE samples: all six contain 0. This is consistent with root number +1 for L(s, chi_5),
  which is classical but not formalized.
* The Lambda scans for n <= 3000 match every kernel closed form. The first negative index is
  12 at (0.6, 0.4) and at (0.9, 0.1), 36 at (0.5, 0.5), and 4 at (1.5, -0.5).
* Certified off-line zeros:
  * exactly one zero in [0.70, 0.86] x [61.0, 61.3] for a = b = 1/2 (mpmath root
    0.779557 + 61.168517i);
  * exactly one in [0.72, 0.88] x [60.95, 61.25] for (3/5, 2/5) (root 0.804688 + 61.083549i).
* Classical DH crown box [0.79, 0.83] x [85.68, 85.72]: re-certified as winding 1. The
  empty control box [0.60, 0.70] x [85.68, 85.72] gives 0.

**Hermite / theta** (`hermite_theta_check.json`): see claim 5.

### The integer-frequency stress test

The setup: f periodic mod q, even, f(1) = 1, f >= 0, and fixed by the unitary DFT. That
last condition is the zeta-shape FE with conductor q and root number +1. Our negative control
is such an f for q = 4: it takes the values 7, 1, 5, 1 on the residues 0 to 3. For each
q <= 24 the script maximizes min_{2 <= n <= 3000} Lambda_F(n)/log n with SLSQP from random
feasible starts.

A first run with N = 64 was not discriminating. For many q the optimizer found f whose first
negative log-coefficient lies beyond 64. For example, at q = 11 it found
zeta(s)(1 + sqrt11*11^{-s}), whose first failure is at n = 121. So the run uses N = 3000.
The results are in `integer_case_stress.json` and summarized in the addendum at the end of
this file. This is floating-point evidence at finite N, not a proof.

---

## Design note: the integer-frequency collapse theorem

**Statement (THEOREM-paper-proof, sketch).** Let F lie in the extended Selberg class of
degree 1, S^#_1, with a(1) = 1 and Lambda_F(n) >= 0 for all n. Then F = zeta.

**Proof sketch** (the scout's argument, reorganized; dependencies in brackets).

1. **Periodicity and theta = 0.**
   * [KP 1999, Acta Math 182, Thm 2(iii)] a(n) n^{i theta} = f(n) with f periodic mod q.
   * P2 gives a(n) >= 0, because F = exp(sum b(n) n^{-s}) with b >= 0.
   * For n = 1 mod q this makes n^{-i theta} = a(n) >= 0, so theta = 0.
   * Kernel: `theta_eq_zero_of_nonneg_twist` (elementary half).
2. **Split good and bad primes.**
   * Let y_p = p^{-s} for p | q and x_p = p^{-s} for p not dividing q.
   * Expanding the periodic coefficients in characters gives
     F = sum_chi R_chi(y) E_chi(x), with E_chi = prod over good p of (1 - chi(p) x_p)^{-1}.
3. **Mixture lemma.**
   * Fix small positive y_0. The coefficients of log F at squarefree good n are the joint
     cumulants of (chi(p)) under the weights c_chi proportional to R_chi(y_0). The weights
     may be complex; the moment-cumulant relations are formal and do not care.
   * P2 makes all these cumulants >= 0. Dirichlet's theorem [primes in progressions] supplies
     every multiplicity pattern across residue classes.
   * Restrict the cumulant generating function to a generic positive ray. This gives
     k(u) = log sum_chi c_chi e^{u w_chi}, with nonnegative Taylor coefficients and distinct
     w_chi.
   * [Pringsheim] Together with e^k >= 1 on [0, R), this makes k entire. So the exponential
     polynomial is zero-free.
   * [Polya-Ritt / Hadamard] A zero-free exponential polynomial has one term. P2 at good
     primes forces that one term to be chi_0.
   * Analyticity in y_0 then gives R_chi = 0 identically for chi != chi_0.
4. **Landau.**
   * Now F = R(y) zeta(s) prod_{p|q} (1 - p^{-s}), and log R has nonnegative coefficients.
   * [Landau] The abscissa of log R is a real singularity of R. Periodic coefficients give
     at most a simple pole at s = 1 (Hurwitz representation), so R has no pole there.
     R >= 1 to the right of the abscissa excludes a real zero. So the abscissa is <= 0.
   * Hence F/zeta is analytic and zero-free for sigma > 0.
5. **Degree 0.**
   * [KP / Conrey-Ghosh: S^#_0 consists of Dirichlet polynomials] F/zeta is a Dirichlet
     polynomial over the divisors of q, with a degree-0 FE. The FE reflects the zero-free
     half-plane, so it is zero-free everywhere.
   * [Polya-Ritt again] So it has a single term. Then a(1) = 1 forces it to be 1, so q = 1
     and F = zeta.

**Attack surface for a hostile referee.**
* The exact form of KP Thm 2(iii) and of the parameter theta. The scout read it through
  Zaghloul's verbatim quotation, not from KP directly.
* That the S^#_1 FE matches zeta's gamma factor after step 3. Step 5 needs the degree-0
  quotient to satisfy a genuine degree-0 FE; this is where KP's invariants (the xi-invariant)
  enter.
* The convergence bookkeeping for formal series in infinitely many variables in step 3. The
  argument only ever uses finitely many variables at a time.
* The claim that nothing in the literature already covers this.

**What the controls say about the hypotheses.**
* The Euler-product control shows that "a(n) >= 0" is too weak: it is in S^#_1, not zeta,
  and fails P2 at 4.
* The DH-type controls show that the conclusion does not need the Euler product: they fail
  P2 at 12, 36 or 6.
* The E8 witness shows that in the Beurling setting the pole normalization cannot be
  dropped. It satisfies P2 and has an Euler product and a degree-1 FE. It has no zero on
  the critical line, yet it has zeros off it: every nontrivial zeta zero gives one, and
  the first is Arb-certified.

**Relation to the repo's FE-uniformity barrier.** `telperion/docs/RH_BARRIER_FE_UNIFORMITY_DESIGN_2026-09-18.md`
was **retracted in part on 2026-09-19**: it is "sound but empty". The collapse theorem is
consistent with that verdict. Shrinking the integer-frequency degree-1 FE bundle by
positivity (P2) does exclude the DH-type witnesses, but what is left is exactly zeta.
(Shrinking it by the Euler product instead leaves {zeta, L(s + i theta, chi)}.) An
argument that is uniform over class P is therefore an argument about zeta, and the class
gives neither a barrier nor a shortcut.

---

## Corrections and cautions raised by this build

1. **DH-type P2 failures come earlier than stated** (kernel-checked): 12, 36, 4/6, not only 42
   and 546.
2. **DH-type zeros in sigma > 1 are not certified.** What is certified are off-line zeros in
   1/2 < sigma < 1.
3. **E8 "only because of the pole"** is right in the general degree-1 frame, not in the
   zeta-shape frame, where the gamma shift 7/4 also differs.
4. **Rigor gap in `telperion.arb_dh.winding_number`.** It encloses D only at boundary nodes,
   then sums quadrant changes between consecutive nodes. Consecutive node values in adjacent
   quadrants do not exclude the value path going the long way round, or making an extra
   turn, between the nodes. So "a returned integer is a rigorous zero count" in
   `telperion/docs/QC_DH_SCOUT.md` section 4 overstates the method. `arb_winding.py` closes
   the gap: it evaluates on the complex ball covering each whole boundary piece and accepts
   a piece only if that enclosure lies in an open half-plane. Re-run with it, the crown box
   still gives winding 1 and the control box 0, so the published conclusion stands. The
   method is what needed fixing.
5. **Scratch-directory collision** (process note). The build shared the session scratchpad
   with another lane that used the same subdirectory name. No repo file was affected.

---

## What remains open or unbuilt

* The collapse theorem itself (claim 2) as a formal proof. It needs KP Thm 2, Pringsheim,
  Polya-Ritt and Landau in Lean; none of these is in Mathlib in the required form.
* Hamburger, KP's S_1 and S^#_1 classifications, Lev-Olevskii, Kahane-Mandelbrojt: cited,
  not formalized.
* Zeros of the DH-type mixture in sigma > 1.
* The FE of L(s, chi_5) (its root number), which is needed to put the mixture in S^#_1.
  Mathlib has the FE for primitive characters with a Gauss-sum root number; evaluating that
  Gauss sum as +sqrt5 was not done.
* A kernel proof of the existence of a zeta zero. It would turn `GE8_zero_of_zeta_zero` into
  an unconditional off-line zero; today that step is Arb.
* The Beurling class-P RH question: still open. The reductions (epsilon = +1, uniformly
  discrete => zeta, KM order, the Hilberdink [alpha, 0] description) are paper-level.

---

## Addendum: integer-frequency stress test results (N = 3000)

Recomputed by `integer_case_stress.py` (SLSQP, 6 random feasible starts per q, cutting-plane
working set). For every modulus q from 2 to 24, the best admissible f found (even,
DFT-self-dual, f >= 0, f(1) = 1) still has a negative log-coefficient below n = 3000.
That is what the collapse theorem predicts. The column "first negative n" is for that best f.

| q | dim of (+1)-eigenspace | max over f of min_{n<=3000} c(n) | argmin n | first negative n |
|---|---|---|---|---|
| 2 | 1 | -3.1000 | 1024 | 4 |
| 3 | 1 | -4.3333 | 729 | 9 |
| 4 | 2 | -1.3993 | 2048 | 4 |
| 5 | 2 | -5.8017 | 3000 | 12 |
| 6 | 2 | -2.4121 | 324 | 36 |
| 7 | 2 | -2.0724 | 2352 | 12 |
| 8 | 3 | -2.8284 | 2280 | 4 |
| 9 | 3 | -2.3450 | 243 | 20 |
| 10 | 3 | -2.5783 | 1500 | 4 |
| 11 | 3 | -2.0451 | 1980 | 4 |
| 12 | 4 | -2.2213 | 2160 | 4 |
| 13 | 4 | -1.4703 | 2535 | 4 |
| 14 | 4 | -1.2898 | 1764 | 4 |
| 15 | 4 | -1.1992 | 2700 | 4 |
| 16 | 5 | -1.3518 | 2640 | 4 |
| 17 | 5 | -1.1365 | 2280 | 4 |
| 18 | 5 | -1.0357 | 2916 | 4 |
| 19 | 5 | -0.8503 | 2394 | 4 |
| 20 | 6 | -0.7693 | 2520 | 4 |
| 21 | 6 | -0.8372 | 2646 | 4 |
| 22 | 6 | -0.6783 | 2904 | 6 |
| 23 | 6 | -0.7359 | 2622 | 4 |
| 24 | 7 | -0.6761 | 2280 | 6 |

`all_negative = True`. **Trust class: CONJECTURE-with-evidence.** This is
floating-point local optimization over a finite range n <= 3000, not a proof. The maximin
drifts toward 0 as q grows (about -0.68 at q = 24), so it says nothing uniform in q. A
first attempt with N = 64 was not discriminating. For many q the optimizer found f whose
first negative log-coefficient lies beyond 64: for example zeta(s)(1 + sqrt q * q^{-s}) for
prime q, which first fails at n = q^2.
