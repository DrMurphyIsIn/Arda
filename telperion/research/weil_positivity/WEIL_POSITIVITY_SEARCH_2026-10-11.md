# Weil positivity: a Gram-matrix search for structure (2026-10-11)

**Status: numerical exploration only. Nothing in this note is progress on the Riemann
Hypothesis. `conjecture1_proved = False`.** Every positive finding below is an
already-known consequence of the explicit formula combined with the (numerically verified)
location of the low zeros of zeta; none of it is evidence for RH beyond what the computed
zeros already are.

Code: `weil_form.py` (explicit formula + Gram matrices, `--validate`),
`gram_experiments.py` (experiments 1-3 and the fake-prime control), `dh_control.py`
(Davenport-Heilbronn control), `rank_prediction.py` (eigenvalue counts vs zero counts).
Tables: `results/`. Logs: `logs/`. The 50/40-digit matrix dumps (8.8 MB, regenerable) are in
`results/matrices/`. Python: `~/hodge-engine/venv/bin/python` (mpmath 1.3.0,
numpy 2.5.3, scipy 1.18.1), because `~/e9-tools/venv` has mpmath/sympy but no numpy.
All runs used `OMP_NUM_THREADS=1`/`OPENBLAS_NUM_THREADS=1`.

The `prony/` subfolder in this directory was written by a different agent and is not
part of this work.

---

## Verdict first

* The explicit formula, in the convention below, is validated to 17-19 significant digits against the
  zeros of zeta. It is validated to 28 digits against the zeros of the Davenport-Heilbronn
  function, for the control.
* Every Weil Gram matrix computed for zeta is positive semidefinite to working precision.
  That covers supports a = 0.2 ... 5, two bases, n up to 188, and 40-80-digit arithmetic. That is expected: it is
  implied by RH for the low zeros, which is numerically known.
* The test can fail. For the Davenport-Heilbronn function (zeros off the line) the same
  machinery gives a minimal eigenvalue of -0.64 at a = 2 (n = 188), and the offending
  eigenvector's Fourier transform peaks at t = 84.5, next to the off-line zero
  0.8085 + 85.6993i. Perturbing the zeta prime weights by a relative 1e-11 also breaks
  positivity at n = 60.
* "Footprints" that did appear, all explained without any new operator:
  1. The number of non-negligible eigenvalues tracks 2 x (number of zeros the basis can see).
  2. The lowest eigenvectors are prolate-like. The first 3-7 of them overlap PSWF_k at
     0.93-0.996, against 0.24 for random functions. They carry > 99.9999 % of their Fourier energy
     in the zero-free window |t| < gamma_1 = 14.1347. That is a Slepian concentration
     problem, so the prolate resemblance is a consequence of the gap below the first zero.
  3. The Fourier transforms of the lowest eigenvectors vanish at the zeta ordinates. At
     a = 1 (prime powers 2, 3, 4, 5, 7 only, plus the archimedean term) the first five
     ordinates are matched to between 4e-9 and 3e-5, and the sixth to 1e-4. At a = 2, n = 100 the first eight are
     matched to between 1e-9 and 8e-5. This reproduces the Connes-Consani-Moscovici observation; it
     is forced by G = sum_gamma |F(gamma)|^2 and disappears when the primes are removed.
* No Hilbert-Polya-type footprint appeared. Toeplitz+Hankel fits in the Hermite basis are
  no better than for a random matrix with the same spectrum once a >= 2. Lanczos/Jacobi
  coefficients of G are irregular; those of the prime-free form are smooth and geometric,
  so the primes destroy, rather than create, simple tridiagonal structure.
* A structural fact worth keeping: the archimedean+pole part A alone stays positive only up
  to a*(n). That is 0.3947 at n = 30 and 0.3757 at n = 180, extrapolating to about 0.372,
  against log(2)/2 = 0.3466. Beyond that, A has a negative eigenvalue
  of size ~ e^a coming from the rank-2 pole term in the odd sector. G stays positive only
  because the prime operator cancels it, leaving eigenvalues of order 1e-11 ... 1e-16.

---

## 1. Convention and derivation

Test functions g: R -> R, compactly supported, at least C^6. Define

    F_g(s) = int g(x) e^{(s-1/2)x} dx,   so that F_g(1/2 + i t) = h(t) := int g(x) e^{itx} dx.

**Explicit formula (validated).** With rho running over the nontrivial zeros of zeta,
counted with multiplicity,

    sum_rho F_g(rho) = W(g) := POLE - PRIME - CONST + ARCH
      POLE  = F_g(0) + F_g(1) = int g(x) 2 cosh(x/2) dx
      PRIME = sum_{n>=2} Lambda(n) n^{-1/2} [ g(log n) + g(-log n) ]
      CONST = (log pi + euler_gamma) g(0)
      ARCH  = int_0^inf [ 2 e^{-2x} g(0) - e^{-x/2} (g(x) + g(-x)) ] / (1 - e^{-2x}) dx.

The ARCH integrand has a removable singularity at x = 0, and it is evaluated with 30 extra
digits near 0.

**Derivation.** Take xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s), which is entire of
order 1, has zeros exactly at the nontrivial zeros, and satisfies xi(s) = xi(1-s). For c > 1,

    sum_rho F(rho) = (1/2 pi i) [ int_(c) - int_(1-c) ] F(s) xi'/xi(s) ds
                   = (1/2 pi i) int_(c) [F(s) + F(1-s)] xi'/xi(s) ds,

using xi'/xi(1-s) = -xi'/xi(s) and s -> 1-s on the left line. Then expand

    xi'/xi(s) = 1/s + 1/(s-1) - (1/2) log pi + (1/2) psi(s/2) + zeta'/zeta(s).

* **Primes.** zeta'/zeta = -sum Lambda(n) n^{-s} converges on Re s = c. By Fourier
  inversion, (1/2 pi i) int F(s) n^{-s} ds = n^{-1/2} g(log n), and the F(1-s) term gives
  g(-log n).
* **Poles.** Shifting the 1/s + 1/(s-1) term to Re s = 1/2 crosses s = 1, with residue
  F(1) + F(0). On Re s = 1/2 the remaining integrand is odd under s -> 1-s, so it vanishes.
* **Gamma factor.** The -(1/2) log pi term gives -log pi * g(0). The (1/2) psi(s/2) term
  on Re s = 1/2 gives (1/2 pi) int h(t) Re psi(1/4 + it/2) dt. Gauss's integral
  psi(z) = -gamma + int_0^inf (e^{-u} - e^{-zu})/(1 - e^{-u}) du with u = 2x turns this into
  -gamma g(0) + ARCH.

Equivalently, ARCH - CONST = (1/2 pi) int h(t) [Re psi(1/4 + it/2) - log pi] dt.

**Weil form.** For real f, set f~(x) = f(-x) and B(f1, f2) = W(f1 * f2~), where
(f1 * f2~)(x) = int f1(y) f2(y-x) dy. Then F_{f*f~}(s) = F_f(s) F_f(1-s). At
rho = 1/2 + i gamma this equals |F_f(rho)|^2, so RH implies B(f,f) = sum_gamma |F_f(rho)|^2 >= 0
(Weil's criterion is the converse). The Gram matrix is G_jk = B(phi_j, phi_k).

**Bases.**

* **Cubic B-splines.** phi_j(x) = M4((x - c_j)/h) with c_j = -a + (j+2)h and h = 2a/(n+3),
  so each phi_j lives in [-a, a]. Then phi_j * phi_k~ = h M8((x - (j-k)h)/h), where M8 is
  the centred degree-7 B-spline. Because W is a functional of g alone, G is exactly
  Toeplitz, and n evaluations of W at 50 digits give the whole matrix. The pole term is in
  closed form, h^2 * 2cosh(d/2) * (sinh(h/4)/(h/4))^8. The prime sum is exact, and ARCH is
  done by tanh-sinh quadrature split at the knots. The mass matrix is M_jk = h M8(j-k), and
  eigenvalues are those of the pencil (G, M), i.e. Rayleigh quotients B(f,f)/||f||^2.
* **Hermite functions.** phi_k(x) = sigma^{-1/2} psi_k(x/sigma), k < n, with
  sigma = a/u* and u* chosen so that every |psi_k(u)| <= 1e-30 for |u| >= u*. These
  functions are not compactly supported, but each is below 1e-30 outside [-a, a].
  Cross-correlations have a closed form as displacement-operator matrix elements:
  sqrt(k!/j!) alpha^{j-k} e^{-alpha^2/2} L_k^{(j-k)}(alpha^2) with alpha = x/(sigma sqrt 2).
  F_j(0) and F_j(1) are in closed form. ARCH uses 24-point Gauss-Legendre panels, which
  change by less than 3e-39 when the panel count doubles. The basis is orthonormal (M = I).
  At fixed n the Hermite functions only really use about sqrt(2n+1)/u* ~ 60 % of [-a, a].

---

## 2. Validation

`python weil_form.py --validate` writes three tables to `results/validation_*.csv`.

| test function g | W(g) (prime + arch side) | zero side | difference | tail bound |
|---|---|---|---|---|
| `M8((x-0)/0.25) supp[-1.0,1.0]` | 0.004515319640985092874850559 | 0.004515319640985092876426447 | -1.5759e-21 | 2.48e-24 |
| `M8((x-0)/0.5) supp[-2.0,2.0]` | 0.0000006166267355069556603773406 | 0.0000006166267355069556600277358 | 3.496e-25 | 1.9375e-26 |
| `M8((x-0)/1.0) supp[-4.0,4.0]` | 2.504084784449736472796934e-8 | 2.504084784449736469988239e-8 | 2.8087e-26 | 1.5137e-28 |
| `M8((x-0.3)/0.25) supp[-0.7,1.3]` | -0.002049956577563617348181074 | -0.002049956577563617349449583 | 1.2685e-21 | 2.48e-24 |
| `M8((x-1.7)/0.5) supp[-0.3,3.7]` | -0.0000001505691452218112490320679 | -0.0000001505691452218112486279744 | -4.0409e-25 | 1.9375e-26 |
| `M8((x-2.5)/0.125) supp[2.0,3.0]` | -0.06758628672302214691476505 | -0.06758628672302214700212088 | 8.7356e-20 | 3.1744e-22 |
| `bump(x/1) supp[-1,1] (1000 zeros)` | -0.01577595019275865919766205 | -0.01577595019275866030773455 | 1.1101e-18 | 7.142e-17 |
| `bump(x/2) supp[-2,2] (500 zeros)` | -0.004753143281231127292649305 | -0.004753143281231127612482407 | 3.1983e-19 | 2.2629e-17 |

Zeros: imaginary parts of the first 20000 zeros (2000 cached at 20 digits, the rest from
`mpmath.zetazero` at 25 digits), with the last one at height 18046. The tail bound for the
spline tests is int_T^inf (1/2pi) log(t/2pi) * 2s(2/(ts))^8 dt. For the bumps it is the
size of the last term times the number of terms. The spline differences sit above the tail
bound. They match the accuracy of the zero ordinates: the first 2000 have 19-20
significant digits, an absolute error of about 1e-17 each. Relative agreement is 17-19
significant digits for zeta. For the Davenport-Heilbronn control (section 6) it is 28
digits, because those zeros were computed at 30 digits.

Whole-matrix checks:

* **Spline Gram, a = 1, n = 20.** Every Toeplitz entry against its zero sum:
  the largest |entry - zero sum| is 7.1e-21, against a tail bound of 3.5e-22 and a diagonal entry of 0.0194
  (`results/validation_spline_gram.csv`).
* **Hermite Gram, a = 1, n = 24.** The full 24 x 24 matrix against
  4 pi sigma sum_{gamma>0} Re(i^{j-k}) psi_j(sigma gamma) psi_k(sigma gamma) over the
  zeros below 427 (219 of them): max |G - zero side| = 8.5e-20, with max |G| = 2.19. The closed
  forms agree with quadrature to 2.7e-41, and the panel-doubling change is 3.4e-39
  (`results/validation_hermite_gram.csv`).
* **Davenport-Heilbronn formula.** Four shifted Gaussians agree to 1e-30. The formula
  itself is in section 6.

The convention is right, and the code that builds every matrix below is the validated code.

---

## 3. Experiment 1: Gram spectra

### B-spline basis (50 digits; `results/exp1_spline_spectra.csv`, full spectra in `exp1_spline_full_spectra.txt`)

| a | n | h | min eigenvalue of (G,M) | max | condition | # eig > 1e-8 |
|---|---|---|---|---|---|---|
| 0.5 | 60 | 0.0159 | 2.04e-6 | 3.73 | 1.8e6 | 60 |
| 1 | 10 / 20 / 40 / 60 | 0.0317 at n=60 | 4.3e-8 / 6.6e-10 / 4.8e-12 / 3.0e-13 | 3.77 | 1.2e13 | 10 / 19 / 36 / 54 |
| 1.5 | 60 | 0.0476 | 1.42e-13 | 4.11 | 2.9e13 | 53 |
| 2 | 60 | 0.0635 | 1.65e-13 | 4.85 | 2.9e13 | 51 |
| 3 | 60 | 0.0952 | 1.65e-14 | 6.37 | 3.9e14 | 50 |
| 4 | 60 | 0.127 | 2.75e-15 | 7.80 | 2.8e15 | 45 |
| 5 | 60 | 0.159 | 2.41e-16 | 9.58 | 4.0e16 | 43 |

The minimum is positive in all 28 (a, n) cases. It falls steadily with n and with a. The
plain eigenvalues of G, without the mass matrix, are also all positive.

### Hermite basis (40 digits; `results/exp12_hermite_summary.csv`)

| a | n | sigma | min eig G | max | # eig > 1e-8 | min eig A | min/max eig P |
|---|---|---|---|---|---|---|---|
| 0.5 | 60 | 0.0275 | 7.6e-3 | 4.08 | 60 | 7.6e-3 | +-2e-8 |
| 1 | 60 | 0.0549 | 1.6e-9 | 3.57 | 59 | -0.55 | -0.90 / 0.90 |
| 1.5 | 60 | 0.0824 | 1.1e-22 | 3.53 | 54 | -1.14 | -1.35 / 1.55 |
| 2 | 60 | 0.110 | 4.6e-41 | 3.73 | 47 | -1.80 | -1.88 / 2.70 |
| 3 | 60 | 0.165 | -2.7e-39 | 4.16 | 32 | -3.95 | -4.10 / 6.30 |
| 4 | 60 | 0.220 | -2.5e-39 | 4.85 | 22 | -8.25 | -8.31 / 12.2 |
| 5 | 60 | 0.275 | -1.1e-39 | 5.70 | 16 | -16.7 | -16.7 / 22.4 |

The n = 40 rows (same file) behave the same way. For a >= 3 the Hermite Gram matrix is
numerically singular at 40 digits. A zero above the band contributes weight of order
exp(-sigma^2 gamma^2), which is below 1e-40, so the smallest eigenvalues there are rounding
noise of size 1e-39 relative to a maximum of about 5. Their sign means nothing.
A rerun of (a = 3, n = 40) at 80 digits, with tail tolerance 1e-70 (so sigma = 0.137), gives
all 40 eigenvalues positive. The smallest are 4.6e-44 and 3.0e-41, and 28 exceed 1e-8
(`logs/herm_hp_a3_n40.log`).
In every case the minimum is above -1e-20, the threshold asked for.

### Eigenvalue count vs zero count (`results/exp1_rank_vs_zero_count.csv`)

Under RH (numerically true here) G = sum_{gamma>0} 2 Re(v_gamma v_gamma^*) with
v_gamma,j = F_j(1/2 + i gamma). Each zero adds a rank-2 piece (cosine and sine) of size
w(gamma) = v^* M^{-1} v. The natural prediction is therefore
count ~ min(n, 2 #{gamma : w(gamma) > 1e-8}).

| Hermite (a, n) | observed count | prediction |
|---|---|---|
| (3, 40) / (3, 60) | 20 / 32 | 26 / 38 |
| (4, 40) / (4, 60) | 14 / 22 | 16 / 24 |
| (5, 40) / (5, 60) | 10 / 16 | 10 / 16 |
| (a <= 1.5) | saturated at n (or n-1) | n |

So the count of significant eigenvalues is the zero-counting function N(T) at the basis's
effective bandwidth, times 2. The bandwidth is about sqrt(2n+1)/sigma for Hermite functions.
For splines it is fuzzy because sinc^8 leaks past the Nyquist frequency pi/h. In that case
aliased high zeros pile into the same dimensions, and the count saturates below n at large
a (43 of 60 at a = 5). This is the expected footprint of N(T) ~ (T/2pi) log(T/2pi e). It
is a restatement of the explicit formula, not new structure. Splines also never become
singular, because sinc^8 decays only polynomially and so infinitely many zeros contribute.

---

## 4. Experiment 2: G = A - P

A = POLE - CONST + ARCH (archimedean place plus the poles at 0 and 1) and P = PRIME, with
G = A - P. Spline basis, 50 digits (`results/exp2_spline_decomposition.csv`,
`exp2_spline_decomposition_extra.csv`, `exp2_A_alone_threshold*.txt`).

| a | primes in play (n <= e^{2a}) | min eig G | min eig A | eig range of P |
|---|---|---|---|---|
| 0.2, 0.3 | none | 0.117, 0.0136 (= A) | same | 0 |
| 0.3466 = log(2)/2 | none (2 sits at the edge) | 2.6e-3 | 2.6e-3 | +-1.9e-22 |
| 0.40 | 2 | 4.4e-4 | **-0.0141** | +-0.489 |
| 0.5 | 2 | 3.8e-6 | -0.255 | +-0.490 |
| 1 | 2, 3, 4, 5, 7 | 2.6e-11 | -1.20 | -1.37 / 1.69 |
| 2 | to 53 | 7.7e-12 | -4.27 | -4.30 / 6.86 |
| 3 | to 401 | 1.2e-12 | -13.1 | -13.1 / 18.6 |
| 5 | up to e^10 ~ 22026 | 1.9e-14 | -101.6 | -101.6 / 114.0 |

(n = 30 throughout. The n = 60 rows in the same file agree to within 5-17 %, and a = 5
differs most.)

* **A alone is positive only up to a threshold a*(n), and that threshold falls with n.**
  Bisection on the smallest eigenvalue of (A, M), with A's negative direction always in
  the odd sector:

  | n | a*(n) bracket |
  |---|---|
  | 30 | 0.394694 - 0.394697 |
  | 60 | 0.383498 - 0.383502 |
  | 90 | 0.379623 - 0.379626 |
  | 120 | 0.377654 - 0.377680 |
  | 180 | 0.375647 - 0.375673 |

  Three fit models were tried: a* + C/n, a* + (C + D log n)/n, and a* + C/n + D/n^2.
  Fitted on n <= 120, the last two predict 0.37565 and 0.37569 at n = 180, and the
  measurement is 0.37566. The extrapolated limit is 0.3714 - 0.3720 depending on the
  model. That is numerical extrapolation, not a bound, and it sits above
  log(2)/2 = 0.34657.
  For a <= log(2)/2 no prime enters and G = A. That is the Connes-Consani regime (Selecta
  Math. 2021: positivity for test functions supported in [2^{-1/2}, 2^{1/2}] needs only the
  archimedean place). Numerically, the archimedean+pole form stays positive a bit further,
  to about 0.372 extrapolated. There the prime 2 is already present in G, but it is not
  yet needed.
* **Where A fails.** By parity sector:
  * In the even sector, the pole term is rank 1 and positive. It rescues the archimedean
    symbol Re psi(1/4 + it/2) - log pi. That symbol is -5.37 at t = 0 and negative for
    |t| < 6.290
    (ARCH - CONST reaches -1.38 at a = 0.4).
  * In the odd sector, the pole term is rank 1 and negative, with direction
    int f(x) sinh(x/2) dx and eigenvalue ~ -e^a (-0.0177 at a = 0.4, -98.7 at a = 5).
  A loses positivity in the odd sector once that negative pole direction beats the
  barely-positive archimedean part.
* **Primes must and do matter.** For a >= 1, min eig A ~ -||P||, both of order e^a, and
  they cancel in G to leave a minimum of 1e-11 ... 1e-14. The near-perfect cancellation is
  between the odd-sector pole direction and the prime sum. At a = 5 the odd-sector minima
  of A and P are both -101.56. P is always indefinite, with an almost symmetric spectrum.

---

## 5. Experiment 3: structure search

### 3a(i). Fourier zeros of the minimal eigenvector (`results/exp3a_min_eigvec_fourier_zeros.txt`)

For the minimal eigenvector f_min = sum c_j phi_j, compute F(1/2 + it), find its real
zeros, and compare them with the zeta ordinates.

| a, n | primes used | |zero - gamma_k|, k = 1..9 |
|---|---|---|
| 1, 60 | 2, 3, 4, 5, 7 | 3e-7, 1e-6, 2e-7, 7e-6, 1e-5, 1e-4, 6e-3, 4e-3, 1e-2 |
| 1, 60 (2nd eigvec) | same | 4e-9, 2e-7, 7e-8, 9e-6, 3e-5, 9e-4, ... |
| 2, 100 | up to 53 | 1.2e-9, 2.0e-7, 2.3e-8, 1.3e-6, 3.5e-6, 1.4e-5, 7.9e-5, 5.6e-5, 8.8e-4 |
| 3, 100 | up to 401 | 6.8e-9, 5.4e-6, 5.0e-6, 1.3e-6 (only 4 ordinates in band) |
| control: A only, any a | none | 0.2 - 1.5 (no match) |

The zeros of zeta are "recovered" from a handful of primes plus the archimedean term. This
is the Connes-Consani-Moscovici observation ("Zeta zeros and prolate wave operators",
2023-24), reproduced here. It is forced by the explicit formula. G = sum_gamma |F(gamma)|^2,
so the minimiser makes |F| vanish where the weights sit. The extra Fourier zeros, spaced
about pi/a, are unconstrained, and removing the primes destroys the match.

### 3a(ii). Prolate overlaps (`results/exp3a_prolate_overlaps.txt`, `exp3a_prolate_bandwidth_scan.txt`)

PSWFs on [-1, 1] at bandwidth c come from the Bouwkamp tridiagonal matrix in the
normalised Legendre basis. Weil eigenvectors are rescaled to [-1, 1], and overlaps are
|<v_k, PSWF_m>| in L^2.

| a, n | best c (Omega = c/a) | eigvec k vs PSWF_k, k = 0..7 |
|---|---|---|
| 1, 60 | 14.75 (14.75) | .994 .992 .992 .988 .985 .925 .593 .229 |
| 2, 80 | 16.0 (8.0) | .975 .961 .954 .940 .974 .973 .975 .860 |
| 3, 100 | 10.5 (3.5) | .995 .993 .982 .933 .831 .594 .073 .242 |
| 4, 120 | 6.5 (1.6) | .996 .978 .927 .490 .194 .461 .751 .736 |

Baselines:

* Ten random orthonormal functions in the same spline space reach at best 0.24 mean max
  overlap.
* The 10 *highest* Weil eigenvectors reach 0.16, so they are not prolate. They are
  basis-limited high-frequency functions.
* The prime-free control A shows the same Sturm-type prolate pattern, shifted by one index
  because of its extra negative pole direction (0.76-0.85 with PSWF_{k-1}, a = 2).

**Explanation.** For a = 2, n = 60 the three lowest eigenvectors carry 0.99999999,
0.99999997 and 0.9999983 of their Fourier energy in |t| < gamma_1 = 14.1347, the
zero-free window. Minimising sum_gamma |F(gamma)|^2 over f in L^2[-a, a] is, to leading
order, the Slepian problem of concentrating F inside (-gamma_1, gamma_1). Its solutions
are PSWFs. The fitted bandwidth is not a stable constant: Omega = c/a falls from 14.75 to
1.6 as a grows from 1 to 4, and the overlap degrades beyond k ~ 4. So "lowest Weil
eigenvectors ~ prolates" is explained by the gap below the first zero plus generic Sturm
ordering. This does not test the deeper Connes-Moscovici claim that the prolate
operator's spectrum matches the zeros.

### 3b. Toeplitz+Hankel structure in the Hermite basis (`results/exp3b_toeplitz_hankel.txt`)

Relative Frobenius residual of the least-squares fit G_jk ~ T_{j-k} + H_{j+k}, n = 60:

| a | G | A | P | same spectrum, random eigenbasis | multiplication by log(1+r^2) (smooth-symbol control) |
|---|---|---|---|---|---|
| 0.5 | 0.12 | 0.12 | 0.49 | 0.29 | 0.076 |
| 1 | 0.22 | 0.16 | 1.00 | 0.38 | 0.088 |
| 2 | 0.49 | 0.30 | 0.99 | 0.58 | 0.10 |
| 3 | 0.69 | 0.57 | 0.98 | 0.73 | 0.12 |
| 5 | 0.86 | 0.94 | 0.98 | 0.86 | 0.14 |

At small a, G is only as T+H as its archimedean part is (G = A at a = 0.5). From a = 2 on
it is no better than a random matrix with the same eigenvalues. P is essentially never
T+H. In the spline basis G is exactly Toeplitz, but that is just translation invariance of
W, which carries no information. No footprint.

### 3c. Jacobi (Lanczos) coefficients (`results/exp3c_jacobi.txt`)

Lanczos at 60 digits with full reorthogonalisation, on the M-orthonormalised pencil
(a = 2, n = 60). The start vectors are the pole direction (coefficients of int f) and a
fixed pseudo-random vector.

* **Weil G.** beta_k = 0.24, 0.48, 0.90, 1.86, 0.55, 0.96, 1.62, 0.94, 0.50, 1.54, ... with
  no trend. From the pole start the Krylov space collapses at k ~ 14 (beta ~ 1e-3 to 1e-8),
  matching the ~14 even-sector eigenvalues that are not tiny, and then restarts in the tiny
  part of the spectrum. Random start: equally irregular.
* **Control A (no primes).** beta_k = 0.595, 0.773, 0.729, 0.688, 0.649, 0.612, ... with
  ratio 0.943-0.949, a smooth geometric decay, and alpha_k rising smoothly.

The archimedean operator has a regular Jacobi shape, and adding the primes turns it into
noise. No regularity attributable to zeta.

---

## 6. Experiment 4: controls (the test can fail)

### Davenport-Heilbronn

Take chi mod 5 with chi(2) = i and kappa = (sqrt(10 - 2 sqrt5) - 2)/(sqrt5 - 1). Then
f = (1 - i kappa)/2 L(s, chi) + (1 + i kappa)/2 L(s, chibar) has real coefficients
(1, kappa, -kappa, -1, 0) mod 5 and satisfies Lambda_f(s) = (5/pi)^{s/2} Gamma((s+1)/2) f(s)
= Lambda_f(1-s). The functional-equation residual is 3e-31. The explicit formula has no
pole term, uses Gamma((s+1)/2) in place of Gamma(s/2), takes "prime" coefficients c(n)
from -f'/f (computed by Dirichlet division), and has
CONST = (gamma + log pi - log 5) g(0) and ARCH with e^{-3x/2}. It was validated against
the six on-line zeros below 22 using shifted Gaussians, to 1e-30. The off-line zero was
refined to rho = 0.808517182456637 + 85.6993484853776 i.

Spline basis with h ~ pi/150, so frequencies near 86 are resolved (`results/exp4_dh_gram.csv`,
`exp4_dh_onset_scan.csv`):

| a | n | DH min eig | zeta min eig, same basis | peak of the DH minimal eigenvector's transform |
|---|---|---|---|---|
| 1 | 93 | +6.8e-5 | +1.1e-14 | - |
| 1.25 | 117 | +1.2e-9 | | |
| 1.5 | 141 | +1.9e-15 (40 digits) | | |
| 1.75 | 165 | +1.3e-16 (40 digits) | | |
| **2** | 188 | **-0.640** (confirmed at 30 digits) | +2.1e-17 (40 digits) | t = 84.5 |
| **3** | 284 | **-3.59** | 4.8e-16 in absolute value (float64 noise) | t = 86.5 |
| **4** | 379 | **-10.4** | 4.4e-16 in absolute value (float64 noise) | t = 85.2 |

The Weil form of DH turns negative between a = 1.75 and a = 2, and the negative direction
sits on the off-line zero. Zeta, with identical code and basis, does not.

### Fake prime side (`results/exp4_fake_prime_control.csv`)

Replace Lambda(n) by Lambda(n)(1 + eps chi(n)) with chi = chi_{-4} or chi_{-3}. The
critical eps is exact: 1/mu_max (and 1/mu_min for negative eps), where mu solves the pencil
(P_chi, G).

| a | n = 10 | n = 20 | n = 40 | n = 60 |
|---|---|---|---|---|
| 1 (chi_-4) | 3.9e-6 / -1.1e-6 | 5.9e-8 / -1.4e-8 | 4.2e-10 / -1.1e-10 | 2.0e-11 / -1.0e-11 |
| 2 (chi_-4) | 2.2e-8 / -5.7e-10 | 4.0e-8 / -1.1e-10 | 9.3e-11 / -5.0e-12 | 1.3e-11 / -3.9e-13 |
| 3 (chi_-3) | 8.5e-8 / -2.8e-11 | 5.2e-9 / -1.1e-11 | 2.5e-9 / -1.7e-12 | 5.2e-11 / -1.8e-14 |

(At a = 0.5 only n = 2 enters, and chi_-4(2) = 0, so nothing changes there.) |eps_crit|
roughly tracks the smallest eigenvalue of G. Positivity of the finite Gram matrices is a
knife-edge: the infimum of B(f,f)/||f||^2 over L^2[-a, a] is 0, as shown by the
prolate-like functions concentrated in the zero-free window. So any perturbation of the
prime weights is detected once n is large enough. The test is sensitive. The flip side is
that "positivity holds with margin" is never available at finite a; the margin goes to 0.

---

## 7. What would have counted as a Hilbert-Polya footprint, and did any appear?

Criteria fixed in advance:

1. **A low-complexity matrix shape.** G (or its prime part) close to Toeplitz+Hankel, banded,
   or tridiagonal in a natural basis, beyond what a smooth symbol gives. **Not seen** (3b).
2. **Regular Jacobi coefficients** (constant, linear, or log-like in k) that persist as n
   grows and that disappear when the primes are removed. **The opposite was seen.** The
   prime-free operator is regular, and the primes make it irregular (3c).
3. **Eigenvectors matching a known self-adjoint operator** (prolates), with a bandwidth law
   tied to the zeros and not explained by the zero-free gap. **Partly seen, but explained.**
   The prolate resemblance comes from the gap |t| < gamma_1 (> 99.9999 % of the Fourier
   energy sits there), the bandwidth is unstable, and the prime-free control shows the same
   shape (3a(ii)).
4. **Spectral data of G encoding the zeros in a way not already forced by
   G = sum |F(gamma)|^2.** Not seen. The eigenvalue counts (Exp 1) and the
   minimal-eigenvector zeros (3a(i)) are both direct consequences of that identity.

**Honest verdict:** nothing resembling a Hilbert-Polya structure appeared. Everything
structured that we found is the explicit formula seen through a finite window. That is:

* rank ~ 2 N(T);
* prolates from the zero-free gap;
* Fourier zeros of the minimiser at the gamma_k;
* the cancellation between the odd pole direction and the prime sum.

The one quantitative fact that was new to us is the threshold a* ~ 0.372 (extrapolated)
for the positivity of the archimedean+pole form alone. It is a statement about the archimedean place and says
nothing about RH.

Nothing here is progress on RH. **conjecture1_proved = False.**

---

## 8. Caveats

* Everything is floating-point at 40-80 digits. Nothing is certified (no interval arithmetic).
* The zero lists are mpmath output at 20-25 digits and are not independently certified.
  Validation agreement is limited to about 1e-17 by this.
* The Hermite "support a" is a 1e-30 tail bound, not exact compact support.
* Splines are C^2 test functions, so g = phi * phi~ is C^6. That is enough for the explicit
  formula (F decays like |t|^{-8}), but it is not the C_c^infinity class of Weil's statement.
* Positivity of finite Gram matrices for zeta is implied by RH for zeros up to roughly the
  basis bandwidth, plus decay. It cannot detect a hypothetical off-line zero far above that
  bandwidth (the DH control needed a >= 2 and bandwidth ~ 150 to see a zero at height 86).
* The A-alone threshold a*(n) depends on n like 1/n. The limit 0.3717 is an extrapolation
  from n <= 180 (0.3714 - 0.3720 across fit models), not a computed infimum over
  L^2[-a, a].

## 9. Reproduction

    PY=~/hodge-engine/venv/bin/python
    $PY weil_form.py --validate
    $PY gram_experiments.py exp1_spline
    for a in 0.5 1 1.5 2 3 4 5; do $PY gram_experiments.py exp12_hermite $a 60; done
    $PY gram_experiments.py exp2_spline; $PY gram_experiments.py exp2_extra; $PY gram_experiments.py exp2_bisect
    $PY gram_experiments.py exp2_bisect_n 120 11; $PY gram_experiments.py exp2_bisect_n 180 11
    $PY gram_experiments.py exp3_ccm; $PY gram_experiments.py exp3_prolate; $PY gram_experiments.py exp3_prolate2
    $PY gram_experiments.py exp3_th; $PY gram_experiments.py exp3_jacobi; $PY rank_prediction.py
    $PY gram_experiments.py exp4_fake; $PY dh_control.py validate; $PY dh_control.py gram; $PY dh_control.py gram_scan

The 20000-zero list `zeros20000.json` (534 KB) was computed by `zeros_compute.py`
(mpmath.zetazero, 12 processes, about 35 minutes on the loaded machine). It is monotone,
and the Riemann-von Mangoldt count at the last ordinate is 19999.4. If the file is absent,
`weil_form.py` falls back to `../zeros2000.json`.
