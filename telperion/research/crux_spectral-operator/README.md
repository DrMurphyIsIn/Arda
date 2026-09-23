# crux_spectral-operator: the Weil-Pontryagin window realization, buildable core

**conjecture1_proved = False.** RH is open, and nothing here moves it. On the structure built
below, RH is *exactly* the statement that the integer `kappa_zeta(x)` (the number of negative
squares of the window Weil form) is zero for every window `x`. That is Weil's criterion, and we
say so wherever it appears. What this directory adds is the part of the idea that can be settled
now: a short, general proof of the Pontryagin version of the Connes-van Suijlekom real-zeros
theorem, with its algebraic core machine-checked; a correction to the idea's claim 2, whose
even-sector form fails for Galerkin truncations and so cannot follow from the structure alone;
the zeta instance of "kappa <= number of off-line zero pairs", checked in the kernel on
the unconditional explicit formula; and a reproducible numerical calibration on the
Davenport-Heilbronn function `D`, the negative control, now covering both parity sectors.

The task input carried the idea in full but only a truncated piece of the referee reports. So
every claim below was re-derived and re-checked here instead of being taken from the idea. Status
tags follow the house convention: THEOREM-kernel-checked, THEOREM-paper-proof, COMPUTED,
CONJECTURE-with-evidence.

---

## 1. The story in one page

The idea starts from the window Weil form `QW_x(f) = W_F(f^* * f)` on `L^2[-L/2, L/2]`,
`L = log x`, for an FE datum `F` (zeta, or `D`). By the explicit formula this is the zero sum
`sum_rho F^(g_rho) conj F^(conj g_rho)`, `g_rho = (rho - 1/2)/i`. Zeros on the line contribute
squares `|F^(gamma)|^2`. Each off-line pair `{rho, 1 - conj rho}` contributes a hyperbolic term
`2 Re(conj F^(w+) F^(w-))`, which has signature (1,1). So the negative index `kappa(x)` counts
off-line pairs that the window can resolve. The idea's claims were: (1)/(2) an eigenvector of
`QW_x` whose eigenvalue has `kappa` eigenvalues below it has at most `kappa` pairs of non-real
zeros; (3) an off-line zero is detected once `x >~ gamma/4 + logs`; (4) `D` goes indefinite near
`x = 31`; and a "Locator" conjecture.

**What we found.**

1. **Claim (2) has a five-line proof in its full-space form; the even-sector form fails for
   Galerkin truncations.** Translation invariance
   of `QW_x` makes multiplication by `z` symmetric for the form (`B(zF, G) = B(F, zG)`). Take
   `E = eta^` for an eigenvector `eta` and a zero `alpha` of `E`, and put `R = E/(z - alpha)`. Then
   `zR = E + alpha R`, and since `B(E, .) = 0` this gives
   `(conj alpha - beta) B(R_alpha, R_beta) = 0`. So the chains attached to zeros in the open
   upper half-plane span a *totally isotropic* subspace. A totally isotropic subspace that misses
   the kernel has dimension at most the negative index. Hence:
   **#zeros of `E` in the open upper half-plane (with multiplicity) <= kappa_full(lambda)**, the
   number of eigenvalues below `lambda` in the **full** space. `kappa = 0` is the
   Connes-van Suijlekom theorem, here with no discretisation and no Hurwitz argument.
   In the even sector, multiplication by `z` leaves the sector, so there one must use `w = z^2`.
   That controls only the zeros in the open **first quadrant**: at most `kappa_even(lambda)`.
   Zeros on the **imaginary axis** are controlled only by `kappa_even + kappa_odd`. The idea's
   even-sector statement ("at most `kappa_even` pairs of non-real zeros") **fails for Galerkin
   truncations**, which carry exactly the structure the proof uses. At `D`, `x = 40`, `N = 60`,
   the even ground state has `kappa_even = 0` and a zero pair at `+-27.5057 i`; the corrected
   bound `1 <= kappa_even + kappa_odd = 0 + 1` holds with equality. So the even-sector statement
   cannot be derived from that structure alone. These imaginary-axis zeros are truncation
   effects, though: they occur only when the even eigenvalue sits above extra odd eigenvalues,
   their positions do not converge, and they vanish under refinement (section 6.2). Whether the
   untruncated operator obeys the even-sector statement is **open**. The idea's own proof route
   (Toeplitz discretisation plus Iohvidov-Krein plus Hurwitz) naturally yields the full-space
   count, which is the corrected statement.
2. **The mechanism is exact on every Galerkin truncation.** The Galerkin matrices satisfy the
   displacement identity `Omega Q - Q Omega = l g^T - g l^T` (`Omega = diag((k w)^2)`, `l` the
   boundary functional) to 1e-40 in both sectors, for zeta and for `D`. For such matrices the
   count bound is a kernel-checked theorem (`galerkin_pontryagin_cvs`). In 46 eigenvector tests
   it held every time, and it was attained with equality in several of them.
3. **`kappa <= #off-line pairs` holds for the real zeta Weil form**, unconditionally and
   kernel-checked (`weil_negIndex_le_offline`, rvm_bridge island). This is the upper half of the
   idea's sandwich. The lower half (detection) is a paper proof; its algebra is kernel-checked.
4. **The `D` calibration holds up, and now includes the odd sector.** The even sector goes
   indefinite between `x = 30.5` and `x = 31`: at `x = 31`, `lambda_1 = -1.8739357e-31`, unchanged
   to 8 digits under dps 120 -> 200 and panels 120 -> 360, and more negative at N = 70 and 80. The
   odd sector turns between `x = 31.5` and `x = 32`. By `x = 60` each sector has `kappa = 2`. The
   `(kappa+1)`-th eigenvector of **each** sector locates both certified off-line zeros of `D`. An
   independent discretisation (Legendre basis, double precision, written in the referee lane)
   gives full-space `lambda = -0.944, -0.923` at `x = 60`, against our even `-0.940` and odd
   `-0.919`.

**Negative control.** Everything above uses only the functional equation and the explicit
formula. It applies verbatim to `D`, and `D` behaves correctly: its index becomes positive, and
the theorems bound eigenvector zeros by that positive index. The Euler product can act in exactly
one place: `kappa_zeta(x) = 0`. That is RH, and it is not touched.

---

## 2. The theorem, precisely

**Abstract form (THEOREM-kernel-checked,
`telperion/examples/li_positivity/lean/Crux/Crux_spectral_operator.lean`).**
Let `B` be a Hermitian form on a complex vector space `V`, and let `E` lie in its radical
(`B(E, .) = 0`). Let `R_i` be vectors with `Z R_i = P_i + alpha_i R_i`, where each `P_i` is `E` or
an `R_k` of lower rank (Jordan chains), and suppose `Z` is `B`-symmetric on these vectors:

* `chain_isotropic_line`: if `conj alpha_i != alpha_j` for all `i, j`, then `B(R_i, R_j) = 0` for
  all `i, j`. The proof is strong induction on rank: `(conj alpha_i - alpha_j) B(R_i,R_j)` equals
  lower terms, which vanish.
* `card_le_of_isotropic` (the Pontryagin inertia lemma): an independent, totally isotropic family
  whose span meets the radical only in 0 has at most `K` members whenever `NegIndexLE B K`.
  Proof: a dual family `B(u_i, y_j) = delta_ij` exists because the span misses the radical. It is
  corrected to `y'` with `B(y'_i, y'_j) = 0`, and then `w = u - y'` has Gram matrix `-2 I`.
* `pontryagin_cvs_line`, `pontryagin_cvs_line_lower`, `pontryagin_cvs_line_pos`,
  `no_upper_zeros_of_psd` (`K = 0`), and the unit-circle analogues `chain_isotropic_circle`,
  `iohvidov_krein_circle`, `iohvidov_krein_circle_outside` (Toeplitz shift invariance
  `B(zu, zv) = B(u, v)`; zeros inside or outside the disk).
* `matForm_diag_symm` and `galerkin_pontryagin_cvs`: for a Hermitian matrix `Q` with
  `(Omega_i - Omega_j) Q_ij = l_i conj g_j - g_i l_j` (real `Omega`, `l`), the roots `w` of the
  secular equation `sum_k l_k c_k/(Omega_k - w) = 0` of an eigenvector `c`, taken in the open
  upper half-plane, number at most every `K` with `NegIndexLE (Q - lambda) K`.

**Window form (THEOREM-paper-proof; the glue is not in Lean).** Let `eta` be an eigenvector of
`QW_x` on `L^2[-L/2, L/2]` at a simple eigenvalue `lambda`, and let `K` be the number of
eigenvalues below `lambda` in the full space. Then `eta^` has at most `K` zeros in the open upper
half-plane and at most `K` in the lower one. If `eta` is even and `lambda` is simple in the even
sector, the zeros in the open first quadrant number at most `kappa_even(lambda)`. The glue:
(i) translation invariance gives `z`-symmetry of `QW_x`, and Plancherel gives it for the `L^2`
product (the zeta instance `B(f', g) + B(f, g') = 0` is kernel-checked: `weilSesq_deriv_symm`);
(ii) `E/(z - alpha)^k` stays in `PW_{L/2}` and in the form domain;
(iii) chains are independent and miss `span(E)` when `lambda` is simple. On Galerkin truncations
all three hold exactly, because the trigonometric polynomials of degree <= N are closed under the
division, and `galerkin_pontryagin_cvs` applies directly.

**Relation to the literature.** The `K = 0` case is Connes-van Suijlekom (arXiv:2511.23257,
proved there by Toeplitz discretisation plus Hurwitz; their hypothesis is an even ground state).
The finite unit-circle case is the classical Iohvidov-Krein bound. The continuous `K > 0`
statement is the natural Krein-school analogue (Krein-Langer, Kaltenbaeck-Woracek). We did not
find it stated for eigenfunctions of truncated translation-invariant forms, but we did not run a
literature search, so **we make no priority claim**. The points that look new are the corrected
even-sector statement (first quadrant versus imaginary axis) and the explicit Galerkin-level
counterexample showing that the idea's version does not follow from the translation-invariant
structure.

---

## 3. The odd sector (new closed forms)

The idea's code (`weilwin.py`) builds only the even sector. The full-space index needs the odd one
too. With `psi_k = (2/L)^{1/2} sin(k w t)`, `w = 2 pi/L`, and
`S[m], Cc[m], Cu[m], Cfix, CL` as in the even code (`wpw.py`):

* archimedean diagonal: `CL + Cc[k] + Cu[k]/L - S[k]/(k w L)`
  (even: `+ S[k]/(k w L)`);
* archimedean off-diagonal: `-(s/L)[(S[k]-S[j])/((j-k)w) + (S[j]+S[k])/((j+k)w)]`,
  `s = (-1)^{j+k}` (even: `-` on the sum-frequency term);
* primes: `g_e(y) = ((L-y)cos(kwy) + sin(kwy)/(kw))/L` on the diagonal, and
  `(s/L)[(sin kwy - sin jwy)/((j-k)w) + (sin jwy + sin kwy)/((j+k)w)]` off it;
* zeta pole: `-8 b_j b_k` with `b_k = (2/L)^{1/2} (-1)^k (k w) sinh(L/4)/((k w)^2 + 1/4)`.
  It is negative semidefinite (even: `+2 v_j v_k`).

**Validation (COMPUTED, `validate_forms.py`, `validate_forms.json`).**
(a) The displacement identity residual is `max|C - (l g^T - g l^T)|/max|C|` <= 1.2e-40 at
dps 40, for zeta and `D`, both sectors, `x = 9, 20, 40`. Translation invariance forces this
identity, and a sign error anywhere breaks it.
(b) Brute-force quadrature of `W_F(f1^* * f2)` from the definitions matches the closed forms to
<= 8e-25 at dps 25 (16 entries).
(c) The even sector agrees with the idea's `weilwin.py` to 3.7e-40.

---

## 4. kappa <= #off-line pairs for zeta, and Weil's criterion as kappa = 0

**THEOREM-kernel-checked** (`telperion/examples/rvm_bridge/lean/Crux/Crux_spectral_operator.lean`,
on top of the unconditional E8 explicit formula of this island):

* `weilSesq_hasSum`: `B(f, g) := weilForm(f * g~) = sum_rho m(rho) f^(g_rho) conj g^(conj g_rho)`
  for smooth compactly supported `f, g`;
* `weilSesq_deriv_symm`: `B(f', g) + B(f, g') = 0`;
* `weil_negIndex_le_offline`: if `S` contains one member of every off-line pair
  `{rho, 1 - conj rho}`, then every family of tests spanning a Weil-negative-definite subspace has
  at most `|S|` members. The same holds per window (`kappaWindow_le_offline`), and `kappa(x)` is
  nondecreasing (`kappaWindow_mono`);
* `rh_iff_weil_negIndex_zero`: RH iff `kappa = 0`. **This is a relabeling of Weil's criterion**
  (it uses `RvMBridge9.weil_positivity_implies_rh`), recorded only so that "RH is `kappa = 0`" is a
  kernel fact rather than a slogan.

If there are infinitely many off-line zeros, no such `S` exists and the bound says nothing.
Under RH it says only `kappa = 0`.

---

## 5. Detection (the lower bound)

The idea's detection theorem is **THEOREM-paper-proof** and is not re-proved here. The detector is
`F = (Phi_x^ - R)(z - a)/((z - w+)(z - w-))`. The pair term is `-Re(X^2)/(2 delta^2)` with
`X = Xi'(w-)(w- - a)`, and a real `a` makes it at most `-|Xi'(w-)|^2/2`. Almost-orthogonal
detectors give `kappa >= m`. All three of these algebraic steps are kernel-checked
(`detector_pair_term`, `exists_detector_phase`, `detector_pair_term_le`,
`isNegFamily_of_diag_dominant`). The analytic half (truncation errors, the horizon
`X(rho) ~ gamma/4 + (1/pi) log 1/|zeta'(rho)| + O(log 1/delta) + ...`) is not checked here, and the
constants were not re-derived.

For `D` the Polya kernel decays like `exp(-pi n^2 e^{2u}/5)`. Comparing `|Xi_D'|^2 ~ e^{-pi gamma/2}`
with the truncation error `e^{-2 pi x/5}` gives a leading-order estimate (not a computation) that
the same detector works only from `x ~ 5 gamma/4 ~ 107` for the first pair. The observed onset is
`x ~ 31` (section 6.3), so the detection horizon is a valid upper bound on the onset but far from
sharp for `D`.

---

## 6. Numerics (COMPUTED; mpmath 1.3.0 at 40-200 digits, /usr/bin/python3)

### 6.1 Pontryagin-CvS on Galerkin eigenvectors (`pcvs_check.py`, `pcvs_*.json`)

For each eigenvector we compute the secular roots `w` exactly as matrix eigenvalues (the zeros of
the transform are `+-sqrt(w)`). We count first-quadrant zeros (`Im w > 0`), positive-imaginary-axis
zeros (`w < 0`), and upper-half-plane zeros (`2 #Q1 + #iR+`), and check the isotropy
`|B(R,R)|/(|R|^2 |Q-lambda|)`.

| case | eigvec | eigenvalue | kappa_e | kappa_o | Q1 | iR+ | C+ | bound | notes |
|---|---|---|---|---|---|---|---|---|---|
| D x=40 N=60 | even #0 | -2.59e-4 | 0 | 1 | 0 | **1** | 1 | 1 <= 0+1 (=) | zero at +-27.5057 i |
| D x=40 N=60 | even #1 | 3.2e-39 | 1 | 1 | 1 | 0 | 2 | Q1 1<=1 (=) | 85.6898 + 0.3059 i |
| D x=40 N=60 | odd #1 | 5.0e-35 | 2 | 1 | 1 | 0 | 2 | Q1 1<=1 (=) | 85.6741 + 0.3015 i |
| D x=60 N=90 | even #1 | -1.39e-11 | 1 | 2 | 1 | **1** | 3 | 3 <= 1+2 (=) | |
| D x=60 N=90 | even #2 | 1.8e-60 | 2 | 2 | 2 | 0 | 4 | Q1 2<=2 (=) | 85.6993484854 + 0.308517182457 i, 114.163341632 + 0.150830044973 i |
| D x=60 N=90 | odd #2 | 6.2e-56 | 3 | 2 | 2 | 0 | 4 | Q1 2<=2 (=) | same two zeros |
| zeta x=20 N=50 | all 8 | 1.3e-75 ... | 0..4 | 0..3 | 0 | 0 | 0 | trivially | all zeros real |

All 46 rows in the JSON files (including the small-N smoke test `pcvs_dh_x40_N20.json` and the
refinement `pcvs_dh_x40_N70.json`) satisfy both bounds. The isotropy residual is 1e-142 to 1e-174
(working precision), while `|B(R, conj R)|` is nonzero in every case: each pair is a genuine
hyperbolic plane. For comparison, the certified off-line zeros of `D` are
`0.808517182457 + 85.6993484854 i` and `0.65083008061 + 114.163342731 i`.

### 6.2 Imaginary-axis zeros and their persistence (`imag_zero.py`, `imag_zero_*.json`)

At `D`, `x = 40`, `N = 60`, dps 140, the even ground state (`lambda = -2.5877e-4`,
`kappa_even = 0`, `kappa_odd = 1`) has a transform zero on the imaginary axis at
`y0 = 27.505747139500995353`. `F(i y)` changes sign there, and `|F(i y0)|` relative to its
neighbours is 2.5e-141. This contradicts the even-sector form of claim 2 **for this Galerkin
form**, and the corrected bound allows it. Refinement:

| x | N | even eigvec | eigenvalue | kappa_e | kappa_o | imaginary-axis zero |
|---|---|---|---|---|---|---|
| 40 | 60 | #0 | -2.59e-4 | 0 | 1 | 27.5057 i |
| 40 | 70 | #0 | -1.48e-2 | 0 | 0 | none |
| 40 | 80 | #0 | -1.89e-2 | 0 | 0 | none |
| 60 | 90 | #1 | -1.39e-11 | 1 | 2 | 119.9823 i |
| 60 | 100 | #1 | -4.17e-11 | 1 | 2 | 47.7704 i |
| 60 | 110 | #1 | -5.61e-10 | 1 | 1 | none |

An imaginary-axis zero appears only when `kappa_odd(lambda) > kappa_even(lambda)`, which is exactly
where the corrected bound leaves room for it. Its position does not converge. It disappears once
the even eigenvalue drops below the odd one; for `x = 40` at `N = 70` the even ground state
(`-0.01476`) lies below the odd one (`-0.00225`). Conclusion (COMPUTED): the violations are
features of the truncations, not evidence against the untruncated even-sector statement, which
remains open. The kernel-checked statement bounds first-quadrant zeros by `kappa_even` and
upper-half-plane zeros by `kappa_even + kappa_odd`.

### 6.3 Onset of indefiniteness for D, both sectors (`dh_onset.py`)

| x | even lambda_1 | odd lambda_1 |
|---|---|---|
| 30 | 1.375e-28 | 7.12e-25 |
| 30.5 | 2.457e-29 | 3.33e-25 |
| 31 | **-1.874e-31** | 1.22e-25 |
| 31.5 | -4.98e-30 | 9.55e-27 |
| 32 | -7.83e-30 | **-1.25e-26** |
| 36 | -2.27e-11 | -3.06e-9 |
| 40 | -2.59e-4 | -1.09e-3 |

(N = 60, dps 120.) Stability at `x = 31`, even sector: `-1.8739357e-31` for
(N, dps, panels) = (60,120,120), (60,200,120) and (60,120,360); `-5.05e-30` at N = 70 and
`-5.96e-30` at N = 80. N = 50 gives `+6.4e-30`: the negative direction needs about 60 modes. At
`x = 30.5` the values decrease with N but level off near `+1.5e-29` (N = 80). Galerkin eigenvalues
are upper bounds, so the negative values certify indefiniteness *provided the entries are
accurate*. They are stable to 8 digits under precision and quadrature changes, but this is **not**
an interval-arithmetic certificate. Status: COMPUTED. Onset: even in (30.5, 31], odd in
(31.5, 32].

### 6.4 Independent discretisation (`legendre_crosscheck.py`, `weilop_legendre_ref.py`)

Legendre basis, double precision, full space:

| x | Legendre N | two lowest | ours (even, odd) |
|---|---|---|---|
| 50 | 200 | -0.4988, -0.4506 | even -0.446 (idea, N = 70) |
| 60 | 200 | -0.9440, -0.9226 | -0.9399, -0.9185 (N = 90) |

The Legendre values sit slightly lower, as expected from a larger basis. At `x = 40` the double
precision floor (~1e-13) and the resolution needed for ordinate 85.7 limit that code.

### 6.5 Annihilator lemma (`annihilator.py`)

This is the Rayleigh quotient of the projected truncated Polya kernel, an unconditional upper
bound for `lambda_1`:

| F | x | RQ(P_N Phi_x) | RQ / e^{-2 pi x} (zeta) or e^{-2 pi x/5} (D) | lambda_1 |
|---|---|---|---|---|
| zeta | 9 | 1.26e-18 | 4.6e6 | 4.0e-37 |
| zeta | 13 | 7.15e-29 | 2.1e7 | 9.5e-54 |
| zeta | 20 | 3.23e-47 | 1.2e8 | 1.3e-75 |
| D | 20 | 3.67e-10 | 30 | 4.7e-18 |
| D | 30 | 1.87e-15 | 44 | 1.4e-28 |
| D | 40 | 9.00e-21 | 61 | -2.6e-4 |

The quotient scales like `poly(x) e^{-2 pi x}` (zeta, roughly `x^4`) and `poly(x) e^{-2 pi x/5}`
(`D`), as the lemma says. The actual `lambda_1` is far smaller. The idea's "true decay about
`e^{-10x}`" is its own observation and is not re-derived here.

### 6.6 Finite models (`finite_models.py`, `finite_models.json`)

* Hermitian Toeplitz (circle): 31,804 eigenpolynomials, **0 violations** of
  `#{|a| < 1} <= min(k, n-1-k)` (the same for `|a| > 1`). The bound is attained in 5,546 cases.
  The isotropy residual is 1.4e-14, and the hyperbolic pairing is always nonzero (min 2.5e-7).
* Hankel pencil `H v = lambda G v` (line; `G` a positive moment matrix): 19,951 eigenpolynomials,
  **0 violations** of `#{Im a > 0} <= min(k, n-1-k)`. The bound is attained in 9,447 cases, and
  the isotropy residual is 1.9e-8 (ill-conditioned moments).

---

## 7. What remains open, exactly

* **`kappa_zeta(x) = 0` for all `x`.** This is RH (Weil). Nothing here addresses it.
* **The Locator conjecture** (CONJECTURE-with-evidence): the `(kappa+1)`-th eigenvector transform
  converges to `Xi_F`. New evidence: at `D`, `x = 60`, the eigenvectors `(kappa+1)` through
  `(kappa+3)` of **both** sectors carry both off-line zeros, with accuracy decreasing in the index.
  So the locating property belongs to the near-null cluster, not to one eigenvector. Any proof has
  to use only the functional equation, since `D` satisfies it.
* **Formalising the glue** of section 2 (Paley-Wiener division, form domains, eigenvalue counts
  versus `NegIndexLE` via Courant-Fischer). These are used as hypotheses in Lean.
* **The analytic half of detection** and its horizon constants. This is a paper proof in the idea
  and is not re-checked here.
* **Interval-certified onset** for `D` near `x = 31`.
* **The even-sector form of claim 2 for the untruncated operator.** It fails for Galerkin
  truncations (section 6.2), so a proof must use more than the `z^2`-structure of the even sector,
  for instance the ordering of even and odd eigenvalues.

## 8. Reproduce

```
cd telperion/research/crux_spectral-operator
python3 validate_forms.py            # section 3 (about 1 min)
python3 pcvs_check.py dh 40 60 140 5 # section 6.1 (also: dh 60 90 170 5; zeta 20 50 120 4; dh 31 60 120 3; dh 40 70 150 3)
python3 imag_zero.py dh 40 60 140    # section 6.2 (also: dh 40 70 150; dh 40 80 160; dh 60 90 170; dh 60 100 180; dh 60 110 190)
python3 dh_onset.py scan; python3 dh_onset.py stability   # section 6.3
python3 legendre_crosscheck.py       # section 6.4
python3 annihilator.py               # section 6.5
python3 finite_models.py             # section 6.6
cd ../../examples/li_positivity/lean && lake env lean Crux/Crux_spectral_operator.lean
cd ../../rvm_bridge/lean && lake env lean Crux/Crux_spectral_operator.lean
```
