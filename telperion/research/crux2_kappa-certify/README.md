# crux2_kappa-certify: kappa_zeta(x) = 0 certified up to x = 11.006, Lemma A in the kernel, and why none of it touches RH

**conjecture1_proved = False.** RH is open, and nothing in this directory moves it. The integer
`kappa_zeta(x)` counts the negative squares of the Weil quadratic form `Q` on test functions supported in
`[-a, a]`, `a = (1/2) log x`. By Weil's criterion RH holds exactly when `kappa_zeta(x) = 0` for **every** `x`.
Everything here concerns finitely many windows `x <= 11.006`. At those scales the certificate excludes no
zero of zeta: the same pipeline certifies `kappa = 0` for the Davenport-Heilbronn function `D`, which has an
off-line zero at `0.8085 + 85.699i`, with margins `10^23` to `10^40` times larger than zeta's. Status tags
follow the house convention: THEOREM-kernel-checked, THEOREM-paper-proof, THEOREM-certified-computation (Arb),
COMPUTED, CONJECTURE-with-evidence, HEURISTIC.

This directory is the **builder** pass on the kappa-certify idea. The task input carried the idea in full,
but the referee reports were cut off. So nothing below takes the idea's word for anything: each claim was
re-derived, re-computed with independent code, or checked in the kernel. The Lean file is
`telperion/examples/li_positivity/lean/Crux/Crux2_kappa_certify.lean`.

---

## 1. The story in one page

The window Weil form on `L^2[-a, a]` is

    Q(f) = 2 F(i/2) F(-i/2) + (1/pi) int_0^inf Psi_a(t) |F(t)|^2 dt,
    Psi_a(t) = Re psi(1/4 + it/2) - log pi - sum_{n < x} c_n cos(t log n),   c_n = 2 Lambda(n)/sqrt(n),

with `F` the Fourier transform of `f`. The only arithmetic input is the finite prime-power comb `n < x`.
A certificate shows `Q >= lam ||f||^2` with some explicit `lam > 0`, and so `kappa(x) = 0`. The difficulty is
that the true margin `lam*(x)` collapses super-exponentially: `lam*` is about `1e-17` at `x = 4.95`, `1e-28` at
`x = 7`, and `7e-49` at `x = 11`.

Zhu (arXiv:2608.24827) certified `x = e^{1.6} = 4.95` with a one-stroke reduction. It bounds the comb pointwise
by its Kronecker sup `A_L = sum c_n`, and then needs a frequency cutoff `T# > 2 pi e^{A_L}`. That is 31,535
at `x = 11`, which means about 38,000 Legendre modes per parity sector.

The idea's new step is the **window-aware reduction**. A test function on `[-a, a]` never sees the comb
pointwise. At high frequency it sees only the comb compressed to a slightly larger window, the operator
`P_A = sum (c_n/2)(S_{log n} + S_{log n}^*)` on `L^2(-A, A)`. Two lemmas make this usable:

- **Lemma A** bounds that operator by `A'(A) = sum c_n cos(pi/(floor(2A/log n) + 2))`, which is about `A_L/2`.
- **Lemma B** moves the bound to high frequencies through an erf plateau, at the cost of an explicit Gaussian
  leakage `eta`.

The cutoff threshold then becomes `2 pi e^{A'}`, which is 957 at `x = 11` instead of 31,535. With it the idea
certified `x = 11.006`, which covers every prime power up to 11:
`Q >= 6.60e-49 ||f||^2`, with `lam*_even` in `[6.60e-49, 8.83e-49]`.

**What the builder pass adds:**

1. **Lemma A is now kernel-checked in its continuous form** (`LemmaA.comb_bound`), for every real square-integrable
   `g` vanishing outside `[-A, A]`. The idea had only the finite path-graph inequality in the kernel. It left the
   orbit decomposition `L^2(-A, A) = direct integral of l^2(orbits)` on paper. The kernel proof avoids the
   decomposition altogether. It takes a Perron weight that is constant on the translation cells
   `floor((u + A)/tau)`, applies a pointwise weighted AM-GM inequality, and integrates using translation
   invariance of Lebesgue measure (section 3).
2. **The Arb-to-kernel link is now a theorem about the full matrix.** `core_schur` states the following: every
   real symmetric block matrix `[[A, B], [B^T, C]]`, with `C` of any size, `C > 0`, and Schur complement in the
   certified Arb box, is positive semidefinite. It is proved through Mathlib's `Matrix.PosDef.fromBlocks22`.
   So the kernel concludes `lam_min(M) >= lam0` for the 2300 x 2300 Galerkin block `M`, from exactly two Arb
   facts per core.
3. **Four certificate cores**: `x = 6.996` even and odd, and `x = 11.006` even and odd. The `x = 11.006` odd core
   is new; the idea had only the even one at `x = 11`. There is also a **rigor fix**. The idea's `x = 11` core
   was computed from a matrix re-read from disk with radii printed to 3 digits and inflated by only
   `1 + 1e-7`, and such a print can round a radius down. The fix inflates by 2% and regenerates both cores.
   The numbers barely move: the even-sector `w0` changes in the sixth digit.
4. **Independent corroboration with no shared code.** A u-domain Legendre Galerkin of the untruncated `Q` uses
   Weil's archimedean distribution directly, with no Bessel functions and no digamma. Its Rayleigh-Ritz values
   stay above every certified lower bound at `x = 4.95, 6.996, 7.99, 11.006`, in both sectors, and they tighten
   six of the idea's eight upper bounds (all but `x = 4.95` even and `x = 7.99` odd). The same code's explicit-formula normalisation matches the zero side over
   2000 zeros to `5e-25`. The same code applied to `D` reproduces the `D` margins, and it shows `D` going
   indefinite at `x = 40` once the basis resolves frequency 86 (section 5).
5. **An audit** found six issues, all minor. None invalidates a certificate (section 6).

**What it is worth: nothing toward RH.** This is said plainly in section 7. The certificate is an instance, and
the negative control `D` passes it with a margin `10^40` times larger at `x = 11`.

---

## 2. What is established

| # | Statement | Status |
|---|-----------|--------|
| S1 | `kappa_zeta(x) = 0` for every `x <= 11.006`: `Q(f) >= 6.60e-49 ||f||^2` for all `f` in `L^2[-307/256, 307/256]` (even sector `>= 6.6018e-49`, odd `>= 4.4579e-45`). Also `x = 7.99` (`>= 2.30e-33`) and `x = 6.996` (`>= 4.39e-28`). Since `Q_x(f)` does not depend on `x` once `supp f` is inside the window, `kappa` is non-decreasing in `x` and the `x = 11.006` result covers all smaller `x`. | THEOREM-certified-computation (Arb), modulo P1-P3 below; finite cores THEOREM-kernel-checked |
| S2 | Lemma A (continuous): `sum c_i int g(u+tau_i) g(u) du <= (sum |c_i| cos(pi/(floor(2A/tau_i)+2))) int g^2` for `g` vanishing outside `[-A, A]`. | **THEOREM-kernel-checked** (`LemmaA.comb_bound`, new in this pass) |
| S3 | Lemma B and the reduction `Q >= R''`, `b'' = b' - A_L(2 eta + eta^2) - deficit - xi`. | THEOREM-paper-proof (re-derived: NOTES_lens.md, BUILDER B2; constants reproduced independently) |
| S4 | Cores: exact rational `Sq - delta I = L D L^T` for four 8 x 8 Schur complements; `core_schur` lifts each to "block matrix PSD" given the Arb facts `C > 0` and `hbox`. | **THEOREM-kernel-checked** (`Core_x6996_even/odd`, `Core_x11006_even/odd`) |
| S5 | Two-sided enclosures: `lam*_even(11.006)` in `[6.60e-49, 8.50e-49]`, `lam*_odd(11.006)` in `[4.458e-45, 5.21e-45]`, `lam*_even(6.996)` in `[4.395e-28, 7.14e-28]`, `lam*_odd(6.996)` in `[1.420e-24, 1.666e-24]`. Lower ends are certified. Upper ends are the idea's certified Rayleigh quotients or the builder's Legendre values, whichever is smaller (the builder's are COMPUTED, not certified). | certified (lower) / COMPUTED (tightened uppers) |
| S6 | Negative control: `kappa_D = 0` certified at `x = 6.996` (`>= 7.25e-5`) and `x = 11.006` (`>= 7.2e-9`). The builder's independent Galerkin gives `8.68e-5` and `7.73e-9`, consistent. | THEOREM-certified-computation (idea) + COMPUTED corroboration |
| S7 | `D` is indefinite at `x = 40`: the idea certified Rayleigh quotients `-2.59e-4` (even) and `-1.09e-3` (odd). The builder's Legendre Galerkin turns negative in both sectors once the degree resolves frequency `~86` (see section 5). | THEOREM-certified-computation (idea) + COMPUTED corroboration |
| S8 | `||P_A||` is within 1-6% of the Fejer mass `sum c_n (1 - log n/(2A))`. | CONJECTURE-with-evidence (not re-examined here) |
| S9 | The elementary identity `int F(t - i d) conj F(t + i d) rho(t) dt = int int f(u) conj f(v) e^{d(u-v)} rhohat(u - v)`: off-line pairs enter the window form as on-line density with the spectrum multiplied by `cosh(d s)`. | THEOREM-paper-proof (Plancherel; re-derived) |

**Paper lemmas the certificates rest on:**

- **(P1)** Weil's explicit formula, arithmetic side, for smooth compactly supported tests. This is all that is
  needed to read `Q >= lam ||f||^2` as `kappa = 0`, because `kappa` is defined through smooth tests. A version is
  kernel-proved on the rvm_bridge island as `RvMBridge4.limit_explicit_formula`. The normalisation used here
  agrees with the zero side to `5e-25` (section 5).
- **(P2)** The Binet envelope `Re psi(1/4 + it/2) - log pi >= log(t/2pi) - 1/t` for `t >= 3/4`. It was re-derived
  and holds, since `|s^2 + z^2| >= |Im z^2| = t/4`. A numerical grid check on `[0.75, 5000]` found a minimum slack
  of `2.0e-4`.
- **(P3)** The reductions `Q >= R` (Zhu) and `Q >= R''` (window-aware). The comb step is S2; Lemma B is on paper.

---

## 3. Lemma A in the kernel: the proof that needs no orbit decomposition

Fix a shift `tau > 0` and a window `[-A, A]`. Let `K = floor(2A/tau)` and `theta = pi/(K+2)`. Assign each point
its translation cell `j(u) = floor((u + A)/tau)`. On the window `0 <= j(u) <= K`, and `j(u +- tau) = j(u) +- 1`.
Put the path-graph Perron vector on the cells:

    W(u) = sin(theta (j(u) + 1))  on [-A, A],   W = 0 outside.

Three facts carry the proof:

- **Recursion.** `sin(theta(j+2)) + sin(theta j) = 2 cos(theta) sin(theta(j+1))`. When `u + tau` leaves the
  window, `W(u + tau) = 0 <= sin(theta(j+2))`, because `j + 2 <= K + 2`. The lower edge works the same way.
  So `W(u+tau) + W(u-tau) <= 2 cos(theta) W(u)` on the window (`LemmaA.W_rec`).
- **Weighted AM-GM, pointwise.**
  `2|g(u+tau)||g(u)| <= (W(u+tau)/W(u)) g(u)^2 + (W(u)/W(u+tau)) g(u+tau)^2`.
  This is trivial when either value is 0, because `W >= 0`.
- **Integrate.** Substitute `u -> u - tau` in the second term, using translation invariance. The two terms
  combine to `int g^2 (W(u+tau) + W(u-tau))/W(u) <= 2 cos(theta) int g^2`. The ratios are bounded by
  `1/sin(theta)`, which gives integrability.

That is `LemmaA.shift_bound`. The signed version and the finite sum over the comb with arbitrary real weights
are `shift_bound_signed` and `comb_bound`. All three depend on `[propext, Classical.choice, Quot.sound]` only.
The hypotheses are: `g` measurable, `g^2` integrable, and `g u != 0 -> u in [-A, A]`. The closed window is
allowed, and it has the same count `K + 1` of points per orbit.

---

## 4. The certificates and their chain of custody

For `x = 11.006` (`a = 307/256`), the steps, their status, and the numbers:

1. **Reduction `Q >= R''`** (paper, S3). Parameters: `eps = 0.34`, `w = 66`,
   `Tc = 1170 / 2000` (even / odd), `Tk = Tc + 8w`, `Tmax = Tk + 11.5w`.
   Constants: `A_L = 8.52099`, `A' = 5.02558`, `b' = 0.200448 / 0.736946`, `eta = 1.13e-56`, `err = 1.93e-55`,
   `deficit = 3.3e-58`, `xi = 4.0e-58`. All were reproduced by `builder/recompute_constants.py`.
2. **Leading block** `M` (Arb). 2300 Legendre modes per sector, 59,568 / 79,488 composite Gauss-Legendre
   nodes, 256 bits, spherical Bessel functions by accuracy-checked backward recurrence.
3. **Quadrature error** (Arb). Mode-weighted Bernstein-ellipse bound on the same nodes:
   `||E||_F <= 1.48e-55 / 6.6e-56`. See finding F6.
4. **Verified Cholesky** (Arb). `M - lam0 I = R R^T + E`, `||E||_F = 8.7e-71 / 1.9e-70`,
   `lam0 = 6.6018e-49 / 4.4579e-45`.
5. **Tails** (Arb). `eps_B <= 1e-103`, `eps_D <= 2e-218`.
6. **Assembly.** `lam_min(Q) >= min(lam0 - resid - quad, b'' - eps_D) - eps_B`, giving `6.6018e-49` (even) and
   `4.4579e-45` (odd). The inequality itself is `block_assembly` in the kernel.
7. **Kernel cores.** `core_schur` turns two Arb facts into `M - lam0 I >= 0`:
   - `C - lam0 I >= 1e-55 I` (verified Cholesky, residual `1.2e-67` even / `1.7e-67` odd);
   - Schur complement within `w0 = 1.99e-59` (even) / `2.30e-60` (odd) of `Sq`.
   The exact margins are `delta = 5.35e-51 > 8 w0 = 1.6e-58` (even) and `delta = 4.38e-47 > 1.8e-59` (odd).
   Tamper twins are rejected by the kernel: a pivot numerator +1, one Schur entry changed in its last digits,
   or `delta` tripled all give `unsolved goals` and `sorryAx`.

---

## 5. Independent corroboration (COMPUTED; different code, different representation)

**(a) Normalisation (P1).** Weil's archimedean term in the u-domain follows from
`psi(z) = -gamma + int_0^inf (e^{-x} - e^{-zx})/(1 - e^{-x}) dx`. With `g` the autocorrelation of `f`:

    Q(f) = 2F(i/2)F(-i/2) + (-gamma - log pi - log(1 - e^{-4a})) g(0)
           + int_0^{2a} 2(e^{-2u} g(0) - e^{-u/2} g(u))/(1 - e^{-2u}) du - sum_{n<x} 2 Lambda(n) n^{-1/2} g(log n).

For `f = (1 - (u/a)^2)^5 (1 + u/3)`, compared with the zero side `2 sum |F(gamma_k)|^2` over 2000 zeros:

| `a` | arithmetic side | zero side | difference |
|---|---|---|---|
| 249/256 | `1.20170654736743442245e-6` | `...4219e-6` | `5e-25` |
| 307/256 | `1.11691389955121861514e-7` | `...8614316e-7` | `8e-26` |

Script: `builder/check_ef_udomain.py`.

**(b) Rayleigh-Ritz upper bounds** for the untruncated `Q` in a Legendre basis on the u-domain form. Here
`lam_min(Q_N) >= lam*` for every `N`, so a value below a certified lower bound would refute that certificate.
None does.

| x | sector | builder Legendre (N) | certified lower | idea's certified upper |
|---|---|---|---|---|
| 4.95 | even | 1.7016e-17 (36) | 1.02e-17 | 1.658e-17 |
| 4.95 | odd | 1.6141e-14 (36) | 1.10e-14 | 1.6317e-14 |
| 6.996 | even | 7.1406e-28 (60) | 4.395e-28 | 7.4649e-28 |
| 6.996 | odd | 1.6663e-24 (60) | 1.4201e-24 | 1.6794e-24 |
| 7.9895 | even | 4.8787e-33 (60) | 2.3075e-33 | 4.8907e-33 |
| 7.9895 | odd | 1.4657e-29 (60) | 1.1478e-29 | 1.4077e-29 |
| 11.006 | even | 8.5038e-49 (120) | 6.6018e-49 | 8.826e-49 |
| 11.006 | odd | 5.2107e-45 (120) | 4.4579e-45 | 5.484e-45 |

At `x = 11`, 4 and 8 quadrature panels agree to 11 digits at `N = 90`. Legendre convergence is algebraic, a sign
of boundary behaviour in the ground state. That is why the builder's values beat the idea's closed-form
cos/sin bounds in some rows and not in others.

**(c) The negative control `D`, same code.** The changes are `Lambda_D` from `-D'/D`, the factor `e^{-3u/2}`,
`log(5/pi)`, and no pole term.

| x | sector | builder Legendre | idea's certified lower |
|---|---|---|---|
| 6.996 | even | 8.683e-5 | 7.253e-5 |
| 6.996 | odd | 2.344e-2 | 2.163e-2 |
| 11.006 | even | 7.730e-9 | 7.205e-9 |
| 11.006 | odd | 8.082e-6 | 7.561e-6 |

At `x = 39.94`, `D`'s Galerkin value stays positive up to degree 99 (for example `1.5e-34` at `N = 50`). It turns
negative at `N = 70` (`-8.8e-15` even, `-1.7e-14` odd). At `N = 110` it reaches `-2.44e-2` (even) and `-4.61e-3`
(odd), with exactly one negative eigenvalue in each sector, so `kappa_D >= 2`. That matches the one resolved off-line
quadruple, which is two pairs, and it is consistent with the idea's certified Rayleigh quotients `-2.59e-4` and `-1.09e-3`.
Zeta at the same window stays positive (`5.9e-78` at `N = 60`, still decreasing). The negative directions need
frequency about 86, the ordinate of `D`'s off-line zero. Legendre polynomials of degree `d` on a window of
half-width 1.84 resolve frequencies only up to about `d/1.84`, so this is the expected onset. It is also the
precise sense in which the Euler product becomes visible only once an off-line zero is resolved.

---

## 6. Audit findings (none invalidates a certificate)

- **F1 (rigor gap, fixed).** `schur_core_file.py` re-read the saved `x = 11` matrix. Radii were printed to 3
  significant digits and inflated by only `1.0000001`, and a 3-digit print can round a radius down by up to
  about 1%. For small entries the `|v| 1e-69` slack does not cover that, so the box fed to the kernel core was
  not provably an enclosure. The fix, `builder/schur_core_file_fixed.py`, inflates by `1.02`. Regenerated even
  core: identical `S`, `L`, `D`, `delta`; `w0` goes from `1.99204400e-59` to `1.99204656e-59`. The odd core is
  new.
- **F2 (reproducibility).** `certify_wa.py` on disk has `GAPK, GAPM = 7, 10`. The `x = 11` runs and the refined
  quadrature bound used `gap_k = 8`, `gap_max = 11.5`; the node counts confirm this. `REPRODUCE.sh` has no
  `x = 11` line. Section 9 gives the right call.
- **F3 (cosmetic).** `combine_x11.py` calls `b'' = 0.200448` "rounded down", but it is rounded up. This is
  harmless, because the minimum in the assembly is attained by the leading block.
- **F4 (documentation).** The idea's `lean/KappaWindowCoreX11.lean` docstring is stale: it describes the
  `a = 249/256` core. The file here replaces it.
- **F5 (overstatement).** "Zhu's method cannot reach `x = 11`" should read: it needs `T# > 31535`, about
  38,000 modes per sector. That is infeasible for this pipeline, not impossible.
- **F6 (read the right field).** The runs' own `final_lower` fields are negative (`-2.9e-43`), because the
  in-run quadrature bound was the crude uniform one. The certificate is the post-hoc combination in
  `combine_x11.py`, which uses the refined mode-weighted bound on the same nodes (`quad_opt2.py`). That bound
  was re-derived in this pass: Trefethen's Gauss-Legendre bound per panel, an analytic digamma bound on the
  ellipse, the pole exclusion, the `erf` continuation bound, and the power-series bound on the spherical Bessel
  functions. It is correct.
- **F7 (arithmetic slip).** `e^{133/64} = 7.98947`, not 7.991 (or 7.9906, as in the lens notes). The prime-power
  set `{2, 3, 4, 5, 7}` is unchanged, because `log 8 = 2.0794 > 133/64 = 2.0781`.

---

## 7. What it is worth: nothing toward RH (deaths check)

- **Circularity.** None. No RH input is used. Every statement is either a finite instance or an unconditional
  inequality.
- **Negative-control failure.** It passes the negative control, which is exactly the problem for any claim of
  RH relevance. `D` has no Euler product and has an off-line zero, yet it passes the same certificate with
  margins `1.6e23` (at `x = 6.996`) and `~1e40` (at `x = 11`) times zeta's. The golden fake, and zeta times a
  surgered Euler factor at `p > x`, have literally the same window form, since only `Lambda(n)` for `n < x`
  enters. Window positivity at certifiable `x` is a zero-sampling statement, fixed by how sparse the zeros are
  below about `2 pi x`. It is not arithmetic.
- **What `kappa = 0` bounds.** The kernel theorem `kappa <= #off-line pairs` makes `kappa = 0` the trivial
  direction. By Krein-Langer, `kappa(x) = 0` says only that the data `n < x`, `Gamma_R` and the pole are
  consistent with all zeros lying on the line. The unconditional content is the inequality
  `sum_{n<x} 2 Lambda(n) n^{-1/2} Re <tau_{log n} f, f> <= Pole(f) + Arch(f) - lam ||f||^2`.
- **Lemma A's value** is methodological. It removes the doubly-exponential Kronecker barrier from the reduction.
  The binding constraint becomes the ground state's truncation loss. The margin still collapses like
  `exp(-2 pi^2 N(2 pi x)/log N)`, so no fixed-`x` certificate can approach the wall.

---

## 8. What remains open

- A kernel proof of Lemma B and of the full reduction `Q >= R''`. This needs Gaussian tail integrals, the
  convolution identity for `kcheck`, and the Binet envelope in Lean.
- The Fejer-mass conjecture `||P_A|| = (1 + o(1)) sum c_n (1 - log n/(2A))`. It would lower the threshold to
  `2 pi exp((4 + o(1)) e^a/a)`.
- A rigorous replacement for `beta* > 0`: a certified bound on the eigenfunction truncation loss
  `~ 2 f_0(a)^2/(pi T)`, the observed failure mode of both reductions in the odd sector.
- Anything about `kappa_zeta(x)` for `x > 11.006`. That is RH, and it is untouched.

---

## 9. Reproduction

The `x = 11.006` certificate is not in the idea's `REPRODUCE.sh`. Run from `idea_pipeline/`, with
`/usr/bin/python3`, python-flint 0.6.0 and mpmath 1.3.0. It takes about 1 to 1.5 hours per sector on one core.

```
python3 -c "import certify_wa as c; c.GAPK, c.GAPM, c.SAVE_M, c.FPREC = 8.0, 11.5, True, 384; \
  c.run('307/256', 0.34, 1170.0, 66.0, 2300, 256, sectors=('even',), tag='wa3_a307_even')"
python3 -c "import certify_wa as c; c.GAPK, c.GAPM, c.SAVE_M, c.FPREC = 8.0, 11.5, True, 384; \
  c.run('307/256', 0.34, 2000.0, 66.0, 2300, 256, sectors=('odd',), tag='wa3_a307_odd')"
python3 quad_opt2.py          # refined quadrature bounds (same nodes)
python3 combine_x11.py        # final lower bounds
PYTHONPATH=. python3 ../builder/schur_core_file_fixed.py M_wa3_a307_odd_odd.txt 4.4579e-45 8 60 core_odd.json
PYTHONPATH=. python3 ../builder/schur_core_file_fixed.py M_wa3_a307_even_even.txt 6.6018e-49 8 60 core_even.json
```

Builder checks, run from `builder/`. Absolute paths inside the `run_*.sh` helpers point at the original scratch
location; the Python scripts take the window as an argument.

```
python3 recompute_constants.py
python3 check_ef_udomain.py 249/256 ; python3 check_ef_udomain.py 307/256
python3 udomain_galerkin.py 307/256 zeta even 80,90,100 768 4
python3 udomain_galerkin.py 472/256 dh even 70,90 512 4
python3 emit_crux2.py OUT.lean [pivot|entry|delta]      # regenerates the Lean file (or a tamper twin)
```

Lean: `cd telperion/examples/li_positivity/lean && lake env lean Crux/Crux2_kappa_certify.lean`, about 30 s.

## 10. File map

- `README.md` (this file). `NOTES_lens.md` holds the lens working notes: the idea's sections 0-28 plus the
  BUILDER section with full derivations.
- `idea_pipeline/`: the idea's certification code, unchanged. The main scripts are `certify.py`,
  `certify_wa.py`, `rmat.py`, `vldlt.py`, `quad_opt2.py`, `combine_x11.py`, `galerkin_cos.py`, `schur_core*.py`,
  `emit_lean_core.py` and `REPRODUCE.sh`.
- `idea_certs/`: the idea's certificate JSONs and logs, and the `x = 6.996` Schur-core JSONs. The large `M_*`
  matrices, around 450 MB each, are not copied.
- `builder/`: the independent checks (`udomain_galerkin.py`, `check_ef_udomain.py`, `recompute_constants.py`),
  the fixed core script, and the Lean emitter with its hand-written parts (`lean_parts/`). Outputs and logs are
  in `builder/outputs/`, including the regenerated `x = 11` core JSONs.
