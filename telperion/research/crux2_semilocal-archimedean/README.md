# crux2 / semilocal-archimedean: the semi-local horizon

**conjecture1_proved = False.** RH is open. Nothing in this directory or in the Lean module that goes
with it proves RH, reduces it, or claims progress toward it. What is here is a *map of the wall* for
one lens, and that map is negative.

Kernel artifact: `telperion/examples/rvm_bridge/lean/Crux/Crux2_semilocal_archimedean.lean`
(Lean v4.33.0-rc2 on the rvm_bridge island, 46 declarations, each `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, no `sorry`).

---

## 1. The question, and the short answer

Connes and Consani's semi-local programme asks whether Weil positivity can be built up one place at
a time: the archimedean place first, then the primes one by one. Make that concrete. Take
`S_q = {primes p < q}` and the **S-local Weil functional** `W_{S_q}`. It keeps the Gamma_R
(archimedean) term, the two pole terms, and every power of every prime in `S_q`, and it drops
everything else. Evaluate it on tests supported in the window `[-L/2, L/2]`, `L = log x`, so the
autocorrelations live on `(1/x, x)`.

On a window with `x <= q` nothing is missing yet: `W_{S_q}` *is* the full Weil functional there. So
"is `W_{S_q}` positive on its natural window?" is exactly "is the Weil form positive on that
window?", and that is RH-hard. It is a relabeling (kernel-checked below as
`rh_iff_semilocal_natural_windows`). The only way the lens could add information is if `W_{S_q}`
stayed positive **beyond** its natural window. That surplus would be a reservoir an induction over
primes could spend: prove positivity for `S_q` a little past `q`, then add `q`.

**The answer is no, and it is sharp.** `W_{S_q}` goes indefinite by

    x = q + Delta(q),   Delta(q) e^{2 pi Delta(q)} = sqrt(q)/(4 pi),   i.e.  Delta(q) = W0(sqrt q / 2)/(2 pi) ~ (1/4pi) log q

(leading order, zeros that matter on the line; `(1/2pi) log q + O(log log q)` fully unconditionally).
Numerically the true horizon is even closer: below `q + 0.08` for `q = 3`, below `q + 0.06` for
`q = 5` and below `q + 0.05` for `q = 7` (Galerkin, cross-checked in section 4b). Every prime is
load-bearing at its own scale, and a proof of window positivity has to know the earlier Euler
factors to precision about `e^{-c(x - n)}` (the two-sided precision barrier, section 5).

---

## 2. The mechanism in one paragraph

Let `Phi` be the Polya kernel, normalised so that `Phi^ = Xi`
(`Phi(u) = sum_n (4 pi^2 n^4 e^{9u/2} - 6 pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}}`; checked to 1e-32 in
`verify_probe_law.py`). The transform of `Phi'` is `-i z Xi(z)`, which vanishes at **every** zero,
on or off the line. So the window probe `g_x = Phi' * 1_W` (or a smooth cutoff of it) has, at each
zero, transform equal to minus the transform of its truncation tail, and the tail is
super-exponentially small. By the explicit formula the full Weil value of the probe is tiny:
`W(g_x) ~ Phi'(L/2)^2 log x/(2 pi x) = O(x^{11/2} log x e^{-2 pi x})`. Deleting the prime `q` adds
`2 (log q/sqrt q) h(log q)`, where `h` is the autocorrelation of the probe. Because the probe is odd
and negative on `(0, L/2)`, `h(log q) < 0` (the sign lemma), and its size is set by the kernel at
`log q / 2`: `|h(log q)| ~ 64 pi^6 q^{11/2} (x - q) e^{-2 pi q}`. The deficit beats the full value
once `(4 pi/sqrt q) Delta e^{2 pi Delta} > 1`. That is the onset law.

---

## 3. What is kernel-checked, and what is a paper proof

Status tags: **THEOREM-kernel-checked** / **THEOREM-paper-proof** / **COMPUTED** /
**CONJECTURE-with-evidence** / **HEURISTIC**.

### 3a. Kernel (the Lean module)

Everything is stated for the **registry** Weil functional of E6Bridge4/5 (`archSide`, `primeSide`,
`weilForm`, `autocorr` and the unconditional explicit formula), not for abstract reals.
`sLocalWeilForm q f := archSide f - (prime side over prime powers with minFac < q)`.

| block | declarations | what it says |
|---|---|---|
| A. deficit identity | `sLocalWeilForm_eq`, `deficit_eq_zero_of_window` | `W_{S_q}(f) = W(f) + deficit_q(f)` for bounded support; the deficit vanishes on `L <= log q` |
| B. the relabeling (labelled as such) | `sLocal_eq_weil_of_window`, `sLocalIndefinite_iff_of_window`, `rh_iff_semilocal_natural_windows`, `rh_iff_no_natural_window_indefinite`, `sLocalIndefinite_mono` | on its natural window `W_{S_q}` is `W`; RH iff no `S_q` is indefinite on its natural window (Weil's criterion restated via E6Bridge9) |
| C. no-go skeleton | `prime_of_missing`, `realAutocorr_eq_overlap`, `overlap_neg_of_odd`, `realAutocorr_neg_of_odd`, `realAutocorr_nonpos_of_odd`, `deficit_re_le`, `overlap_first_neg`, `sLocal_neg_of_probe`, `weilForm_autocorr_hasSum`, `weilForm_re_le_zero_majorant`, `sLocalIndefinite_of_zero_side`, `ProbeInput`, `horizon_of_probeInput` | on `q < x < q^2` the deleted prime powers are the primes in `[q, x]`; the sign lemma holds for the sharp probe `G 1_W` and for smooth probes; the whole deficit is at most its first term, which is `< 0`; `Re W(g) <= U < 2 (log q/sqrt q) |h_g(log q)|` forces `Re W_{S_q}(g) < 0`; the analytic input in zero-side form (`Re W(g*g~) <= sum_rho m(rho) |g^(gamma_rho)| |g^(conj gamma_rho)|`, every zero on or off the line); the horizon upper half **modulo the single named obligation `ProbeInput q x`** |
| D. precision barrier (structural half) | `perturbed_re_eq`, `precision_decrease_detected`, `precision_increase_detected`, `realAutocorr_pos_of_pos` | changing `Lambda(n0)` to `(1+delta) Lambda(n0)` lowers `W` by a strictly positive amount on the odd probe (`delta < 0`) or on the even positive probe (`delta > 0`) |
| E. surgery negative controls | `latticeForm_two`, `latticeForm_nonneg_of_abs_le`, `latticeForm_nonneg_iff`, `surgery_local_rh_iff`, `partial_shift_bound`, `surgery_term_ge`, `pair_probe_identities`, `pair_probe_surgery_value`, `pair_probe_rayleigh`, `golden_violates`, `w1_violates` | the surgery term on `N` lattice points (coefficients `c_m = C_m(-a) = (-1)^m (r^m + r^{-m})`) is PSD for every `N` iff `abs a <= 2` iff all zeros of `2 cosh w + a` have `Re w = 0` (local RH for the extra Euler factor); on windows `p0 < x < p0^2` it is `>= log p0 (2 - abs a) ||g||^2`, and the pair probe attains `log p0 (2 - a)` exactly |
| F. Fourier envelope | `poisson_kernel_le`, `local_symbol_ge` | each prime's symbol `log p (1 - P_{p^{-1/2}}(t log p)) >= -2 log p/(sqrt p - 1)` |

The module supersedes the idea-stage scratch `SemilocalHorizonCore.lean` (li_positivity, abstract
reals): its sign lemma, assembly and deficit bound now live on the registry functional, and its
two-point lattice lemma is strengthened to all `N` and tied to local RH.

### 3b. The horizon theorem (THEOREM-paper-proof, asymptotic, constants sketched)

**Statement.** For `q` prime, `x*_{S_q} := sup{x : W_{S_q} >= 0 on window x}` satisfies

* (a) `x*_{S_q} >= q` **iff** Weil positivity holds on the window `(1/q, q)`. *Identity, kernel-checked
  (`sLocalIndefinite_iff_of_window`).* Unconditional only for `q = 2, 3` (Zhu's certificate covers
  `x <= 4.95`; for `q = 2` in the pole-free normalisation also Yoshida / Connes-Consani).
* (b) `x*_{S_q} <= q + Delta(q)`, with `Delta(q) = W0(sqrt q/2)/(2 pi) (1 + o(1))` when the zeros that
  matter are on the line, and `Delta(q) <= (1/2pi) log q + O(log log q)` unconditionally.

**Proof of (b), and exactly where the kernel stops.** The kernel proves (b) from `ProbeInput q x`
(`horizon_of_probeInput`). `ProbeInput` asks for one smooth odd probe, negative on `(0, L/2)`,
whose absolute zero sum is below the first overlap. Take `g = Phi' chi` with `chi` a smooth even
cutoff, equal to 1 on `[-L/2 + eps, L/2 - eps]`, positive inside the window and zero outside.
1. `g` is odd and negative on `(0, L/2)` because `Phi' < 0` on `(0, oo)` (Csordas-Norfolk-Varga 1986;
   grid-checked in `verify_probe_law.py`).
2. `g^(z) = (Phi')^(z) - (Phi'(1 - chi))^(z) = -i z Xi(z) - tau^(z)`, so `g^(gamma_rho) = -tau^(gamma_rho)`
   at every zero. **Needs `Phi^ = Xi` (Riemann's theta identity), which is not in Mathlib or Zeta23.**
3. `tau` lives on `|u| >= L/2 - eps` and decays like `exp(-pi e^{2u})`. Integration by parts gives
   `|tau^(gamma)| <= C |Phi'(L/2 - eps)| e^{|Im gamma| L/2} min(1/kappa, 1/|gamma|)`, `kappa ~ 2 pi x`.
   Summing with the local zero count (RvM, kernel-proved on this island) gives
   `sum_rho m |g^(gamma)| |g^(conj gamma)| <~ Phi'(L/2)^2 log x/(2 pi x)` when the zeros up to a few
   times `kappa` are on the line, and at most `x^{1/2}` times that unconditionally
   (`|Im gamma| < 1/2`). Choosing `eps ~ x^{-2}` makes the cutoff cost negligible.
4. `|h_g(log q)| = 64 pi^6 q^{11/2} (x - q) e^{-2 pi q} (1 + O(1/q) + O((x - q)^2/q))` from the overlap
   at `v ~ log q/2`.
5. Compare: the deficit wins when `(4 pi/sqrt q) Delta e^{2 pi Delta} > 1` (RH-evaluated) or
   `> x^{1/2}` (unconditional). That gives the two forms of `Delta(q)`. Window monotonicity
   (`sLocalIndefinite_mono`) extends indefiniteness to every larger window.

**Range of the RH-evaluated law (correction to the idea).** The idea claimed the `(1/4pi)` law is
unconditional "in Platt's verified range, q up to about 1e11". Zeros above the verified height
`T0 = 3e12` could, if off the line, contribute up to `4 x^{3/2} log T0/(T0 log x)` times the main
term. That ratio is `0.075` at `x = 1e7`, `0.76` at `5e7`, `2.1` at `1e8` and `4.8e4` at `1e11`. So the
law is unconditional to within `0.09` in `Delta` for `q <= 5e7`. At `1e11` the unconditional slack
is up to `(1/2pi) log(4.8e4) = 1.7`.

---

## 4. Numerics, and how each number was cross-checked

### 4a. The load-bearing step, re-derived independently (`verify_probe_law.py`, builder stage)

* `Phi^ = Xi` in this normalisation: `|2 int_0^oo Phi cos(tu) du - xi(1/2 + it)| <= 2.4e-32` at
  `t = 0, 5, 10, gamma_1`.
* `Phi' < 0` on `(0, 3]` (30001-point grid; scaled evaluation where float64 underflows).
* Overlap versus `64 pi^6 q^{11/2} Delta e^{-2 pi q}`: ratio `0.69` (q=7), `0.82` (13), `0.95` (47),
  `0.975` (97), `0.988` (199). The deviation is the `O(1/q)` subleading part of `Phi'`, not a wrong
  constant. The independent referee script (`ref-semilocal-archimedean/indep.py`) uses half the
  kernel, so its `16 pi^6` is this `64 pi^6`, with the same ratios.
* Full value `W(g_x)` from the zero side (2000 zeros, all verified on the line, plus a
  Lorentzian density tail) versus `Phi'(L/2)^2 log x/(2 pi x)`: ratio `1.071, 1.029, 1.006, 1.004,
  0.995` for `q = 7, 13, 47, 97, 199`. For `q >= 97` the density tail is 23-39% of the value.
* **Probe onsets versus the law** (COMPUTED; THEOREM-paper-proof as an asymptotic):

  | q | probe onset `x - q` | `W0(sqrt q/2)/(2pi)` | `(1/4pi) log q` |
  |---|---|---|---|
  | 7 | 0.1195 | 0.1073 | 0.155 |
  | 11 | 0.1304 | 0.1224 | 0.191 |
  | 13 | 0.1353 | 0.1282 | 0.204 |
  | 23 | 0.1539 | 0.1493 | 0.250 |
  | 47 | 0.1807 | 0.1781 | 0.306 |
  | 97 | 0.2114 | 0.2098 | 0.364 |
  | 199 | 0.2437 | 0.2433 | 0.421 |

  The gap to the law falls from 11% to 0.2%. The idea-stage values (`onsets_all.json`: 0.1194,
  0.1299, 0.1347, 0.1530, 0.1791, 0.2087, 0.2404) agree to within the tail treatment. For
  `q = 2, 3, 5` the direct zero-free evaluation gives 0.1199, 0.1070, 0.1115.

### 4b. The Galerkin horizons, re-evaluated from the other side of the explicit formula (`crosscheck_galerkin_zero_side.py`, builder stage)

The idea-stage horizons come from Galerkin matrices (N = 28, dps 50) assembled from the archimedean,
pole and S-prime terms (`wpw.py`, `semilocal.py`). A negative eigenvalue certifies indefiniteness
only if the matrix entries are right. So we took each bottom eigenvector `c`, formed the test
`g_c`, and recomputed `W_{S_q}(g_c)` as
`sum_rho |g_c^(gamma_rho)|^2 + 2 sum_{missing n} Lambda(n) n^{-1/2} h_{g_c}(log n)`.
That uses the zeros and the deleted primes only, and no archimedean term. It is an evaluation,
not an assumption: the first 2000 zeros are verified on the line. All 14 agree:

| x | S | pole-free | sector | Galerkin eigenvalue | zero-side value |
|---|---|---|---|---|---|
| 2.13 | {} | no | odd | -1.20638e-2 | -1.20638e-2 |
| 2.2 | {} | no | odd | -5.64075e-2 | -5.64075e-2 |
| 3.08 | {2} | no | odd | -9.55012e-6 | -9.55012e-6 |
| 3.13 | {2} | no | odd | -9.95047e-3 | -9.95047e-3 |
| 5.06 | {2,3} | no | odd | -2.00534e-10 | -2.00537e-10 |
| 5.1 | {2,3} | no | odd | -2.30804e-5 | -2.30805e-5 |
| 5.1 | {2,3} | no | even | -5.31276e-17 | -5.31595e-17 |
| 7.05 | {2,3,5} | no | odd | -3.69497e-14 | -3.69558e-14 |
| 7.1 | {2,3,5} | no | odd | -1.52883e-7 | -1.52884e-7 |
| 3.3 | {} | yes | even | -1.58002e-3 | -1.57966e-3 |
| 3.35 | {} | yes | even | -1.43083e-2 | -1.43080e-2 |
| 3.14 | {2} | yes | odd | -5.46467e-3 | -5.46467e-3 |
| 3.2 | {2} | yes | odd | -2.03642e-2 | -2.03642e-2 |
| 4.5 | {2} | yes | even | -2.49468e-1 | -2.49467e-1 |

So these **indefiniteness** statements are COMPUTED with two independent evaluations. They are not
interval-certified.

| lens statement | status |
|---|---|
| with poles: `x*_{S}` in (2.10, 2.13) for `S = {}`, (3.06, 3.08) for `{2}`, (5.04, 5.06) for `{2,3}`, (7.02, 7.05) for `{2,3,5}` | upper ends COMPUTED and cross-checked; lower ends are positive Galerkin eigenvalues, evidence only (a finite basis cannot certify PSD) |
| pole-free: (3.25, 3.30) for `S = {}`, (3.12, 3.14) for `{2}`, (5.05, 5.10) for `{2,3}` | same; the pure archimedean pole-free functional (Connes-Consani's `W_inf`) is indefinite at 3.3 (checked both ways) and numerically PSD up to about 3.27 |
| non-monotone in `S` | rigorous in the "adding a prime restores positivity" direction, given Zhu: with poles at `x = 2.5`, `S = {}` is indefinite (certified above) while `S = {2}` is the full form there, which is PSD (Zhu, `x <= 4.95`). Pole-free at `x = 3.2`, `S = {2}` is indefinite (checked both ways) while `S = {2,3}` is the full form, PSD. The other direction (adding 2 *destroys* pole-free positivity at 3.2) rests on `S = {}` being PSD there, which is evidence only |
| Connes-Consani's window `(1/2, 2)` | not a threshold. CC restrict to it because no prime enters; they never claim sharpness. The archimedean reservoir is finite (about 3.27), which is the point |

### 4c. Correction: the idea-stage zero side at small `x` (`check_small_x.py`)

`probe_fast.py` integrates the tail transform with 80 Gauss nodes per panel. For `x < 4`, `Phi'`
decays slowly and those panels carry hundreds of oscillations, so its zero-side values there are
wrong (e.g. 0.554 instead of 0.1668 at `x = 2.3`; `direct_eval_np.log`). With dense quadrature the
zero side matches the direct zero-free evaluation to 5-6 digits at every `x` tested: 0.1667908 vs
0.1667901 at `x = 2.3`, 9.9656e-12 vs 9.9643e-12 at `x = 7.3`. The reported small-`q` onsets came
from the direct evaluation, so they stand. This also validates the archimedean normalisation of the
direct formula at probe level. The builder's own zero-side code agrees with the dense version to
8e-4 at `x = 7.2` and 1e-6 at `x = 11`.

### 4d. Idea-stage computations not re-run by the builder (COMPUTED, single evaluation)

* Pole-free probe `(1/4 - d^2) Phi'` onsets 0.134-0.198 for `q = 11..199` (`probe_polefree.py`).
* Precision-barrier onsets (`precision_scan.py`, `precision_n*_s*.json`): logarithmic in
  `1/delta`, 0.16-0.25 per decade.
* Surgery fakes (`scan_golden_N24.json`, `logs/log2_golden_fine.txt`, `logs/log2_w1.txt`): golden
  onset in (5.5, 5.6), plateau -0.379937 = log 5 (2 - sqrt 5); W1(29,11) onset in (34, 36), plateau
  about -0.1433 at x = 60 versus log 29 (2 - 11/sqrt 29) = -0.14361.

---

## 5. The rest of the idea, claim by claim

1. **Fooling identity** (THEOREM-paper-proof). For the one-prime surgery `F = zeta E`,
   `E = 1 + c p0^{-s} + p0^{1-2s}`, `a = c/sqrt p0`: `Q_F = Q_zeta + Z`,
   `Z = log p0 sum_m c_m h(m log p0)`, `c_0 = 2`, `c_m = (-1)^m (r^m + r^{-m})`, `r + 1/r = a`. So for
   `p0` not in `S`, `Q_S^F = Q_S^zeta + 2 log p0 Id`: every S-local positivity statement about zeta
   transfers verbatim to the fake. Validated numerically to 1e-26 (`validate_semilocal.json`). The
   algebra of `Z` is kernel-checked (block E).
2. **Surgery detection and plateau.** Kernel: on windows `p0 < x < p0^2`,
   `Z >= log p0 (2 - |a|) ||g||^2`, and the pair probe attains `log p0 (2 - a)`. Paper:
   `lambda_min(Q_F|x) >= lambda_min(Q_zeta|x) + log p0 (2 - |a|)`. That lower bound is conditional on
   window positivity for zeta at `x`, which is RH-window above 4.95. The pair probe gives
   `lambda_min(Q_F|x) <= log p0 (2 - a) + 2 lambda_min(Q_zeta|x/p0)` (Cauchy-Schwarz on the cross
   term, again under window positivity).
   *Correction:* the idea's "universal function Y" is a bracket
   `[Y_1, Y_2]`, `Y_k(e) = inf{y : k lambda*_zeta(y) < e}`, not a single function. The cross term
   `B(phi, tau_l phi)` depends on `p0`.
3. **Two-sided precision barrier.** The structural half is kernel-checked (block D). The log law
   `Delta ~ (1/2pi) log(1/|delta|)` is THEOREM-paper-proof via the even and odd probes; the
   Galerkin slopes (0.16-0.25 per decade) sit below the probe slope 0.37. The conjectured
   super-exponential sharpening (true horizon excess tends to 0) is HEURISTIC.
4. **Fourier envelope** (THEOREM-paper-proof; per-prime inequality kernel-checked). The inequality
   `Q_S(g) >= 2A(g)B(g) + (1/2pi) int |g^|^2 (2 theta'(t) - 2A_P) dt` is correct.
   *Correction:* the "positive class" it names is empty inside the Weil test class. A nonzero
   compactly supported test has a transform analytic in the strip, so its spectral mass cannot sit
   in `|t| >= T_P`. The pole term `2AB = -2A^2` is negative on odd tests anyway. The statement is
   about the symbol, not about tests. The numbers `T_2 ~ 178` and `T_3 ~ 3.6e3` check out.

---

## 6. Negative controls and circularity

*Davenport-Heilbronn and Epstein.* The probe mechanism uses only the explicit-formula bookkeeping
and a kernel whose transform is the completed function (`Xi_D` for D). So the no-go goes through
verbatim for coefficient truncations of D. That is the right behaviour: the result asserts no
positivity, so D cannot contradict it. Kernel blocks A-D are about zeta's registry functional, but
every step is FE-generic.

*Golden fake, H4, W1, surgered factors.* For `p0` not in `S`, S-local positivity cannot separate
them from zeta (fooling identity). For `p0` in `S`, they are separated **only** through the local
failure `|a| > 2` at their own prime (kernel: `latticeForm_nonneg_iff`, `surgery_local_rh_iff`),
and only once the window reaches about `p0 Y`. The lens therefore has no Euler-product-specific
positivity lever.

*Circularity.* Nothing here is equivalent to RH except the relabeling
`rh_iff_semilocal_natural_windows`, which is Weil's criterion restated and is labelled as such.
The horizon upper bound, the precision barrier, the surgery algebra and the envelope are
statements about explicit quadratic forms, true whether or not RH holds.

---

## 7. What remains open

* `ProbeInput q x` in the kernel. The only missing analytic brick is `Phi^ = Xi` (Riemann's theta
  identity for the Polya kernel) plus the tail-sum estimate; `Phi' < 0` would also be needed.
  With those, the horizon upper half would be kernel-proved outright.
* Interval-certified Galerkin entries. Today the horizon intervals are two independent float
  evaluations.
* The true horizon excess `x*_{S_q} - q` for large `q`. Probe upper bound
  `~ (1/4pi) log q`; the Galerkin excess shrinks (0.115, 0.07, < 0.06, < 0.05 for q = 2, 3, 5, 7).
  CONJECTURE-with-evidence that it tends to 0.
* The lower half `x*_{S_q} >= q` for `q >= 5`. That is window Weil positivity: the wall.

---

## 8. Reproduce

```
cd telperion/research/crux2_semilocal-archimedean
python3 verify_probe_law.py               # ~90 s: normalisation, sign, overlap, W(g_x), onsets -> verify_probe_law.json
python3 crosscheck_galerkin_zero_side.py  # ~2 min: 8 with-pole certificates -> crosscheck_galerkin_zero_side.json
python3 crosscheck_galerkin_zero_side.py polefree   # 6 pole-free / even certificates
python3 check_small_x.py                  # dense zero side vs direct evaluation -> check_small_x.json
python3 direct_eval_np.py                 # idea-stage direct vs (under-resolved) zero side, see 4c
cd ../../examples/rvm_bridge/lean && lake env lean Crux/Crux2_semilocal_archimedean.lean
```

Idea-stage scripts (copied from the scratch directory, paths made relative): `wpw.py`
(Galerkin builder, validated against CCM's table to 2e-34), `semilocal.py`, `validate_semilocal.py`,
`scan_onsets.py`, `scan2.py`, `polefree.py`, `probe.py`, `probe_fast.py`, `direct_eval.py`,
`direct_eval_np.py`, `onsets_all.py`, `probe_polefree.py`, `precision_scan.py`, `validate_forms.py`,
with outputs `*.json` and `logs/`. Zeros: `../zeros2000.json`.
