# Heat-flow diffraction: searching for an arithmetic Lyapunov functional (2026-10-11)

**Status: a bounded numerical search, not a proof.** Nothing here is progress on RH; conjecture1_proved = False.
Nothing here estimates the de Bruijn-Newman constant Λ either. Λ ≥ 0 is a theorem (Rodgers-Tao, formalized
on this island) and Λ ≤ 0 is RH. No collision time is reported as a bound on anything.

Files in this directory:

| file | content |
|---|---|
| `heat_flow_ode.py` | conventions, ODE with mean-field tail, direct H_t evaluation, validation, forward runs (zeta + controls) |
| `diffraction_flow.py` | Bragg amplitudes, explicit-formula check, H1-H3, functionals, controls, the task-4 identity, backward flow |
| `zeros5001.txt` | first 5001 zeta ordinates (1-2000 from `research/zeros2000.json`; 2001-5001 from `mpmath.zetazero`, 20 significant digits, spot-checked) |
| `validation_ode_vs_direct.{txt,csv}` | ODE vs zeros of H_t computed directly from the integral |
| `spacing_stats_*.csv` | unfolded nearest-neighbour spacing statistics along t, zeta and six controls |
| `lamhat_zeta_{smooth,sharp}.csv` | effective von Mangoldt weights read off the diffraction, all t |
| `h2_measured_vs_predicted.csv` | H2 table |
| `functionals.csv`, `nprime_derivatives.{txt,csv}` | task 3 |
| `task4_identity_check.csv`, `task4_derivative_at_zero.csv` | task 4 |
| `task6_offline_signature.csv` | task 6 |
| `F_grid_zeta_smooth.csv` | F_t(u) on u in [0,5] at t = 0, 0.2, 0.5, 1 |
| `results_summary.txt` | full console output of `diffraction_flow.py` |
| `anchors_dh.py`, `anchors_results.txt`, `anchors_landau_residual.csv`, `anchors_dh_control.csv`, `dh_online_ordinates.txt` | section 7: certified anchors, Landau residuals, the Davenport-Heilbronn control |

Reproduce: `python3 heat_flow_ode.py all` then `python3 diffraction_flow.py` and `python3 diffraction_flow.py nprime`
(trajectories go to the session scratchpad; set `HEATFLOW_SCRATCH` to relocate).
**Interpreter deviation:** `~/e9-tools/venv` has mpmath and sympy but no numpy or scipy, so everything ran under
`/usr/bin/python3` (3.9.6; numpy 1.23.5, scipy 1.13.1, mpmath 1.3.0, numba 0.56.4) with
`OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=1`. Total compute is a few minutes; the O(N²) pair sums are numba loops.

## 1. Conventions, the ODE, the tail, validation

H_t(z) = ∫_0^∞ e^{tu²} Φ(u) cos(zu) du with the usual Φ, and H_0(z) = ξ(1/2 + iz/2)/8. Checked to 30+ digits at
z = 0, 10, 28. Differentiating under the integral gives ∂_t H = ∫ u² e^{tu²}Φ cos(zu) du = −∂_z² H, the
**backward** heat equation. At a simple zero, H(z_k(t), t) = 0 gives

    dz_k/dt = −∂_t H / ∂_z H = H''(z_k)/H'(z_k) = 2 Σ_{j≠k} 1/(z_k − z_j)

summed over all zeros of both signs, symmetrically. For t increasing this is repulsion. Using only the positive
zeros, dz_k/dt = 1/z_k + 4 z_k Σ_{j≠k} 1/(z_k² − z_j²). In zeta ordinates γ = z/2 it reads
dγ_k/dt = (1/2) Σ_{j≠k} 1/(γ_k − γ_j). This is the factor 2 the brief warns about. I derived the normalization
here and verified it numerically below. I did not re-read Polymath15 or Rodgers-Tao in this session.

The flow is the gradient flow ż = −2∇E of E = −Σ_{j<k} log|z_j² − z_k²| − ½ Σ log 2z_k, so dE/dt = −½ Σ ż_k².

**Tail correction (derived).** Zeros beyond z_N are replaced by a continuum on w ≥ Z_c = (z_N + z_{N+1})/2 plus
its mirror image. The continuum has density ρ(w) = (1/4π) log(w/4π) in z-units. Its force on a discrete zero is

    f_tail(z) = 2 ∫_{Z_c}^∞ ρ(w) [1/(z − w') + 1/(z + w')] dw = −4z ∫_{Z_c}^∞ ρ(w) / (w'² − z²) dw,    w' = w − πt/4.

The tail must move. A log density on all of R has mean-field velocity 2 PV∫ρ(w)/(z − w) dw. The Hilbert
transform of log|w| is −(π/2) sgn, so the velocity is 2·(1/4π)·(−π²/2) = **−π/4** (z-units; −π/8 for γ), a rigid
translation. This agrees with the known shift of the counting function, N_t(Z) = N_0(Z) + (t/16) log(Z/4π),
because (π/4)ρ(Z) = (1/16) log(Z/4π). The tail's potential is V(z,t) = −∫ρ log(1 − z²/w'²) dw. The model ignores
the tail's fluctuations, so diffraction uses only the first N' = 3000 of N = 5000 evolved zeros.

**Validation.** The first 8 zeros of H_t were computed directly from the integral with mpmath at 32 digits for
t = 0.01, 0.05, 0.2 and 1.0. The ODE was integrated with RK45 at rtol = atol = 1e-11.

| zero k | t | z_k(t) direct | ODE error, moving tail | no tail | static tail |
|---|---|---|---|---|---|
| 1 | 0.05 | 28.240474254649 | +4.5e-09 | +3.2e-04 | +5.0e-09 |
| 1 | 1.0 | 27.692038648375 | +8.9e-08 | +6.4e-03 | +3.0e-07 |
| 4 | 1.0 | 59.921622826244 | +1.9e-07 | +1.4e-02 | +6.6e-07 |
| 8 | 1.0 | 86.176638866335 | +2.7e-07 | +2.0e-02 | +9.4e-07 |

All 40 rows are in `validation_ode_vs_direct.csv`. The error grows linearly in t, which is consistent with a
small constant velocity error from the unmodelled tail fluctuations. Removing the tail costs five orders of
magnitude. A coordinate-local energy-gradient check agrees with the velocity to about 1e-6, the
finite-difference error.

**Crystallization (task 1).** Unfolded nearest-neighbour spacing variance over zeros 100-3000:

| t | zeta | GUE (seed 1) | Poisson (seed 1) |
|---|---|---|---|
| 0 | 0.1501 | 0.1800 | 0.936 |
| 0.1 | 0.1039 | 0.1245 | 0.714 |
| 0.25 | 0.0647 | 0.0793 | 0.545 |
| 0.5 | 0.0320 | 0.0417 | 0.382 |
| 1.0 | 0.0093 | 0.0145 | 0.218 |

The variance decreases monotonically for every ensemble. The minimum unfolded spacing of zeta rises from 0.089
to 0.758.

## 2. Diffraction at t = 0: the explicit formula, verified

Define A_t(u) = Σ_k w_k e^{iγ_k(t)u}, so F_t(u) = Re A_t(u) is the island's Bragg amplitude. The weights attach
to particles: sharp means w_k = 1 for k ≤ N'; smooth means w_k = cos²(πγ_k(0)/2T), with T between γ_{N'} and
γ_{N'+1}.

The explicit formula with h(r) = w(|r|/T)e^{iru} predicts

    F(u) = F_sm(u) + cosh(u/2) − ½ Σ_n Λ(n) n^{−1/2} [K_T(u − log n) + K_T(u + log n)],
    K_T(y) = (1/π) ∫_0^∞ w(r/T) cos(ry) dr,
    F_sm(u) = ∫_0^∞ w(r/T) cos(ru) θ'(r)/π dr.

The peak height is K_T(0)/2 = T⟨w⟩/2π with ⟨w⟩ = ∫_0^1 w. This is Landau's formula,
Σ_{0<γ≤T} x^{iγ} ≈ −(T/2π) Λ(x)/√x. The effective von Mangoldt weight read off the diffraction is

    Λ̂_t(n) := −2π√n (A_t(log n) − bg(log n)) / (T⟨w⟩).

Results at N' = 3000, T = 3533.7 (`results_summary.txt`):

- **Smooth window.** Λ̂_0(n) equals Λ(n) to all 4 printed digits for every n from 2 to 16. Prime powers give
  log p, and n = 6, 10, 12, 14, 15 give 0.0000. F_0(log n) matches the full prediction to 4 decimals, for
  example −137.2363 at n = 2.
- **Sharp window.** The agreement is to about 0.5%, with residuals of about 0.01 at composites. These are Gibbs
  and S(T) edge effects.

The t = 0 diffraction is understood to high accuracy.

## 3. H1-H3 along the flow

**H1 holds: the log-prime Bragg amplitudes decay monotonically.** The table shows Re Λ̂_t(n)/Λ(n), which is
F_t(log n) normalized by its t = 0 explicit-formula peak. Smooth window, N' = 3000.

| t | n=2 | 3 | 4 | 5 | 7 | 8 | 9 | 11 |
|---|---|---|---|---|---|---|---|---|
| 0 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 |
| 0.1 | 0.932 | 0.904 | 0.910 | 0.880 | 0.870 | 0.929 | 0.916 | 0.865 |
| 0.2 | 0.868 | 0.817 | 0.826 | 0.773 | 0.755 | 0.854 | 0.831 | 0.744 |
| 0.5 | 0.700 | 0.598 | 0.608 | 0.517 | 0.484 | 0.631 | 0.586 | 0.459 |
| 1.0 | 0.486 | 0.350 | 0.348 | 0.254 | 0.215 | 0.327 | 0.277 | 0.179 |

The sharp window gives the same picture. At t = 1 it reads 0.439 for n = 2 and 0.126 for n = 11.

**H2 holds in a corrected form: the decay is not exp(−c t log² p).** Two independent derivations give the same law.

1. *Effective Dirichlet series.* Write ξ ≈ M(s)Σn^{−s} + reflection, as in the approximate functional equation.
   In s, the flow is H_t = e^{(t/4)∂_s²}H_0. Acting on each term M(s)n^{−s} = e^{f(s)} with f' = M'/M − log n and
   M'/M ≈ ½ log(s/2π), it multiplies the n-th coefficient by

       a_n(t, γ) = exp((t/4) log² n) · (γ/2π)^{−(t/4) log n} · n^{−iπt/8}.

   This is the form of the Polymath15 effective approximation, b_n^t = exp((t/4) log² n) with a shifted s. The
   n^{−iπt/8} factor is the uniform drift −π/8 in γ.
2. *Log-gas phonons.* For a crystal of spacing a = 1/ρ under E = −Σ log|x_j − x_k|, the Hessian on the mode
   e^{iux} has eigenvalue θ(2π − θ)/(2a²), with θ = u/ρ, because Σ_{m≥1}(1 − cos mθ)/m² = θ(2π − θ)/4. With
   γ̇ = −½∇E, a density mode at frequency u relaxes at rate

       r(u, γ) = (u/4)(2πρ̄(γ) − u) = (u/4)(log(γ/2π) − u),   for 0 < u < 2πρ̄.

So the Bragg peak at log p decays like exp(−(t/4) log p · log(γ/(2πp))), averaged over the height window. The
log² p term enters with a **plus** sign: it is the curvature of the phonon branch. The rate goes to zero at u = 0
and at the local lattice frequency u = log(γ/2π).

**The law is universal, not arithmetic.** On the GUE controls, the band power ratio ⟨|A_t(u)|²⟩/⟨|A_0(u)|²⟩
follows the same phonon prediction:

| t | u ≈ 0.5 | u ≈ 1 | u ≈ 2 | u ≈ 3 |
|---|---|---|---|---|
| 0.2 | 0.822 vs 0.810 | 0.703 vs 0.691 | 0.609 vs 0.588 | 0.666 vs 0.616 |
| 0.5 | 0.617 vs 0.592 | 0.424 vs 0.403 | 0.324 vs 0.283 | 0.434 vs 0.352 |
| 1.0 | 0.389 vs 0.355 | 0.194 vs 0.172 | 0.153 vs 0.106 | 0.290 vs 0.268 |

Each cell is measured vs predicted, three GUE samples pooled. Agreement is within 3-10% at small u. The larger
deviations at large u and t are nonlinear effects.

**Composite Bragg peaks are born, as predicted.** The coefficients a_n are not multiplicative:
log²(mn) ≠ log² m + log² n. So −D'/D acquires weights at composite n, for example
Λ_b(6) = log 6 · (b_6 − b_2 b_3) ≈ (t/2) log 2 log 3 log 6.

The prediction is Λ̂_t(n) ≈ Λ_b(n; t) n^{−iπt/8} ⟨(γ/2π)^{−(t/4) log n}⟩_w. The height average uses Landau's range
γ ∈ [0, T]; in brackets is the variant starting at γ_1 = 14.13, which brackets the heuristic's
low-height uncertainty. Smooth window, N' = 3000; the last column is the control noise.

| t | n | measured Λ̂ | predicted, from 0 | [from γ_1] | sd of Re: GUE, Poisson |
|---|---|---|---|---|---|
| 0.2 | 2 | 0.6018 − 0.0319i | 0.6019 − 0.0328i | [0.5962 − 0.0325i] | 0.007, 0.052 |
| 0.2 | 7 | 1.4696 − 0.2244i | 1.4737 − 0.2270i | [1.4546 − 0.2241i] | 0.010, 0.083 |
| 0.2 | **6** | 0.0984 − 0.0135i | 0.1004 − 0.0142i | [0.0991 − 0.0140i] | 0.097, 0.081 |
| 0.5 | **6** | 0.1506 − 0.0527i | 0.1558 − 0.0572i | | 0.070, 0.045 |
| 0.5 | **10** | 0.2480 − 0.1196i | 0.2649 − 0.1286i | | 0.098, 0.041 |
| 1.0 | 2 | 0.3370 − 0.0916i | 0.3375 − 0.0942i | [0.3312 − 0.0924i] | 0.002, 0.006 |
| 1.0 | 11 | 0.4294 − 0.5463i | 0.4906 − 0.6741i | [0.4176 − 0.5738i] | 0.036, 0.089 |
| 1.0 | **6** | 0.1252 − 0.0987i | 0.1360 − 0.1154i | [0.1262 − 0.1071i] | 0.043, 0.018 |
| 1.0 | **12** | 0.1439 − 0.1789i | 0.1829 − 0.2702i | [0.1527 − 0.2256i] | 0.012, 0.049 |

The full table is `h2_measured_vs_predicted.csv`. For t ≤ 0.5 the agreement is within 1-7%. At t = 1 and
n ≥ 10 the two height conventions straddle the measurement. The heuristic is not valid at heights γ ≲ 2πn.

Along the flow, a single composite peak stands about 2-3 control standard deviations above noise at t ≥ 0.5. The
clean discrimination is the derivative at t = 0, shown in section 5.

**H3 holds for zeta and fails for every control.** The lattice peak is measured in unfolded coordinates, because
the local lattice frequency 2πρ̄ = log(γ/2π) is chirped across the window:
L_t = |Σ_k w_k e^{2πi N̄_t(γ_k(t))}| / Σ_k w_k, with N̄_t = N̄_0 + (t/16) log(γ/2π).

| t | zeta | gue1 | gue2 | gue3 | poi1 | poi2 | poi3 |
|---|---|---|---|---|---|---|---|
| 0 | 0.209 | 0.027 | 0.032 | 0.030 | 0.012 | 0.021 | 0.029 |
| 0.2 | 0.394 | 0.027 | 0.036 | 0.029 | 0.017 | 0.018 | 0.015 |
| 0.5 | 0.614 | 0.039 | 0.037 | 0.036 | 0.025 | 0.023 | 0.024 |
| 1.0 | 0.824 | 0.061 | 0.036 | 0.052 | 0.013 | 0.025 | 0.037 |

Zeta has zero monotonicity violations. The controls have 7-21 violations out of 43.

The mechanism is arithmetic only in a weak sense. Global phase coherence needs the counting fluctuation
x_k − k to be small. At t = 0 that coherence is already about e^{−2π² Var S}, with Var S(T) ~ (1/2π²) log log T
(Selberg). The coherence then grows because zeta's diffraction has **no mass in 0 < u < log 2**: there is no
prime below 2. Every mode zeta has therefore relaxes at rate at least r(log 2, γ). GUE and Poisson carry
long-wavelength modes, u → 0, whose rate r ∝ u goes to zero, so they never lock in phase over 3000 levels. I did
not attempt a quantitative prime-sum prediction of L_t, because it needs a cutoff convention at t = 0.

## 4. Candidate functionals (task 3)

All values use the smooth window, N' = 3000, and the 44-point t-grid on [0, 1]. "Violations" counts
finite-difference steps against the dominant sign, out of 43. Data are in `functionals.csv`.

| functional | zeta | GUE (3 samples) | Poisson (3 samples) |
|---|---|---|---|
| (a) log-gas energy E (moving tail) | ↓ 0 | ↓ 0, 0, 0 | ↓ 0, 0, 0 |
| (b) B = Σ_{p^m ≤ e^5} F_t(log p^m)² / N'² | ↓ 1 | ↑/↓ 18, 5, 7 | 15, 17, 20 |
| (b') B' = Σ \|A_t(log p^m)\|² / N'² | **↓ 0** | 11, 10, 9 | 16, 21, 20 |
| (c1) ℓ² distance to the t = 0 explicit-formula curve | ↑ 0 | 17, 7, 7 | 0, 10, 3 |
| (c2) ℓ² distance to the time-t lattice | **↓ 0** | 19, 17, 0 | 11, 1, 7 |
| (d) pure-point fraction (top-K window energy share) | ↓ 0 | ↑ 0, 0, 0 | ↑ 3, 6, 3 |
| lattice peak L_t | **↑ 0** | 7, 20, 8 | 21, 8, 11 |

Notes on each:

- **(a)** A frozen-tail run makes the system exactly autonomous. There, E decreases at every step, with the
  largest increment −12.9 (the sanity check). With the moving tail, ∂_t V is positive but smaller than the
  dissipation on [0, 1].
- **(b')** For zeta, B' runs from 0.0937 to 0.0247. It exceeds the controls by about 23x (GUE) and 18x (Poisson)
  at t = 0, and by 6x and 10x at t = 1. The real-part version (b) has one violation because the drift phase
  n^{−iπt/8} rotates Re A.
- **(c1)** This is trivially increasing for zeta. It starts at 0.006, which is the section 2 check, and ends at
  1.33.
- **(d)** This is monotone for every ensemble, but in opposite directions for zeta and the controls. It measures
  crystallization in general, not primes.

**Derivative at 0+ versus N'** (`nprime_derivatives.txt`). None of the zeta derivatives converges as N' grows.

| N' | T | zeta dB'/dt | zeta (dB'/dt)/B' | d Re Λ̂(2)/dt | d(dist_latt)/dt | dL/dt |
|---|---|---|---|---|---|---|
| 500 | 812 | −0.039 | −0.26 | −0.31 | −0.50 | +0.61 |
| 1000 | 1420 | −0.089 | −0.70 | −0.38 | −0.75 | +0.74 |
| 2000 | 2516 | −0.143 | −1.36 | −0.45 | −1.01 | +0.88 |
| 3000 | 3534 | −0.170 | −1.81 | −0.49 | −1.21 | +0.96 |

Each grows roughly like log T, as the phonon law predicts through ⟨log(γ/2π)⟩_w. The phonon prediction for
(dB'/dt)/B' is −1.66 at N' = 3000 and −1.09 at N' = 2000. It fails at N' = 500, predicting +0.82 against a
measured −0.26. There e^{u_max} = 148 exceeds T/2π, so some peaks sit outside the first Brillouin zone, where the
parabola law does not apply. dE/dt is extensive (−4.47e3 for zeta, all N), as it must be.

The height scaling makes the T → ∞ statement explicit. Fitting log|A_t(log 2)| against log T over the four N'
values gives:

| t | fitted slope | phonon law, 1 − (t/4) log 2 |
|---|---|---|
| 0 | 1.010 | 1.000 |
| 0.5 | 0.927 | 0.913 |
| 1.0 | 0.845 | 0.827 |

So the Bragg weight per zero at log p tends to 0 as T → ∞ for every t > 0. **In the infinite-height limit, the
normalized prime Bragg functional is discontinuous at t = 0:** the heat flow destroys the quasicrystal
instantly, only logarithmically slowly in T.

## 5. The analytic derivative at t = 0 (task 4)

**Exact identity.** Let S_t(u) = Σ_a cos(x_a u) over any finite symmetric configuration {x_a} = {±γ_k} moving by
ẋ_a = ½ Σ_{b≠a} 1/(x_a − x_b). Then

    ∂_t S_t(u) = (u²/4) S_t(u) − (u/4) ∫_0^u S_t(v) S_t(u − v) dv.

*Proof.* (e^{iau} − e^{ibu})/(a − b) = i∫_0^u e^{iav} e^{ib(u−v)} dv. Symmetrizing the pair sum gives
Σ_{a≠b} sin(x_a u)/(x_a − x_b) = ½[(S⋆S)_{[0,u]}(u) − u S(u)]; the diagonal term a = b produces the −uS. Then
∂_t S = −u Σ_a sin(x_a u) ẋ_a. This is the u-space form of the Burgers-type equation
∂_t G = −G'' − 2GG' for G = H_t'/H_t, which follows from ∂_t log H = −(G' + G²).

*Numerical check* (`task4_identity_check.csv`): with N = 1000 zeta zeros (2000 signed points), the pair sum and
the quadrature autoconvolution agree to relative error 4e-15 to 8e-14 at u = 0.4, log 2, log 3, log 5, 2, log 11.

**Arithmetic form (explicit formula applied twice, Montgomery-style).** Insert
S_0 = smooth − Σ_n Λ(n) n^{−1/2}(δ_{log n} + δ_{−log n}) + 2cosh(u/2). Writing the Bragg weight at log N as the
coefficient c(N) in −c(N) N^{−1/2} δ_{log N}, the three contributions to dc(N)/dt at t = 0 are:

- **Prime-prime:** −(u/4)(S_pr ⋆ S_pr) contributes +(1/4) log N · (Λ*Λ)(N). The Dirichlet convolution creates
  peaks at products of prime powers.
- **Linear:** (u²/4)S contributes +(1/4) log² N · Λ(N).
- **Smooth-prime cross term:** this one is heuristic. The central peak of S near v = 0, convolved with a prime
  peak, picks out π × local density plus i × the mean force. It contributes
  −(1/4) log N · Λ(N) · (log(γ/2π) + iπ/2), height-resolved.

Window-averaged, this gives

    dΛ̂_t(N)/dt |_{t=0} = (1/4)[log² N · Λ(N) + log N · (Λ*Λ)(N)] − (1/4) log N · Λ(N) · [⟨log(γ/2π)⟩_w + iπ/2].

This agrees exactly with the effective-Dirichlet-series derivative,
d/dt Λ_D(n) = (1/4)[log² n Λ_D(n) + log n (Λ_D*Λ_D)(n)] − …, which comes from d/dt log D = (1/4)D''/D.

*Numerical check against the exact ODE velocities, with tail* (`task4_derivative_at_zero.csv`; smooth window,
N' = 3000; ⟨log(γ/2π)⟩_w = 4.743 over [0, T]):

| n | (Λ*Λ)(n) | zeta measured | arithmetic prediction | [γ_1-window variant] | GUE1 measured | Poisson1 measured |
|---|---|---|---|---|---|---|
| 2 | 0 | −0.4871 − 0.1865i | −0.4864 − 0.1887i | [−0.4873 − 0.1872i] | −0.028 + 0.005i | +0.372 − 0.162i |
| 5 | 0 | −2.0384 − 1.0043i | −2.0290 − 1.0172i | | −0.144 + 0.002i | +0.218 + 0.184i |
| **6** | 1.523 | **+0.6729 + 0.0060i** | **+0.6822** | [+0.6768] | −0.077 − 0.289i | +0.063 + 0.273i |
| 8 | 0.961 | −0.4768 − 0.5499i | −0.4602 − 0.5660i | | −0.188 + 0.183i | −0.503 − 0.760i |
| **10** | 2.231 | **+1.2560 + 0.0115i** | **+1.2844** | | −0.039 + 0.089i | −1.506 + 0.927i |
| 11 | 0 | −3.4172 − 2.2246i | −3.3706 − 2.2580i | | +0.603 + 0.081i | +0.660 + 1.371i |
| **15** | 3.536 | **+2.3275 + 0.0225i** | **+2.3941** | | −0.103 + 0.555i | −0.605 + 0.567i |
| 16 | 1.441 | −0.0328 − 0.7345i | +0.0525 − 0.7547i | [+0.0331 − 0.7487i] | −0.359 − 0.371i | −3.386 − 0.311i |

For zeta, all 15 values of n from 2 to 16 agree within about 0.5-3% of the dominant component, including every
composite. n = 16 has a near-cancelling real part. The controls show no relation to the arithmetic formula.

**What this says.** The time-derivative of the zero-diffraction at t = 0 is a quadratic functional of the
diffraction itself. Through the explicit formula, its prime content is:

- a universal linear term, the log-gas phonon rate at u = log N;
- a genuinely arithmetic source term, (1/4) log N (Λ*Λ)(N). The heat flow breaks the Euler product, and
  composite Bragg peaks at log 6, log 10, log 12, … are born at first order. This is the arithmetic signature of
  the flow, and it is confirmed numerically.

**What it does not say.** It contains no sign information that could constrain Λ. It is a t = 0⁺ statement,
under RH-type assumptions implicit in the explicit-formula reading, about frequencies u = log N of order 1. RH
and the value of Λ are governed by local collision events at frequency scale 1/δ, as section 6 shows. The
smooth-prime cross term is heuristic; only the finite-N identity is exact.

## 6. Backward flow and the off-line signature (task 6, qualitative)

The closest pair among the first 5000 zeros is γ ≈ 5229.1986 and 5229.2418 (k = 4765, 4766), with gap 0.0433.
Integrating backward, this pair reaches z-gap 1e-3 after a short negative time. That time is an artifact of the
truncated model and **is not, and is not reported as, a bound on Λ**.

Just before the event, the log-prime amplitudes have barely moved:

| | F(log 2) | F(log 3) | F(log 5) | F(log 7) | F(log 11) |
|---|---|---|---|---|---|
| t = 0 | −137.236 | −177.532 | −201.290 | −205.501 | −201.650 |
| just before the event | −137.327 | −177.700 | −201.531 | −205.767 | −201.922 |
| relative change | 6.6e-4 | 9.4e-4 | 1.2e-3 | 1.3e-3 | 1.4e-3 |

These are smooth, slight backward growths, consistent with the phonon law run in reverse. **The collision is
invisible at log p.** The colliding pair contributes O(1) to amplitudes of size O(T).

A pair of H-zeros z = x ± iy corresponds to zeta zeros 1/2 ± y/2 + ix/2. So γ = x/2 and δ = y/2, and the pair
contributes cos((x+iy)u/2) + cos((x−iy)u/2) = **2 cosh(δu) cos(γu)**, the island's off-line signature. The
excess envelope over an on-line pair is 2(cosh δu − 1) (`task6_offline_signature.csv`):

| δ | u = log 2 | u = 5 | u = 20 |
|---|---|---|---|
| 0.01 | 4.8e-5 | 2.5e-3 | 4.0e-2 |
| 0.05 | 1.2e-3 | 6.3e-2 | 1.09 |
| 0.2 | 1.9e-2 | 1.09 | 52.6 |
| 0.5 | 0.12 | 10.3 | 2.2e4 |

Continuing the colliding pair into the complex domain with the complex ODE, discrete part only, the off-line
displacement grows like √|Δt|. Seeded at δ = 0.0071, it reaches 0.0123, 0.0158, 0.0187, 0.0212 and 0.0235 after
further backward times of 2, 4, 6, 8 and 10 × 10⁻⁴. This is the local square-root birth law
Δ² ∝ 8(t − t_c) of the pair. RH failure would show in F_t as an **exponentially growing envelope at large u, of
order 1/δ**, not as any change at u = log p, where it is suppressed by about δ²u²/2.

## 7. Certified anchors, Landau normalization, and the Davenport-Heilbronn control

This section was added after the island owner supplied certified anchors. It uses the island convention
F_T(u) = Σ_{0<γ≤T} cos(γu): one-sided, unweighted, no normalization. The script is `anchors_dh.py` and the
output is `anchors_results.txt`. The island files were read only.

**First validation: BraggH100 reproduces.** With the 29 zeros below T = 100 at u2 = 693147/10⁶, the computed
value is F_100(u2) = −7.07807476640591. That lies inside the certified interval
[−7.0780948677, −7.0780546651] of `bragg_amplitude_h100`. The Landau peak is −(100/2π)·log 2/√2 = −7.8006.

**Landau normalization at t = 0.** The prediction is F_T(log n) ≈ −(T/2π)Λ(n)/√n + O(log T), in Gonek's uniform
form; no explicit constant exists in the project. The table shows the ratio to the Landau peak, the residual R,
and R_sm, which is R minus the smooth gamma-factor and Gibbs term of the explicit formula (section 2).

| T | log T | n=2 ratio | R | R_sm | n=3 ratio | R | R_sm | n=5 ratio | R | R_sm |
|---|---|---|---|---|---|---|---|---|---|---|
| 100 | 4.61 | 0.907 | +0.72 | −0.00 | 0.925 | +0.76 | −0.11 | 0.958 | +0.48 | −0.45 |
| 500 | 6.21 | 0.974 | +1.03 | −0.41 | 0.971 | +1.45 | +0.34 | 0.969 | +1.76 | +0.45 |
| 1000 | 6.91 | 0.981 | +1.48 | −0.16 | 0.994 | +0.64 | +0.40 | 0.984 | +1.82 | +0.30 |
| 2000 | 7.60 | 1.002 | −0.31 | +0.11 | 0.999 | +0.20 | +0.17 | 0.992 | +1.77 | +0.12 |
| 3500 | 8.16 | 0.993 | +1.86 | +0.32 | 0.997 | +1.07 | +0.38 | 0.999 | +0.24 | −0.76 |

At t = 0, |R| ≤ 2.2, well inside O(log T). Most of R is the explicit-formula smooth term: after subtracting it,
|R_sm| ≤ 0.8 for every n in the table. All n up to 11 are in `anchors_landau_residual.csv`.

**Landau normalization along the flow, T = 3500.** The table shows the ratio F_t(log n)/Landau and R/log T.

| t | n=2 ratio | R/logT | n=3 | R/logT | n=5 | R/logT | n=7 | R/logT |
|---|---|---|---|---|---|---|---|---|
| 0 | 0.993 | +0.23 | 0.997 | +0.13 | 0.999 | +0.03 | 0.996 | +0.20 |
| 0.1 | 0.916 | +2.81 | 0.887 | +4.89 | 0.859 | +6.93 | 0.843 | +7.89 |
| 0.2 | 0.844 | +5.20 | 0.788 | +9.17 | 0.737 | +12.94 | 0.710 | +14.53 |
| 0.5 | 0.660 | +11.38 | 0.550 | +19.50 | 0.458 | +26.64 | 0.417 | +29.28 |
| 1.0 | 0.434 | +18.95 | 0.296 | +30.50 | 0.197 | +39.45 | 0.159 | +42.24 |

These are the H1 numbers in the owner's normalization, with the same conclusion. The departure from Landau along
the flow is of order T, not O(log T). By t = 0.1 the residual is already 3-8 times log T. This is the
finite-height form of the section 4 statement: per zero, the Bragg weight scales like T^{1−(t/4) log n}.

**Davenport-Heilbronn comb as a fourth control.** `telperion.arb_dh` needs libflint, which is not installed. I
therefore re-implemented D(s) = 5^{−s}[ζ(s,1/5) + κζ(s,2/5) − κζ(s,3/5) − ζ(s,4/5)] in mpmath Hurwitz zeta,
with the island's κ and gamma factor (π/5)^{−(1+s)/2}Γ((1+s)/2). I refined all 204 certified on-line boxes of
`dh_zeros.json` to ordinates by a sign change of the real Z_D inside each box; every root lies inside its box.

The implementation passes both certified ZooDH checks:

| quantity | computed | certified box |
|---|---|---|
| F_on,100(u2) | −0.156521 | [−0.170181, −0.152173] |
| F_on,100(u5) | −2.198128 | [−2.254028, −2.031779] |

At t = 0 and T = 250, the DH comb has Bragg weights at log n equal to the −D'/D coefficients Λ_D(n). These are
not prime-supported: they are large at n = 4, 6, 9, 12 and zero at n = 5. The on-line comb alone undershoots
them by about 25%. Adding the 4 off-line pairs as 2cosh(δu)cos(γu) closes the gap. The entry at γ = 166.5,
δ = 0.1 is used as given; it is flagged as unverified.

| n | Λ(n) | zeta Λ̂ | Λ_D(n) | DH on-line only | DH + 4 off-line pairs | GUE sd | Poisson sd |
|---|---|---|---|---|---|---|---|
| 2 | 0.693 | 0.699 | 0.197 | −0.096 | 0.153 | 0.035 | 0.186 |
| 4 | 0.693 | 0.613 | −1.442 | −1.118 | −1.346 | 0.156 | 0.132 |
| 5 | 1.609 | 1.541 | 0 | −0.019 | −0.068 | 0.465 | 0.617 |
| 6 | 0 | −0.017 | 1.936 | 1.297 | 1.777 | 0.400 | 0.534 |
| 9 | 1.099 | 0.962 | −2.286 | −1.689 | −2.083 | 0.242 | 0.308 |
| 11 | 2.398 | 2.223 | 2.398 | 1.867 | 2.432 | 0.166 | 0.742 |
| 12 | 0 | −0.004 | −0.763 | −0.066 | −0.611 | 0.491 | 0.287 |

At this small height, the off-line zeros carry a visible share of DH's Bragg weight even at u = log 2, where
cosh(δu) − 1 is small. That is because each off-line pair contributes about 2, against a total of order T/2π.

I evolved the on-line DH comb under the same ODE, with a conductor-5 mean-field tail. Its peaks, which are not
prime-supported (n = 4, 6, 9, 11), also decay monotonically. For example, at n = 6 the weight falls from 1.30 to
0.99, 0.64 and 0.29 at t = 0.2, 0.5 and 1. This is the same universal phonon damping as for zeta. The decay
therefore does not distinguish a prime-supported (Euler product) comb from a non-Euler one. This supports the
verdict below: the monotonicity is not arithmetic.

This evolved comb is not the heat flow of the DH function: its 4 off-line pairs, which are complex in z, are
left out. So the DH heuristic prediction is not expected to match along t, and it does not, being off by factors
up to 2. At T = 250 the zeta heuristic is also only good to 5-40%, versus 1-7% at T = 3534, because the
effective-Dirichlet-series picture fails at low heights. Full rows are in `anchors_results.txt` and
`anchors_dh_control.csv`.

## 8. Verdict

The brief asked whether some functional both carries the primes and is monotone. Measured against that:

- **Monotone and arithmetic-looking, on [0, 1] at finite height:** the complex Bragg weight
  B'(t) = Σ_{p^m ≤ e^5} |A_t(log p^m)|²/N'² and the lattice peak L_t. Both have zero violations for zeta and are
  non-monotone for all six controls. B' exceeds the controls by 6-31x and L_t by about 7-60x. The ℓ² distance
  to the lattice is also monotone for zeta, but it is monotone for one GUE sample too.
- **But the monotonicity is not arithmetic.** It is the universal log-gas phonon damping,
  rate (u/4)(log(γ/2π) − u), evaluated where zeta happens to have diffraction mass. That law is confirmed on GUE
  within about 10%. The primes enter only through the initial data: the t = 0 Bragg peaks for B', and the
  diffraction gap (0, log 2) for L_t.
- **B' fails three structural tests.** Its derivative at 0⁺ diverges like log T. Its per-zero normalized value is
  discontinuous at t = 0 as T → ∞, with slope 1 − (t/4) log 2 confirmed. Its monotonicity needs
  e^{u_max} < T/2π, because peaks outside the first Brillouin zone are governed differently, as the N' = 500
  failure shows.
- **The genuinely arithmetic dynamical content** is the exact quadratic evolution law. Through the explicit
  formula it produces the source term (1/4) log N (Λ*Λ)(N). That source term carries no sign and gives birth to
  composite Bragg peaks rather than controlling a Lyapunov quantity.
- **The DH control confirms this.** A comb whose peaks are not prime-supported decays the same way.
- **No candidate sees the events that matter for Λ.** Collisions and off-line pairs are invisible at log p and
  appear only at frequencies of order 1/δ.

**Bottom line:** no functional examined here is both arithmetic in its mechanism and monotone in a way that
survives T → ∞. The search found one confirmed piece of structure: the u-space Burgers identity and its
prime-sum evaluation, verified to 1-3%. It also found a corrected H2: the phonon law, with a positive log² p
term.

**Nothing here is progress on RH; conjecture1_proved = False.**
