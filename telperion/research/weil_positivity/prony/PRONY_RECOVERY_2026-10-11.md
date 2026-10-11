# Recovering zeta ordinates from the prime side of the Weil form (Prony / MUSIC experiment), 2026-10-11

**Status: a bounded numerical search for structure. Not a proof, not evidence for RH beyond what the explicit formula already says. Nothing here is progress on RH; conjecture1_proved = False.**

Code: `weil_prony.py` (explicit formula, Gram matrix, recovery, controls, driver `python weil_prony.py run zeros_1e4.npy`), `zeros_rs.py` (zero list). Independent of `../weil_form.py` (not read, not imported); the parent should reconcile conventions.

## 1. Convention and the explicit formula used

For g continuous, compactly supported in [-A, A]:

* h(r) = ghat(r) = ∫ g(x) e^{irx} dx;  F(s) = ∫ g(x) e^{(s-1/2)x} dx, so F(1/2+ir) = h(r), F(0) = h(i/2), F(1) = h(-i/2).
* ZERO SIDE: Σ_ρ F(ρ) = Σ_γ h(γ), γ over ordinates (ρ = 1/2 + iγ) of both signs, with multiplicity.
* PRIME SIDE (zeta):

  W(g) = F(0) + F(1) - g(0) log π + Arch_{1/4}(g) - Σ_n Λ(n) n^{-1/2} (g(log n) + g(-log n)),

  Arch_κ(g) := (1/2π) ∫ h(r) Re ψ(κ + ir/2) dr
            = -γ_E g(0) + ∫_0^∞ [2 g(0) e^{-2x} - (g(x)+g(-x)) e^{-2κx}] / (1 - e^{-2x}) dx

  (x-space form from Gauss's integral ψ(z) = -γ_E + ∫_0^∞ (e^{-t} - e^{-zt})/(1-e^{-t}) dt). So the prompt's "archimedean term" is g(0) log π - Arch_{1/4}(g).
* Generic form used for the controls: W_c(g) = P·(F(0)+F(1)) + g(0) log(q/π) + Arch_κ(g) - Σ c(n) n^{-1/2}(g(log n)+g(-log n)), where P ∈ {0, 1} marks the pole term. Zeta has c = Λ, P = 1, q = 1, κ = 1/4. An odd character mod q, or Davenport-Heilbronn with q = 5, has P = 0 and κ = 3/4.

## 2. Gram matrix in the Fourier basis: closed form

φ_j(x) = (2a)^{-1/2} e^{iπjx/a} on [-a, a], j = -N..N, ω = π/a, n = 2N+1.

* Atoms: u_j(γ) := φ̂_j(γ) = √(2a) sinc(γa + πj) = √(2a) (-1)^j sin(γa) / (γa + πj).
  **These are Cauchy vectors in the node set {-ωj}, not Vandermonde vectors.** The Fourier basis is orthonormal, so Σ_j u_j(γ)² = 2a for γ deep inside the band |γ| < πN/a (Parseval).
* g_jk := φ_j ∗ φ̃_k, φ̃(x) = conj φ(-x), is supported in [-2a, 2a], and ĝ_jk(γ) = u_j(γ) u_k(γ) is real. Hence **G_jk := W(g_jk) = Σ_γ u_j(γ) u_k(γ)**, a real symmetric sum of rank-one atoms with unit weights. The atom pair for ±γ is u(γ)u(γ)ᵀ + J u(γ)u(γ)ᵀ J, where J is the flip j → -j.
* Explicitly, for x in [0, 2a]: g_jk(x) = (-1)^d sgn(x)(e^{ikωx} - e^{ijωx})/(2πi d) when d = j-k ≠ 0, and g_kk(x) = (1 - |x|/2a) e^{ikωx}. Only the even part matters, so each entry reduces to one-dimensional families:

  * j ≠ k:  **G_jk = (-1)^{j-k} (T(k) - T(j)) / (π (j-k))**. This is a Loewner matrix, so G is not Toeplitz in j - k.
    T(m) = 2C(m) - S(m) - Ps(m), with
    C(m) = ∫_0^{2a} sin(mωx) cosh(x/2) dx = -mω (cosh a - 1)/(m²ω² + 1/4),
    S(m) = ∫_0^{2a} sin(mωx) e^{-x/2}/(1-e^{-2x}) dx,
    **Ps(m) = Σ_{n ≤ e^{2a}} Λ(n) n^{-1/2} sin(mω log n)**, the sinc-type prime kernel.
  * j = k:  G_kk = D1(k) - log π - γ_E - log(1-e^{-4a}) + D2(k) - 2 Σ_{n ≤ e^{2a}} Λ(n) n^{-1/2} (1 - log n/2a) cos(kω log n),
    D1(k) = 4∫_0^{2a}(1-x/2a) cos(kωx) cosh(x/2) dx, D2(k) = ∫_0^{2a}[2e^{-2x} - 2(1-x/2a)cos(kωx)e^{-x/2}]/(1-e^{-2x}) dx.

  So the whole n×n matrix is fixed by 2N+1 numbers: T(1..N) and the diagonal values G_00..G_NN. Each is a finite prime sum over n ≤ e^{2a} plus elementary integrals.
* **First-moment matrix** K_jk := W(i g_jk'), whose zero side is Σ_γ γ u_j(γ) u_k(γ). That sum converges absolutely once ±γ are paired. It has the same structure: K_jk = -(-1)^{j-k}(k T(k) - j T(j))/(a(j-k)) and K_kk = T(k)/a - kω G_kk. It is cross-checked against the zero side below.
* Displacement identity behind the "ESPRIT": (γ I + Ω) D u(γ) = (√(2a) sin(γa)/a)·1, with Ω = diag(ωj) and D = diag((-1)^j). Projecting off the all-ones vector turns the signal subspace into a pencil whose eigenvalues are the atom frequencies (`esprit_loewner`).

## 3. Validation

**Zero list (`zeros_1e4.npy`).**
* The list is the first 10^4 ordinates, with γ_10000 = 9877.782654. They were bracketed with a vectorized Riemann-Siegel formula (C0 term only) and refined with `mpmath.siegelz`.
* The index check against `mpmath.zetazero` passes at 15 spot indices from k = 1 to k = 10000, with difference 0.
* **Defect found and fixed.** The first refinement left 46 zeros on Riemann-Siegel grid nodes, off by up to 4.3e-3. The C0-only grid had put the sign change one cell off, and the bisection fallback drifted to a bracket endpoint.
  * The index check could not see this.
  * The Gram cross-check did: it was off by 4e-3 at a = 1, |k| ≈ 30, where a bad zero near 92.5 sits under an O(1) atom.
* A second pass re-refined those 46 zeros (`rerefine_zeros.py`; folded into `zeros_rs.py`). Afterwards:
  * max |Z(γ)| is 2.4e-12 on the fixed zeros and 1.1e-11 on 300 random others;
  * the first 300 equal `mpmath.zetazero` exactly.

  All numbers below use the corrected list.

**Explicit formula, smooth test function.** The test function is g = cos^4(πx/2A) on [-A, A], with ĝ ~ 3(π/A)^4/r^5. The prime side is computed at 40 digits with exact log p. The zero side is 2Σ_{k ≤ 10^4} ĝ(γ_k); its tail is below 1e-15.

| A | primes used | prime side W(g) | zero side | difference |
|---|---|---|---|---|
| 2 | n ≤ 7 | -1.062757664082918e-5 | -1.062757664082839e-5 | -7.9e-19 |
| 6 | n ≤ 403 | 3.738401633235737e-8 | 3.738401633232925e-8 | 2.8e-20 |
| 12 | n ≤ 162754 | 1.107338665512107e-9 | 1.107338665518682e-9 | -6.6e-21 |

The pieces at A = 12 are F(0)+F(1) = 68.1031473259, Arch = -3.5240529122 and primes = 63.4343645268, so the cancellation is about 10 orders of magnitude. The x-space and r-space forms of the archimedean term agree to 2.1e-13 at A = 2, where the r-integral is truncated at 600.

**Gram matrix.** The closed form above is compared with the zero side Σ_{k ≤ 10^4} [u uᵀ + J u uᵀ J] plus a smooth-density tail with an N0(T) = θ(T)/π + 1 boundary correction. N = 30 throughout. Source: `validation.txt`.

| a | max abs(G_prime - G_zero) | max abs(G) | max abs(K_prime - K_zero) | max abs(K) |
|---|---|---|---|---|
| 1 | 2.4e-8 | 3.7 | 4.6e-6 | 335 |
| 2 | 3.6e-8 | 4.2 | 3.4e-6 | 172 |
| 3 | 1.7e-8 | 6.1 | 1.1e-6 | 185 |
| 4 | 2.6e-8 | 8.0 | 1.2e-6 | 141 |
| 5 | 4.0e-7 | 4.1 | 1.5e-5 | 59 |
| 6 | 4.4e-9 | 12.0 | 1.4e-7 | 170 |

The remaining differences come from the zero side's tail model, which replaces sin²(γa) by 1/2 and the zero count by its smooth part beyond γ_10000. They are not from the prime side: the same closed form with only 300 zeros was off by about 1e-5, and the error shrinks as zeros are added. **PSD check:** the minimum eigenvalue of G in double precision lies between -1.2e-15 and -4.1e-13 in every zeta configuration, which is PSD to roundoff (`summary_zeta.csv`). At 40 digits (`mp_precision.txt`):
* a = 1, N = 30: the smallest eigenvalues are 1.3e-29, 3.3e-26, 4.4e-23 and so on, all **positive**, with an exponentially decaying spectrum.
* a = 3, N = 20: the smallest six are ±1e-40, which is the 40-digit floor. This G has eigenvalues below 1e-40, so their sign is not certified here.

## 4. What resolution to expect

* **Band.** The n = 2N+1 modes span frequencies |γ| ≤ Γ_N := πN/a. An ordinate inside the band gives an atom of norm² ≈ 2a, so it shows up as an eigenvalue near 2a when it is isolated. Ordinates above the band leak in only through the 1/γ sinc tails.
* **Rayleigh.** Test functions supported in [-a, a] see frequencies with resolution π/a. Zeros near height T are spaced 2π/log(T/2π) apart. They are separated without super-resolution while T < T_R := 2π e^{2a}.
* **Information.** The Slepian count says the space of type-a functions concentrated on |γ| ≤ T has dimension about 2aT/π. The number of atoms below T is 2N_ζ(T) ≈ (T/π) log(T/2πe). The atoms fit while T < T_I := 2π e^{2a+1}. Beyond T_I the in-band atoms outnumber the available dimensions, and no subspace method can separate them at any precision.
* Expected number of resolvable ordinates is N_ζ(min(Γ_N, T_I)), with T_R as the threshold above which precision is needed:

| a | T_R = 2πe^{2a} | N_ζ(T_R) | T_I = 2πe^{2a+1} | N_ζ(T_I) | Γ_N, N_ζ(Γ_N) for N = 30 / 60 / 100 |
|---|---|---|---|---|---|
| 1 | 46.4 | 8 | 126.2 | 41 | 94.2, 26 / 188.5, 73 / 314.2, 147 |
| 2 | 343 | 165 | 932 | 595 | 47.1, 8 / 94.2, 26 / 157.1, 56 |
| 3 | 2535 | 2018 | 6890 | 6581 | 31.4, 4 / 62.8, 14 / 104.7, 31 |
| 4 | 1.87e4 | 2.1e4 | 5.1e4 | 6.5e4 | 23.6, 2 / 47.1, 8 / 78.5, 20 |
| 5 | 1.38e5 | 2.0e5 | 3.8e5 | 6.0e5 | 18.8, 1 / 37.7, 6 / 62.8, 14 |
| 6 | 1.02e6 | 1.8e6 | 2.8e6 | 5.3e6 | 15.7, 1 / 31.4, 4 / 52.4, 10 |

  For a ≥ 2 and N ≤ 191 the band is always the binding constraint, so every in-band ordinate should be recoverable. For a = 1 the band at N ≥ 60 goes past T_I = 126, so recovery has to fail there. At N = 30 the band (94) lies between T_R and T_I, so recovery needs precision beyond double.
* The prime side needs only n ≤ e^{2a}: the primes and prime powers up to 7 for a = 1, up to 403 for a = 3, and up to 162 754 for a = 6.

## 5. Recovery of the ordinates from the prime-side G (zeta)

**Methods.**
* **(a) MUSIC.** It uses the exact sinc steering vectors u(γ). The signal dimension m is chosen blind, as the number of eigenvalues with absolute value above 0.4a. It is run raw (p = 0) and on the **tapered subspace** p = 6: trigonometric polynomials vanishing to order 6 at ±a, which lie inside the same span. There the out-of-band atoms decay like γ^-7 instead of γ^-1. The tapered subspace is the main tool; the raw Fourier basis leaks too much.
* **(b) Loewner/Cauchy ESPRIT.** This uses the displacement identity of §2.
* **(c) NNLS.** w ≥ 0 on a grid with step 0.02, at N = 30.
* **(d) Ritz pencil (K, G)** on the signal subspace; see §7.
* **Weights:** least squares in the tapered subspace with one weight per ±γ pair. Unit weight means multiplicity one.

**Spectrum of G.** For every a ≥ 2 the spectrum has a sharp edge. Exactly 2·#{γ < πN/a} eigenvalues sit near 2a, one per ±γ atom, followed by a drop of 5 to 20 times. The blind m equals 2·#{in-band zeros} or exceeds it by 1 or 2. The excess is an above-band ordinate whose atom is partly captured at the band edge.

**Summary table.** Source: `summary_zeta.csv`. Columns:
* "found" counts MUSIC peaks within 0.5 of a zero;
* errors are in γ;
* w6 is the weight range at the recovered ordinates;
* ESPRIT and Ritz are the maximum errors; their imaginary parts are exactly 0 in every zeta case.

| a | N | band πN/a | zeros in band | m | found p=0 / p=6 | max err p=0 | max err p=6 | median err p=6 | w6 range | ESPRIT err | Ritz err |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 30 | 94.2 | 26 | 48 | 17 / 14 | 0.44 | 0.49 | 0.16 | 0.82 to 1.88 | 0.50 | 0.48 |
| 1 | 100 | 314 | 147 | 188 | 61 / 60 | 0.49 | 0.48 | 0.21 | 0.68 to 2.49 | 0.49 | 0.48 |
| 2 | 30 | 47.1 | 8 | 18 | 8 / 8 | 2.3e-3 | 6.8e-3 | 1.2e-3 | 1.0007 to 1.0084 | 0.34 | 0.06 |
| 2 | 60 | 94.2 | 26 | 54 | 26 / 26 | 7.1e-3 | 1.7e-4 | 8.7e-7 | 1.002 to 1.033 | 0.33 | 0.21 |
| 2 | 100 | 157.1 | 56 | 114 | 56 / 55 | 7.6e-2 | 0.23 | 3.3e-4 | 0.994 to 1.63 | 0.41 | 0.36 |
| 3 | 60 | 62.8 | 14 | 28 | 14 / 14 | 1.5e-3 | 1.1e-4 | 5.8e-6 | 1.0000 to 1.0001 | 0.14 | 0.07 |
| 3 | 100 | 104.7 | 31 | 63 | 31 / 31 | 9.8e-3 | 2.4e-3 | 3.7e-5 | 1.0002 to 1.0024 | 0.27 | 0.22 |
| 4 | 100 | 78.5 | 20 | 40 | 20 / 20 | 9.5e-4 | 2.8e-5 | 1.1e-6 | 1.0000 to 1.0001 | 0.14 | 0.05 |
| 4 | 128 | 100.5 | 29 | 58 | 29 / 29 | 1.8e-3 | 2.6e-5 | 6.6e-7 | 1.0000 to 1.0001 | 0.11 | 0.05 |
| 5 | 160 | 100.5 | 29 | 58 | 29 / 29 | 8.5e-4 | 7.3e-4 | 3.3e-6 | 1.0000 to 1.0016 | 0.08 | 0.02 |
| 6 | 30 | 15.7 | 1 | 2 | 1 / 1 | 2.4e-4 | 9.8e-9 | 9.8e-9 | 1.0000 | 6.6e-3 | 6.5e-3 |
| 6 | 100 | 52.4 | 10 | 20 | 10 / 10 | 1.4e-4 | 1.0e-4 | 4.4e-6 | 1.0000 to 1.0005 | 0.03 | 0.02 |
| 6 | 191 | 100.0 | 29 | 58 | 29 / 29 | 1.5e-3 | 1.6e-4 | 2.5e-6 | 1.0000 to 1.0013 | 0.04 | 0.03 |

**Per-ordinate table** at a fixed band of about 100, with N = ⌈100a/π⌉. It shows MUSIC p = 6 error and weight. Source: `table_band100_music_p6.md`; every row, with raw MUSIC, ESPRIT and Ritz values, is in `recovery_zeta.csv`.

| k | gamma_k (zetazero) | a=2 err / w | a=3 err / w | a=4 err / w | a=5 err / w | a=6 err / w |
|---|---|---|---|---|---|---|
| 1 | 14.134725 | +1.4e-04 / 1.0013 | -6.1e-06 / 1.0002 | +1.4e-07 / 1.0000 | -2.0e-07 / 1.0000 | +5.4e-07 / 1.0000 |
| 2 | 21.022040 | -1.0e-04 / 1.0018 | +9.0e-06 / 1.0001 | +1.3e-09 / 1.0000 | -1.3e-06 / 1.0000 | +3.5e-07 / 1.0000 |
| 3 | 25.010858 | +1.0e-04 / 1.0014 | +3.3e-06 / 1.0001 | -7.7e-08 / 1.0000 | +1.0e-07 / 1.0000 | -2.1e-07 / 1.0000 |
| 4 | 30.424876 | +6.4e-05 / 1.0019 | +1.0e-06 / 1.0001 | -2.2e-07 / 1.0000 | +6.0e-08 / 1.0000 | +6.7e-07 / 1.0000 |
| 5 | 32.935062 | +3.3e-05 / 1.0012 | +4.7e-06 / 1.0002 | -2.1e-07 / 1.0000 | -7.5e-07 / 1.0000 | -5.7e-07 / 1.0000 |
| 6 | 37.586178 | -2.9e-04 / 1.0013 | -1.2e-05 / 1.0001 | -3.8e-07 / 1.0000 | -2.2e-06 / 1.0000 | -1.1e-06 / 1.0000 |
| 7 | 40.918719 | -7.3e-04 / 1.0010 | -1.4e-05 / 1.0001 | -2.3e-07 / 1.0000 | +1.3e-06 / 1.0000 | -4.1e-07 / 1.0000 |
| 8 | 43.327073 | +6.9e-04 / 1.0016 | +2.0e-05 / 1.0001 | -3.1e-07 / 1.0000 | -3.2e-06 / 1.0000 | -1.7e-07 / 1.0000 |
| 9 | 48.005151 | +9.7e-04 / 1.0014 | -1.1e-06 / 1.0001 | -6.6e-07 / 1.0000 | +3.8e-06 / 1.0000 | +1.1e-06 / 1.0000 |
| 10 | 49.773832 | +5.2e-04 / 1.0011 | +3.1e-05 / 1.0001 | -2.8e-08 / 1.0000 | -1.4e-06 / 1.0000 | -1.6e-06 / 1.0000 |
| 11 | 52.970321 | +4.7e-04 / 1.0012 | +2.0e-05 / 1.0001 | -2.2e-07 / 1.0000 | -2.3e-06 / 1.0000 | -2.5e-06 / 1.0000 |
| 12 | 56.446248 | +1.2e-04 / 1.0012 | +1.3e-05 / 1.0001 | +6.7e-07 / 1.0000 | +3.3e-06 / 1.0000 | +2.3e-06 / 1.0000 |
| 13 | 59.347044 | +1.4e-03 / 1.0006 | +6.6e-06 / 1.0001 | -2.3e-07 / 1.0000 | -2.2e-06 / 1.0000 | -2.6e-06 / 1.0000 |
| 14 | 60.831779 | -4.8e-05 / 1.0010 | +4.8e-06 / 1.0001 | -1.1e-06 / 1.0000 | +6.4e-06 / 1.0000 | -2.3e-06 / 1.0000 |
| 15 | 65.112544 | -3.9e-04 / 1.0012 | +7.6e-06 / 1.0002 | +5.2e-07 / 1.0000 | +2.4e-07 / 1.0000 | -3.8e-06 / 1.0000 |
| 16 | 67.079811 | -4.8e-04 / 1.0011 | +1.9e-05 / 1.0002 | -3.6e-07 / 1.0000 | +2.8e-06 / 1.0000 | +2.9e-06 / 1.0000 |
| 17 | 69.546402 | +1.7e-04 / 1.0017 | -4.4e-05 / 1.0002 | -1.3e-06 / 1.0000 | -4.7e-06 / 1.0000 | +1.0e-06 / 1.0000 |
| 18 | 72.067158 | +5.0e-04 / 1.0008 | +6.6e-06 / 1.0001 | -1.8e-06 / 1.0000 | -9.6e-06 / 1.0000 | -5.9e-06 / 1.0000 |
| 19 | 75.704691 | +2.6e-03 / 1.0023 | +4.0e-05 / 1.0003 | +2.2e-06 / 1.0000 | -2.3e-06 / 1.0001 | -4.1e-06 / 1.0000 |
| 20 | 77.144840 | -2.9e-04 / 1.0000 | -4.7e-05 / 1.0003 | +1.6e-06 / 1.0000 | -1.6e-05 / 1.0001 | +8.3e-06 / 1.0001 |
| 21 | 79.337375 | +1.5e-03 / 1.0027 | -1.1e-04 / 1.0004 | -1.7e-06 / 1.0000 | +1.8e-05 / 1.0001 | +2.1e-06 / 1.0001 |
| 22 | 82.910381 | +6.4e-04 / 1.0025 | -2.3e-05 / 1.0002 | +2.7e-06 / 1.0000 | -2.1e-05 / 1.0001 | +8.1e-06 / 1.0001 |
| 23 | 84.735493 | -5.6e-03 / 1.0039 | -1.7e-04 / 1.0005 | -6.3e-07 / 1.0000 | -2.5e-05 / 1.0002 | -4.6e-06 / 1.0001 |
| 24 | 87.425275 | +1.7e-02 / 1.0030 | +1.5e-04 / 1.0007 | -3.6e-06 / 1.0000 | -3.8e-05 / 1.0002 | -1.3e-05 / 1.0001 |
| 25 | 88.809111 | +6.4e-03 / 0.9950 | +9.9e-05 / 1.0009 | -3.1e-06 / 1.0000 | -9.9e-06 / 1.0002 | +2.4e-05 / 1.0001 |
| 26 | 92.491899 | +9.0e-03 / 1.0050 | -3.9e-04 / 1.0010 | +2.3e-06 / 1.0000 | -7.0e-05 / 1.0003 | +7.3e-06 / 1.0002 |
| 27 | 94.651344 | +3.1e-02 / 0.9895 | -9.5e-04 / 1.0010 | -1.1e-05 / 1.0000 | -2.9e-05 / 1.0003 | -4.3e-06 / 1.0001 |
| 28 | 95.870634 | -6.0e-02 / 0.9989 | -1.8e-03 / 1.0019 | +1.4e-05 / 1.0000 | -2.1e-04 / 1.0005 | +8.1e-05 / 1.0002 |
| 29 | 98.831194 | +3.7e-02 / 1.0177 | +3.4e-03 / 1.0077 | -2.6e-05 / 1.0001 | +7.3e-04 / 1.0016 | -1.6e-04 / 1.0013 |

**Reading.**
* **All in-band ordinates are recovered for every a ≥ 2, with no spurious peaks.** For a ≥ 3 the weights are **1 to 4-5 digits**: positive, multiplicity one.
* **Accuracy is limited by out-of-band leakage, not by the primes.**
  * Raw basis: errors of 1e-4 to 1e-3.
  * Taper p = 6: errors of 1e-7 to 1e-5 below the band edge.
  * The last 2 to 3 ordinates under the band edge are always the worst.
* At fixed N, increasing a shrinks the band, about πN/a, but sharpens resolution. The best per-ordinate accuracy is at a = 4 to 6, around 1e-7.
* **ESPRIT and Ritz are much less accurate** than MUSIC, with errors of 1e-2 to 0.4. They are biased by the same leakage, which they cannot down-weight. Their values for zeta are always **exactly real**.
* **NNLS** (`nnls_zeta.csv`, N = 30) returns each in-band ordinate as a single atom. Weights are 0.92 to 1.002 and errors 2e-4 to 1.5e-2. It adds a comb of tiny weights, about 1e-3, spaced π/a apart, which models the out-of-band tail. It also puts one large atom at the grid end, which absorbs everything above the band.

**a = 1, double precision versus 40 digits.** At a = 1 the prime side uses only n = 2, 3, 4, 5, 7. In double precision recovery fails beyond the first few ordinates, because the needed eigenvalues are below 1e-14. With 40-digit eigenvectors, MUSIC at N = 30 with m = 52 = 2·26 in-band atoms gives the following (`mp_precision.txt`):

| γ_k | 14.134725 | 21.022040 | 25.010858 | 30.424876 | 32.935062 | 37.586178 | 40.918719 | 43.327073 | 48.005151 | 49.773832 | 52.970321 | 56.446248 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| error | 8.4e-9 | 1.6e-8 | 3.0e-8 | 4.2e-7 | 9.9e-7 | 4.5e-6 | 3.8e-5 | 8.2e-5 | 1.0e-3 | 2.8e-3 | 3.8e-3 | 1.5e-2 |

Above about 59 the errors exceed 0.1. This matches the heuristic: Rayleigh-free up to T_R = 46, which is 8 zeros, then super-resolution limited by precision up to about 56, short of the information limit T_I = 126. With m = 44 or 48 the recovery is much worse, so the a = 1 result depends on choosing m correctly. m was not chosen blind here.

## 6. Controls

### What the controls are, exactly (worked out before running them)

* **Character perturbation, c(n) = Λ(n)(1 + εχ(n)), with χ = χ_{-4} or χ_{-3}.** Both are odd, so κ = 3/4. The archimedean and pole terms are left as for zeta, as the prompt specifies. The explicit formula for L(s,χ) gives
  W_ε(g) = Σ_{γ_ζ} ĝ(γ_ζ) + ε Σ_{γ_χ} ĝ(γ_χ) - ε (1/2π) ∫ ĝ(r) m_χ(r) dr,  with m_χ(r) = log(q/π) + Re ψ(3/4 + ir/2).
  Under GRH, the "fake" spectral measure is therefore made of three parts:
  * unit atoms at the zeta ordinates;
  * atoms of weight ε at the L(χ) ordinates;
  * a **continuous** density -ε m_χ(r)/2π.

  The continuous density is negative for large r, since m_χ grows like log(qr/2π), and positive for small r, since m_χ(0) = log(q/π) + ψ(3/4) < 0. Averaged over windows wider than the zero spacing, the ε-atoms cancel the continuous part, because the L(χ) zero density is also (1/2π) log(qr/2π). The negativity is therefore only visible to test functions that resolve the gaps between ordinates.
  * For ε < 0 the L(χ) atoms carry **negative weights**.
  * For ε > 0 the failure lives entirely in the **continuous negative part**. No complex frequencies are predicted in either case.
* **Davenport-Heilbronn**, f = Σ a(n) n^{-s} with a(n) = Re χ(n) + κ_DH Im χ(n) for χ mod 5 with χ(2) = i, and κ_DH = (√(10-2√5) - 2)/(√5 - 1). The coefficients are real. The completed function (π/5)^{-(s+1)/2} Γ((s+1)/2) f(s) is invariant under s → 1-s. The prime side uses the Dirichlet coefficients b(n) of -f'/f, obtained by Dirichlet-series division. They are not multiplicative or prime-supported, and they grow in n. Parameters are P = 0, q = 5, κ = 3/4. Check: Σ b(n) n^{-3} = -f'(3)/f(3) to 8e-14.

  Off-line zeros come in quadruples ρ, 1-ρ̄ and their conjugates. Each gives the atom pair u(γ)u(γ)ᵀ + conj, with γ = t - iδ, δ = Re ρ - 1/2. That pair equals 2(xxᵀ - yyᵀ) with u = x + iy, an indefinite rank-2 term whose negative part is of relative size about (δa)². The first off-line zero is ρ = 0.808517 + 85.699348i, so δ = 0.3085, refined here with mpmath.findroot. The second is 0.650830 + 114.163343i.

  **Prediction:** a visible failure, either a complex frequency or a negative eigen-direction, should appear exactly when the band πN/a contains 85.70 and a is large enough that (0.31a)² beats the positive leakage from neighbours.

### Results

The table uses N = ⌈100a/π⌉, so the band is about 100 at every a. Each cell shows the minimum eigenvalue of G, then the number of negative eigenvalues below -1e-8·‖G‖ in parentheses, then in brackets the number of negative MUSIC/LS weights and the number of complex Ritz pairs. Full grid, which also includes N = 60 and χ_{-3}: `controls.csv`.

| form | a=1 | a=2 | a=3 | a=4 | a=5 | a=6 |
|---|---|---|---|---|---|---|
| zeta | -1.8e-15 (0) [0/0] | -1.6e-14 (0) [0/0] | -7.4e-14 (0) [0/0] | -1.7e-13 (0) [0/0] | -3.3e-13 (0) [0/0] | -4.1e-13 (0) [0/0] |
| χ_{-4}, ε=+0.05 | -0.052 (6) [0/0] | -0.12 (33) [0/0] | -0.19 (69) [0/0] | -0.20 (113) [0/0] | -0.21 (171) [0/0] | -0.21 (228) [0/0] |
| χ_{-4}, ε=-0.05 | -0.052 (6) [0/0] | -0.15 (36) [0/0] | -0.25 (63) [0/0] | -0.36 (84) [0/0] | -0.47 (91) [0/0] | -0.56 (98) [0/0] |
| χ_{-4}, ε=+0.30 | -0.32 (6) [0/0] | -0.78 (33) [0/0] | -1.1 (70) [0/0] | -1.2 (119) [0/0] | -1.2 (173) [0/0] | -1.2 (229) [0/0] |
| χ_{-4}, ε=-0.30 | -0.32 (7) [0/0] | -0.93 (38) [0/0] | -1.5 (65) [1/0] | -2.2 (85) [1/0] | -2.8 (92) [6/4] | -3.4 (98) [5/6] |
| χ_{-3}, ε=+0.05 | -0.042 (3) [0/0] | -0.11 (30) [0/0] | -0.17 (70) [0/0] | -0.19 (119) [0/0] | -0.19 (175) [0/0] | -0.19 (230) [0/0] |
| χ_{-3}, ε=-0.30 | -0.28 (9) [0/0] | -0.91 (40) [0/4] | -1.6 (64) [1/2] | -2.1 (79) [1/6] | -2.8 (89) [3/0] | -3.4 (92) [9/0] |
| Davenport-Heilbronn | +3.5e-5 (0) [0/0] | -0.73 (2) [0/0] | -3.6 (2) [0/2] | -11 (2) [0/2] | -25 (2) [0/2] | -53 (2) [0/2] |

**Character perturbation: the failure is immediate and first-order.**
* PSD fails at **every** a and every ε tested. The minimum eigenvalue is about -ε·c, with c ≈ 1 at a = 1 and c ≈ 3.5 (ε > 0) or 11 (ε < 0) at a = 6.
* The failure is linear in ε **down to ε = 1e-12**, where it reaches the double-precision floor (`supplement.txt` (i)):

  | a | N | min eig / ε for ε = 1e-12 / 1e-9 / 1e-6 / 1e-3 |
  |---|---|---|
  | 1 | 30 | -0.59 / -0.60 / -0.95 / -1.03 |
  | 3 | 60 | -3.3 / -3.4 / -3.4 / -3.4 |
  | 6 | 100 | -3.6 / -3.5 / -3.5 / -3.5 |

* The reason is that zeta's G has a large near-null space, with eigenvalues of 1e-29 or below at a = 1. These are test functions whose transform nearly vanishes at every ordinate in reach. The perturbation is an indefinite form of size ε and is not orthogonal to that space. So at fixed (a, N), positivity holds only for the exact Λ: at a = 1 it pins log 3, log 5 and log 7 to about the size of the smallest eigenvalue.
* **This is a rigidity statement about a single matrix, not a robustness margin.**

**How the failure shows in the spectral recovery.**
* **Small ε (0.05, 0.1).** The dominant subspace still contains only the zeta atoms. MUSIC returns the zeta ordinates with unit weights, so the failure is invisible to peak-finding and visible only as dozens of negative eigenvalues in the sub-threshold directions.
* **Oracle fit** (`controls_oracle_weights.csv`). Atoms are placed at the known zeta and L(χ) ordinates below 97 in the tapered subspace. At a = 6:
  * the weights at L(χ) ordinates are about 0.8ε: +0.040 to +0.044 for ε = +0.05, and -0.23 to -0.25 for ε = -0.3;
  * the zeta weights average within 1% to 7% of 1, though individual zeta weights next to a colliding L(χ) ordinate deviate much more;
  * the residual has a most-negative eigenvalue between -0.19 and -2.5.

  This is the predicted -ε × (continuous archimedean density). The shrinkage of ε to 0.8ε is that continuous part being partly absorbed into the atoms.
* **ε = -0.3, a ≥ 3.** MUSIC finds peaks at L(χ) ordinates with **negative** least-squares weights, up to 9 of them.
* **Complex Ritz/ESPRIT pairs** appear only at ε = -0.3 (`controls_complex_frequencies.txt`). Examples are 79.31 ± 0.054i and 95.73 ± 0.088i for χ_{-4} at a = 6, and 43.44 ± 0.19i for χ_{-3} at a = 3. Each sits where a **positive zeta atom and a negative χ atom fall within about π/a of each other**: for example ζ 79.337 against χ_{-4} 78.81 and 80.21. An indefinite pencil with colliding opposite-sign atoms produces complex Ritz values. These are **artifacts of the collision, not zeros off the line**: the character control has none.

**Davenport-Heilbronn: the failure appears exactly where predicted.**
* **a = 1, band 100 or 188.** The form stays PSD, with minimum eigenvalue +3.5e-5. The predicted negative part, about -0.13 for an isolated pair, is masked by positive neighbours within the resolution π.
* **a ≥ 3 with N = 60.** The band (63, 47, 38 or 31) is below 85.70, and the form is **PSD to roundoff**, about -1e-13. The off-line zero is invisible, as predicted.
* **Band 100 contains 85.70.** There are **exactly two negative eigenvalues** for a ≥ 2, one per off-line quadruple-half (±t). Their size tracks the rank-2 prediction -2(sinh(2δa)/(2δ) - a) with δ = 0.308517:

  | a | observed eigenvalues | predicted |
  |---|---|---|
  | 2 | -0.73, -0.68 | -1.10 |
  | 3 | -3.64, -3.57 | -4.06 |
  | 4 | -10.55, -10.48 | -10.99 |
  | 5 | -24.66, -24.55 | -25.37 |
  | 6 | -53.1, -52.5 | -53.7 |

  This is `supplement.txt` (iii); the remaining gap is overlap with positive neighbours.
* **Complex Ritz and ESPRIT pairs.** For a ≥ 3 both methods give a complex pair at the off-line ordinate. The true value is 85.6993 ∓ 0.3085i.

  | a | Ritz | ESPRIT |
  |---|---|---|
  | 3 | 85.671 ± 0.223i | 85.608 ± 0.195i |
  | 4 | 85.710 ± 0.351i | 85.710 ± 0.323i |
  | 5 | 85.671 ± 0.319i | 85.683 ± 0.321i |
  | 6 | 85.694 ± 0.298i | 85.689 ± 0.306i |

  At a = 2 G is indefinite but the pair is not yet resolved as complex.
* MUSIC peaks for DH land on DH's **on-line** ordinates, which are 5.094, 8.940, 12.134 and so on (`control_lfunction_zeros.txt`), with positive weights.
* **The control fails visibly, at the predicted place and with the predicted size**, and the experiment is informative in the sense the prompt asked for.

## 7. Structure: residual, Hilbert-Polya compression, Jacobi coefficients

**Residual (tail) spectrum** (`residual_spectrum.csv`). This is R = G - Σ_{in-band γ} [u uᵀ + J u uᵀ J] with unit weights.
* R is PSD to -2.6e-13.
* R equals the sum over zeros above the band plus the density tail, to a relative Frobenius error between 7e-7 and 2.1e-6.
* Its eigenvalues decay faster than geometrically. For a = 3, N = 60 they are 0.963, 0.251, 0.065, 0.014, 3.0e-3, 4.8e-4, 7.0e-5, 7.9e-6, 9.3e-7 and 1.0e-7.
* The top 8 residual eigenvectors capture 100.0% (to 3 digits) of each of the first 8 above-band atoms.

So the "tail of the sum of squares" is a smooth, effectively low-rank object concentrated on the band-edge modes j ≈ ±N. It is the sinc leakage of the next few ordinates and is structurally uninteresting. If MUSIC's estimated ordinates are subtracted instead of the true ones, the residual is no longer PSD, with minimum eigenvalues of -7e-4 at a = 3 and -3.7e-3 at a = 6. That negativity is caused by the ordinate errors.

**Hilbert-Polya in finite dimension.** The natural self-adjoint object is the **Ritz pencil (K, G)**: Rayleigh-Ritz for "multiplication by γ" on L²(Σ_γ δ_γ), compressed to the type-a trial space. On the signal subspace, S = G_s^{-1/2} K_s G_s^{-1/2} is a real symmetric matrix computed **from primes only**, and its eigenvalues approximate ±γ. Accuracy is limited by the trial space; MUSIC is much better.

| a | N | max abs(Ritz value - true γ) |
|---|---|---|
| 6 | 100 | 2.0e-2, all 10 in-band ordinates |
| 3 | 60 | 6.6e-2, 14 ordinates |
| 4 | 128 | 5.2e-2, 29 ordinates |

In this basis K is not an independent operator. It is W applied to i g'_jk, which is the compression of i d/dx, whose eigenfunctions are the Fourier modes with frequencies -πj/a, plus the rank-one boundary correction from the jumps of φ_j at ±a. That correction is exactly the Cauchy displacement identity (γI + Ω) D u(γ) = s(γ)·1. **The self-adjointness is the positivity of G and nothing more.** S is symmetric because G_s is positive definite. When G is indefinite, as for DH, the same construction gives the complex pair at 85.7 ± 0.3i. This is the finite-dimensional version of the standard observation that a Hilbert-Polya operator built from the explicit formula is self-adjoint iff the Weil form is positive, so it carries no independent information.

**Jacobi coefficients.**
* *Lanczos on G from φ_0* (`jacobi_coefficients.csv`). α_k lies in [0, 2a] and β_k is irregular.
  * For a ≥ 3 the iteration breaks down (β ≈ 1e-4 to 1e-6) after about as many steps as there are even-symmetric signal directions, about 14 to 19. At a = 2, N = 100 there is no breakdown within 40 steps, since the signal dimension is 114.
  * Later entries are roundoff-driven and meaningless.
  * These coefficients encode the spectrum of G, which clusters at about 2a and about 0. They carry **no ordinate information**, which lives in the eigenvectors.
* *Lanczos on the Ritz operator S from φ_0* (`supplement.txt` (ii)). This is the Jacobi matrix of the measure Σ |u_0(γ)|² δ_γ seen through the signal subspace.
  * α_k = 0 to 1e-12, as expected for a symmetric measure.
  * β_k **alternates**. At a = 6, N = 100 it runs 33.8, 20.3, 33.4, 14.3, 36.7, 13.8, 32.6, 16.0 and so on. At a = 4, N = 128 it runs 54.5, 44.7, 55.6, 46.2, 54.5, 39.8 and so on.
  * This is the generic asymptotics of a symmetric measure on two intervals [-B, -A] ∪ [A, B], where β alternates between about (B+A)/2 and (B-A)/2. For A = 14.13 (the first ordinate) and B = the band edge, that predicts 32 and 17.8 at a = 6, and 56.5 and 42.3 at a = 4, which is what is seen.
  * **The regularity is the gap below γ_1 plus the band edge. Nothing arithmetic shows up.**

## 8. Verdict

1. The experiment works as designed. From the prime side alone (n ≤ e^{2a}), G is a positive sum of unit-weight atoms at the zeta ordinates. Every ordinate below the band πN/a is recovered with weight 1 and with no complex frequencies, for every a ≥ 2. Accuracy reaches 1e-7 in double precision with tapering, and 8e-9 at a = 1 from **only 2, 3, 4, 5 and 7** with 40-digit arithmetic. The resolution limits match the band, Rayleigh and Slepian heuristics of §4.
2. **The controls fail visibly.**
   * Λ(1 + εχ) breaks PSD at first order for every a and every ε down to 1e-12.
   * With ε < 0, L(χ) atoms get negative weights.
   * Davenport-Heilbronn shows exactly two negative eigenvalues of the predicted size, and a complex pair at its off-line zero 85.70 ± 0.31i, exactly when the band contains it and a ≥ 3.
3. **Nothing beyond the known identity appeared.**
   * The Gram matrix is a sum of rank-one atoms only because of the explicit formula. Recovering the atoms is a numerically clean way of computing zeros from primes, already well known in spirit; it is not new information.
   * The residual is the sinc tail of the next ordinates.
   * The finite Hilbert-Polya matrix is self-adjoint exactly because G is positive definite.
   * The Jacobi regularity is two-interval asymptotics.
   * The one quantitatively striking feature, first-order rigidity of PSD under any perturbation of Λ, is a property of the near-null space of a finite Gram matrix. It does not give a robustness margin that could be pushed to an argument.
4. Detecting a hypothetical off-line zeta zero at height T this way needs a band above T, so N ≳ aT/π, and enough a that (δa)² beats neighbour leakage. That makes it a zero-location computation, strictly weaker than standard verification of RH to height T.

**Nothing here is progress on RH; conjecture1_proved = False.**

## 9. Caveats

* Nothing is certified. All values are floating point or mpmath at 40 digits, with no interval arithmetic, and zeros come from mpmath's Riemann-Siegel.
* Below 1e-40 the 40-digit computation cannot certify PSD; this happens at a = 3, N = 20.
* PSD statements in double precision are "minimum eigenvalue at least -4e-13".
* The blind signal dimension (|eigenvalue| > 0.4a) is a heuristic. It fails at a = 1, where the in-band atoms are not resolved in double precision.
* The archimedean term was validated in two forms that agree to 2e-13, and through the explicit formula to 1e-20. Reconciling conventions with `../weil_form.py`, written by another agent, is left to the parent.

## Files

* `weil_prony.py`: everything. `python weil_prony.py run zeros_1e4.npy` runs the full pipeline, about 6 minutes on the loaded machine. `python weil_prony.py supp` runs the supplements.
* `zeros_rs.py`, `rerefine_zeros.py`, `zeros_1e4.npy`, `zeros_1e4_indexcheck.txt`: the zero list.
* `validation.txt`, `summary_zeta.csv`, `recovery_zeta.csv`, `table_band100_music_p6.md`, `nnls_zeta.csv`, `mp_precision.txt`.
* `controls.csv`, `controls_oracle_weights.csv`, `controls_complex_frequencies.txt`, `control_lfunction_zeros.txt`.
* `residual_spectrum.csv`, `jacobi_coefficients.csv`, `supplement.txt`, `run_log.txt`.
