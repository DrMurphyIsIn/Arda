# kappa-certify lens -- working notes (2026-09-23)

conjecture1_proved = False. Nothing here proves RH.

## 0. Conventions (Zhu arXiv:2608.24827 convention; a = half-width of supp f)
- f real, supp f in [-a,a]; F(t) = int f(u) e^{itu} du; x = e^{2a} (only n < x = e^{2a} enter).
- Q(f) = Pole(f) + (1/2pi) int_R |F(t)|^2 Psi_a(t) dt,
  Psi_a(t) = Re psi(1/4 + it/2) - log pi - sum_{log n < 2a} 2 Lambda(n) n^{-1/2} cos(t log n).
- Pole(f) = 2 F(i/2) F(-i/2): even f -> +2 F(i/2)^2 ; odd f -> -2 (int f sinh(u/2))^2 (NSD).
- Q(f) = Q(f_even) + Q(f_odd), Q(u + iv) = Q(u) + Q(v): kappa = 0 iff both real parity sectors PSD.
- Legendre basis phi_n(u) = sqrt((2n+1)/(2a)) P_n(u/a); F_n(z) = i^n c_n j_n(a z), c_n = sqrt(2a(2n+1)).
  F_n(i/2) = (-1)^n c_n i_n(a/2), F_n(-i/2) = c_n i_n(a/2)  (i_n = modified spherical Bessel).
- Envelope (own derivation, Binet's 2nd formula): Re psi(1/4+it/2) - log pi >= log(t/2pi) - 1/(2t^2) - 1/(3t)
  >= log(t/2pi) - 1/t for t >= 3/4. [|s^2+z^2| >= |Im z^2| = t/4, int_0^inf s/(e^{2pi s}-1) = 1/24.]
- Zhu one-stroke: for T# with beta* = log(T#/2pi) - 1/T# - A_L > 0 (A_L = sum 2Lambda(n)/sqrt n),
  Q(f) >= R(f) = Pole(f) + (1/pi) int_0^{T#} (Psi_a - beta*) |F|^2 dt + beta* ||f||^2.

## 1. Validation of my independent implementation against Zhu (a = 0.8)
- lam_min(R_150, even) = 1.3564e-18  (Zhu reference spectrum of R_150: 1.356e-18)  MATCH
- lam_min(R_200, even) = 1.0277e-17  (Zhu certified lambda_0 = 9e-18 for R_200, "1e-19 to spare") CONSISTENT
- lam_min(R_200, odd)  = 1.1411e-14  (Zhu: 8.206e-15 <= lambda_1^odd(Q) <= 2.347e-14) CONSISTENT

## 2. Exploration a = 0.97 (x = e^{1.94} = 6.96; prime powers 2,3,4,5; A_L = 4.38150, T_1 = 502.6)
- T# = 560, beta* = 0.106775; lam_min(R, even) = 7.1551e-28, lam_min(R, odd) = 1.7245e-24 (stable N=300 vs 370)
- Bessel j_n(x) by backward recurrence in ball arithmetic loses ~0.9 x bits (wrapping) -> working prec base + x + 96.
- Arb bessel_j at large order near turning point needs prec ~ 2.5 x bits (adaptive).

## 3. Explicit-formula normalization cross-check (COMPUTED, mpmath dps 30)
f(u) = (1-(u/a)^2)^3 on [-a,a], a = 249/256.  Arithmetic side Q(f) = 2F(i/2)^2 + (1/pi) int_0^inf Psi_a F^2
= 2.05537479369649e-7 ; zero side 2 sum_{k<=2000} F(gamma_k)^2 + smooth tail = 2.05537479402218e-7.
Agreement 3e-17 absolute (= quad accuracy on the cancelling pole/integral pair 1.6237 vs -1.6237).  So Q is the
Weil form sum_rho F(gamma)conj F(conj gamma) with the right constants.

## 4. Rigorous certificate machinery (certify.py, run_cert.py, vldlt.py)
- [C1] leading block of R: composite GL (near panels [0,8] width 0.5, 48 nodes; far width 2, 48 nodes), dyadic
  x-nodes, Bessel j_n by backward recurrence from Arb J_{n+1/2} (adaptive precision) at working prec base+x+96.
- [C2] per-panel Bernstein ellipse bound (64/15) h M rho^{-2n}/(rho^2-1); psi on ellipse bounded ANALYTICALLY
  (shift k, Binet: |psi(u) - log u + 1/(2u)| <= 1/(12 (Re u)^2) for Re u > 0; |s^2+u^2| >= (Re u)^2).
  (Arb's acb digamma returns NaN on wide balls -- do not use ball covers.)
- [C3] node perturbation via Cauchy |f'| <= M/dist.
- [C4] tails: |j_n(x)| <= x^n/(2n+1)!!, |j_n| <= 1, |i_n(y)| <= y^n cosh y/(2n+1)!!; Schur test + Gershgorin.
- [C5] verified LDL^T (Rump/Zhu L5.2): floating LDL^T on exact dyadic midpoints, rigorous residual
  E = (M - lam0 I) - L D L^T in Arb; D > 0 => lam_min(G) >= lam0 - ||E||_F for all G in the box.
  (Plain interval LDL^T blows up by ~8x per pivot -> fails beyond ~80 pivots; do NOT use.)
- Reproduction of Zhu (a = 0.8, T# = 200, N = 200): lam_min(Q_even) >= 1.02e-17 (Zhu 8.9e-18), odd >= 1.1e-14.
  Certifier sharp: succeeds at lam0 = 1.020e-17, fails at 1.030e-17 (true lam_min(R_200) = 1.02769e-17).

## 5. FINDING: Zhu's reduction R can be INDEFINITE in the odd sector when T# is only just above T_1
a = 249/256, T# = 560 (beta* = 0.107): R_odd has exactly one negative eigenvalue in (-1e-14, -1e-18)
(floating LDL^T inertia count; stable).  Q_odd itself is PD (Galerkin upper bound ~1e-24 region; R <= Q).
Mechanism: Q - R = (1/pi) int_{T#}^inf (Psi_a - b*)|F|^2 ~ 2 f(a)^2/(pi T#) for f with boundary values
(|F| ~ 2|f(a)|/t); the odd pole term -2 s^2 needs the high-frequency archimedean growth that R discards.
Fix: raise T#: at T# = 800 R_odd is PD with lam_min in (1e-24, 1e-22).
Lesson for any one-stroke certificate: beta* > 0 is necessary, not sufficient; each sector must be checked.

## 6. Rigorous closed-form Galerkin matrices of the UNTRUNCATED Q_x (galerkin_cos.py)
W(u) = sum_j 2 e^{-beta_j u}; S, Cc, Cu, CL via Im/Re psi((beta0 + i m w)/2), Re psi'(.), + geometric tails.
No quadrature at all.  Agrees with wpw.py (mpmath GL) to 1e-44 at x = 9, 20, 40 (zeta and D, both sectors),
rigorous radii ~1e-57.  Gives: certified Rayleigh quotients of Q (upper bounds, negative directions).

## 7. MAIN CERTIFICATE (a = 249/256 = 0.97265625, x = e^{2a} = 6.99582, prime powers 2,3,4,5)
- even sector: T# = 560 (b* = 0.106775), N = 450 Legendre modes (orders 0..898):
  lam_est(R) = 4.48421e-28; verified LDL^T of M - 4.395e-28 I: D > 0, ||E||_F = 1.28e-64;
  eta (quadrature+node) = 1.7e-45; eps_B = 5.0e-75; eps_D = 1.1e-155  =>  lam_min(Q_even) >= 4.395e-28.
- odd sector: T# = 800 (b* = 0.463986), N = 620 (orders 1..1239):
  lam_est(R) = 1.28619e-24; verified at 1.260e-24, ||E||_F = 3.1e-66; eta 3.3e-45; eps_B 9.2e-85
  =>  lam_min(Q_odd) >= 1.26e-24.   (T# = 560 FAILS in the odd sector: R_odd indefinite, see section 5.)
- => for all f in L^2[-a,a] (complex):  Q(f) >= 4.39e-28 ||f||^2, i.e. kappa_zeta(e^{249/128}) = 0.
  (Zhu: [-0.8,0.8] with 8.9e-18.)  Wall time ~3 min total on 1 core.

## 8. Certified zeta-vs-D separation on one explicit test space (x = 40, cos/sin modes k <= 60 on [-L/2,L/2])
- D even: certified Rayleigh quotient c^T Q_D c/c^T c = -2.5877383e-4 (radius 3e-12)   => kappa_D(40) >= 1
- D odd : certified -1.0854653e-3                                                      => kappa_D(40) >= 2
- zeta even: Galerkin Q_zeta PD, verified LDL^T at 9.58e-110 (prec 1024, resid 4e-293); lam_min ~ 1.0645e-109
- zeta odd : PD, verified at 7.85e-106; lam_min ~ 8.72e-106
- Rayleigh-Ritz => certified UPPER bound lam*_zeta(40) <= ~1.07e-109 (Galerkin not converged in N: N=24 5e-61,
  N=40 <1e-76, N=60 1e-109; Zhu-law estimate ~1e-198).

## 9. NEGATIVE CONTROL: the same certificate for Davenport-Heilbronn at the same window (a = 249/256)
(D: Gamma((1+s)/2), conductor 5, no pole; A_L^D = sum 2|Lambda_D(n)|/sqrt n over n = 2,3,4,6 = 3.6621; Lambda_D(5)=0.
 D envelope: Re psi(3/4+it/2) + log(5/pi) >= log(5t/2pi) - 1/t for t >= 27/16 (Binet, |Im z^2| = 3t/4).)
- T# = 200 (b* = 1.4028), N = 140: lam_min(Q_D,even) >= 7.2530e-5 ; lam_min(Q_D,odd) >= 2.1628e-2.
=> kappa_D(e^{249/128}) = 0 CERTIFIED TOO, with a margin 1.6e23 times LARGER than zeta's.
Reading (zero side): margin = min over PW_a of sum_gamma |F(gamma)|^2; PW_a has ~2aT*/pi = 27 degrees of freedom
on [-T*,T*], T* = 2 pi x ~ 44.  zeta has 16 zeros there (sparse -> F can vanish on all -> tiny margin);
D (conductor 5) has ~36 (dense -> cannot vanish on all -> big margin).  The certificate is FE-generic at this
scale: it cannot see the Euler product.  D's first detectable off-line pair (0.8085 + 85.699i) needs x ~ 31.

## 10. KERNEL CHECK (Lean 4, Mathlib via li_positivity island, `lake env lean`, no build)
File: lean/KappaWindowCore.lean (35 kB, generated by emit_lean_core.py from schur_core_k8.json).
- Schur complement core: M - lam0 I = [[A,B],[B^T,C]] (even, a=249/256, T#=560, N=450, lam0 = 4.39e-28,
  A = first 8 modes).  Arb: C - lam0 I >= 1e-40 I (verified LDL^T, resid 2.9e-72); S = A - B C^{-1} B^T via
  arb_mat.solve, radius 4.3e-72; rounded to /10^48 (w0 = 2e-48 + rad).  lam_min(S) ~ 6.31e-30, delta = 3.155e-30.
- Kernel theorem core_posdef: every G with |G_ij - Sq_ij| <= w0 is positive definite.  Load-bearing: EXACT
  rational congruence Sq - delta I = L D L^T (324-digit rationals) closed by `ring`; generic Cauchy-Schwarz box
  lemma.  Axioms: [propext, Classical.choice, Quot.sound]; no sorry/native_decide.  ~22 s elaboration.
- Negative controls (kernel REJECTS): D_3 numerator +1 (1 part in 10^300); one S entry +7e-48; delta x3.
  All give `unsolved goals` at the ring step and sorryAx in the axiom list.

## 11. What does kappa_zeta(x) = 0 bound?  (analysis)
(a) Direction.  Kernel: kappa(x) <= #off-line pairs (weil_negIndex_le_offline).  So kappa = 0 is the TRIVIAL lower
    bound on #off-line pairs: a certified kappa(x) = 0 bounds nothing about zeros from above.  The only
    zero-theoretic converse is the detection lemma (paper, unrefereed): a simple off-line zero with horizon
    X(rho) ~ gamma/4 + (1/pi) log 1/|zeta'(rho)| + O(logs) <= x forces kappa(x) >= 1.  At certified x <= 8 the
    horizon covers gamma <~ 30: vacuous (first zero 14.13; zeros verified on the line to 3e12).
(b) Precise content (Krein / Krein-Langer): kappa(x) = min number of non-real pairs in any "fake zero
    configuration" (positive measure on R + pairs) whose Fourier transform matches the Weil distribution on
    (-log x, log x).  kappa(x) = 0 <=> the explicit-formula data up to x (primes <= x, Gamma_R, pole) is consistent
    with ALL zeros on the line.  It is a statement about n <= x, not about zeros.
(c) Why small windows are blind (new elementary identity): for F in PW_a (f in L^2(-a,a)) and any real delta,
       int_R F(t - i delta) conj F(t + i delta) dt = int_R |F(t)|^2 dt
    (Plancherel for f e^{+delta u} vs f e^{-delta u}: the weights cancel).  So a UNIFORM density of off-line pairs
    t +- i delta contributes to Q exactly like on-line zeros of the same density; only density FLUCTUATIONS at the
    resolution 2 pi/log x can create a negative direction.  Window positivity is an averaged statement at
    resolution ~1/a; an off-line pair must be individually resolved (Nyquist spacing 2pi/log x vs zero spacing
    2pi/log(t/2pi) => x ~ t/2pi scale, consistent with the linear detection horizon).
(d) Euler-product blindness at certifiable scales: D passes the SAME window certificate with a 1.6e23x larger
    margin (section 9).  Separation (zeta PD, D indefinite) appears only at x ~ 31 (D's pair at 85.699), where the
    zeta margin is ~1e-109 (Galerkin) -- far beyond any full kappa certificate (doubly exponential T#).
(e) What IS new and explicit: an unconditional certified inequality valid for ALL f in L^2(-a,a), a = 0.9727:
       sum_{n<=6} 2 Lambda(n) n^{-1/2} Re int f(v + log n) conj f(v) dv
          <= 2 F(i/2)F(-i/2) + (1/2pi) int |F|^2 (Re psi(1/4+it/2) - log pi) dt - 4.39e-28 ||f||^2
    (primes 2,3,4,5 bounded by the archimedean place + pole, with a certified margin).  Zero-free content: none.

## 12. SECOND CERTIFICATE (brute-force Zhu reduction) a = 133/128 = 1.0390625, x = e^{2a} = 7.9906, prime powers 2,3,4,5,7
- T# = 2300 (b* = 0.049884), N = 1720 per sector (orders to 3439/3440), 55776 nodes, 256 bits, ~30 min/sector.
- even: lam_est(R) = 3.93001e-33; verified LDL^T at 3.851e-33, ||E||_F = 1.54e-33 (large: cond ~1e33 at 256 bits)
  quad 3.2e-44, eps_B 5.8e-84, eps_D 6.8e-175  =>  lam_min(Q_even) >= 2.3075e-33.
- odd : lam_est(R) = 1.17131e-29; verified at 1.148e-29, resid 1.6e-33  =>  lam_min(Q_odd) >= 1.1478e-29.
=> for all f in L^2[-133/128, 133/128]:  Q(f) >= 2.30e-33 ||f||^2  (kappa_zeta(7.99) = 0).
- two-sided at a = 249/256: lam*_even in [4.395e-28, 7.465e-28], lam*_odd in [1.26e-24, 1.679e-24]
  (upper = certified Rayleigh quotients of the untruncated Q, closed-form cos/sin Galerkin N = 200).

## 13. NEW METHOD: window-aware two-stroke reduction (certify_wa.py) -- halves the exponent of Zhu's barrier
Zhu Thm 1.4: any ONE-STROKE POINTWISE-envelope certificate needs T# > T_1 = 2 pi e^{A_L}, A_L = sum 2Lambda(n)/sqrt n
(sup of the comb, attained by Kronecker alignment).  The window never sees the pointwise sup: <P g,g> for g in
L^2(-a',a') is bounded by the OPERATOR norm of the compressed comb.
LEMMA A (paper proof, 5 lines).  S_tau (compressed translation) on L^2(-a',a'): the orbits u0 + j tau (u0 in
[-a',-a'+tau)) have <= M = floor(2a'/tau)+1 points; L^2 = direct integral of l^2(orbit); S_tau + S_tau^* acts as the
path-graph adjacency => ||S_tau + S_tau^*|| <= 2cos(pi/(M+1)).  Hence ||P_{a'}|| <= A'(a') = sum_n |c_n| cos(pi/(M_n+1)).
  For n > e^{a'} (= sqrt x'), M_n = 2 -> factor 1/2.  Asymptotically A' ~ A_L/2, so T' = 2 pi e^{A'} ~ sqrt(2 pi T_1).
LEMMA B (localization, paper proof).  h = 1 - k, k = erf-bump (plateau Tk, width w); g = FT^{-1}(hF) = f - kcheck*f,
  kcheck(s) = sin(Tk s) e^{-w^2 s^2/4}/(pi s); ||g 1_{|u|>a+eps}|| <= eta ||f||, eta^2 = 2a (2/(pi^2 eps^2)) e^{-w^2eps^2/2}/(w^2 eps).
  (1/pi) int h^2 p |F|^2 = <P_R g, g> <= A'(a+eps) (1/pi) int h^2 |F|^2 + A_L (2 eta + eta^2) ||f||^2.
REDUCTION.  Q >= R'' = Pole + (1/pi) int_0^{Tmax} chi (Phi - p - b')|F|^2 + b''||f||^2,  chi = 1 - h^2,
  b' = log(q Tc/2pi) - 1/Tc - A' (> 0 needs Tc > T' = 2pi e^{A'}),  b'' = b' - err - deficit - xi (all explicit).
Thresholds (T_1 Zhu vs T' window-aware):  a=0.9727: 502 vs 99 | a=1.039: 2187 vs 206 | a=1.098: 3571 vs 322 |
  a=1.2 (x=11): 31535 vs 957.
VALIDATION a = 249/256 even: Tc = 121 (< T_1 = 503!), w = 50, Tmax = 971, N = 740:  R'' PD, lam_min 4.039e-28
  (Zhu R_560: 4.484e-28; lam* <= 7.465e-28).  CERTIFIED lam_min(Q_even) >= 3.958e-28 via the new reduction.
  odd sector at Tc = 121: R'' NOT PD (lam_min in [-1e-23, 0)) -- same phenomenon as Zhu R_560 odd.
  => the binding constraint is the LOSS (1/pi) int h^2 (Phi - A' - b')|F_0|^2 ~ f0(a)^2/T for the ground state
     (boundary jump of the eigenfunction), NOT the Kronecker sup.  Even ground states have tiny boundary values;
     odd ones larger -> odd sector needs a larger effective cutoff.
Numerical LDL^T fix: blocked panel via explicit inverse L_JJ^{-T} D^{-1} is NOT backward stable when D has tiny
  pivots (residual 1.3e-64 at cond 1e28, 1.5e-33 at cond 1e33); stable triangular 'approx' solve -> 2.9e-72.
Threshold table (eps = 0.34; Fejer column = resolution-limited heuristic Atilde = sum c_n (1 - log n/2a)):
   a      x      A_L     T_1(Zhu)     A'      T'(window-aware)   Atilde   T_fejer
 0.8000   4.95   2.942   119          2.037   48                 1.046    18
 0.9727   7.00   4.381   502          2.756   99                 1.631    32
 1.0390   7.99   5.852   2187         3.492   206                1.900    42
 1.0986   9.00   6.343   3571         3.936   322                2.141    53
 1.2000  11.02   8.521   3.15e4       5.026   957                2.559    81
 1.3000  13.46   9.944   1.31e5       6.035   2625               3.037    131
 1.4000  16.44  10.290   1.85e5       6.372   3677               3.533    215
 1.5000  20.09  13.016   2.82e6       7.735   1.44e4             4.085    374
 2.0000  54.60  24.383   2.44e11     14.142   8.71e6             7.538    1.18e4
(Proof-of-principle only for the Fejer column: a general PW_a |F|^2 is not Fejer-shaped; A' is rigorous.)

## 14. Kernel-checked finite core of LEMMA A (lean/PathGraph.lean)
theorem PathGraph.path_quad_le (M : N) (x : N -> R) :
  2 * sum_{j < M-1} x j * x (j+1) <= 2 * cos(pi/(M+1)) * sum_{j < M} x j ^ 2
Proof: weighted AM-GM with the Perron vector w j = sin(pi (j+1)/(M+1)) and w(j+1) + w(j-1) = 2cos(pi/(M+1)) w j
(w_rec), w(M) = sin pi = 0 (w_last).  Axioms [propext, Classical.choice, Quot.sound].  The orbit decomposition
L^2(-a',a') = direct integral of l^2(orbits) remains paper-level.

## 15. Window-aware reduction VALIDATED in both sectors at a = 249/256 (certified, independent of Zhu's R)
- even: Tc = 121 (< T_1 = 502), w = 50, Tk = 471, Tmax = 971, N = 740: lam_min(R'') = 4.039e-28;
  certified lam_min(Q_even) >= 3.958e-28.
- odd : Tc = 400 (< T_1 = 502), w = 50, Tk = 750, Tmax = 1250, N = 900: lam_min(R'') = 1.4505e-24
  (Zhu R_800: 1.286e-24; lam*_odd <= 1.679e-24); certified lam_min(Q_odd) >= 1.4201e-24 (resid 2.9e-67,
  quad 2.3e-44, eps_B 1.0e-65).
- odd at Tc = 121 (Tk = 471): R''_odd indefinite.  => the effective cutoff needed is set by the ground-state loss
  (~ Tk in (471, 750] here), NOT by the Kronecker sup T_1.  The WA reduction lets the cutoff sit wherever the loss
  is small, independent of T_1 -- that is what removes the doubly-exponential pointwise barrier from the
  *reduction* (the loss scale T_loss(a) is the new, empirical, frontier).

## 16. LEMMA A' (weighted Schur test) -- the comb constant is the FEJER mass, not the Kronecker sup
For any w > 0 on [-A,A]:  <P_A g, g> <= sup_u (|P| w)(u)/w(u) ||g||^2,
  (|P|w)(u) = sum_n (|c_n|/2)[w(u+tau_n) 1_{u+tau_n in [-A,A]} + w(u-tau_n) 1_{u-tau_n in [-A,A]}]
(proof: 2|g(u+tau)||g(u)| <= |g(u+tau)|^2 w(u)/w(u+tau) + |g(u)|^2 w(u+tau)/w(u), integrate, substitute).
Numerical top eigenvalue of the compressed comb (piecewise-constant Galerkin, 1600 cells) vs bounds:
  a      A=a+eps   A_L(Zhu)  path A'   lam_max(P)  Fejer sum c_n(1 - log n/2A)
  0.9727  1.313     4.381     2.756     2.374       2.343
  1.0391  1.379     5.852     3.492     2.899       2.875
  1.1992  1.539     8.521     5.026     3.912       3.873      (T: 31535 / 957 / 314)
  1.1992  1.199     8.521     4.826     2.698       2.555      (eps -> 0: T ~ 93)
  1.4000  1.740    10.290     6.372     4.890       4.854
=> ||P_A|| ~ Fejer mass ~ 8 sqrt(x)/log x (the top eigenvector is an unmodulated bump: Kronecker alignment is
   automatic at theta = 0 and irrelevant).  Zhu's pointwise barrier exp(4 e^a) is an artifact of pointwise
   envelopes; the window-aware reduction needs exp(Lambda) with Lambda = O(e^a/a) (+ eps-price).  What then binds is
   the eigenfunction truncation loss (section 5, 15).

## 17. Two-sided certified enclosures of the window margin lam*(a) (lower: R-reduction + verified LDL^T; upper:
certified Rayleigh quotient of the untruncated Q in the closed-form cos/sin basis, N=200-250, 512 bits)
  a = 0.8     even [1.02e-17, 1.6580e-17] (Zhu: [8.9e-18, 2.27e-17])   odd [1.10e-14, 1.6317e-14] (Zhu [8.2e-15, 2.35e-14])
  a = 0.9727  even [4.395e-28, 7.4649e-28]                               odd [1.4201e-24, 1.6794e-24]
  a = 1.0391  even [2.3075e-33, 4.8907e-33]                              odd [1.1478e-29, 1.4077e-29]
  a = 1.1992  even upper 8.826e-49 (x = 11.006)

## 18. More kernel checks
- lean/SchurTest.lean: SchurTest.schur_test -- symmetric nonnegative K, positive w, K w <= Lam w  =>
  x^T K x <= Lam |x|^2.  Axioms [propext, Classical.choice, Quot.sound].  (Discrete core of LEMMA A'.)
- lean/PathGraph.lean: PathGraph.path_quad_le (discrete core of LEMMA A).

## 19. Sharp rigorous Legendre tails (certify_wa.WindowWA.tail_bounds_sharp)
For n > x: j_{n+1}(x) < j_n(x) x/(2n+3-x) (minimal-solution continued fraction, Pincherle) and j_n' = (n/x)j_n - j_{n+1} > 0,
so sup_{t<=Tmax}|j_n(a t)| <= j_n(a Tmax) (Arb) with geometric decay.  Needs first tail order n0 ~ 1.2-1.3 a Tmax
instead of ~1.5 a Tmax for the crude x^n/(2n+1)!! bound.
Rigorous weighted-Schur bounds with the DISCRETISED Perron vector as weight (K = 2000 cells; exact step-function
evaluation, Arb): a=0.9727: 3.709 (path 2.756, lam_max 2.375) | a=1.039: 3.519 (path 3.492) | a=1.2, A=1.539: 4.768
(path 5.026, T 739 vs 957) | a=1.2, A=1.299: 4.291 (path 4.826, T 459 vs 784) | a=1.4: 5.827 (path 6.372, T 2133 vs 3677).
The discretised Perron vector is a poor continuous weight (the true Perron function has jumps/kinks where orbit
lengths change), so the rigorous Schur constant sits between lam_max and the path bound.  Closing to lam_max
(~ Fejer mass) needs a weight adapted to those jumps -- open engineering item.

## 20. Numerical spot-check of LEMMA B (a = 249/256, Tk = 471, w = 50; f = cos(theta u) 1_[-a,a])
effective comb constant  [(1/pi) int h^2 p |F|^2] / [(1/pi) int h^2 |F|^2]  for theta = 0, 50, 300, 471, 480, 600,
1000, 1500:  -0.06, -0.04, -0.04, +0.31, +1.53, +0.46, +0.08, -0.48   -- all <= A' = 2.756 (and << A_L = 4.38).
x = 11 upper bounds: lam*_even <= 8.826e-49, lam*_odd <= 5.484e-45 (certified Rayleigh quotients, N=250, 512 bits).

## 21. D at x = 11.006 (a = 307/256) via the window-aware reduction (Tc = 300, w = 66, Tk = 828, Tmax = 1587, N = 1100,
sharp tails): even sector CERTIFIED lam_min(Q_D,even) >= 7.2054e-9 (A_L^D = 7.061, A'^D = 4.006, b' = 1.466).
zeta at the same window: lam*_even <= 8.826e-49 (certified upper bound).  Ratio of margins ~ 1e40: the window
certificate remains Euler-product-blind at x = 11 (D's detectable off-line pair needs x ~ 31).

## 22. x = 11.006 (a = 307/256) EVEN sector, window-aware reduction (Tc = 1170, w = 66, eps = 0.34, Tk = 1698,
Tmax = 2457, N = 2300, 59568 nodes, 2128 s build):  R''_even IS POSITIVE DEFINITE, lam_min(R'') ~ 6.743e-49
(certified upper bound on lam*_even: 8.826e-49).  eps_B 5.4e-275, eps_D 3e-557, quad 2.9e-43 -- all fine.
BUT the verified-LDL^T residual was 8.0e-10 (blocked LDL^T with unit L: huge L entries ~ D^{-1/2} ~ 1e24 destroy the
Schur-update rounding) -> certification FAILED numerically, not mathematically.  Fix: blocked CHOLESKY (R = L D^{1/2},
bounded entries) -- implemented next; needs a rebuild of M (not saved).
x = 11 ODD sector exploration (Tc = 2000, w = 66, Tk = 2528, Tmax = 3287, N = 2200, 79488 nodes, 2820 s build):
R''_odd POSITIVE DEFINITE, lam_min(R'') ~ 4.553e-45 (certified upper bound lam*_odd <= 5.484e-45).
=> both sectors of the window-aware reduction are PD at x = 11.006, where Zhu's one-stroke method needs T# > 31535.
Certification-grade reruns launched (even: N=2300 Cholesky-verified; odd: N=2300, sharp tails, Cholesky).
D at x = 11.006 BOTH sectors certified (window-aware, Tc = 300): lam_min(Q_D) >= 7.2054e-9 (even), 7.5612e-6 (odd)
=> kappa_D(11.006) = 0 with margin >= 7.2e-9, versus zeta's lam* <= 8.83e-49 at the same window.

## 23. Certified margins vs Zhu's Landau-Widom law  -ln lam* ~ 2 pi^2 N(T*)/ln N(T*), T* = 2 pi x
  x       T*     N(T*)  law    -ln(certified upper bound on lam*)   ratio
  4.953   31.1    4     57.0   38.6                                  0.678
  6.996   44.0    8     75.9   62.5                                  0.823
  7.991   50.2   10     85.7   74.4                                  0.868
 11.006   69.2   16    113.9  110.6                                  0.971
(ratio -> 1 from below; Zhu measured R_1 ~ 1.02 at L >= 1.4.)  Certified data points for the decay law.

## 24. BUG FOUND AND FIXED (numerics only): Bessel recurrence precision with ntop >> x
With nmax fixed large (4598) and moderate x (500-2000), the ball-arithmetic backward recurrence loses up to ~1.4x
bits (long decaying stretch + oscillatory region), exceeding the old headroom (1.0x + 96): j_n radii up to 4e-14
(x ~ 1440).  Consequence: Galerkin entries of the x = 11 matrices had radii up to 8e-12 -> verified residual 8e-10
(the certificate correctly FAILED; nothing false was certified -- radii are rigorous).  Earlier certificates
(x = 6.996, 7.991) remain valid (their radii were small enough: residuals 1e-64 / 1.5e-33 < margins).
Fix: sph_j_all now checks the output accuracy (absolute in the oscillatory range, relative beyond) and re-runs
with more precision; radii back to ~1e-80.  x = 11 even/odd certification rerun launched (wa3).

## 25. SUMMARY (status tags)
THEOREM-certified-computation (Arb; modulo standard paper lemmas P1 frequency form, P2 Binet envelope, P3 reduction):
  kappa_zeta(x) = 0 at x = 6.9958 (lam >= 4.39e-28) and x = 7.9906 (lam >= 2.30e-33); enclosures of lam*.
THEOREM-kernel-checked: KappaWindowCore(.Odd).core_posdef (Schur cores, x = 6.9958), PathGraph.path_quad_le,
  SchurTest.schur_test; negative controls rejected.
THEOREM-paper-proof (new): window-aware reduction (Lemma A path/Schur norm of the compressed comb; Lemma B erf
  localisation) -> threshold 2 pi e^{A'} with A' ~ A_L/2; validated by certificates at x = 6.9958 (both sectors, cutoffs
  below Zhu's T_1) and D at x = 11.006.
COMPUTED: odd-sector indefiniteness of R_560 (b* > 0 insufficient); numerical ||P_A|| ~ Fejer mass; x = 11 R'' PD.
CONJECTURE-with-evidence: ||P_A|| = (1+o(1)) sum c_n (1 - log n/2A); loss scale << T_1.
HEURISTIC: margins = zero-sampling constants (sparsity below 2 pi x/q), explaining D >> zeta.
Deaths check: no circularity (finite instances + FE-generic tool); negative control passes for D (as it must) ->
  certificates carry no Euler-product information; separation only at x >~ 31 (kappa_D(40) >= 2 certified).

## 26. x = 11.006 EVEN SECTOR CERTIFIED (window-aware reduction; run wa3 with fixed Bessel precision)
Tc = 1170, w = 66, eps = 0.34, Tk = 1698, Tmax = 2457, N = 2300 even Legendre modes (orders <= 4598), 59568 nodes.
- lam_min(R''_even) ~ 6.743e-49; verified blocked Cholesky of M - 6.6018e-49 I at 384 bits: ||E||_F = 8.70e-71.
- quadrature: the run's own (crude, uniform c_max^2) Bernstein bound 2.9e-43 was too weak; refined rigorous bound for
  the SAME nodes (quad_opt2.py: per-panel pole-free ellipses, mode-weighted |E_kl| <= sum_p Q_p G_pk G_pl with
  |j_n(z)| <= |z|^n e^{|z|^2/(2(2n+3))}/(2n+1)!!): ||E_quad||_F <= 1.48e-55 (worst panel [0, 0.5]).
- Legendre tails (sharp): eps_B <= 9.7e-489, eps_D <= 2.1e-988; b'' = 0.200448.
=> lam_min(Q_even) >= 6.6017985e-49 on L^2[-307/256, 307/256]  (certified upper bound 8.826e-49).
   (combine_x11.py)

## 27. x = 11.006 FULLY CERTIFIED (both sectors) -- kappa_zeta(e^{307/128}) = 0
odd: Tc = 2000, Tk = 2528, Tmax = 3287, N = 2300 odd modes, 79488 nodes (3478 s build): lam_min(R''_odd) ~ 4.553e-45;
  verified Cholesky at 4.4579e-45 (||E||_F = 1.94e-70); refined quadrature ||E||_F <= 6.6e-56; eps_B 1.0e-103,
  eps_D 1.6e-218  =>  lam_min(Q_odd) >= 4.4579e-45.
even (section 26): lam_min(Q_even) >= 6.6018e-49.
=> For every complex f in L^2[-307/256, 307/256] (x = e^{2a} = 11.006; prime powers 2,3,4,5,7,8,9,11):
       Q(f) >= 6.60e-49 ||f||^2.
   Two-sided: lam*_even in [6.602e-49, 8.826e-49] (factor 1.34), lam*_odd in [4.458e-45, 5.484e-45].
   Zhu's pointwise one-stroke method would need T# > 2 pi e^{A_L} = 31535 (A_L = 8.521); the window-aware reduction
   used frequency ranges 2457 / 3287.

## 28. Kernel-checked core at x = 11.006 (even sector): lean/KappaWindowCoreX11.lean
Schur complement onto the first 8 even modes of M - 6.6018e-49 I (M = saved 2300x2300 R''_even matrix, reloaded with
string-rounding radii): C - lam0 I >= 1e-55 - 1.24e-67 > 0 (verified Cholesky); S radius 1.8e-59; lam_min(Sq) = 1.07e-50;
delta = 5.35e-51 >> k w0 = 1.6e-58.  KappaWindowCoreX11.core_posdef: axioms [propext, Classical.choice, Quot.sound].
Tampered twin (one pivot numerator +1) rejected by the kernel.

====================================================================================================================
## BUILDER SECTION (2026-09-23, independent builder/referee pass).  conjecture1_proved = False.
The task input carried the idea in full but the referee reports were truncated away, so every claim below was
re-derived or re-computed here.  Files: builder/ (this lens dir) and telperion/research/crux2_kappa-certify/.

### B1. Lemma A, continuous form, proof used in the kernel (no orbit decomposition)
Window [-A, A], shift tau > 0, K = floor(2A/tau), theta = pi/(K+2).  Cell index j(u) = floor((u+A)/tau).
For u in [-A, A]: 0 <= j(u) <= K (since 0 <= (u+A)/tau <= 2A/tau), j(u +- tau) = j(u) +- 1.
Weight W(u) = sin(theta (j(u)+1)) on [-A, A], 0 outside.  On the window sin(theta) <= W <= 1 (theta(j+1) in
[theta, pi - theta]).  Perron inequality on the window: W(u+tau) <= sin(theta(j+2)) (equality if u+tau is in the
window; else W = 0 <= sin(theta(j+2)) because theta(j+2) <= pi), W(u-tau) <= sin(theta j) likewise, and
sin(theta(j+2)) + sin(theta j) = 2 cos(theta) sin(theta(j+1)).  Hence W(u+tau) + W(u-tau) <= 2cos(theta) W(u).
Pointwise weighted AM-GM: 2|g(u+tau)||g(u)| <= (W(u+tau)/W(u)) g(u)^2 + (W(u)/W(u+tau)) g(u+tau)^2 (trivial when
either value of g is 0, since then the left side is 0 and W >= 0).  Integrate; substitute u -> u - tau in the second
term (translation invariance): int 2|g(u+tau)||g(u)| <= int g(u)^2 (W(u+tau) + W(u-tau))/W(u) <= 2cos(theta) int g^2.
Integrability: each weighted term is <= g^2/sin(theta).  Summing over n with weights |c_n| gives
<P_A g, g> = sum c_n int g(u + log n) g(u) du <= A'(A) ||g||^2, A'(A) = sum |c_n| cos(pi/(floor(2A/log n)+2)).
Kernel: Crux2KappaCertify.LemmaA.{shift_bound, shift_bound_signed, comb_bound}.

### B2. Lemma B and the reduction Q >= R'' re-derived (THEOREM-paper-proof; agrees with certify_wa.py)
k = 1_[-Tk,Tk] * (w sqrt(pi))^{-1} e^{-t^2/w^2} = (erf((t+Tk)/w) - erf((t-Tk)/w))/2, 0 < k < 1, k decreasing on t >= 0.
With F(t) = int f e^{itu}, FT^{-1}(k)(s) = sin(Tk s) e^{-w^2 s^2/4}/(pi s) =: kcheck(s) (checked: convolution theorem).
h = 1 - k, g = FT^{-1}(hF) = f - kcheck * f (real for real f).  For |u| > a + eps: g(u) = -int kcheck(u-v) f(v) dv with
|u - v| > eps, so ||g 1_{|u|>a+eps}||^2 <= ||f||^2 * 2a * int_{|s|>eps} kcheck^2 <= ||f||^2 * 2a * (2/(pi^2 eps^2)) *
int_eps^inf e^{-w^2 s^2/2} ds <= ||f||^2 * 4a e^{-w^2 eps^2/2}/(pi^2 eps^3 w^2) = eta^2 ||f||^2 (Mills ratio).
(1/pi) int_0^inf h^2 p |F|^2 = <P_R g, g>; split g = g1 + g2 (g1 = g on [-a-eps, a+eps]): <P g1, g1> <= A'(a+eps)
||g1||^2 (B1), ||P_R|| <= A_L, ||g1|| <= ||g|| <= ||f||, ||g2|| <= eta ||f||.  Then
(1/pi) int h^2 (Phi - p)|F|^2 >= (1/pi) int h^2 (Phi - A' - b')|F|^2 + b'(1/pi) int h^2 |F|^2 - A_L(2eta + eta^2)||f||^2.
For t >= Tc: Phi >= log(Tc/2pi) - 1/Tc = A' + b' (Binet envelope, valid t >= 3/4; |s^2 + z^2| >= |Im z^2| = t/4).
For t < Tc: Re psi(1/4 + it/2) >= psi(1/4) (monotone in |t|) and h(t) <= h(Tc) give the deficit term.
Truncation at Tmax: chi = k(2-k) <= erfc((t-Tk)/w), |Phi - p - b'| <= log(t/2+1) + 4/3 + |psi(1/4)| + log pi + A_L + |b'|
(Binet remainder <= 1/(12 (1/4)^2) = 4/3); the product is decreasing for t >= Tmax (d/ds log erfc(s) < -2s), so xi is
its value at Tmax.  => Q >= R'' with b'' = b' - A_L(2eta+eta^2) - deficit - xi, exactly as coded.
Independent mpmath recomputation (builder/recompute_constants.py) reproduces every constant of the x = 11.006 logs:
A_L = 8.52099088425, A' = 5.02557938322, M_n = {2:5, 3:3, 4:3, else 2}, b' = 0.200447877308 / 0.736946009913,
eta = 1.1322e-56, err = 1.9295e-55, deficit 3.338e-58 / 3.507e-58, xi 4.0424e-58 / 4.1907e-58; thresholds
2 pi e^{A_L} = 31535.46, 2 pi e^{A'} = 956.67.

### B3. Code audit of the rigorous pipeline (certify.py, certify_wa.py, quad_opt2.py, vldlt.py, rmat.py)
- Galerkin: F_n = i^n c_n j_n(a t), signs sg, pole +-2 p p^T with p_n = c_n i_n(a/2): correct.
- Quadrature: Trefethen's GL bound (64/15) M rho^{-2n}/(rho^2-1) per panel; psi bounded on the Bernstein ellipse
  analytically (shift + Binet remainder 1/(12 p^2), |s^2+u^2| >= (Re u)^2 checked); poles of psi(1/4 +- iz/2) at
  +-i(2k+1/2) excluded (b < 1/2 near t = 0, ellipse in Re z > 0 elsewhere); |k(z)| <= 1 + (2/sqrt pi)(b/w)e^{(b/w)^2};
  |j_n(z)| <= min(e^{|Im z|}, |z|^n e^{|z|^2/(2(2n+3))}/(2n+1)!!); rank-one entry bound -> Frobenius sum.  Correct.
- Verified Cholesky: G - lam0 I = R R^T + E with R R^T >= 0 for ANY floating R, E in Arb: lam_min >= lam0 - ||E||_F.
- Tails (sharp): j_n increasing on [0, x] for n > x and the Pincherle ratio bound; pole tail i_n(y) <= y^n cosh y/(2n+1)!!.
FINDINGS (none invalidates a certificate):
 (F1) schur_core_file.py reloaded the saved x = 11 matrices with radii printed to 3 digits and inflated by only
      1.0000001; a 3-digit string can round a radius DOWN by up to ~1% and the |v| 1e-69 slack does not cover small
      entries.  So the Arb box feeding the x = 11 kernel core was not provably an enclosure.  FIXED: builder/
      schur_core_file_fixed.py inflates by 1.02; both x = 11 cores regenerated (even: identical S, L, D, delta;
      w0 1.99204400e-59 -> 1.99204656e-59; odd: NEW, delta = 4.379e-47 vs 8 w0 = 1.84e-59).
 (F2) certify_wa.py on disk has GAPK, GAPM = 7, 10, but the x = 11 runs (and quad_opt2's refined bound) used
      gap_k = 8, gap_max = 11.5 (Tk = Tc + 8w, Tmax = Tk + 11.5w; node counts 59568 / 79488 confirm).  REPRODUCE.sh
      has no x = 11 line.  Reproduction must pass gap_k=8, gap_max=11.5.
 (F3) combine_x11.py says b'' was "rounded down" but uses 0.200448 > 0.2004478773 (even).  Harmless: the minimum
      min(lead, b'' - eps_D) is the leading block (6.6e-49), not b''.
 (F4) lean/KappaWindowCoreX11.lean docstring is stale (says a = 249/256, 450 x 450 block, Q >= 4.39e-28).
 (F5) "Zhu's one-stroke method cannot reach x = 11" overstates Zhu Thm 1.4: it needs T# > 31535 (~3.8e4 Legendre
      modes per sector at this a), infeasible for this pipeline, not impossible.
 (F7) e^{133/64} = 7.98947 (the idea writes 7.991 / 7.9906); prime powers {2,3,4,5,7} unchanged (log 8 = 2.0794 > 2.0781).
 (F6) The runs' own final_lower fields are NEGATIVE (-2.9e-43) because the crude uniform quadrature bound was used
      in-run; the certificate is the post-hoc combination with the refined mode-weighted bound (same nodes, same
      window parameters) -- which I re-derived and consider correct.

### B4. Independent numerical corroboration (COMPUTED, not certified)
(a) Explicit-formula normalisation in the u-DOMAIN (Weil's archimedean distribution, from
    psi(z) = -gamma + int_0^inf (e^{-x} - e^{-zx})/(1-e^{-x}) dx):
      Q(f) = 2F(i/2)F(-i/2) + (-gamma - log pi - log(1 - e^{-4a})) g(0)
             + int_0^{2a} 2(e^{-2u} g(0) - e^{-u/2} g(u))/(1 - e^{-2u}) du - sum_{n<x} 2 Lambda(n) n^{-1/2} g(log n),
    g = autocorrelation of f.  Against the zero side 2 sum_k |F(gamma_k)|^2 (2000 zeros, 20 digits) for
    f = (1-(u/a)^2)^5 (1+u/3): a = 249/256: 1.2017065473674344224e-6 vs ...4219e-6 (diff 5e-25);
    a = 307/256: 1.11691389955121861514e-7 vs ...8614316e-7 (diff 8e-26).  (check_ef_udomain.py)
(b) Rayleigh-Ritz upper bounds lam_min(Q_N) >= lam* in a Legendre basis on the u-domain form (no Bessel, no
    digamma; composite GL for the single archimedean integral, 4 vs 8 panels agree to 11 digits):
      x = 4.95   even N=36 1.7016e-17 (cert. [1.02e-17, 1.658e-17]);  odd N=36 1.6141e-14 (cert. [1.10e-14, 1.6317e-14])
      x = 6.996  even N=60 7.1406e-28 (cert. [4.395e-28, 7.4649e-28]); odd N=60 1.6663e-24 (cert. [1.4201e-24, 1.6794e-24])
      x = 7.990  even N=60 4.8787e-33 (cert. [2.3075e-33, 4.8907e-33]); odd N=60 1.4657e-29 (cert. [1.1478e-29, 1.4077e-29])
      x = 11.006 even N=120 8.5038e-49 (cert. [6.6018e-49, 8.826e-49]); odd N=120 5.2107e-45 (cert. [4.4579e-45, 5.484e-45])
      (x = 11 sequence even: N=80 9.763e-49, 90 8.995e-49, 100 8.896e-49, 110 8.754e-49, 120 8.504e-49; odd: 5.779, 5.366,
       5.320, 5.279, 5.211 e-45 -- monotone decreasing, still above the certified lower bounds)
    Every value lies above the certified LOWER bound (a value below it would refute the certificate); several
    tighten six of the idea's eight upper bounds (all but x = 4.95 even and x = 7.99 odd).  Legendre convergence is algebraic
    (boundary behaviour of the ground state), so these are upper bounds only.
(c) Davenport-Heilbronn with the same u-domain code (Lambda_D from -D'/D, e^{-3u/2}, log(5/pi), no pole):
      x = 6.996  even N=40 8.683e-5 (cert. >= 7.253e-5), odd 2.344e-2 (cert. >= 2.163e-2)
      x = 11.006 even N=40 7.730e-9 (cert. >= 7.205e-9), odd 8.082e-6 (cert. >= 7.561e-6)
      x = 39.94  even: N <= 50 still positive (1.5e-34), N = 70: -8.78e-15;  odd: N <= 50 positive, N = 70: -1.75e-14
      (the negative directions need frequency ~ 86 = D's off-line ordinate, which Legendre degree <= 99 on a
      window of half-width 1.84 cannot resolve; see B5)

### B5. D at x = 40 (independent u-domain Galerkin, COMPUTED)
a = 472/256 (x = 39.945), Lambda_D over the 31 n < x with Lambda_D(n) != 0:
  even: N = 50: +1.49e-34 ; N = 70: -8.78e-15 ; N = 90: -2.297e-2 ; N = 110: -2.442e-2 (next eigenvalue +1.9e-39)
  odd : N = 50: +4.30e-31 ; N = 70: -1.75e-14 ; N = 90: -4.149e-3 ; N = 110: -4.612e-3 (next eigenvalue +2.6e-35)
Exactly one negative eigenvalue per sector: kappa_D(39.945) >= 2, matching the one resolved off-line quadruple
(0.8085 +- 85.699i and its reflection = 2 pairs).  The onset needs Legendre degree ~ 85.7 x 1.84 ~ 160, i.e. the basis
must resolve D's off-line ordinate; below that, D looks positive (as zeta does: +5.9e-78 at N = 60, same window).
The idea's certified Rayleigh quotients (-2.59e-4 even, -1.09e-3 odd, on V_60(40)) are consistent (they are upper
bounds on lam*_D; the Legendre space finds deeper directions).

### B6. Lemma B numerical sanity (check_lemmaB_eta.py)
(1) int kcheck(s) e^{its} ds = k(t) to 10 digits at t = 0, 10, 19, 20, 21, 30 (Tk = 20, w = 8): the kcheck formula
    and the FT convention are right.  (2) Leakage ||(kcheck*f) 1_{|u|>a+eps}||/||f|| for f = cos(theta u) 1_[-a,a],
    theta in {0, 5, Tk, Tk+3w}, three parameter sets: 3e-6 .. 2.2e-3, always below eta = 4.1e-3 .. 1.15e-1 (eta is
    conservative by 1-2 orders, as expected from Cauchy-Schwarz + Mills).

### B7. Kernel deliverable (Crux/Crux2_kappa_certify.lean, li_positivity island, ~30-40 s)
LemmaA.{W_rec, shift_bound, shift_bound_signed, comb_bound, prime_comb_bound} (continuous Lemma A, NEW),
schur_link + Core_*.core_schur (Arb facts -> PSD of the full block matrix, NEW), posdef_of_box, block_assembly,
PathGraph.path_quad_le, SchurTest.schur_test, and four cores Core_x6996_{even,odd}, Core_x11006_{even,odd}
(x = 11 odd NEW; x = 11 even regenerated with the F1 radius fix).  All [propext, Classical.choice, Quot.sound].
Tamper twins (x = 11 odd core: pivot numerator +1; one Schur entry +7 in its numerator; delta x 3) -> unsolved goals
at Sq_ldl, sorryAx in the axiom list.
