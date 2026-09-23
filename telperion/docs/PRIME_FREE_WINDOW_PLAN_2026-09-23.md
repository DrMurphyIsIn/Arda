# Prime-free window: Weil positivity on the MIRRORMERE goal node's own test class (plan, 2026-09-23)

Branch `mm/prime-free-window`, island `telperion/examples/rvm_bridge/lean` (Mathlib v4.32.0 pin
through Zeta23).  `conjecture1_proved = False`: nothing here is RH progress.  The target is the
classical archimedean positivity theorem (Yoshida 1992, Burnol 2000, Connes-Consani 2021) read
on this island's coordinates, which certifies the goal node on a region of its own test class.

## 0. The statement, and the one fact that reshapes the plan

The goal node (E6Bridge9 `zeta_comb_membership_iff_rh`) is `RH <-> for all g, IsWeilTest g ->
0 <= (weilForm (autocorr g)).re`, with `weilForm f = archSide f - primeSide f`.  The window
statement asked for is

    WINDOW(L):  for all g, IsWeilTest g -> tsupport g ⊆ Icc (-L) L -> 2 L <= log 2 ->
                0 <= (weilForm (autocorr g)).re.

Stage 0 (below) shows `primeSide (autocorr g) = 0` on the window, so WINDOW(L) is
`0 <= (archSide (autocorr g)).re`, i.e. positivity of

    Q(g) := 2 Re[G(1/2) conj G(-1/2)]  -  log(pi) ||g||^2  +  (1/2pi) ∫ |ĝ(r)|^2 Re psi(1/4 + i r/2) dr,

    G(s) = ∫ g(u) e^{s u} du (so h(±i/2) = G(1/2) conj G(-1/2) and its conjugate: the two pole
    terms of archSide), ĝ(r) = ∫ g(u) e^{i r u} du (= paperFT g r), ||g||^2 = f(0) = (1/2pi) ∫ |ĝ|^2.

THE FACT.  The literature theorem is NOT this statement.  Connes-Consani (arXiv 2006.13771, p. 2
and Theorem 1) and Yoshida (as quoted there) prove `W_infinity(g * g^*) >= 0` for g supported in
`[2^{-1/2}, 2^{1/2}]` WITH the vanishing condition `ĝ(i/2) = 0` (Theorem 1 also `ĝ(0) = 0`), i.e.
with the two pole terms removed.  On the pole-free subspace the archimedean form has a healthy
margin; on the goal node's full class (no vanishing condition) the pole terms are a rank-two
indefinite perturbation.  Numerics (scripts in the scratchpad, reproduced in
`telperion/examples/rvm_bridge/prime_free_window_numerics.py`):

| half-width L of supp g | 2L | min eigenvalue of Q / ||g||^2, full class | same, class ĝ(±i/2) = 0 |
|---|---|---|---|
| 0.05  | 0.10 | +0.991 | +2.470 |
| 0.20  | 0.40 | +0.103 | +1.121 |
| 0.30  | 0.60 | +0.0076 | +0.692 |
| (log 2)/2 = 0.3466 | log 2 | +0.001329 | +0.547 |
| 0.36  | 0.72 | +0.0011 | +0.509 |
| 0.38  | 0.76 | -0.024 | +0.454 |

(Legendre basis on [-L, L], K = 12..40, converged to six digits; the u-space and r-space
evaluations of Q agree to seven digits.)  So WINDOW((log 2)/2) is TRUE numerically but with margin
1.3e-3 of ||g||^2.  Consistency check: for the minimising g at L = (log 2)/2, the zero sum
`sum over the first 200 zeta zero pairs of |ĝ(gamma)|^2 / ||g||^2` is 0.001301, against the min
eigenvalue 0.001329: on the window the form IS the zero sum (explicit formula, all known zeros on
the line), and the margin is the floor of that zero sum over window-supported tests.  No
elementary or literature route proves a 1.3e-3 margin; the literature route (pole-free class,
margin 0.55) needs the vanishing constraint in an essential way (Connes-Consani, Toeplitz/Sonin;
Yoshida, an explicit finite computation at t = (log 2)/2).

## 1. Dictionary (checked against E6Bridge4/5/11)

archSide f = weilKernel f 0 + weilKernel f 1 - f(0) log pi + (1/2pi) ∫ archIntegrand f, with
weilKernel f (1/2 + i r) = paperFT f r = |paperFT g r|^2 for f = autocorr g (E6Bridge5
`weilKernel_autocorr_line`), and archIntegrand f r = paperFT f r * Re psi(1/4 + i r/2) where
psi = Complex.digamma; Re psi(1/4 + i r/2) - log pi = 2 Re (Gamma_R'/Gamma_R)(1/2 + i r),
Gamma_R(s) = pi^{-s/2} Gamma(s/2).  `psiR` (E6Bridge11) is this weight; floors on it at 20 radii
are in E6Bridge30 (`psiR_floor_*`, `psiR_mono`).

Exact u-space form of the same functional (verified numerically to 1e-7, NOT yet in Lean; the
pole terms in the same coordinates are 2|∫ g cosh(u/2)|^2 - 2|∫ g sinh(u/2)|^2):

    Q(g) = 2 Re[G(1/2) conj G(-1/2)] + (psi(1/4) - log pi) ||g||^2
           + (1/2) ∫∫ |g(v) - g(w)|^2 k(v - w) dv dw,   k(u) = e^{3|u|/2} / (e^{2|u|} - 1) = sum_n e^{-(2n + 1/2)|u|},

from the vertical-line digamma series (Zeta23 `re_digamma_vertical`), the Fourier pair
e^{-b|u|} <-> 2b/(b^2 + r^2) and Tonelli (the series terms are nonnegative).  psi(1/4) - log pi
= -5.372; the Dirichlet term supplies ~ log(1/L) + 2.8 for narrow supports.

## 2. Stages (status at the end of the session, 2026-09-23)

PROVED: Stage 0; Stage 1 at L <= 1/14 by the r-space route (E6Bridge31); the u-space route
(E6Bridge32-34) at L <= 1/10 (`RvMBridge34.weil_positivity_window_tenth`, margin 0.134 of
||g||^2).  NOT PROVED: the full window 2L <= log 2 (named Prop `PrimeFreeWindowPositivity`).


Stage 0 (prime side vanishes; PROVE).  tsupport g ⊆ Icc (-L) L gives tsupport (autocorr g)
⊆ Icc (-2L) (2L) (Zeta23 `tsupport_weilTest_subset`); for n >= 2, log n >= log 2 >= 2L and
continuity kills the boundary point; Lambda(0) = Lambda(1) = 0.  Hence `primeSide (autocorr g) = 0`
and `weilForm (autocorr g) = archSide (autocorr g)`.

Stage 1 (narrow support, PROVED with explicit constants).  r-space dominance with two cheap
sharpenings over the first draft: |ĝ(r)| <= A := ||g||_1 and A^2 <= 2 L f(0) (AM-GM under the
integral with a free parameter = Cauchy-Schwarz against the indicator of [-L, L]), so
|ĝ|^2 <= 2 L f(0) instead of 4 L f(0); ∫ |ĝ|^2 = 2 pi f(0) (E6Bridge4 `inversion_zero` applied to
f); the pole terms are ĝ(i/2) conj ĝ(-i/2) + conjugate = 2 Re (a conj b) >= -|a - b|^2 / 2
(polarization) with a - b = ∫ g (e^{u/2} - e^{-u/2}) of modulus <= (e^{L/2} - e^{-L/2}) A, an
O(L^3) loss instead of the O(L) Cauchy-Schwarz loss; and a 19-band layer cake over the
E6Bridge30 floors (generic weight version of E6Bridge30 `Cake`, base psiR(0) >= -4.2315, band sum
24.67252): (1/2pi) ∫ |ĝ|^2 psiR >= f(0) [2.3499 - (2L/pi) * 24.67252].  The bound is positive for
L <= 0.076; the theorem `weil_positivity_narrow_support` is stated at L₁ = 1/14 (margin 0.068 of
||g||^2).  This is the ceiling of the r-space route: a band at radius rho helps only while
rho < pi/(2L), and the floors above rho = 21 cost more than they give at L ~ 0.08.  The
Dirichlet u-space route below would reach L ~ 0.12 (Poincare split of g into its mean on [-L, L]
and the fluctuation; the mean part is nearly tight at the edge, the fluctuation part loses the
crude kernel minimum k(2L)); the exact threshold is ~ 0.36.

Stage 1b (the u-space route, PROVED at L <= 1/10; E6Bridge32, E6Bridge33, E6Bridge34).
E6Bridge32: the Lorentzian pair e^{-b|u|} <-> 2b/(b^2+r^2) (Mathlib inversion through Zeta23
`paper_inversion` of f, Fubini) and the digamma series (E6Bridge30 `psiR_ge_series`, M = 0)
paired termwise: (1/2pi) ∫ |ĝ|^2 psiR >= (-gamma + sum_{n<N} 1/(n+1)) f(0) - Re ∫ f e^{-|u|/2}
- sum_{n<N} Re ∫ f e^{-b_n|u|}, b_n = 2n + 5/2.  E6Bridge33: for one kernel, f(0) ∫ K_b
- Re ∫ f K_b = (1/2) ∫∫ |g(v) - g(w)|^2 K_b(v - w) (Fubini, substitution, symmetrisation on
the plane), and >= (2 e^{-bL}/b) f(0) + e^{-2bL} (2 L f(0) - |∫ g|^2) (pointwise split of the
plane into the square and the cross regions; outer mass (e^{-b(L-v)} + e^{-b(L+v)})/b
>= 2 e^{-bL}/b by AM-GM).  E6Bridge34: the pole terms refined to Re (W0 + W1) >= 2 |∫ g|^2
- (2 D^2 + S^2/2) ||g||_1^2 (polarisation; ĝ(-i/2) + ĝ(i/2) - 2 ∫ g = ∫ g (e^{u/2} + e^{-u/2} - 2)
is O(L^2)), the kernel sums by induction on N, k_10(2L) >= 2 so the |∫ g|^2 terms cancel
against the poles, the tangent bound e^{-bL} >= e^{-b/10}(1 + b(1/10 - L)) to move from L to
1/10, and (1 - x/16)^16 <= e^{-x} for the eleven exponentials; c_10 >= -4.2549, F_10(1/10)
>= 5.1499, log pi <= 1.159, total margin 0.134.  The bound's own threshold is L ~ 0.125
(k_N(2L) >= 2 fails beyond, and the Poincare split then needs the true first eigenvalue of
the kernel on the interval, which is where Connes-Consani's prolate machinery starts).

Stage 2 (full window).  Literature mechanism extracted (Connes-Consani 2006.13771, Yoshida): it
is a theorem about the pole-free class only, and its proof is a Sonin-space compression plus a
numerically computed Toeplitz spectrum.  The goal-node-class statement WINDOW((log 2)/2) has
margin 1.3e-3 and is beyond every route available (it is the zero-sum floor).  Deliverable: the
full-window statement as ONE named Prop `PrimeFreeWindowPositivity` (no `sorry`), the Stage-0
reduction showing it is equivalent to the archSide form, and the pole-free-class statement as a
second named Prop `PrimeFreeWindowPositivityPoleFree` (the Yoshida / Connes-Consani theorem
itself) with the implication pole-free-class positivity + pole terms zero -> window positivity
for such g.  If time permits after Stage 1: the exact u-space series identity as infrastructure.

## 3. Files

* `E6Bridge31.lean`: Stage 0, the pointwise bounds, the generic layer cake, Stage 1
  (`weil_positivity_narrow_support`, L <= 1/14), the named Props and the reductions.
* `E6Bridge32.lean`, `E6Bridge33.lean`, `E6Bridge34.lean`: the u-space route,
  `weil_positivity_window_tenth` (L <= 1/10).
* `AxiomGuardRvMBridge.lean`: `#print axioms` for every new theorem.
* `lakefile.toml`: `E6Bridge31` in defaultTargets.
* `prime_free_window_numerics.py` (island directory): the numerics above.

conjecture1_proved = False.
