# Fixed-width residual, heat-flow and orthogonal lenses (2026-09-21)

Finder thread of the creative survey on the two-parameter Wall (WALL_MAP_2026-09-21.md section 1).
Research only; no Lean; no git state touched. Scratch: `scratchpad/heat_lens.py`, `heat_lens2.py`
(numpy, toy zero sets; identities checked to 1e-9 / 2e-31, they are algebraic and hold for any zero
configuration). **conjecture1_proved = False.** Nothing here proves RH. Every survivor is an instrument
or a reduction with its wall named. `checked: true` only where a primary was read (abstract or text).

Notation as in the wall map: gamma_rho = (rho - 1/2)/i, x = Im rho - c, y = 1/2 - Re rho, so
gamma_rho - c = x + i y (the reflected zero gives x - i y).

    F(c, lam)     := Re Sum_rho m(rho) (gamma_rho - c)^2 e^{-2 lam (gamma_rho - c)^2}     (the Wall face)
    Theta(c, lam) := Re Sum_rho m(rho) e^{-2 lam (gamma_rho - c)^2}                       (plain Gaussian face)

## 0. Verdict table

| # | lens | verdict | one line |
|---|---|---|---|
| 1 | heat flow / S(t) | COLLAPSE_TO_FREE | the differential inequality on the smoothed zero DENSITY is unconditionally true for the ordinate comb; it is y-blind; RH content = "complex comb equals ordinate comb" |
| 1' | width semigroup | TRANSFER (new instrument) | Theta is exactly heat-monotone in lam (positivity at width lam gives every smaller width); F is not (negative source term); RH <-> Theta >= 0; a de Bruijn-Newman-type constant Lambda_Theta with RH <-> Lambda_Theta = infinity |
| 2 | de Bruijn-Newman | TRANSFER (structure only) | not a change of variables (heat on Xi vs heat on the log-derivative measure); Lambda >= 0 kills every t < 0 statement; the Polymath15 closure pattern = large-height analytic + finite numerics + monotone flow, which is exactly what lens 1' supplies for Theta |
| 3 | Laguerre-Polya / Jensen | COLLAPSE_TO_FREE | Laguerre inequality = S8 rational face at shift a -> 0; GORZ fixed-degree free region = archimedean (first theta term) dominance, the exact analogue of envelopeC; Farmer's critique applies verbatim |
| 4 | GUE / Keating-Snaith | RECORDED, no instrument | on-line background mean ~ log c, O(1) fluctuations (hyperuniform), relative deficit O(1/log c): fragility DECREASES with height; fragility is only ever an off-line zero at width lam ~ 1/y^2 |
| 5a | Gabor / Husimi / Wigner | COLLAPSE_TO_FREE | F is the u_0 = 0 fibre of a Hermite-windowed Gabor transform of the Weil distribution; Wigner of the zero comb = pair correlation (S4/S9 territory) |
| 5b | Hamburger / Hankel | TRANSFER (dictionary) | F = -(1/2) d/dlam Theta; all Hankel moment entries are (d/dc, d/dlam)-derivatives of Theta; RH <-> Hankel PSD <-> Widder positive initial trace; backward heat ill-posedness IS the fixed-width residual |
| 5c | partition function / Lee-Yang | COLLAPSE_TO_FREE | Theta = harmonic-trap partition function at inverse temperature 2 lam; Knauf's ferromagnetic chain gives a Lee-Yang zero-free HALF-PLANE, never the line |
| 5d | tropical lam -> infinity | COLLAPSE_TO_RH | limsup -(1/2lam) log|Theta(c,lam)| = min_rho Re (gamma_rho - c)^2; the Wall at infinite width is each zero pointwise; this is E6Bridge7's maximiser step |
| 5e | Tauberian lam -> 0 | COLLAPSE_TO_FREE / UNRESOLVED | free region = "Sum_{|gamma-c| <= X} y_rho^2 <= C log c X^3", a counting fact; the band = short-interval zero density at H = O(1), the S3/S10 clustering lemma |

## 1. The seed identity, and what it does and does not say (lens 1)

Verified (scratch, both on-line and with an off-line pair): d^2/dc^2 K = (16 lam^2 u^2 - 4 lam) K for
K = e^{-2 lam u^2}, hence

    F(c, lam) = ( Theta_cc + 4 lam Theta ) / (16 lam^2),        and also    F = -(1/2) Theta_lam.

Heat normalisation: Theta(c, lam) = sqrt(pi/(2 lam)) u(c, tau), tau = 1/(8 lam), with u_tau = u_cc; the
prefactor is why Theta_cc is not simply Theta_lam (it is -8 lam^2 Theta_lam - 4 lam Theta).

S(t) reading. Write dN for the ORDINATE counting measure (Riemann-von Mangoldt counts every zero of the
strip by Im rho, on or off the line). Then rho_ord(c) := Sum m K(Im rho - c) = (K * dN)(c), and with
N = smooth + S, rho_ord = rho_sm + S_lam', S_lam := S * K. The inequality

    S_lam''' + 4 lam S_lam' >= -(4 lam rho_sm + rho_sm'') ~ -(log(c/2pi)/2pi) sqrt(8 pi lam)

is the seed's "smoothed density never too concave", and it is UNCONDITIONALLY TRUE: it is dN >= 0 tested
against the nonnegative kernel u^2 K, i.e. the Gaussian shadow of the classical "S'(t) >= -log(t/2pi)/2pi
between zeros" (N non-decreasing). The corpus's Backlund node (`RH.backlund_s_log`, proved) and every
S(t) bound (Backlund unconditional O(log t); Littlewood O(log t/loglog t) on RH; Selberg's CLT) bound the
SIZE of S_lam', never its sign, and are not needed for the sign. F equals this ordinate object iff every
gamma_rho is real; the RH content is entirely in F - F_ord = Re Sum m [G(x+iy) - G(x)] =
-(1/2) Sum m y^2 G''(x) + O(y^4), G''(0) = 2 > 0 (the negative dip at the ordinate, E6Bridge7's bracket
-(x^2+y^2) at x = 0). Verdict: the S(t) lens is the y-blind shadow (same failure as S7a's ordinate
sweep). Not an orthogonal route. What survives of it is used in lens 4 (size of the on-line background).

## 1'. Width semigroup: the plain Gaussian face is heat-monotone (the one new instrument)

Gaussian convolution of a Gaussian with COMPLEX centre is the same identity as with real centre (both
sides entire in gamma, equal on the real axis; Fubini over zeros by |e^{-2 lam (x+s+iy)^2}| <= e^{lam/2}
e^{-2 lam (x+s)^2} against the zero count). With P_s the heat semigroup of time s and
lam' = lam/(1 + 8 lam s) < lam (checked to 1e-8 on-line and off-line, two centres):

    Theta(., lam') = sqrt(lam/lam')  P_s Theta(., lam),                                        (M)
    F(., lam')     = (lam/lam')^{5/2} P_s F(., lam)  -  2 s (lam/lam') Theta(., lam').           (D)

(D) was recovered by least squares from the scratch data with residual 2e-31: the fitted coefficients equal
sqrt(lam'/lam)(lam'/lam)^2 and sqrt(lam'/lam)(lam'/lam) 2s exactly. Consequences:

- (M): if Theta(., lam) >= 0 on ALL of R then Theta(., lam') >= 0 on all of R for every lam' < lam.
  The free set of widths for the plain face is an interval (0, Lambda_Theta] (or all of (0, infinity)).
- (D): F has NO such monotonicity; the source term -2s(lam/lam') Theta is negative wherever Theta > 0.
  Positivity of F at one width says nothing about F at another width, in either direction. This is the
  precise reason the two-parameter Wall for F is a diagonal and not a threshold.
- RH <-> Theta >= 0 for all (c, lam). Forward trivial (each term e^{-2 lam x^2} >= 0). Converse: E6Bridge7's
  six steps go through verbatim with the bracket (x^2-y^2)cos(4 lam x y) + 2xy sin(4 lam x y) replaced by
  cos(4 lam x y): at the generic centre c with 0 < |x_1| < |y_1| (phi_c = y^2 - x^2 > 0 at the maximiser)
  choose lam = (pi + 2 pi k)/(4 x_1 y_1) >= lam_0 so that cos = -1; the pair term is then
  -2 m_1 e^{2 lam M} and the assembly is unchanged. Scratch: pair at x_0 +- 0.3 i, centre x_0 + 0.15,
  lam = 17.45: Theta = -21.06 against an on-line background of 0.04. NOTE the difference from F: at the
  ordinate itself (x = 0) the plain pair term is +2 e^{2 lam y^2} > 0; the dip is at |x| ~ y/2, not at x = 0.
- Define Lambda_Theta := sup { lam : Theta(., lam) >= 0 on R }. By (M) the set is an interval. RH <->
  Lambda_Theta = infinity. If a zero sits at (x_0, y_0) then Lambda_Theta <= C/y_0^2 (E6Bridge7 constants,
  configuration-dependent). This is a de Bruijn-Newman-type constant for the ZERO MEASURE: unconditional
  lower bounds on Lambda_Theta are the analogue of "Lambda <= 0.2"; RH is "Lambda_Theta = infinity".
- The prime side of Theta is the k = 0 member of the Hermite family (lens 5b, attribution below); its
  archimedean-dominance region (seam B mechanism) gives Lambda_Theta >= lam_0 unconditionally by the same
  proof as `re_weilForm_gauss_nonneg` (the test f0 = A e^{-u^2/(8 lam)} has no polynomial factor, so the
  constants are slightly better; not derived here).

Wall named honestly: certifying Theta(., lam) >= 0 on ALL of R at one width lam still needs the ladder for
|c| <= T - D, the envelope for |c| >= envelopeC(lam), and the band between; (M) only removes the need to
repeat this at every smaller width, and in particular removes the sub-threshold band (lam_0 < lam < lam_1,
the factor 2-3 gap between U and L at every height in WALL_LANDSCAPE section 4): certify once at lam_1 and
every width below it follows. The largest certifiable width is envelopeC^{-1}(T - D): with the crude
constant of the memo (c >= 2 pi exp(2 P_abs/f(0)), P_abs/f(0) = 2 lam sqrt(8 pi lam) e^{lam/2} for the
F-face) that is lam ~ 0.4 at T = 6.4e5 (kernel ladder) and lam ~ 0.9 at T = 3e12 (Platt-Trudgian,
checked). Pushing Lambda_Theta's certified lower bound to infinity is RH; the cost is doubly exponential in
lam through envelopeC. No RH progress.

## 2. de Bruijn-Newman (lens 2)

Checked: Rodgers-Tao arXiv 1801.05914 (Forum Math. Pi 2020): Lambda >= 0, mechanism = if Lambda < 0 the
zeros of H_0 would be in local equilibrium (lattice-like spacing), contradicting pair-correlation-type
knowledge. Checked: Platt-Trudgian arXiv 2004.09765 = RH verified to 3e12 (the Lambda <= 0.2 bound is the
companion paper, not read: unchecked). Analysis:

- H_t = "e^{t u^2} on the Fourier side of Xi" is a heat flow on the FUNCTION (d_t H = -d_z^2 H, backward
  heat as t increases); Theta is a heat flow on the ZERO MEASURE (linear). Zeros of H_t obey Newman's
  nonlinear ODE (mutual repulsion); Gaussian smoothing of the zero measure moves no zero. Log does not
  commute with heat: there is no change of variables between the two flows. The Fourier transform of the
  zero measure is the Weil distribution (prime side), not Phi. Verdict: unrelated objects.
- Since Lambda >= 0, every H_t with t < 0 has non-real zeros, so "fixed-width positivity translates to
  H_t for some t < 0" is false as stated: the Gaussian positivity of H_t's zero set FAILS for every t < 0.
  The only open dBN band is 0 <= t < 0.2, where the Gaussian family for H_t's zeros is another Wall.
- Structural transfer (the useful part): Polymath15's closure of t = 0.2 is (i) an analytic proof of
  reality above a height X(t) (the Dirichlet series is effectively absolutely convergent there), (ii)
  numerics below X(t), (iii) de Bruijn's monotonicity in t to fill the rest. Our F-face has (i) = envelope
  and (ii) = ladder but NO (iii); the Theta-face has (iii) by (M). That is the whole content of proposal P1.

## 3. Laguerre-Polya, Jensen, Bochner (lens 3)

Checked: Griffin-Ono-Rolen-Zagier arXiv 1902.07321 (PNAS 2019): for each degree d the Jensen polynomials
J^{d,n} of Xi are hyperbolic for all n >= N(d) (density-one statement, all n for d <= 8), via Hermite
asymptotics of the central derivatives. Checked: Farmer arXiv 2008.07206: "no justification for the
suggested connection to the Riemann Hypothesis"; Jensen polynomials "not useful for attacking" RH.

- Mechanism transfer: the Taylor coefficients of Xi are moments of Phi(u), large n probes large u, where
  Phi is dominated by its FIRST theta term (the Gamma-factor piece). GORZ's fixed-degree free region is
  archimedean dominance in Taylor-coefficient coordinates, exactly our envelopeC(lam) region; the band
  (small n at fixed d, where the n >= 2 theta terms, i.e. the primes, matter) is untouched, exactly as
  our band. Farmer's criteria apply to the (c, lam) family word for word.
- Jensen/Laguerre: the Laguerre inequality f'^2 - f f'' >= 0 on the line is -(log Xi)''(c) =
  Re Sum 1/(c - gamma)^2 >= 0, the S8 rational face at shift a -> 0 (a Cauchy window instead of a
  Gaussian window); Csordas-Varga's higher Laguerre inequalities are its higher members. Already
  COLLAPSE_TO_FREE in the reconciliation.
- Bochner reading: RH <-> the zero measure is a positive measure on R <-> its Fourier transform (the Weil
  distribution W, prime side) is positive-definite; the Gaussian family tests W against the Hermite
  windows e^{-icu} f0_lam(u); E6Bridge7 is the statement that Gaussian(-derivative) windows are total for
  this positive-definiteness. Lee-Yang / Polya-Schur multipliers act on the FUNCTION side and give
  de Bruijn's direction only. No zeros-on-a-line theorem for order-1 entire functions from Gaussian sums
  beyond this Bochner tautology was found.

## 4. Random-matrix prediction (lens 4)

At width lam and height c the on-line background is F_ord = window law (log(c/2pi)/2pi) sqrt(pi)/
(2 (2 lam)^{3/2}) plus a linear statistic of the zeros with a smooth test of scale 1/sqrt(2 lam). Under
GUE (Montgomery pair correlation, on RH and bandwidth-restricted; unconditional only as the S9 second
moment) the variance of such a linear statistic is O(1), independent of height (hyperuniformity), so the
relative deficit is O(1/log c) and large deviations are Gaussian in log c. Gaps: largest gap among N
zeros ~ sqrt(32 log N) in CUE units (Ben Arous-Bourgade 2013, abstract checked; Vinson's prediction),
i.e. O(sqrt(log N)) mean spacings; rigorously for zeta, gaps > 3.18 x average infinitely often
(Bui-Milinovich QJM 2018, abstract checked). Since the mean spacing 2 pi/log c shrinks faster than
sqrt(log N) grows, the absolute half-gap g ~ sqrt(log N)/log c -> 0 and at FIXED lam the midway margin
2 g^2 e^{-2 lam g^2} is eventually dominated by the many-zeros window law: fragility DECREASES with
height. The only fragile configuration is an off-line zero at distance y probed at width lam ~ 1/y^2
(E6Bridge7's scale), which no on-line statistic sees. To make any of this unconditional: nothing
available; the c-averaged version is S9. Recorded for calibration of proposal P1 only.

## 5. Orthogonal readings (lens 5)

- Gabor / Husimi. On the prime side F = int W(u) e^{-icu} f0_lam(u) du: a short-time Fourier transform
  of the Weil distribution with a Hermite window centred at u_0 = 0, frequency c, scale sqrt(4 lam).
  Sweeping u_0 (window at +-u_0) multiplies the zero-side test by cos(u_0 z), which is not nonnegative on
  the line: Weil positivity lives ONLY on the u_0 = 0 fibre of the Gabor plane. The Wigner distribution
  of the zero comb is the comb of midpoints (gamma+gamma')/2 with frequencies gamma-gamma': pair
  correlation, Montgomery's F(alpha) is its marginal (S4/S9). Husimi >= 0 always, no criterion.
- Hamburger / Hankel. For fixed (c, lam) the Gaussian-damped moments s_n = Sum (gamma-c)^n
  e^{-2 lam (gamma-c)^2} satisfy s_1 = Theta_c/(4 lam), s_2 = -(1/2) Theta_lam = F, and in general every
  s_n is a (d/dc, d/dlam)-polynomial derivative of Theta. Carleman's condition holds (Gaussian decay), so
  RH <-> [s_{i+j}] PSD for all (c, lam); F >= 0 is the (1,1) diagonal entry and by E6Bridge7 the diagonal
  already suffices. Widder (Trans. AMS 55, 1944; statement from secondary sources, the AMS PDF returned
  403: unchecked): a nonnegative solution of the heat equation on R x (0, T) is the heat evolution of a
  unique nonnegative measure. So RH <-> Theta is a nonnegative solution on the whole half-plane, and
  positivity on R x (tau_1, infinity) (widths <= lam_1) says only that Theta(., lam_1) is nonnegative,
  nothing about earlier times: backward heat is ill-posed. That is the fixed-width residual in one
  sentence. Dictionary: Theta(c, lam) = 2 int_lam^infinity F(c, mu) dmu (from F = -(1/2) Theta_lam and
  Theta -> 0): F >= 0 for ALL widths above lam_1 implies Theta >= 0 at lam_1 and hence below; the converse
  fails ((D) has the wrong-sign source). No pinch: the F free region is below, the integral runs from above.
- Partition function / Lee-Yang. Theta is Z = Sum e^{-beta E_rho} with E = (gamma - c)^2 (harmonic
  trap at centre c) and beta = 2 lam; F = Z <E>. Real energies <-> RH: Hilbert-Polya relabelled. Knauf's
  number-theoretical spin chain (CMP 196, 1998; abstract checked via MPI MIS preprint 15/1997) has
  Z = zeta(s-1)/zeta(s) and is ferromagnetic; a Lee-Yang theorem there yields a zero-free HALF-PLANE in
  the temperature variable (the corpus's RH_BARRIER_CRACK note on Bost-Connes says the same: encodes zeta
  as a partition function, not its zeros as a spectrum). No mechanism confines zeros to a line. NIL.
- Tropical lam -> infinity. -(1/(2 lam)) log |Theta(c, lam)| -> min_rho Re (gamma_rho - c)^2 =
  min (x^2 - y^2) along a subsequence (scratch: -0.0766 at lam = 80 vs -0.0875 exact; the cos phase makes
  it a limsup). RH <-> this tropical distance is >= 0 for every c, i.e. y_rho = 0 for every rho: the
  Wall at infinite width is pointwise, the maximiser step (3) of E6Bridge7. No instrument.
- Tauberian lam -> 0. F - F_ord = -Sum_off y^2 (1 + O(lam x^2)) e^{-2 lam x^2} + ..., so positivity at
  width lam at height c is implied by Sum_{|Im rho - c| <= X} y_rho^2 e^{2 lam y_rho^2} <= (1/2) window law
  with X ~ 3/sqrt(lam). For lam -> 0 the right side is ~ log c X^3 and the left is <= (1/4) log c X (count):
  free, and the archimedean-dominance proof of seam B is the prime-side shadow of this counting fact.
  In the band X = O(1): a short-interval zero-density statement at window length O(1), which Ingham /
  Selberg-type N(sigma, T+H) - N(sigma, T) bounds do not reach (they need H >= T^theta). This is the
  S3 / S10 clustering lemma again. UNRESOLVED as a lemma, COLLAPSE_TO_FREE as a foothold.
- Attribution found (checked, arXiv 2312.00108 pp. 1-3, Balanzario-Cardenas, Ramanujan J. 2025):
  Theorem 1 evaluates S(xi, k) = (1/xi) sqrt(k/2pi) Sum_n exp{-2 (k/xi^2)(gamma_n - xi)^2} as
  (1/4pi) log(xi/2pi) - c_2 Sum Lambda(n) n^{-1/2} e^{-xi^2 log^2 n/(4k)} H_{2k}(xi log n/(2 sqrt k)) + E,
  ASSUMING RH and simple zeros. This is the plain Gaussian face Theta at centre xi and width lam = k/xi^2
  with a Hermite-weighted prime side; the corpus's `zeroSide_gaussTest_eq` is the unconditional,
  free-width, k = 1-type (Gaussian-derivative) member. No positivity or equivalence is claimed there.
  Fills one line of the wall map's "no published attribution found" footer.

## 6. Ranked proposals (closure or reduction of the fixed-width residual)

| rank | proposal | cost | establishes | wall |
|---|---|---|---|---|
| P1 | Plain-Gaussian face with width monotonicity: Lean (a) RH <-> Theta >= 0 (E6Bridge7 clone with cos bracket), (b) identity (M) as a convolution lemma over the zero sum, (c) `Lambda_Theta >= lam_cert` from ONE whole-line certificate at lam_cert (ladder + envelope + band at that width) | (a) ~ E6Bridge7 size, (b) ~200 lines (Gaussian convolution with complex centre + Fubini), (c) numerics at one width | an unconditional dBN-type constant for the zero measure, Lambda_Theta >= ~0.4 (T = 6.4e5) or ~0.9 (T = 3e12, crude envelope constant); kills the sub-threshold band for the Theta face | Lambda_Theta = infinity is RH; lam_cert is capped by envelopeC^{-1}(T), doubly exponential cost in lam |
| P2 | Sharpen envelopeC for the Theta face (no polynomial factor in f0; the sharp c_1(lam) ~ 2 pi e^{2 P(lam)} rather than e^{16 lam}) so that P1's lam_cert is as large as the ladder allows | paper + numerics, then a Zeta23-style constant chase | raises lam_cert; each doubling of lam needs T squared-ish | same wall as P1 |
| P3 | Short-interval zero-density lemma at O(1) windows: state the band condition Sum_{|Im rho - c| <= X} y^2 e^{2 lam y^2} <= (1/2) window law as a crisp obligation and search the literature for ANY unconditional local density at fixed-length windows | paper survey, cheap | either a new unconditional strip of the band or a clean statement of why none exists | it is the S3/S10 clustering lemma; likely UNRESOLVED |
| P4 | Calibration numerics: distribution of the on-line margin of Theta and F in the ladder window against the GUE prediction of section 4, to size the band margin P1 must beat at height T - D | numerics only, 1 day | the margin law used in P1(c) is measured, not assumed | establishes nothing unconditional |
| P5 | Hygiene: register the dictionary F = -(1/2) Theta_lam, Theta = 2 int_lam^infinity F, identities (M)/(D), and the Balanzario-Cardenas attribution in the wall map; add the Widder sentence as the one-line explanation of the fixed-width residual | ~50 lines Lean for the identities, doc edits | scope clarity: why widths do not talk to each other on the F face and do on the Theta face | none; no content |

Nothing above collapses the residual to nothing: P1/P2 turn the two-parameter Wall of the Theta face into
one number and push it up at doubly-exponential cost; P3 is the same open lemma as S3/S10; P4/P5 are
instruments and hygiene. A proposal that closes the band at every width is RH, and none is offered.

## 7. Honesty footer

conjecture1_proved = False. Primaries read: Rodgers-Tao 1801.05914 (abstract), Platt-Trudgian 2004.09765
(abstract), GORZ 1902.07321 (abstract), Farmer 2008.07206 (abstract), Ben Arous-Bourgade 1010.1294
(abstract, via search), Bui-Milinovich 1410.3635 (abstract, via search), Knauf 1998 (abstract, MPI preprint
page), Balanzario-Cardenas 2312.00108 (pp. 1-3, Theorem 1 read). Unchecked: Widder 1944 (AMS 403),
Platt-Trudgian Lambda <= 0.2 companion paper, Newman 1976, Csordas-Norfolk-Varga 1986, Littlewood /
Selberg S(t) results (standard, not re-read), Montgomery 1973. The identities (M), (D), the seed identity,
the sign flip and the tropical limit were checked numerically on toy configurations, not proved in Lean;
the RH <-> Theta >= 0 converse is an argued E6Bridge7 clone, not a theorem in the corpus. Single-agent
pass; no blind replication.
