# Literature survey: the Li face and the Gaussian face of the wall (2026-09-21)

conjecture1_proved = False. Nothing in this document proves, or is meant to prove, the Riemann
Hypothesis. The diagonal of the wall is RH in every coordinate system below. Every proposal in
section C is an identity, an implication with a named hypothesis, or a finite unconditional
inequality. Claims I could not check against a primary text are marked UNVERIFIED.

Sources were read as primary texts where possible (arXiv PDFs converted locally; the Connes-Consani
Selecta paper, Lagarias 2007, Bombieri 2000, Burnol 2000, Voros 2016/2022, Coffey 2005, Freitas
2005, Sekatskii 2014, Palojarvi 2020, Suzuki 2026, Groskin 2026 were all read in full or in the
relevant sections). Secondary claims (Wikipedia, search summaries) are flagged as such.

Companion documents: LI_FACE_BRIEF_2026-09-21.md (the campaign's mathematics: Lemmas A, B,
Theorems C, D, the box), WALL_MAP_2026-09-21.md (Gaussian face, sections 0-3, 9),
FIXED_WIDTH_SURVEY_SYNTHESIS_2026-09-21.md (fixed-width lenses, lam_* = 0.597).

## 0. Ten-line summary

1. The campaign's exchange rate "zeros on the line up to height T  =>  lambda_n >= 0 for
   n <= pi T / 2" is, in that explicit termwise form, NOT found in the literature. The folklore
   rate is QUADRATIC: "RH verified to height T_0  =>  lambda_n > 0 for n < T_0^2" (Oesterle,
   uncirculated typescript 2000/2001; Biane-Pitman-Yor 2001, quoted by Coffey 2005 and Voros
   2016/2022). Its only published rigorous form is asymptotic with unspecified constants
   (Lagarias 2007, Theorem 1.1/6.1: n <= T^2 / (2 (log T)^2)).
2. The campaign's termwise Theorem C can be improved by a factor 3 at zero cost: cos(b) <= 0 on
   [pi/2, 3pi/2], so the threshold 2N/pi in Theorem C can be 2N/(3 pi) and Theorem D reads
   n + 1 <= 3 pi T / 2 (section A.1.3; needs the skeptic's eyes before Lean relies on it).
3. Beyond 3 pi T / 2 the termwise method is sharp: a zero with N theta = 2 pi k contributes
   2 - 2 cosh(a) < 0. The quadratic folklore rate needs an aggregate argument (section A.1.4).
4. Numerics: lambda_n rigorously enclosed (ball arithmetic) for n <= 100000 by Johansson
   (2013/2015, Arb); non-rigorous high precision to n = 7000 (Keiper 1992) and ~3300
   (Maslanka 2004). Every computed coefficient is positive.
5. Effective converse: the RH-false asymptotic is lambda_n ~ -Sum_{Re rho' > 1/2} z_{rho'}^{-n}
   (Voros 2006 with 2014 sign erratum; Lagarias 2007 "exponential in n"); an off-line zero
   1/2 + t + iT is invisible until n >~ T^2 / t (Voros). Explicit windows [N1, N2] whose signs
   force zero-free regions: Brown 2005 (one direction flawed), Palojarvi 2020 (both directions,
   explicit but with heavy constants).
6. Reference point a != 1/2 (Sekatskii 2013/2014) does not improve the exchange rate: angle and
   log-modulus both scale by (2a - 1), so the termwise threshold is N (2a - 1) <= 3 pi gamma / 2.
   But Sekatskii's Theorem 5 is a second hypothesis-free source of finitely many rungs at large
   reference points, using only Re s > 1 zero-freeness.
7. Gaussian face: unconditional Weil positivity is known EXACTLY on the prime-free window, test
   support in [2^{-1/2}, 2^{1/2}] (autocorrelation in [1/2, 2]): Yoshida 1992 (finite calculation
   at t = (log 2)/2), Burnol 2000 (some c < sqrt 2), Connes-Consani 2021 (lambda = 2, sharp, with
   vanishing conditions at +-i/2 and a correction c |g^(0)|^2). No result beyond log 2 is known
   (one September 2026 preprint claims more; UNVERIFIED, see B.3).
8. In campaign coordinates the autocorrelation of the Gaussian test has log-x standard deviation
   2 sqrt(lam); the prime-free window log 2 corresponds to lam ~ 0.03 (two sigma) to 0.12 (one
   sigma). The campaign's crude lam0 = 1e-7 is far inside; the numerical c-uniform threshold
   ~0.1 quoted in the wall map matches the window; lam_* = 0.597 is beyond it, as it must be.
9. Non-compact tests: no unconditional positivity for Gaussian-type tests exists in the
   literature; Balanzario-Cardenas (2023/2026) state the Gaussian-Hermite explicit formula only
   under RH. The campaign's hypothesis-free `zeroSide_gaussTest_eq` is stronger than their
   Theorem 1 as an identity.
10. Proposals (section C): five per face, ranked; the two cheapest are the factor-3 termwise
    improvement (Li) and porting Yoshida's finite calculation on the log 2 window (Gaussian).

## A. Li coefficients

### A.1 The exchange rate between verified height and nonnegative rungs

Notation as in the brief: N = n + 1, w = rho/(rho - 1) = r e^{i theta}, a = N log r, b = N theta,
paired term 2 - 2 cosh(a) cos(b).

A.1.1 What the literature states.

* Keiper 1992 (Math. Comp. 58, 765-773, https://doi.org/10.1090/S0025-5718-1992-1122072-5):
  introduced the coefficients (his normalisation lambda_n / n), conjectured the asymptotic
  (1/2)(log n + gamma - log 2 pi - 1), computed to n = 7000. No height-to-index statement.
* Li 1997 (J. Number Theory 65, 325-333): the criterion. No height-to-index statement.
* Bombieri-Lagarias 1999 (J. Number Theory 77, 274-287,
  https://doi.org/10.1006/jnth.1999.2392): the criterion for arbitrary multisets with
  Sum 1/|rho|^2 < infinity, the arithmetic formula, and Theorem 1(c): if some zero is off the
  line the incomplete sums are exponentially large in n (cited this way by Lagarias 2007, p.
  1694). I did not obtain the primary PDF (paywalled); the statements above are as quoted by
  Lagarias 2007 and Freitas 2005. UNVERIFIED that B-L contain any explicit height statement.
* Oesterle, "Regions sans zeros de la fonction zeta de Riemann", typescript 2000, revised 2001,
  uncirculated (cited by Voros 2016 ref [19] and Voros 2022 ref [24]). Voros 2022, section
  2.2.2, states verbatim: "Re rho = 1/2 holds up to a height T_0  =>  lambda_n > 0 as long as
  n < T_0^2", attributing it to Oesterle. Voros 2016 (arXiv 1602.03292, p. 3) attributes the
  same to Oesterle and to Biane-Pitman-Yor. The proof is not available to me. UNVERIFIED.
* Biane-Pitman-Yor 2001 (Bull. AMS 38, 435-465,
  https://www.ams.org/journals/bull/2001-38-04/S0273-0979-01-00912-0/): Coffey 2005 (arXiv
  math-ph/0505052, p. 8) writes "apparently it is already known [BPY] that lambda_n >= 0 for all
  n <= 2.975 x 10^17"; that number is exactly T^2 for T = 5.454 x 10^8 (van de Lune, te Riele,
  Winter 1986, 1.5 x 10^9 zeros). The arXiv v1 of BPY (math/9912170) does not contain the Li
  section; the Bulletin version's Section 2.3 is cited by Lagarias 2007 for a probabilistic
  interpretation. I could not read the Bulletin text. UNVERIFIED at the primary source.
* Coffey 2005 (Math. Phys. Anal. Geom. 8, 211-255, https://doi.org/10.1007/s11040-005-7584-9;
  arXiv math-ph/0505052) and Coffey 2005b "Polygamma theory, the Li/Keiper constants, and
  validity of the Riemann Hypothesis" (arXiv math-ph/0507042, p. 3): "From improved numerical
  calculation to height T ~ 2.38 x 10^12 ... this effectively ensures that approximately the
  first 10^26 lambda_k's are nonnegative." Note (2.38e12)^2 = 5.7e24, not 1e26; Coffey's
  "approximately" is generous by a factor 20. No proof is given; the rule n < T^2 is used as
  known.
* Lagarias 2007 (Ann. Inst. Fourier 57, 1689-1740, https://doi.org/10.5802/aif.2311,
  numdam PDF read): the ONLY published rigorous statement. Define the incomplete Li coefficient
  lambda_n(T) = Sum_{|Im rho| < T} (1 - (1 - 1/rho)^n). Theorem 1.1 / Theorem 6.1
  (unconditional, GL(N) automorphic, so in particular zeta):

      lambda_n = (N/2) n log n + C_1 n - lambda_n(sqrt n) + O(sqrt n log n),
      C_1 = (N/2)(gamma - 1 - log 2 pi) + (1/2) log Q.

  Consequence stated on p. 1694: "if the Riemann hypothesis holds up to height T, then a bound
  of shape O(sqrt n log n) holds for all n <= T^2 / 2 (log T)^2, with the implied O-constant
  depending on pi." This is the quadratic exchange rate, rigorous, with an unspecified constant
  (a contour-integral estimate with |L'/L| = O(log|s|) away from zeros, Lemma 6.2). Lagarias
  also remarks (p. 1695) that with zeros verified to height 10^9 "we may expect the first 10^16
  Li coefficients will also exhibit similar asymptotic behavior".
* Voros 2006 (Math. Phys. Anal. Geom. 9, 53-63, https://doi.org/10.1007/s11040-005-9002-8, arXiv
  math/0506326), Voros 2016 (arXiv 1602.03292), Voros 2022 (arXiv 2204.01036): the RH-true
  asymptotic lambda_n ~ (n/2)(log n + gamma - log 2 pi - 1) (Keiper's conjecture, proved under
  RH; Lagarias improved o(n) to O(sqrt n log n); Arias de Reyna 2011 sharpened it to an
  l^2 criterion), and the RH-false form lambda_n ~ - Sum_{|z_rho'| < 1} z_rho'^{-n}, z_rho = 1 - 1/rho
  (sign corrected in the 2014 erratum, arXiv 1403.4558 refs [23]). Voros 2022 eq. (23): a
  violating zero rho' = 1/2 + t + iT competes with the RH-true growth only when n >~ T^2 / t,
  "the uncertainty principle for the Fourier-conjugate variables theta and n".
* Arias de Reyna 2011 (Funct. Approx. Comment. Math. 45, 7-21,
  https://doi.org/10.7169/facm/1317045228): RH iff (y_m) in l^2 where
  lambda_m / m = (1/2)(log m + gamma - log 2 pi - 1) + y_m. No height statement (abstract only;
  body paywalled).
* Maslanka 2004 (arXiv math/0402168), Sekatskii 2014 (arXiv 1404.7276), Freitas 2005 (arXiv
  math/0507368), Omar-Mazhouda 2007 (J. Number Theory 125, 50-58), Odzak-Smajlovic 2011
  (J. Number Theory 131, 519-535): no height-to-index statement found.

Verdict on A(1): the explicit termwise statement "zeros with |gamma| >= 2N/pi contribute
nonnegatively whether or not on the line" and the resulting linear ladder n + 1 <= pi T/2 are not
in any text I read. The literature's rate is quadratic (n < T^2) but either folklore
(Oesterle, BPY) or asymptotic with an unspecified constant (Lagarias 2007). The campaign's
contribution is the explicit constant and the kernel-checkable termwise proof; its cost is the
exponent (linear, not quadratic).

A.1.2 Why the folklore rate is quadratic. For a zero rho = beta + i gamma with gamma large,
theta ~ 1/gamma and log r ~ (2 beta - 1)/(2 gamma^2), so a ~ N (beta - 1/2)/gamma^2 and the term
is 2 - 2 cosh(a) cos(b). The negative part is at most 2(cosh a - 1) ~ a^2, which is tiny unless
N >~ gamma^2 / (beta - 1/2). Verified zeros below T contribute 2(1 - cos b) >= 0 each. So the
sign of lambda_N is safe until the off-line tail above T can overpower the on-line mass, which
needs N of order T^2. This is Voros's eq. (23) and the content of Lagarias's Theorem 6.1.

A.1.3 A free factor 3 in the campaign's termwise theorem (survey observation, not in the
literature, to be checked by the skeptic). Lemma A of the brief uses |a| <= |b| <= pi/2. But for
pi/2 <= |b| <= 3 pi/2 one has cos(b) <= 0, so cosh(a) cos(b) <= 0 < 1 with no condition on a at
all. Hence:

    Lemma A'. If |a| <= |b| and |b| <= 3 pi/2 then cosh(a) cos(b) <= 1.
    Theorem C'. If |Im rho| >= max(1, 2N/(3 pi)) then Re liPairedSummand (N-1) rho >= 0.
    Theorem D'. Zeros on the line for |Im rho| <= T  =>  0 <= Re taylorCoeff n for n + 1 <= 3 pi T/2.

With T = 4000 (AllZeros_h4000) this is rungs 0..18848 instead of 0..6282; with T = 3 x 10^12
(Platt-Trudgian 2021, Bull. LMS 53, 792-797, arXiv 2004.09765, not in kernel) n + 1 <= 1.4 x 10^13.
The brief's own rung analysis (section 4: "the only region where cos b > 0 with cosh a > 1 is
b in (3 pi/2, 5 pi/3]") already uses this fact for N <= 5 but Theorem C does not.

A.1.4 Where the termwise method stops. At b = 2 pi k the term is 2 - 2 cosh(a) < 0 whenever
a != 0. So no termwise lemma can pass 3 pi/2, and the folklore quadratic rate requires an
aggregate inequality: the negative tail above T, bounded by

    Sum_{|gamma| > T} m(rho) a^2 cosh(a),  a <= N |2 beta - 1| / (2 ((1 - beta)^2 + gamma^2)) <= N/(2 gamma^2)

(using cosh a - 1 <= (a^2/2) cosh a), against the on-line mass Sum_{|gamma| <= T} 2 (1 - cos(N theta)).
The tail is controlled by an unconditional zero count above T (the campaign has the local-count
sum Sum m/(1 + (Im rho - a)^2) = O(log a) in E6Bridge23; explicit counts: Trudgian 2014,
Hasanalizade-Shen-Wong 2022). The on-line mass is a finite sum over verified zeros, computable
for each N but, for N beyond 3 pi T/2, oscillatory: its lower bound is a per-N certificate, or an
equidistribution argument averaged over N-windows (Dirichlet-kernel averages), which does not
give termwise sign statements. This is exactly where Oesterle's typescript would have to live.
See proposal A2.

A.1.5 Is a different constant available from lambda_n ~ (n/2) log n plus tail bounds? Only
asymptotically: Lagarias's O(sqrt n log n) hides a constant depending on explicit
zero-density and |zeta'/zeta| bounds; nobody has made it explicit. Voros 2016/2022 explicitly
say the useful range n >~ 10^25 "looks way beyond reach" numerically.

### A.2 What is numerically known

| who | year | range | rigor | precision | source |
|---|---|---|---|---|---|
| Keiper | 1992 | n <= 7000 | not rigorous | high (Mathematica) | Math. Comp. 58, 765-773 |
| Maslanka | 2004 | n <= ~3300 ("over three thousand") | not rigorous | not stated in abstract | arXiv math/0402168 |
| Coffey | 2005 | bounds, small n by hand | mixed | - | arXiv math-ph/0505052 |
| Johansson | 2013/2015 | n <= 100000 | rigorous ball arithmetic (Arb) | 2900 to 33000 digits | arXiv 1309.2877; Numer. Algorithms 69 (2015) 253-270; data at https://fredrikj.net/math/hurwitz_zeta.html |
| Maslanka | 2022 | analytic extension lambda(s), 3500 complex zeros of it | not rigorous | 14 digits | arXiv 2211.08993 |

Every computed lambda_n is positive; Maslanka's "tiny oscillations" about the smooth trend are
Sf(n) in Lagarias's decomposition, observed |Sf(n)| < 20 for n <= 7000 (Lagarias 2007, p. 1695).
Wikipedia's "positivity verified up to n = 10^5 by direct computation" refers to Johansson
(secondary; https://en.wikipedia.org/wiki/Li%27s_criterion). Johansson's balls are a certified
proof of lambda_n > 0 for n <= 10^5 modulo the software, independent of any zero verification:
this is the numerical analogue of the campaign's hypothesis-free rungs, four orders of magnitude
above rung 4.

Explicit small values: lambda_1 = 1 + gamma/2 - (1/2) log(4 pi) = 0.0230957... (Bombieri-Lagarias
arithmetic formula; also the campaign's rung 0). Higher rungs are explicit in the Stieltjes
constants (Bombieri-Lagarias; Coffey; Maslanka), so rungs 1..4 could be closed either by the
campaign's box argument or by a certified evaluation of the arithmetic formula.

### A.3 Effective converse

* Bombieri-Lagarias 1999, Theorem 1(c) (as cited by Lagarias 2007): an off-line zero makes the
  incomplete coefficients exponentially large. No explicit first negative index.
* Voros 2006/2016/2022: lambda_n ~ - Sum_{|z_rho'|<1} z_rho'^{-n}, |z_rho'|^{-1} = |rho'/(rho'-1)| = r in
  campaign notation, so the amplitude is r^n = e^{a}. Onset n >~ T^2/t for rho' = 1/2 + t + iT.
  This is the campaign's cosh(a) with a = N log r ~ N t / T^2: consistent. The 2014 erratum
  (arXiv 1403.4558, refs [23]-[24]) fixes the sign of the RH-false term in Voros 2006 and in
  Voros's 2010 book.
* Voros 2022 tests the mechanism on the Davenport-Heilbronn counterexamples (off-line zeros
  known explicitly) for his closed-form variant sequence; the campaign's registry already uses
  Davenport-Heilbronn as a negative control.
* Brown 2005 (J. Number Theory 111, 1-32): Theorem 3, finitely many nonnegative Li coefficients
  imply a zero-free region; Theorem 2 (converse) has a flawed Lemma 5 (Palojarvi 2020, p. 2:
  "Brown's Theorem 2 is left unproved").
* Palojarvi 2020 (Albanian J. Math. 14, 47-77, arXiv 1807.01506): for tau-Li coefficients and
  functions with a Riemann-von Mangoldt count (explicit constants A_F, B_F, C_{F,j}):
  Theorem 3.1, if Re lambda_F(n, tau) >= 0 for all n in an explicit window then every zero has
  |rho/(rho - tau)| < R; Theorem 3.3, if some Re lambda_F(n, tau) < 0 for n in [n_0, n_1]
  (n_0, n_1 explicit in R, N_F(T), Lambert W) then some zero has |rho/(rho - tau)| >= R. These are
  the only explicit "which n" statements I found; the constants are unwieldy but the shape is
  the campaign's (a modulus bound r <= R instead of a height bound). Bucur, Ernvall-Hytonen,
  Odzak, Smajlovic 2016 (LMS J. Comput. Math. 19, 259-280) study the numerics for RH-violating
  Dirichlet series.
* Bombieri 2000 (Rend. Lincei (9) 11, 183-233, http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0)
  on the Gaussian face: if RH fails with finitely many off-line zeros, the number of negative
  eigenvalues of large truncations of Weil's form equals half the number of off-line zeros
  (abstract; Theorems 10-11). This is the Weil-side counterpart of "which rung goes negative".

Verdict on A(3): no clean N*(beta, gamma) exists; the literature gives the amplitude r^n, the
onset n ~ T^2/t, and explicit but heavy windows (Palojarvi). The brief's section 6 is correct.

### A.4 Generalisations and reference points

* Selberg class and beyond: Omar-Mazhouda 2007 (J. Number Theory 125, 50-58; corrigendum 130
  (2010) 1109-1114), Smajlovic 2010 (J. Number Theory 130, 828-851), Odzak-Smajlovic 2011
  (J. Number Theory 131, 519-535: full asymptotic expansion of the archimedean part), Lagarias
  2007 (automorphic, above), Droll 2012 (thesis, tau-Li for an extended Selberg class), Mazhouda
  and coauthors, "Variants of the Li-type criteria for GRH" (Springer 2024,
  https://doi.org/10.1007/978-3-031-52163-8_8). All are RH-equivalences plus asymptotics; the
  archimedean part (N/2) n log n + C_1 n is unconditional in every case.
* Freitas 2005 (arXiv math/0507368; published 2006): tau-Li coefficients
  lambda_n(tau) = Sum (1 - (rho/(rho - tau))^n), tau in [1, 2): nonnegative for all n iff no zero
  has Re s > tau/2. tau = 1 is Li. A tau-ladder would trade "on the line up to T" for "in the
  strip Re s <= tau/2 up to T", which is not known for any fixed tau < 2 either, so no free
  hypothesis-free rungs come from it.
* Sekatskii 2013/2014 (arXiv 1304.7895, Ukrainian Math. J. 66, 371-383; arXiv 1404.7276; arXiv
  1403.4484): generalised Bombieri-Lagarias theorem and Li criterion at any real reference point
  a != 1/2: RH iff Sum_rho (1 - ((rho - a)/(rho + a - 1))^n) >= 0 for all n (sign reversed for
  a < 1/2), equivalently nonnegativity of (1/(n-1)!) d^n/dz^n ((z + b)^{n-1} ln xi(z)) at
  z = 1 + b for all b > -1/2 (Theorem 3). Theorem 5 (arXiv 1404.7276, p. 9, proof p. 13): for
  every m there is c(m) such that these derivatives are >= 0 for all n <= m and all b >= c(m).
  The proof uses only that |ln zeta(b + it)| is bounded for b > 1 (Euler product), so the
  zero-dependent part is exponentially small at large b and a positive explicit term dominates.
  This is an unconditional finite-rung theorem at large reference point; it says nothing about
  a = 1 (Li's own coefficients).
* Exchange rate at reference point a. With w_a = (rho + a - 1)/(rho - a),
  |w_a|^2 - 1 = (2 beta - 1)(2a - 1)/|rho - a|^2 and arg w_a ~ (2a - 1)/gamma, so both a and b scale
  by (2a - 1): the termwise threshold becomes N (2a - 1) <= 3 pi gamma / 2. The invariant is the
  "frequency" s = N (2a - 1); no reference point beats a = 1 by more than the trivial rescaling,
  and a -> 1/2 degenerates to a continuous family Sum (1 - cos(2 s gamma/|rho - 1/2|^2)), a
  Weil-type functional with the same termwise threshold s <= 3 pi gamma/4. Verdict on A(4): no.
* Continuous index: Lagarias 2007 section 7 constructs an entire function F(z) of exponential
  type <= pi (under RH) interpolating lambda_n; Maslanka 2022 constructs an even entire lambda(s)
  whose zeros form quadruplets iff RH. Suzuki 2023 (arXiv 2301.05779): each lambda_n is the norm
  of an explicit function in a model space iff RH. These give a third parametrisation of the
  same wall, see proposal A5.

### A.5 Unconditional sign theorems beyond lambda_1

* lambda_1 > 0 is explicit (value above). Coffey 2004 (J. Comput. Appl. Math. 166, 525-534)
  "Relations and positivity results for the derivatives of the Riemann xi function": positivity
  of certain xi-derivative combinations at s = 1/2 and s = 1, unconditional but not a Li
  coefficient beyond n = 1 (abstract only; UNVERIFIED which combinations).
* Sekatskii's Theorem 5 (above): finitely many rungs, any m, at reference points b >= c(m).
* Johansson's certified balls: n <= 10^5 at a = 1, modulo software.
* The campaign's box (Boxes 1 and 2, rungs 0..4): I found no published analogue. The nearest
  classical fact is that zeta has no zeros with |Im s| < 14.13 (numerical), and the elementary
  bound |zeta(s)| via the summation-by-parts representation is textbook (Titchmarsh 2.1); the
  combination into a hypothesis-free rung statement appears new. The brief's remark that rung 5
  fails termwise at (beta, gamma) ~ (0.64, 0.9) is consistent with the folklore that Li's
  criterion carries no information at small n (Voros 2022: "low values of n are actually
  inessential").

## B. Gaussian face: unconditional Weil positivity

### B.1 What is proved, and on what support

Dictionary. Write the test as f(x) on R_+^* with u = log x, and the Weil functional
W(f) = Sum_rho f^(rho) - (pole terms) - Sum_p Sum_k (log p) p^{-k/2} (f(p^k) + f(p^{-k})) - (archimedean term).
Positivity of W on f = g * g^* with g supported in [lambda^{-1/2}, lambda^{1/2}] means f supported
in [1/lambda, lambda], |u| <= log lambda. For lambda <= 2 no prime power enters the finite sum
(2 is at the boundary), so the statement involves only the archimedean distribution against the
zero sum: this is why every unconditional result sits at lambda = 2.

* Yoshida 1992, "On Hermitian forms attached to zeta functions", Zeta functions in geometry
  (Tokyo 1990), Adv. Stud. Pure Math. 21, 281-325 (primary text not accessed). As reported by
  Bombieri 2000 (p. 184, read): Yoshida reproves Weil's criterion; shows positivity on smooth
  even compactly supported functions is equivalent to RH excluding real zeros; reduces
  positivity on [-t, t] to a finite calculation depending on t, and "verifies this positivity
  for t = (log 2)/2"; Lemma 2 gives positivity for t sufficiently small (also Suzuki 2026, p. 2).
  Support of the test function itself [-t, t] with t = (log 2)/2 means autocorrelation support
  |u| <= log 2, i.e. lambda = 2. Yoshida's exact statement at t = (log 2)/2: UNVERIFIED at the
  primary source.
* Bombieri 2000 (Rend. Lincei (9) 11, 183-233, read): variational study; the infimum of the
  functional on the L^2 unit ball of functions supported in [M^{-1}, M] is attained (Theorem 3);
  Theorem 5 claims continuity of the even/odd infima in M (Suzuki 2026 flags this proof as
  needing "a more careful analysis"); Section 12 reproves Yoshida's small-support positivity
  without an explicit constant; Theorems 10-11 give the trichotomy RH / infinitely many
  off-line zeros / an explicit linear relation among x^{-rho}. Bombieri 2003 (part II,
  "Remarks on Weil's quadratic functional in the theory of prime numbers II", cited by Suzuki as
  [2]): not accessed. UNVERIFIED.
* Burnol 2000, "Sur les formules explicites I: analyse invariante", C. R. Acad. Sci. Paris 331,
  423-428, arXiv math/0101068 (read). Theorem 3.7 / Theorem (p. 2): there is c > 1 such that
  Z(k) >= 0 for all smooth g supported in [1/c, c], k = g * g^*. The proof works for c <= sqrt 2
  (so k on [1/2, 2]) by writing Z(k) as an integral of alpha(tau) |g^(1/2 + i tau)|^2 with
  alpha(tau) = 8 sqrt 2 cos(tau log 2)/(1 + 4 tau^2) + h_+(tau), h_+(tau) = -log pi + Re psi(1/4 + i tau/2),
  which tends to +infinity; adding A_eps cos(eps tau), which integrates to zero against |g^|^2
  when g is supported in [e^{-eps/2}, e^{eps/2}], makes the integrand nonnegative. Burnol: "a
  further idea seems necessary to reach c = sqrt 2." So Burnol's c is some unspecified value in
  (1, sqrt 2).
* Connes-Consani 2021, "Weil positivity and trace formula, the archimedean place", Selecta
  Math. 27, 77, https://doi.org/10.1007/s00029-021-00689-4, arXiv 2006.13771 (PDF read).
  Theorem 1: for g in C_c^infinity(R_+^*) supported in [2^{-1/2}, 2^{1/2}] with g^(i/2) = 0 and
  g^(0) = 0, W_infinity(g * g^*) >= Tr(theta(g) S theta(g)^*) >= 0, where S is the projection on
  Sonin's space (even functions vanishing with their Fourier transform on [-1, 1]) and
  W_infinity = -W_R is the archimedean distribution. Theorem 6.11: dropping g^(0) = 0,
  W_infinity(g * g^*) >= Tr(...) - c |g^(0)|^2 with c = 4 gamma/log 2 in the paper's normalisation
  (the introduction phrases the same correction as "as if one would multiply zeta by
  (z - 1/2)^17"; the two numbers differ by the normalisation of g^, so I quote both without
  reconciling them). Corollary 2: c |g^(0)|^2 + Sum_{zeros} g^(s) g^(s-bar) >= Tr(theta(g) S theta(g)^*).
  The paper states (p. 2) that Weil's inequality on (1/2, 2) with the vanishing at +-i/2 "was
  proved in [Yoshida] by reducing it to an explicit computation", and that its own result is a
  strengthening giving a conceptual (operator-theoretic) reason. So lambda = 2 exactly, smooth
  compactly supported tests, two vanishing conditions (the pole terms).
* Connes-Consani-Moscovici 2023/2024, "Zeta zeros and prolate wave operators", arXiv
  2310.18423 (read, introduction): frames Weil positivity as a property P(n) of the quadratic
  form Q_n on tests supported in [1/n, n], involving only primes below n; semilocal prolate
  operator; no new unconditional positivity range. Connes-Consani-Moscovici, "Zeta spectral
  triples", arXiv 2511.22755 (not read).
* Suzuki 2023, "On the Hilbert space derived from the Weil distribution", arXiv 2301.00421
  (Canad. J. Math.), and "Aspects of the screw function", J. London Math. Soc. 2023
  (https://doi.org/10.1112/jlms.12785): unconditional Hilbert-space and de Branges-space
  constructions, "a few partial but unconditional results". Suzuki 2026, "Weil's quadratic
  form via the screw function", arXiv 2606.09096 (read): unified operator framework for
  Yoshida, Bombieri, Connes-Consani, CCM; Theorem 1.3 (continuity of the lowest eigenvalue
  lambda_a in a, unconditional, repairing Bombieri's Theorem 5); Theorem 1.4: for sufficiently
  small a the lowest eigenvalue is positive and simple with lambda_a = log(1/a) + mu_1 - log 2 pi +
  psi(2) - 1 + O(a). No explicit a; Yoshida's window is not enlarged.
* Groskin 2026, "A finite Guinand-Weil dictionary and archimedean tail order for the truncated
  Weil quadratic form", arXiv 2607.02828 (read; July/August 2026 preprint, not peer reviewed):
  for the Connes-van Suijlekom / CCM Galerkin truncations (prime cutoff c, band N, archimedean
  cutoff T), every Galerkin value equals an exact zero sum for a band-limited test (Theorem
  2.5), and the omitted archimedean tail is totally positive with explicit budget
  B_T ~ (2N + 1) rho (log(T/2 pi) + 1)/(pi^2 T) (Theorem 3.2, Corollary 3.3): a finite-cutoff
  eigenvalue >= 0 certifies cutoff-free positivity, one below -B_T certifies negativity, the band
  [-B_T, 0) certifies nothing. This is the same decision shape as the campaign's
  `gaussian_positivity_of_window_dominance`.
* Balanzario-Cardenas Romero 2023/2026, "An explicit formula for the zeros of the Riemann zeta
  function [and the statistics of their local distribution]", arXiv 2312.00108, Ramanujan J. 69
  (2026), https://doi.org/10.1007/s11139-025-01297-y (arXiv version read): Theorem 1 is an explicit
  formula for a Gaussian-weighted zero sum in terms of primes weighted by Hermite polynomials,
  and the note states (p. 4) "Through all this note we assume the validity of the Riemann
  hypothesis". Their application (local zero statistics) uses PNT and Kac's formula. The
  campaign's `zeroSide_gaussTest_eq` (Gaussian-derivative test, dominated convergence, all three
  sides) is the hypothesis-free version of the identity.
* Liu 2026, "Certified Weil positivity beyond the unit window" (alphaXiv, 15 Sept 2026,
  "AI-Native Mathematical Research Lab, Taiwan", stated as under review at Math. Comp.): claims
  Q(f) >= 2^{-151} ||f||^2 for smooth f supported in (-1, 1) and Q(f) >= 2^{-49162} ||f||^2 on
  (-17/16, 17/16), the latter "including prime power 8". If the variable is u = log x for g,
  the autocorrelation reaches |u| <= 2.125 > log 8, far beyond the log 2 window of every
  published result. Preprint, no independent reproduction claimed, constants implausibly small.
  UNVERIFIED; do not rely on it.

### B.2 Translation into (c, lam)

Campaign: F(c, lam) = Re Sum m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2), the zero side of
the autocorrelation f = g * g^* of the Gaussian-derivative test with g^(gamma) = (gamma - c)
exp(-lam (gamma - c)^2). Fourier side in u = log x: exp(-lam gamma^2) has u-standard deviation
sqrt(2 lam), so f has u-standard deviation sigma_f = 2 sqrt(lam), modulated by e^{i c u} and a
second-derivative factor.

| region | width in u | lam equivalent (sigma_f = width) | lam equivalent (2 sigma_f = width) |
|---|---|---|---|
| prime-free window, Yoshida / Burnol / Connes-Consani | log 2 = 0.693 | 0.120 | 0.030 |
| campaign hypothesis-free strip (E6Bridge11) | 2 sqrt(1e-7) = 6.3e-4 | 1e-7 | - |
| campaign numerical c-uniform threshold (wall map section 2) | 2 sqrt(0.1) = 0.63 | 0.1 | - |
| campaign sharp envelope lam_* = 0.597 above T = 640000 | 2 sqrt(0.597) = 1.55 | 0.597 | - |
| Liu 2026 claim (UNVERIFIED) | 2.125 | 1.13 | 0.28 |

Readings. (i) The campaign's proved strip lam <= 1e-7 is three orders of magnitude narrower in
u than the classical prime-free window; the mechanism (archimedean dominance against the prime
bound 64 A exp(-(log 2)^2/(16 lam))) is the Gaussian shadow of the same window, since
(log 2)^2/(16 lam) is exactly the prime-2 term's Gaussian suppression. (ii) The numerical
c-uniform threshold ~0.1 corresponds to sigma_f = 0.63, i.e. the log 2 window at one sigma: the
numerics and the literature agree on where the free region ends. (iii) lam_* = 0.597 lies beyond
the window by a factor 2.2 in u, so it must consume the ladder; consistent with the wall map.
(iv) Gaussian tests are not compactly supported, so Connes-Consani's theorem does not transfer
verbatim: the tail |u| > log 2 carries prime terms, exponentially small in 1/lam but nonzero, and
the two vanishing conditions at +-i/2 are the pole terms the campaign carries explicitly.

### B.3 Unconditional positivity for non-compact tests

None in the literature. Suzuki's unconditional Hilbert spaces are completions of compactly
supported functions; Bombieri's and Yoshida's results are on [-t, t]; Connes-Consani's on
[2^{-1/2}, 2^{1/2}]. The campaign's `re_weilForm_gauss_nonneg` (lam <= 1e-7, all c) and
`gaussian_positivity_envelope` (|c| >= envelopeC lam) are, to my knowledge, the only
hypothesis-free positivity statements for a non-compactly supported family; the price is the
tiny width.

## C. Proposals

Each: statement, input, what it would NOT prove. Ranked by plausibility within each face. None
touches the diagonal.

### C.1 Li face

A1 (plausibility: very high, cost: hours). Theorem C' / D' with threshold 2N/(3 pi).
Statement: if |Im rho| >= max(1, 2N/(3 pi)) then Re liPairedSummand (N-1) rho >= 0; hence zeros
on the line for |Im rho| <= T give 0 <= Re taylorCoeff n for all n + 1 <= 3 pi T/2. Input: Lemma B
as is; the case split b <= pi/2 (Lemma A) versus pi/2 < b <= 3 pi/2 (cos b <= 0). Would not
prove: any rung beyond 3 pi T/2; anything about zeros. Skeptic first: check the sign convention
of theta for gamma < 0 and the multiplicity weighting.

A2 (plausibility: high for the inequality, low for turning it into a theorem beyond 3 pi T/2;
cost: days for the inequality). The aggregate (Oesterle-Lagarias) ladder.
Statement (hypothesis: zeros on the line for |Im rho| <= T; T >= 2; any N):
    Re taylorCoeff (N-1) >= Sum_{|gamma| <= T} 2 m(rho) (1 - cos(N theta_rho))
                            - cosh(N/(2 T^2)) (N^2/4) Sum_{|gamma| > T} m(rho)/gamma^4.
Input: cosh a - 1 <= (a^2/2) cosh a; Lemma B's |log r| <= 1/(2 gamma^2); an unconditional
explicit bound for Sum_{|gamma| > T} m(rho)/gamma^4 (from E6Bridge23's local-count sum by dyadic
blocks, or an explicit Riemann-von Mangoldt count). The first sum is a finite computable
quantity; for N <= 3 pi T/2 it is termwise nonnegative and A1 already covers that range, so A2
only matters for N > 3 pi T/2, where its lower bound is a per-N Arb certificate (the finite sum
over the verified zeros), not a theorem. Would not prove: a termwise statement; the folklore
n < T^2 as a theorem (that needs a lower bound on the oscillatory finite sum uniform in N).
It would, however, give a rigorous per-N certificate with reach ~T^2 instead of ~T, which is
the honest content of Coffey's "10^26".

A3 (plausibility: medium, cost: weeks). Explicit converse window in the campaign's vocabulary.
Statement: if some zero rho_0 has r_0 = |rho_0/(rho_0 - 1)| >= R > 1 then Re taylorCoeff (N-1) < 0
for some N in an explicit window depending on R, |rho_0| and an unconditional upper bound U(N)
for the remaining sum. Input: an unconditional upper bound Sum_rho |liPairedSummand| over the
other zeros, which needs an unconditional bound on the count and on r for all zeros (r <= R
for all zeros is Palojarvi's hypothesis, and is not available unconditionally). Would not
prove: a first negative index for a hypothetical zero without also bounding all other zeros;
this is why the brief's section 6 says "which rung depends on the whole zero set". Palojarvi
2020 is the template; her constants show the cost.

A4 (plausibility: high as a formalisation, low as information; cost: days). Sekatskii's
Theorem 5 in the kernel: for each m there is c(m) such that the generalised Li derivatives at
1 + b are nonnegative for n <= m and b >= c(m). Input: the Euler product bound
|log zeta(b + it)| <= zeta(b) - 1 for b > 1 (Mathlib has the Euler product), Cauchy estimates,
the explicit positive term (n/2)(log(b + 1/2) + ...) of Sekatskii's eq. (7). Would not prove:
anything at a = 1; RH. Value: a second hypothesis-free source of rungs, complementary to the
box, and a check that "finitely many rungs are free" is the generic situation, not a feature of
the box.

A5 (plausibility: high, cost: days, value: dictionary only). The continuous-index Li family
as the third coordinate system of the wall. Statement: for real s >= 1 define
L(s) := Sum m(rho) (2 - 2 cosh(s log r_rho) cos(s theta_rho))/2 (absolutely convergent by the weighted
genus theorem); then L(N) = Re taylorCoeff (N-1), L is real-analytic, and B7's closed form gives
L(s) = arch(s) + finite(s) for real s (Maslanka 2022's lambda(s) and Lagarias 2007's F(z) are
this object). Row for the wall map: the Li family probes zeros at height ~ s with unit
resolution, the Gaussian family probes offset delta at width 1/delta^2 at every height, and the
two are related by the Fourier transform of the kernel 1 - cos(s theta) in the height variable.
Would not prove: any sign statement. It would make section 7 of wall map v2 precise.

### C.2 Gaussian face

B1 (plausibility: high, cost: weeks). Port Yoshida's finite calculation on the prime-free
window. Statement: for the archimedean distribution W_infinity of Connes-Consani (equivalently
the campaign's archSide minus pole terms), W_infinity(f) >= 0 for every smooth f = g * g^* with g
supported in [2^{-1/2}, 2^{1/2}] and g^(+-i/2) = 0. Input: Burnol's kernel identity
Z(k) = Int (8 sqrt 2 cos(tau log 2)/(1 + 4 tau^2) + h_+(tau)) |g^(1/2 + i tau)|^2 dtau/2 pi on that support
(a one-page computation from the explicit formula) plus a certified lower bound on alpha(tau)
with the Burnol trick A_eps cos(eps tau) for a numerically chosen eps < log 2; or Connes-Consani's
Sonin-space argument (much heavier: prolate functions, Toeplitz matrices). Would not prove:
positivity for any prime-carrying support; positivity of F(c, lam) for any lam, because the
Gaussian tail is not zero (see B2). Value: the Gaussian face gets the same foothold the
literature has, in the kernel, and Burnol's "further idea needed to reach c = sqrt 2" becomes a
precise open lemma rather than a remark.

B2 (plausibility: medium-high, cost: weeks). Raise lam0 from 1e-7 toward 1e-2 hypothesis-free.
Statement: for all c and all 0 < lam <= lam1 (target lam1 in [0.01, 0.03]), F(c, lam) >= 0.
Input: replace the Stirling lower bound on Re psi(1/4 + i r/2) by the exact kernel h_+ plus
Burnol's cos(tau log 2) term (which is the prime-2 term written on the spectral side, so it is
what the campaign's 64 A exp(-(log 2)^2/(16 lam)) bound throws away); keep the pole terms
explicit. The Burnol correction A_eps cos(eps tau) is no longer exactly zero on the zero side
for a Gaussian, but its contribution is exp(-eps^2/(16 lam))-small and can be absorbed. Would
not prove: anything at lam near lam_* = 0.597; the diagonal. Value: the free region's edge
would sit where the numerics (0.1) and the literature (log 2) say it is, up to a factor 3-10,
instead of five orders of magnitude below.

B3 (plausibility: high, cost: days, value: validation). Adopt Groskin's explicit tail budget as
an independent cross-check of `gaussian_positivity_of_window_dominance`. Statement: in the
ladder-certified region, the finite window sum exceeds the tail envelope
exp(2 (lam - 1)(1/4 - D^2)) constB c; Groskin's B_T ~ (2N + 1) rho (log(T/2 pi) + 1)/(pi^2 T) is the
Galerkin analogue and the two envelopes should agree in order of magnitude at matched cutoffs.
Input: numerics only. Would not prove: anything beyond the ladder; it is a consistency test of
two independent truncation calculi (preprint status of Groskin noted).

B4 (plausibility: medium, cost: weeks). Off-line zero counting in (c, lam) coordinates, after
Bombieri's Theorems 10-11. Statement: if zeta has exactly k pairs of off-line zeros then for
every lam above an explicit lam_k(T) the negative set {c : F(c, lam) < 0} has at least k
components, one near each off-line ordinate. Input: E6Bridge7's `gaussian_dominance` (each
off-line zero carves a negative region) plus a separation argument. Would not prove: RH or
any zero location; it sharpens the dictionary "negative eigenvalue count = half the off-line
zero count" into the Gaussian family. Value: a negative-control theorem with a clean
statement; low priority.

B5 (plausibility: high, cost: days, value: writeup). State the campaign's Gaussian explicit
formula as the hypothesis-free Balanzario-Cardenas identity. Statement: for every c, lam > 0,
Sum m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2) = archSide - primeSide where primeSide is
the prime sum with Gaussian-times-Hermite weights (their Theorem 1 has H_k; the campaign's
(gamma - c)^2 prefactor is the k = 2 case up to normalisation). Input: `zeroSide_gaussTest_eq`
already proved; only a change of variables. Would not prove: anything new; it records that the
identity is unconditional and pins the comparison to a 2026 journal paper that assumes RH for it.

## D. Reading list with locators

* Keiper, Math. Comp. 58 (1992) 765-773. https://doi.org/10.1090/S0025-5718-1992-1122072-5
* Li, J. Number Theory 65 (1997) 325-333.
* Bombieri, Lagarias, J. Number Theory 77 (1999) 274-287. https://doi.org/10.1006/jnth.1999.2392
* Bombieri, Rend. Lincei (9) 11 (2000) 183-233. http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0
* Burnol, C. R. Acad. Sci. Paris 331 (2000) 423-428. https://arxiv.org/abs/math/0101068
* Biane, Pitman, Yor, Bull. AMS 38 (2001) 435-465. https://arxiv.org/abs/math/9912170 (arXiv v1 lacks the Li section)
* Maslanka, arXiv math/0402168 (2004). https://arxiv.org/abs/math/0402168
* Coffey, Math. Phys. Anal. Geom. 8 (2005) 211-255. https://arxiv.org/abs/math-ph/0505052
* Coffey, arXiv math-ph/0507042 (2005). https://arxiv.org/abs/math-ph/0507042
* Voros, Math. Phys. Anal. Geom. 9 (2006) 53-63. https://arxiv.org/abs/math/0506326 ; erratum in https://arxiv.org/abs/1403.4558
* Freitas, arXiv math/0507368 (2005). https://arxiv.org/abs/math/0507368
* Brown, J. Number Theory 111 (2005) 1-32.
* Lagarias, Ann. Inst. Fourier 57 (2007) 1689-1740. https://doi.org/10.5802/aif.2311
* Omar, Mazhouda, J. Number Theory 125 (2007) 50-58; corrigendum 130 (2010) 1109-1114.
* Odzak, Smajlovic, J. Number Theory 131 (2011) 519-535.
* Arias de Reyna, Funct. Approx. 45 (2011) 7-21. https://doi.org/10.7169/facm/1317045228
* Sekatskii, arXiv 1304.7895 (Ukrainian Math. J. 66 (2014) 371-383); arXiv 1404.7276; arXiv 1403.4484.
* Johansson, Numer. Algorithms 69 (2015) 253-270. https://arxiv.org/abs/1309.2877 ; https://fredrikj.net/math/hurwitz_zeta.html
* Voros, arXiv 1602.03292 (2016); arXiv 1703.02844 (2017); arXiv 2204.01036 (2022).
* Bucur, Ernvall-Hytonen, Odzak, Smajlovic, LMS J. Comput. Math. 19 (2016) 259-280.
* Palojarvi, Albanian J. Math. 14 (2020) 47-77. https://arxiv.org/abs/1807.01506
* Platt, Trudgian, Bull. LMS 53 (2021) 792-797. https://arxiv.org/abs/2004.09765
* Connes, Consani, Selecta Math. 27 (2021) 77. https://arxiv.org/abs/2006.13771
* Maslanka, arXiv 2211.08993 (2022).
* Suzuki, arXiv 2301.00421 (2023); arXiv 2301.05779 (2023); J. London Math. Soc. (2023) https://doi.org/10.1112/jlms.12785 ; arXiv 2606.09096 (2026).
* Connes, Consani, Moscovici, arXiv 2310.18423 (2023/2024); arXiv 2511.22755 (2025).
* Balanzario, Cardenas Romero, arXiv 2312.00108 (2023); Ramanujan J. 69 (2026) https://doi.org/10.1007/s11139-025-01297-y
* Groskin, arXiv 2607.02828 (2026, preprint).
* Liu, alphaXiv "Certified Weil positivity beyond the unit window" (Sept 2026, preprint, UNVERIFIED).
* Yoshida, Adv. Stud. Pure Math. 21 (1992) 281-325 (not accessed; cited via Bombieri 2000, Connes-Consani 2021, Suzuki 2026).

## E. Follow-up: the archimedean side for Gaussian tests (Burnol/Yoshida kernels, Binet)

conjecture1_proved = False. Everything here is about the archimedean term of the explicit formula,
an identity valid whether or not RH holds. Notation: the island's test has autocorrelation
f(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)} e^{-icu}, spectral profile h(r) = (r - c)^2 e^{-2 lam (r - c)^2}
(so h(r) = Int f(u) e^{iru} du up to the normalising constant A = sqrt(pi/(2 lam))/(4 lam), and the
modulus profile f_0(u) := A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)} satisfies Int h(r) cos(ru) dr = f_0(u) cos(cu)),
and the archimedean side is

    arch(c, lam) = (1/2 pi) Int h(r) Re psi(1/4 + i r/2) dr - (log pi) (1/2 pi) Int h(r) dr + h(i/2) + h(-i/2).

### E.1 Exact statements of the small-support positivity results, and what they give off support

Burnol 2000 (C. R. Acad. Sci. Paris 331, 423-428, arXiv math/0101068, Theorem 3.7, read). For g
smooth with compact support in (0, infinity), k = g * g^*, g^ its Mellin transform on Re s = 1/2,
and Z(k) := Sum_rho g^(rho) g^(1 - rho) (zero side), the explicit formula for k supported in [1/2, 2]
(no prime power enters) reads

    Z(k) = 2 Re k^(0) + Int_{s = 1/2 + i tau} h_+(tau) |g^(s)|^2 dtau/(2 pi),
    h_+(tau) = - log pi + Re psi(1/4 + i tau/2),

where 2 Re k^(0) is the pole term. Burnol's trick is the identity, valid ONLY for k supported in
[1/2, 2], rewriting the pole term spectrally: 2 Re k^(0) = Int 8 sqrt 2 cos(tau log 2)/(1 + 4 tau^2) |g^|^2 dtau/(2 pi),
so that Z(k) = Int alpha(tau) |g^(s)|^2 dtau/(2 pi) with alpha(tau) = 8 sqrt 2 cos(tau log 2)/(1 + 4 tau^2) + h_+(tau).
Since alpha -> +infinity, for small eps there is A_eps with A_eps cos(eps tau) + alpha(tau) >= 0 for all tau,
and Int cos(eps tau) |g^|^2 dtau = 0 when g is supported in [e^{-eps/2}, e^{eps/2}]; hence Z(k) >= 0 for
support in [1/c, c], c = e^{eps/2}, some c in (1, sqrt 2), not made explicit ("computer calculations
help being more precise").

Yoshida 1992 (Adv. Stud. Pure Math. 21, 281-325; primary text NOT accessed, UNVERIFIED). As
reported by Bombieri 2000 (p. 184) and Suzuki 2026 (p. 2): the Hermitian form H(v, v) = W(v * v~) on
smooth functions supported in [-t, t] (variable u = log x), or on K(t) = {smooth 2t-periodic
functions restricted to [-t, t]}; Lemma 2: positive definite for t sufficiently small; positivity
on [-t, t] "reduced to a finite calculation depending on t" and verified for t = (log 2)/2 (again
the prime-free window, autocorrelation in [1/2, 2]). Normalisation of W: Bombieri's Explicit
Formula (2000, p. 186, read): Sum_rho f^(rho) = Int_0^inf f + Int_0^inf f^* - Sum Lambda(n)(f(n) + f^*(n))
- (log 4 pi + gamma) f(1) - Int_1^inf (f(x) + f^*(x) - (2/x^2) f(1)) x dx/(x^2 - 1), and the last two
terms equal -(log pi) f(1) + (1/2 pi i) Int_{(1/2)} (Gamma'/Gamma)(w/2) f^(w) dw. So Yoshida's and
Burnol's archimedean term is the same h_+ integral; only the pole-term bookkeeping differs.

Off support. Neither result yields a lower bound for the archimedean form on non-compactly
supported f, for two separate reasons. (a) h_+(tau) is NOT nonnegative: h_+(0) = -log pi + psi(1/4)
= -1.145 - 4.227 = -5.37, and h_+ < 0 for |tau| < ~4 (numerically Re psi(1/4 + i tau/2) crosses
-log pi = -1.145 near tau ~ 2). So the archimedean term is not a positive-definite kernel by itself;
the positivity of the prime-free window comes from the POLE term absorbing the negative part of
h_+ at small tau, and Burnol's spectral rewriting of the pole term is exactly the step that needs
support in [1/2, 2] (it uses k^(s)/s and the vanishing of Int k(u) u^{s-1} du outside the window).
(b) The A_eps cos(eps tau) correction integrates to zero only against tests supported in
[e^{-eps/2}, e^{eps/2}]; for a Gaussian its contribution is Gaussian-small, of size
A_eps f_0(eps) ~ A_eps e^{-eps^2/(8 lam)}, not zero. What survives off support is only the
pointwise inequality alpha(tau) + A_eps cos(eps tau) >= 0, i.e. a lower bound on h_+ by an explicit
elementary function, which is the content of E.3 below, and the fact (for the island's test) that
the two pole terms are themselves nonnegative:

    h(i/2) + h(-i/2) = 2 (c^2 + 1/4) e^{lam/2} e^{-2 lam c^2}     [from g^(gamma) = (gamma - c) e^{-lam (gamma - c)^2};
                                                                   check the island's sign convention for the pole terms].

Connes-Consani 2021 add nothing here: Theorem 1 requires support in [2^{-1/2}, 2^{1/2}] for the Sonin
compression, and the constant c |g^(0)|^2 in Theorem 6.11 is a correction, not a lower bound.

### E.2 Binet's formula turns the digamma integral into a one-dimensional elementary integral

For Re z > 0 (here z = 1/4 + i r/2, so Re z = 1/4 uniformly in r):

    psi(z) = log z - 1/(2z) - Int_0^inf phi(t) e^{-zt} dt,   phi(t) = 1/(e^t - 1) - 1/t + 1/2,

with 0 < phi(t) < 1/2, phi(t) ~ t/12 at 0, phi increasing to 1/2 (DLMF 5.9.13 form of Binet's first
formula for psi). Taking real parts with |z|^2 = 1/16 + r^2/4 and Re(1/(2z)) = 1/(8 |z|^2):

    Re psi(1/4 + i r/2) = (1/2) log(1/16 + r^2/4) - 1/(8 (1/16 + r^2/4)) - Int_0^inf phi(t) e^{-t/4} cos(rt/2) dt.

Integrating against h(r) >= 0 and using Fubini (h Gaussian, phi bounded), with u = t/2:

    (1/2 pi) Int h(r) Re psi(1/4 + i r/2) dr
      = (1/2 pi) Int h(r) [ (1/2) log(1/16 + r^2/4) - 1/(8 (1/16 + r^2/4)) ] dr
        - (1/pi) Int_0^inf phi(2u) e^{-u/2} f_0(u) cos(cu) du.                                   (E.2.1)

Checked numerically (mpmath, 30 digits) at (c, lam) = (30, 0.05): both sides 75.65474981..., relative
error 2e-30. The second line is the one-dimensional integral the team lead guessed: the c-dependence
sits in cos(cu), the kernel phi(2u) e^{-u/2} = (1/(e^{2u} - 1) - 1/(2u) + 1/2) e^{-u/2} is elementary,
and this is nothing but Bombieri's x dx/(x^2 - 1) term with x = e^u after the change of variables
(e^{-u/2}/(e^{2u} - 1) = e^{-u/2} e^{-2u}/(1 - e^{-2u}); the -1/(2u) piece is the f(1) subtraction). So
Binet is the derivation of Weil's classical archimedean kernel, not a new representation; what is
new for Gaussian tests is only that Int h(r) cos(ru) dr = f_0(u) cos(cu) is closed-form.

Closed forms. (i) The kernel piece: expand 1/(e^{2u} - 1) = Sum_{k >= 1} e^{-2ku}; each term
Int_0^inf e^{-(2k + 1/2) u} e^{-u^2/(8 lam)} (1 - u^2/(4 lam)) cos(cu) du is a Gaussian times the complementary
error function of the complex argument (2k + 1/2 - ic) sqrt(2 lam) (Faddeeva w-function), so the
whole piece is a convergent erfc series; the -1/(2u) e^{-u/2} piece integrates to an exponential
integral against the Gaussian. No published source does this for the island's test: Balanzario-
Cardenas (arXiv 2312.00108, Theorem 1) work on the PRIME side with Hermite weights, under RH, and
handle the archimedean side by asymptotics; Bombieri 2000 works with compactly supported f;
Lagarias 2006, "Hilbert spaces of entire functions and Dirichlet L-functions" (Frontiers in
Number Theory, Physics, and Geometry I, 365-377) uses de Branges spaces, no Gaussians (from
memory, UNVERIFIED). The Gaussian explicit formula in E6Bridge10 is, as far as I can find, the
only place the full identity is written for this family. (ii) The log piece
Int h(r) log(1/16 + r^2/4) dr has no elementary closed form for c != 0; its derivative in the
parameter b^2 = 1/16 is Int h(r)/(b^2 + r^2/4) dr, and for a centred Gaussian
Int e^{-a r^2}/(r^2 + b^2) dr = (pi/b) e^{a b^2} erfc(b sqrt a) is classical, so the c = 0 value is an
erfc integral in b; for general c one uses the lower bound in E.3 instead.

### E.3 Explicit c-uniform lower bounds for the archimedean side

Two pointwise bounds, both elementary, both checked numerically at r in {0, 0.1, 0.5, 1, 2, 5, 10,
50, 1e3, 1e5} against mpmath's psi (equality at r = 0 for the first):

    (B) Re psi(1/4 + i r/2) >= (1/2) log(1/16 + r^2/4) - 1/(8 (1/16 + r^2/4)) - 0.84116,
        0.84116 = Int_0^inf phi(t) e^{-t/4} dt = log(1/4) - 2 - psi(1/4)   [exact, from Binet at z = 1/4];
    (S) Re psi(1/4 + i r/2) >= (1/2) log(1/16 + r^2/4) - 1/(8 |z|^2) - 1/(6 |z|^2),
        from the Stirling remainder bound |psi(z) - log z + 1/(2z)| <= (1/(12 |z|^2)) sec^2(arg z / 2)
        with |arg z| < pi/2 (DLMF 5.11(ii)-type bound; the psi version is UNVERIFIED as a cited
        theorem, numerically valid at the sampled points).

(B) follows from |cos| <= 1 and phi > 0 in the Binet integral; it is tight at r = 0 and loses
exactly 0.84 at large r. (S) is tight at large r and loses 1.8 at r = 0. Compared with the island's
Re psi(1/4 + i r/2) >= log(|r|/2) - 5 (wall map, section 2), (B) gives log(|r|/2) - 2.84 uniformly
(since (1/2) log(1/16 + r^2/4) >= log(|r|/2) and 1/(8 |z|^2) <= 2), i.e. an improvement of 2.16 in the
additive constant, uniformly in r and hence in c, and it is finite at r = 0 where the old bound
is -infinity. Integrated against the Gaussian profile, (E.2.1) gives the c-uniform statement

    arch(c, lam) >= (1/2 pi) Int h(r) [ (1/2) log(1/16 + r^2/4) - 1/(8 (1/16 + r^2/4)) - 0.84116 - log pi ] dr
                    + 2 (c^2 + 1/4) e^{lam/2 - 2 lam c^2},

with the last term subject to the pole-term sign check above. The kernel piece can be kept
exactly as the one-dimensional integral - (1/pi) Int_0^inf phi(2u) e^{-u/2} f_0(u) cos(cu) du if one
wants c-dependence beyond a uniform bound; its absolute value is at most
(1/pi) Int_0^inf phi(2u) e^{-u/2} |f_0(u)| du, a lam-only quantity.

Published explicit c-uniform lower bounds for the archimedean side: none found. Burnol states
only alpha(tau) -> +infinity; Connes-Consani give W_R as "a locally rational positive function
tending to +infinity at 1" outside x = 1 (Appendix B, formula (150)), which is the kernel
e^{-u/2}/(1 - e^{-2u}) in u; the explicit-formula literature (Bombieri 2000, Lagarias 2007 Lemma 6.2,
Groskin 2026 Lemma 3.1 with h_+(r) <= log r as an UPPER envelope) uses O(log) bounds without
constants. The Stirling-type bound (S) is the standard tool (e.g. in explicit zero-density papers
such as Trudgian 2014, Hasanalizade-Shen-Wong 2022, for Re(Gamma'/Gamma)) but I found no paper
stating it for the Gaussian family or in c-uniform form; the island's E6Bridge11 constant is, to my
knowledge, the only kernel-checked one, and (B) is the cheap way to sharpen it.

What this does not give: positivity of arch - prime for any lam beyond what the island's prime
bound allows; the prime side is untouched by everything above. conjecture1_proved = False.

conjecture1_proved = False.
