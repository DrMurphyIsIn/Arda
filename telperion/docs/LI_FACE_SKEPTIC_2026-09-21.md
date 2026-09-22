# Skeptic review of the Li-face brief (2026-09-21)

conjecture1_proved = False. Nothing below is progress on the Riemann Hypothesis. Every
statement checked is an identity, a finite inequality, or an implication with a named hypothesis.

Reviewed: `docs/LI_FACE_BRIEF_2026-09-21.md`, sections 2 to 5, against the upstream definitions
in the LiCriterion snapshot (`Basic.lean`: `liSummand` at line 2780, `liPairedSummand` at 2787,
`pairedZero_val` at 1655, `taylorCoeff` at 525, `riemannXi` at 1236), the li island files
`AllZeros_h4000.lean`, `AllZerosUpToHeight.lean`, `ZetaZeroConfinement.lean`, and the rvm island
files `E6Bridge15.lean`, `E6Bridge19.lean`, `E6Bridge20.lean`, `E6Bridge25.lean`, `E6Bridge27.lean`.
Numerics: mpmath, 25 to 30 digits, script `li_skeptic.py` (scratchpad; not committed).

Summary: no REFUTED item. Eight CORRECTED items, all fixable, three of which change what the
Lean formalizers must build (items 5, 8, 10). The rest are CONFIRMED.

## Verdicts

1. CONFIRMED. Section 2 identity. With the upstream definitions
   `liSummand n rho = 1 - (1 - 1/rho)^(-(n+1))` (zpow, integer exponent) and
   `(pairedZero rho).val = 1 - rho`, put N = n + 1 and w = rho/(rho - 1). Then
   1 - 1/rho = 1/w, so `liSummand n rho = 1 - w^N`; and 1 - 1/(1 - rho) = -rho/(1 - rho) = w,
   so `liSummand n (pairedZero rho) = 1 - w^(-N)`. Sum: 2 - w^N - w^(-N). With w = r e^{i theta},
   Re = 2 - r^N cos(N theta) - r^(-N) cos(-N theta) = 2 - (r^N + r^(-N)) cos(N theta)
   = 2 - 2 cosh(N log r) cos(N theta). Checked to 1e-28 on 3000 random (rho, n).
   Sign conventions all correct. w is defined because rho is not 0 or 1 (0 < Re rho < 1).
   Two notes for the formalizers: (a) the pair term is NOT real in general; its imaginary part
   is -(r^N - r^(-N)) sin(N theta) (for example -0.3498 at rho = 0.3 + 2i, n = 3). Only the
   full sum is real. Take Re of each term, do not expect `liPairedSummand` itself to be real.
   (b) The involution rho -> 1 - rho sends w to 1/w, i.e. (log r, theta) -> (-log r, -theta),
   as the brief says.

2. CONFIRMED. Lemma A: cosh(a) cos(b) <= 1 for |a| <= |b| <= pi/2. Both functions are even,
   so take 0 <= a <= b <= pi/2. cos is decreasing on [0, pi/2] and cos b >= 0 there, and
   cosh a >= 1 > 0, so cosh(a) cos(b) <= cosh(a) cos(a). Then f(a) = cosh a cos a has f(0) = 1
   and f'(a) = sinh a cos a - cosh a sin a = cosh a cos a (tanh a - tan a) <= 0 on [0, pi/2)
   because tanh a <= a <= tan a; at a = pi/2, f = 0. Grid check: min of 1 - cosh a cos b over
   the region is 0 (attained only at a = b = 0). The proof in the brief is right as written.
   Lean hint: prove tanh a <= a via sinh a <= a cosh a (derivative of a cosh a - sinh a is
   a sinh a >= 0) and a <= tan a via Mathlib `Real.lt_tan` / `Real.le_tan`.

3. CONFIRMED. Lemma B, exact angle and the two upper bounds. For rho = beta + i gamma,
   gamma > 0: arg rho = pi/2 - arctan(beta/gamma), arg(rho - 1) = pi/2 + arctan((1 - beta)/gamma),
   so theta = arg w = -(arctan(beta/gamma) + arctan((1 - beta)/gamma)), which lies in (-pi, 0),
   so no branch issue with the principal argument; |theta| is the stated sum (checked to 1e-17).
   theta is negative for gamma > 0; only cos(N theta) is used, so the sign is harmless.
   |theta| <= 1/gamma from arctan x <= x. For the modulus, WLOG beta >= 1/2:
   log r = (1/2) log(1 + (2 beta - 1)/((1 - beta)^2 + gamma^2)) <= (1/2)(2 beta - 1)/((1 - beta)^2
   + gamma^2), and min(beta, 1 - beta) = 1 - beta; the beta < 1/2 case is the mirror. Then
   <= 1/(2 gamma^2) since |2 beta - 1| < 1. Checked: max over 2000 random points of
   |log r| - refined bound is -6.7e-14 (never positive).

4. CORRECTED. Lemma B, the claim "|log r| <= |theta| whenever gamma >= 1 (needs only
   gamma >= 2/pi)". The STATEMENT is true, and in fact stronger: numerically the inequality
   |log r| <= |theta| holds for every beta in (0, 1) as soon as gamma >= 0.2852 (worst beta is
   the strip edge beta -> 0 or 1; at gamma = 0.3, beta -> 0: |theta| = 1.2793, |log r| = 1.2471).
   But the PROOF route in the brief does not reach 2/pi: the step |theta| >= pi/(4 gamma) uses
   arctan x >= (pi/4) x, valid only for x <= 1, i.e. it needs gamma >= max(beta, 1 - beta).
   Without confinement that means gamma >= 1. Concrete failure of the intermediate bound:
   gamma = 0.64, beta -> 0 gives |theta| = arctan(1/0.64) = 1.0014 < pi/(4 * 0.64) = 1.2272.
   Fix: state the lemma as "|log r| <= |theta| for gamma >= 1", which is all Theorem C uses,
   and add the separate confined version "for gamma >= 2/pi and max(beta, 1 - beta) <= gamma"
   for section 4 (there the box gives (1 - beta)/gamma <= 0.911 for gamma < 1, so it applies).
   Worst beta at gamma = 1 is the edge, margin |theta| - |log r| = 0.4393.

5. CORRECTED. Theorems C and D. The exchange rate is right: |b| = N|theta| <= N/gamma <= pi/2
   iff gamma >= 2N/pi, and gamma >= 1 feeds Lemma B, so the hypothesis |Im rho| >= max(1, 2N/pi)
   is exactly what the proof consumes; for T >= 1 every zero with |Im| > T satisfies it when
   N <= pi T/2. With T = 4000: pi T/2 = 6283.18, so n <= 6282; with T = 3e12: 4.71e12. The
   on-line case gives r = 1 exactly (|rho| = |rho - 1| when Re rho = 1/2), term 2 - 2 cos(N theta)
   >= 0. Multiplicities: m(rho) = analyticOrderNatAt riemannXi rho is a natural number, so
   Re(m * term) = m * Re(term) >= 0. Negative imaginary parts: w(conj rho) = conj(w(rho)), so the
   pair term of conj rho is the conjugate of that of rho and has the same real part; Theorem C
   for gamma < 0 is Theorem C for |gamma| applied to the NUMBER conj rho (Lemma B should be
   stated for an arbitrary complex number with 0 < Re < 1, Im /= 0, not for a zero, so no
   "conj rho is a zero" lemma is needed inside C). No circularity: the hypothesis is finite
   (zeros with |Im| <= T) and the conclusion is finite (rungs N <= pi T/2); the T -> infinity
   limit is the known forward half of Li's criterion, not a new statement.
   Three corrections:
   (a) Summability: `Complex.re_tsum` needs `Summable`. It is available upstream as
   `summable_weighted_Li_paired_summand_of_weighted_genus` (Basic.lean line 3313) fed by the
   weighted genus theorem. Note also that it is not logically needed for the sign: if the family
   were not summable Lean's tsum is 0 and Re 0 = 0 >= 0, so a `by_cases Summable` proof also
   works. Use the genus route (it is what the formula proof already carries).
   (b) The composition with `AllZeros_h4000` covers ONLY 0 < Im rho <= 4000 (its conclusion is
   `forall rho, riemannZeta rho = 0 -> 0 < rho.im -> rho.im <= 4000 -> rho.re = 1/2`). Negative
   imaginary parts need Mathlib `riemannZeta_conj` (ZetaAsymp.lean line 458) to reflect a zero
   with -4000 <= Im < 0 to one with 0 < Im <= 4000. That step is missing from the brief.
   (c) Zeros with Im = 0 in the strip are NOT covered by h4000 (its `hgamma` hypothesis also has
   `0 < rho.im` in its antecedent, so it says nothing about real zeros). A hypothetical real zero
   rho = beta in (0, 1), beta /= 1/2, has w real negative, theta = pi, r = beta/(1 - beta), and
   the pair term is 2 - (-1)^N (r^N + r^(-N)), which is NEGATIVE for every even N (for beta = 0.3:
   N = 2 gives -3.63, N = 4 gives -27.7). So the composition must separately exclude real zeros.
   This is provable, not a hypothesis: rvm island already has it kernel-clean
   (`E6Bridge25.riemannZeta_ne_zero_of_unit_interval`, via Re zeta(sigma) < 0 for 0 < sigma < 1);
   the li island must port it, or derive it from Box 1 (item 7), which implies it. Corollary
   sentence "under exactly those hypotheses" should read "under those hypotheses, plus the
   conjugation symmetry and the real-zero exclusion, both provable".
   Zeros with Re outside the band [1/2000000, 1 - 1/2000000]: handled inside the capstone.
   `ZetaZeroConfinement.zero_in_band` (with `haC_4000` proved) puts every zero with
   0 < Im <= 4000 and 55/16 <= |Im| into the band from the dVP zero-free region plus the
   functional equation; the band hypotheses `hband_i`/`hseg_i` then place it on the line. So the
   capstone conclusion is unconditional in Re given its stated hypotheses. The `hgamma`
   hypothesis (55/16 <= |Im| for every zero with 0 < Im <= 4000) is a genuine hypothesis of
   h4000; Box 1 gives only sqrt(3)/2 and does not discharge it.

6. CONFIRMED. Rung 0. 2 - w - 1/w = 2 - (rho^2 + (rho - 1)^2)/(rho(rho - 1)) = -1/(rho(rho - 1))
   = 1/(rho(1 - rho)); checked numerically to 1e-20. rho(1 - rho) = beta(1 - beta) + gamma^2
   + i gamma(1 - 2 beta), so Re of the reciprocal is (beta(1 - beta) + gamma^2)/|rho(1 - rho)|^2
   > 0 for 0 < beta < 1, for ALL gamma including gamma = 0. So rung 0 needs no zero localisation
   at all (consistent with Li's lambda_1 = 0.0230957 > 0). Same on the rvm side: Re liKernel 1 rho
   = Re(1/rho) = beta/|rho|^2 > 0 termwise without pairing.

7. CORRECTED. Section 4, the representation and the J bound. The representation
   zeta(s) = s/(s - 1) - s J(s), J(s) = int_1^inf {x} x^(-s-1) dx, Re s > 0, s /= 1, is the
   classical one (Titchmarsh 2.1.5); verified numerically at s = 0.1, 0.5, 0.3 + 2i, 0.7 + 0.5i
   and at the first zero (agreement 1e-8 with a 2e5-term direct sum plus tail). The bound: for
   real sigma > 0, I(sigma) = int_1^inf {x} x^(-sigma-1) dx satisfies
   1/(2 sigma) - 1/8 <= I(sigma) <= 1/(2 sigma). The by-parts sign is right: with
   B(x) = ({x}^2 - {x})/2 <= 0, continuous, B' = {x} - 1/2 a.e., B(1) = 0,
   I - 1/(2 sigma) = int B' x^(-sigma-1) = [B x^(-sigma-1)]_1^inf + (sigma + 1) int B x^(-sigma-2)
   = (sigma + 1) int B x^(-sigma-2) <= 0. Checked via I(sigma) = 1/(sigma - 1) - zeta(sigma)/sigma:
   sigma = 0.1: I = 4.9193 in [4.875, 5]; sigma = 0.5: 0.9207 in [0.875, 1]; sigma = 0.9: 0.4779
   in [0.4306, 0.5556]. For complex s with Re s = sigma: |J(s)| <= int {x} x^(-sigma-1) = I(sigma)
   <= 1/(2 sigma), valid for every sigma > 0 including (0, 1). All CONFIRMED.
   The correction is about what is on the island. The brief says "on the rvm island this is
   Zeta0EqZeta plus the bound used in E6Bridge25". Not quite: E6Bridge25 uses the SAWTOOTH form
   zeta(s) = 1/2 + 1/(s - 1) + s J0(s), J0(s) = int_1^inf (floor x + 1/2 - x) x^(-s-1) dx, with the
   trivial bound |J0| <= 1/(2 sigma) from |floor x + 1/2 - x| <= 1/2. The two forms are the same
   function (J0 = 1/(2s) - J), but the brief's |J| <= 1/(2 sigma) is a strictly stronger fact
   that needs the monotonicity argument above; it is NOT in E6Bridge25. What the sawtooth bound
   alone gives at a zero is sigma |s + 1| <= |s| |s - 1|, whose Box 1 analogue is |t| >= 0.770
   (at sigma = 1/2: t^4 + t^2/4 - 1/2 >= 0), weaker than sqrt(3)/2 = 0.866. This matters for
   item 9: rung 4 (N = 5) needs gamma >= 0.806 (numerically, beta free), so the sawtooth box
   would not reach rung 4 without extra confinement. The li-box worker must prove the {x} bound.
   Lean suggestion (simpler than integration by parts): on each [k, k + 1], reflect u -> 1 - u
   about the midpoint; ({x} - 1/2) x^(-sigma-1) pairs to (u - 1/2)[(k + u)^(-sigma-1)
   - (k + 1 - u)^(-sigma-1)] <= 0 for u >= 1/2 because x^(-sigma-1) is decreasing. Sum over k.
   Also: E6Bridge25's real-zero exclusion (Re zeta(sigma) < 0) is exactly what item 5(c) needs.

8. CORRECTED (minor). Boxes 1 and 2. Derivation: zeta(s) = 0 gives 1/(s - 1) = J(s), so
   1/|s - 1| <= 1/(2 sigma), i.e. (1 - sigma)^2 + t^2 >= 4 sigma^2. The partner: the functional
   equation zeta(1 - s) = 2 (2 pi)^(-s) cos(pi s/2) Gamma(s) zeta(s) with the prefactor nonzero in
   the strip gives 1 - s as a zero (Re = 1 - sigma, Im = -t); conjugation gives 1 - conj s
   (Im = +t). The brief attributes 1 - conj s to the functional equation; strictly it is
   functional equation plus conjugation, but the inequality involves only sigma and t^2 so it
   does not matter which partner is used. On the li island the partner 1 - rho is already a
   NontrivialZero (`zero_pairing`); on the rvm island `RvMBridge20.isNontrivialZero_one_sub_iff`.
   Applying the bound to the partner: 4 (1 - sigma)^2 <= sigma^2 + t^2. Adding:
   3 (sigma^2 + (1 - sigma)^2) <= 2 t^2, and sigma^2 + (1 - sigma)^2 = 2 (sigma - 1/2)^2 + 1/2,
   so (sigma - 1/2)^2 <= t^2/3 - 1/4. Box 2 CONFIRMED. Box 1: the right side must be >= 0, so
   t^2 >= 3/4. CONFIRMED, and it is the best this pair of inequalities gives (both are tight at
   sigma = 1/2, t^2 = 3/4). Consistency: the first zero 1/2 + 14.1347i has |s - 1| = 14.14 >= 1 and
   t^2/3 - 1/4 = 66.35 >= 0; Box 2 is informative only for |t| < sqrt(3/2) = 1.2247 (beyond that
   the right side exceeds 1/4, which (sigma - 1/2)^2 never reaches). Nothing known contradicts
   them; they are far weaker than the numerically verified fact that no zero has |t| < 14.13.
   Wording correction: "new unconditional zero localisation" should be "new to the island";
   mathematically these boxes are folklore-level consequences of the Titchmarsh representation
   and should not be described as new zero information in any outward-facing text.

9. CORRECTED (status, not content). Rungs 0..4 termwise on the box region, rung 5 failing.
   Numerics (grid 1200 x 600 over gamma in [sqrt(3)/2, 4], beta in (0, 1), box region):
   min of Re pair term is N = 1: 0.0588 (tends to 0 as gamma grows, always positive),
   N = 2: 0.232, N = 3: 0.510, N = 4: 0.878, N = 5: 1.016 (at (0.4625, 0.8686)),
   N = 6: -0.715 (at (0.303, 0.931)), N = 7: -2.91. The brief's point (0.64, 0.9) is inside the
   box (0.0196 <= 0.02) and gives -0.533 for N = 6. So "0..4 pass, 5 fails" is CONFIRMED.
   The max of |theta| over the whole strip at fixed gamma is 2 arctan(1/(2 gamma)) (at
   beta = 1/2, by concavity of arctan), equal to pi/3 at gamma = sqrt(3)/2, so |b| <= 5 pi/3 for
   N <= 5 needs only Box 1, not Box 2. In the window b in (3 pi/2, 5 pi/3], the max of
   cosh(a) cos(b) on the box region is 0.4995 (the brief's "<= 0.5" is right, and the sup is the
   corner (1/2, sqrt(3)/2) where a = 0 and cos(5 pi/3) = 1/2; the term there is 1).
   Further: with beta FREE in (0, 1) and only gamma >= sqrt(3)/2, the N = 5 term is still >= 0.93
   on gamma in [0.866, 3.2] (Theorem C covers gamma >= 3.19); the largest gamma at which some beta
   gives a negative term is 0.385 (N = 3), 0.606 (N = 4), 0.806 (N = 5). So rungs 1..4 need
   Box 1 only; Box 2 is not needed for the sign, though it helps the proof of the (3 pi/2, 5 pi/3]
   window. Status correction: the brief's argument for that window is numerical ("numerically
   cosh(a) cos(b) <= 0.5 there"). A Lean proof needs a real inequality. One route that closes
   by hand for N = 5: b > 3 pi/2 forces |theta| > 3 pi/10, hence 1/(2 gamma) > tan(3 pi/20),
   gamma < 0.981; Box 2 then gives |beta - 1/2| <= 0.266; the exact
   log r = (1/2) log(1 + |2 beta - 1|/(min(beta, 1 - beta)^2 + gamma^2)) <= (1/2) log(1.661)
   = 0.2537, so |a| <= 5 * 0.2537 = 1.269 and cosh(a) <= 1.92 < 2, giving cosh(a) cos(b) <= 0.96.
   The crude bound log(1 + x) <= x does NOT close here (it gives 0.33 > 0.263); keep the log.
   Margins are thin; the formalizers should expect interval-style case work, not a one-liner.

10. CORRECTED. Section 3 consequence "Theorem D holds for all T >= sqrt(3)/2". True but vacuous
    beyond T >= 1: for T in [0.866, 1) the ladder N <= pi T/2 < 1.571 contains only N = 1, which
    is hypothesis-free anyway (item 6). Drop the sentence or say so.

11. CONFIRMED. Section 5, the rvm copy. `liKernel n rho = 1 - (1 - 1/rho)^n` (E6Bridge15 line
    64; positive exponent, so `liKernel N rho = 1 - w^(-N)`, which equals the li island's
    `liSummand (N-1)` at 1 - rho; the two islands agree on the total because the divisor is
    symmetric under rho -> 1 - rho). `liPaired n rho = zeroMult rho * Re(liKernel n rho)` and
    `liLimit n = tsum over all of C of liPaired n` (lines 156, 160). For rho' = 1 - conj rho:
    1 - 1/rho' = conj(w), so liKernel N rho' = 1 - conj(w^N), Re = 1 - r^N cos(N theta), while
    Re liKernel N rho = 1 - r^(-N) cos(N theta). Sum 2 - (r^N + r^(-N)) cos(N theta): the SAME
    expression as item 1. The divisor is symmetric: under conj by `RvMBridge15.zeroMult_conj`
    and `isNontrivialZero_conj_iff` (E6Bridge15 lines 99, 109), under s -> 1 - s by
    `RvMBridge20.isNontrivialZero_one_sub_iff` and `RvMBridge20.zeroMult_one_sub` (E6Bridge20
    lines 459, 501; both in the AxiomGuard list). Formalization note: rho -> 1 - conj rho is an
    involution WITH fixed points (exactly the on-line zeros), so do not split the tsum into
    fixed points and pairs. Instead reindex the whole tsum by the involution (`Equiv.tsum_eq`,
    using `summable_liPaired`, E6Bridge15 line 409) and average: liLimit N = (1/2) tsum of
    zeroMult(rho) * [Re liKernel N rho + Re liKernel N (1 - conj rho)]; then every summand is the
    pair expression and Theorems C, D transfer. `liLimit 1 >= 0` with no hypothesis: item 6.
    `RvMBridge27.liValue n (0 < n) : LiValue n` is stated hypothesis-free in E6Bridge27 (line 27)
    via `RvMBridge25.liValue_of_two`, `RvMBridge23.local_count_sum`, `RvMBridge24.stripDerivBound`;
    the closed-form inequality 0 <= Re(archSide N + finiteSide N) inherits exactly the axioms of
    those three, so run `#print axioms` on them before quoting it as unconditional.

12. CORRECTED (wording only). RH language. The brief's framing is honest: the header states
    conjecture1_proved = False, section 6 says the ladder consumes localisation and does not
    produce it, and nothing claims a rung is nonnegative for all n. Three phrases to tighten:
    (a) "new unconditional zero localisation" (section 4 title): see item 8, say "new to the
    island". (b) "the ladder replaces them [the per-rung certificates] and extends the reach"
    (section 3 corollary): true only after the additions in item 5(b, c); until those are in the
    kernel the existing rung certificates are not superseded. (c) "Rungs 0..4 should be
    nonnegative with NO hypothesis": correct as a mathematical claim (item 9), but the classical
    literature already has lambda_1 .. lambda_5 > 0 numerically and more; keep the claim as
    "kernel-checked with no Arb hypothesis", not as new knowledge about the coefficients.
    No sentence in the brief can be read as progress on RH; the exchange rate n + 1 <= pi T/2
    is a finite conditional statement and is labelled as such.

## What the Lean workers must add beyond the brief

* li-rung0: Lemma B stated for arbitrary beta + i gamma (0 < beta < 1, gamma /= 0), conj case of
  Theorem C via w(conj rho) = conj w(rho); the h4000 composition needs `riemannZeta_conj` and a
  real-zero exclusion (port of `E6Bridge25.riemannZeta_ne_zero_of_unit_interval` or Box 1).
* li-box: the {x}-kernel bound int_1^inf {x} x^(-sigma-1) dx <= 1/(2 sigma) is NOT the E6Bridge25
  bound; prove it by midpoint reflection on each unit interval. Rungs 1..4 then need Box 1 and a
  genuine case analysis for N = 5 in the b in (3 pi/2, 5 pi/3] window (numbers in item 9).
* rvm-li: reindex-and-average, do not split on fixed points of rho -> 1 - conj rho.

conjecture1_proved = False.

## Addendum: the factor-3 improvement (survey claim)

13. CONFIRMED. Theorem C holds with threshold |Im rho| >= max(1, 2N/(3 pi)): then
    |b| = N|theta| <= N/gamma <= 3 pi/2; on |b| <= pi/2 Lemma A applies (|a| <= |b| from
    Lemma B, gamma >= 1), and on pi/2 <= |b| <= 3 pi/2 cos b <= 0 so cosh(a) cos(b) <= 0 <= 1
    with no condition on a. Hence Theorem D with n + 1 <= 3 pi T/2 for T >= 1 (T = 4000 gives
    n <= 18848). Consistent with the numerics: the N = 5 threshold becomes max(1, 1.061) and the
    grid shows no negative term above gamma = 0.806. Everything else in items 5 and 9 unchanged.
