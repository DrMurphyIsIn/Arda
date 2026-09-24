# RH Fourier-quasicrystal probe (crux-fq, round 2), 2026-09-24

`conjecture1_proved = False`. Nothing in this document proves RH, reduces RH, or moves a wall clause. Every
zero-side statement below is one of three things: an obstruction, a dictionary entry that is RH-equivalent (and
tagged CIRCULARITY), or a statement that holds for the negative controls too.

## 0. Preamble

**What this is.** A four-seat probe (literature, rigidity, negative-control, kernel) with hostile referees on
three of the four seats. The user asked for it this way: "probe the quasicrystal angle properly, the stronger lead
is the Fourier-quasicrystal literature against round 1's Theorem A." Round 1 is
`RH_AXIOM_ISOLATION_2026-09-22.md`, the class-P round, whose Theorem A is the Beurling-Hamburger rigidity.

**Tags.** THEOREM-kernel-checked, THEOREM-paper-proof, CONJECTURE-with-evidence, HEURISTIC, plus COMPUTED
(floating point, not interval-certified) and Arb-certified (ball arithmetic, not kernel).

**Death tests.**
- (a) CIRCULARITY: the statement is RH-equivalent by a short argument.
- (b) NEGATIVE-CONTROL FAILURE: the statement also holds for Davenport-Heilbronn (DH), Epstein, the golden fake,
  or zeta times a surgered Euler factor (W1, W2, nu_{p,c}). The added control E_theta = zeta(s+theta)zeta(s-theta)
  is described in section 3.3.

**Provenance.**
- Seat notes live in `/private/tmp/claude-0/crux-fq/{literature,rigidity,negative-control,kernel}/NOTES.md`.
  Referee recomputations are in `ref-*/`.
- Seat scores (mean of referees; no seat was killed): literature 7.0 (7/7/7), negative-control 6.3 (7/7/5),
  rigidity 5.7 (7/6/4).
- The kernel seat's referee reports did NOT reach this writer: the harness payload was truncated inside the kernel
  seat's result. Its skeptic status is therefore UNKNOWN. This writer rebuilt its artifacts independently (section 5b).
- Numerics are single-process: mpmath, python-flint, and a numpy sieve. There are no multiprocessing pools.

## 1. The question and where it sits

**Question.** Does Fourier-quasicrystal (FQ) theory supply a zero-side rigidity for the Guinand-Weil pair
(zeta zero measure, regularized prime measure) that an off-line zero would violate, that survives the controls, and
that is not RH? And how does FQ theory bear on round 1's Theorem A?

**Theorem A (round 1).** N >= 0 on [1, inf), N({1}) = 1, polynomial growth, and zeta's exact conductor-1 FE for
int x^{-s} dN together force N = sum_{n>=1} delta_n.
- It is a statement about the coefficient (prime/additive) side. No discreteness is assumed.
- Round 1 kernel-checked Step 3 only, conditional on a Cohn-Elkies pairing identity.
- It is NT4 in the round-1 plan (registry draft `RH_classP_collapse_beurling_q1`).

**The mirrormere Guinand-Weil membership program.**
- The goal node `MM_zeta_comb_membership` is honestly RH-hard. The kernel dictionary E6Bridge9
  `zeta_comb_membership_iff_rh` shows that Weil positivity (positive-definiteness of the arithmetic dual) is
  equivalent to RH.
- `ARITHMETIC_FQ_MEMBERSHIP_SPEC_2026-09-16.md` defines an "arithmetic FQ" by four clauses:
  - (i) pure-point diffraction;
  - (ii) T log T density;
  - (iii) Euler Bragg intensities;
  - (iv) torus restriction.
- It poses "AFQ implies reality" as the reverse-Dyson route, with node A0 described as "author the regularization".

**How this probe relates.**
- Theorem A is literally a crystalline-measure rigidity. The probe asks whether it has a zero-side mirror, and
  whether FQ structure theory (Lev-Olevskii, Kurasov-Sarnak, Olevskii-Ulanovskii, Alon-Cohen-Vinzant, Goncalves,
  Favorov, Vedana) can force the membership / reality clause.
- The short answer is no. Section 6 gives the verdict: the FQ angle is a real lever on the prime side, is a
  relabeling on the zero side, and is blocked by the controls.

## 2. Literature map

### 2.1 Verified citations

The literature seat read each theorem's text in the arXiv PDF and checked venues on Crossref. The referees
spot-checked Arias de Reyna, Kurasov-Sarnak, Vedana, and Favorov-Deger Thm 1.

| # | Work | What it proves | Load-bearing hypotheses |
|---|---|---|---|
| L1 | Lev-Olevskii, Invent. Math. 200 (2015) 585-606, arXiv:1312.6884 | 1D: uniformly discrete (u.d.) support and u.d. spectrum give finitely many lattice cosets | u.d. on both sides |
| L2 | Lev-Olevskii, Adv. Math. 315 (2017) 1-26, arXiv:1512.08735 (NOT Annals) | positive-definite, u.d. support, discrete closed spectrum give a periodic measure | positive-definite, u.d. |
| L3 | Lev-Olevskii, Rev. Mat. Iberoam. 32 (2016) 1341-1352 | non-periodic counterexample without u.d. | -- |
| L4 | Kurasov-Sarnak, J. Math. Phys. 61 (2020) 083501, arXiv:2004.05678 | positive FQs from stable (Lee-Yang) polynomials on a finite torus; eq. (27) is a toy Guinand-Weil formula | finite rank, integer masses |
| L5 | Olevskii-Ulanovskii, C. R. Math. 358 (2020) 1207-1211 | a unit-mass FQ is the zero set of a real-rooted exponential polynomial | unit masses, FQ |
| L6 | Alon-Cohen-Vinzant, J. Funct. Anal. 286 (2024) 110226, arXiv:2303.03201 | those exponential polynomials are Lee-Yang restrictions | same |
| L7 | Goncalves, arXiv:2312.11185, Thms 3 and 5 | positive FS-pairs correspond to Hermite-Biehler E with almost-periodic A/B | almost periodicity (fails for Xi' - iXi: digamma term) |
| L8 | Favorov, Stud. Math. 278 (2024) 81-98; arXiv:2311.02728 (not re-read), 2504.03365; Boyvalenkov-Favorov arXiv:2503.19567 | structure of pure-point / measure-FT pairs | pure-point or measure FT, bounded spectrum, almost periodicity |
| L9 | Favorov-Deger, arXiv:2605.10766, Thm 1 | a positive strip measure of polynomial growth whose c-FT is a measure is translation bounded | positivity (verified by two referees) |
| L10 | Vedana, arXiv:2608.10121, Cor 5 | every Selberg-class L gives a strip FS-pair, unconditionally; eta = delta_{i/2} + delta_{-i/2} - (off-line zeros) | none; reality-blind dictionary |
| L11 | Bondarenko-Radchenko-Seip, Constr. Approx. 57 (2023) 405-461, arXiv:2005.02996 | (zeta zeros, log n / 4 pi) is an unconditional Fourier interpolation / uniqueness pair with complex nodes | FE plus Dirichlet series; section 5.3.3 extensions to DH-type and surgered L are a REMARK, not proved |
| L12 | Arias de Reyna, arXiv:2402.10604, Thm 3 | RH iff mu = -sum Lambda(n) n^{-1/2}(delta_{log n} + delta_{-log n}) + 2cosh(x/2) dx is tempered | none; RH-equivalent |
| L13 | Miller, Duke 112 (2002), math/0112196 | "highest lowest zero": LP on the explicit formula over the prime-free window [-log 2, log 2] | GRH or effective box; FE-generic |
| L14 | Baake-Spindeler-Strungaru 2023, arXiv:2104.06812 (Thm 6.3, sec. 7) | signed Fourier eigenmeasures with gaps at 0 | signed |
| L15 | Meyer, PNAS 113 (2016) 3152 | Guinand r_3(n)/sqrt(n) crystalline measures on sqrt(n)-type supports, self-dual or eigen, signed; "the measures studied by Weil in 1952 are not crystalline" | signed |
| L16 | Kahane-Mandelbrojt 1958 (Numdam, OCR) | Thms 4, 5, 10: density-gap product >= 1, equality only for the Poisson comb | discrete frequencies; NO positivity |
| L17 | Montgomery 1973 (under RH); Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh, Acta Arith. 214 (2024) | pair-correlation FT = delta_0 + |alpha| on |alpha| < 1, which is absolutely continuous and so not pure point | -- |

**Not re-read** (use with care):
- Guinand 1948/1959, Cordoba 1988/89, Meyer 2017/2022 and Bourbaki, Landau 1912.
- Tselishchev arXiv:2608.09354, Favorov arXiv:2311.02728, Alon-Vinzant arXiv:2307.13498.
- Goncalves Remark 5 (N-valued completeness), Hamburger 1921/22, Bochner 1951, Bochner-Chandrasekharan 1956,
  Chandrasekharan-Mandelbrojt, Knopp, Kaczorowski-Perelli.

**Verbatim confirmations.**
- Kurasov-Sarnak: Guinand's prime example "does not give a Fourier quasicrystal, even assuming the Riemann
  hypothesis."
- Meyer 2016: Weil's measures "are not crystalline measures".

### 2.2 Applicability to the Guinand pair

| FQ result | Applies to zeta's pair? | Why / why not | Separates zeta from controls? |
|---|---|---|---|
| L1-L3, L5, L6 (positive/unit-mass FQ classification) | NO, even under RH | Theorem G (section 3.1): the zero measure is not translation bounded, so its FT is not a Radon measure | no; vacuous for all |
| L4 Kurasov-Sarnak Lee-Yang | only locally | the reality mechanism is finite-torus stability; zeta's global zeros have T log T density, which no exponential polynomial reaches (Jensen gives O(T)) | decides the LOCAL off-line zeros of surgered controls exactly (Theorem L) |
| L7 Goncalves HB | NO | E = Xi' - iXi is Hermite-Biehler iff RH, and A/B are not almost periodic | reality-blind / RH-equivalent |
| L8, L9 Favorov (incl. Favorov-Deger) | only as an obstruction | L9 is the load-bearing citation for Theorem G(b), unconditionally | no |
| L10 Vedana | YES, unconditionally | a dictionary: RH iff eta >= 0 | CIRCULARITY |
| L11 BRS | YES, unconditionally | complex nodes are allowed | no (DH-type and surgered covered, per the remark) |
| L12 Arias de Reyna | YES | tempered iff RH | CIRCULARITY |
| L13 Miller | YES | FE-generic; about low zeros, not reality | no (DH identical in form) |
| L14-L16 | prime side only | witnesses that Theorem A's positivity and gap are necessary; nearest classical ancestor | -- |
| AFQ clause (i) pure-point diffraction | ill-posed / false | the autocorrelation diverges (central mass ~ (1/pi) log T); at the unfolded scale Montgomery gives an a.c. FT | cannot be a lever |

## 3. Seat results, referee verdicts, salvage

### 3.1 Literature seat (score 7.0; 0 kills)

**Claims.**
- **Theorem G, the archimedean obstruction** (THEOREM-paper-proof, unconditional).
  - For zeta, DH, Epstein, the golden fake, W1, Ftwin and every Selberg-class L, the zero measure is positive, has
    polynomial growth, and is not translation bounded (window counts ~ (d_F / 2 pi) log T).
  - By L9 its strip FT is therefore not a measure.
  - On (0, log 2), mu_zeta^ is the smooth archimedean kernel ~ -1/(2x) plus 2cosh(x/2).
  - So every positive-measure FQ theorem is vacuous for zeta and for every control alike.
- **The Arias de Reyna / Bochner-Schwartz triangle** (CIRCULARITY): Weil positivity => tempered => RH => Weil
  positivity.
  - This is the only zero-side twin of Theorem A.
  - The writer's completion of the converse is referee-checked: choose a zero with beta_0 > 1/2 + (Theta - 1/2)/3,
    so that the k-terms cannot cancel.
- **The QC memo's R1** is a theorem with idle hypotheses. (H-temp) is equivalent to the conclusion, function by
  function; DH is included (writer's check, unrefereed). As written ("|mu^| tempered"), (H-temp) is false for zeta
  even under RH (T4).
- **Theorem L**: the only reality-forcing mechanism is finite-torus Lee-Yang. It decides the controls' local zeros
  and never reaches zeta's global zeros.
- **A4**: the zero-side "magic function" is Xi^2, so the zero-side LP is tautological (THEOREM-paper-proof,
  elementary).
- **Theorem A vs the FQ literature.**
  - The u.d. subcase reduces to L1 / L14 (HEURISTIC-to-paper).
  - The gap is necessary: mu_p + c mu_1 + mu_{1/p} is positive and self-dual with points in the gap; this is Ftwin.
  - Positivity is necessary (L14, and Guinand's odd distribution).
- **Citation corrections** (section 7).
- **Landau / Bohr numerics** (first 2000 zeros): coefficients at prime powers match -Lambda(m)/sqrt(m) to
  about 1 percent, and non-prime-powers give < 0.01.

**Decisive referee objections.**
1. The novelty map for Theorem A was aimed at the wrong literature. The Hamburger 1921 / Bochner 1951 /
   Bochner-Chandrasekharan 1956 / Kahane-Mandelbrojt 1958 / Knopp / Kaczorowski-Perelli lineage was not checked;
   KM58 itself mentions Hamburger 11 times.
2. Numerics error: the alpha range [-2.80, -2.20] came from 9 sample points. The dense range is [-3.39, -1.91],
   and the script computes -mu_AdR(0, x], not mu(0, x]. The writer re-ran the script and confirmed the
   sampled-point values.
3. The A3 witness breaks both the gap and the normalization N({1}) = 1.
4. The squeeze ("class P = {zeta}, so any survivor is a relabeling") is a non sequitur: a genuine proof of RH would
   also single out zeta.
5. Tag inflation: "Lee-Yang is the only mechanism" is a survey claim and should be HEURISTIC. Three citations were
   marked read but were not.

**Salvage.**
- Keep Theorem G as the standing uniform no-go.
- Keep the triangle as a CIRCULARITY tripwire.
- Keep T4 and A4.
- Retag Theorem L's "only mechanism" clause and the squeeze as HEURISTIC, and restate the squeeze as "the listed FQ
  properties do not discriminate."
- Record node A0's regularization as already in print (Guinand 1959, Arias de Reyna 2024, Vedana 2026).

### 3.2 Rigidity seat (score 5.7; 0 kills)

**Claims.**
- **Theorem D, "dual Beurling-Hamburger"** (THEOREM-paper-proof, conditional on Theorem A).
  - Hypotheses: an even positive prime side P with no atom at 0, and a symmetric complex zero multiset in a strip
    with n_Z(T) = O(T log T).
  - If together they satisfy zeta's explicit formula with zeta's exact archimedean and pole terms, then
    P = P_zeta and Z = Z_zeta.
  - This holds whether or not RH does.
- **Cor D1**: the positive integer-valued real partners are {Z_zeta} if RH and none otherwise (classification;
  CIRCULAR as a route).
- **Lemma M**: positive partners cannot be nested.
- **Cor D2** (Arb-certified): the continuous Beurling system s/(s-1) has an exact tempered SIGNED partner,
  negative on 0.7244 < |r| < 5.9471. Consequently t P_zeta + (1 - t) P_cont has no positive partner for t < 1,
  unconditionally.
- **Prop 3.6**: tempered signed partner <=> positive partner <=> RH.
- **Theorem E, Euler-support collapse** (elementary; possibly folklore).
  - A Kurasov-Sarnak quasicrystal on Q-independent logs whose Bragg support is on pure prime powers is a finite
    union of lattices, with non-decaying coefficients.
  - So zeta's (log p) p^{-m/2} is never realized.
  - Local Lee-Yang <=> the local root has modulus sqrt(p) <=> the local zeros lie on the line.
  - Non-trivial Lee-Yang quasicrystals carry composite Bragg peaks, which is DH's signature.
- **Miller 2002** is the zero-side mirror of Theorem A, and it is FE-generic.
- **Circularity ledger Z1-Z15.**
- **Prop K**: the window partners E(L) are nonempty iff kappa(e^L) = 0. DH has positive real partners for
  L < log 30.5 (COMPUTED).
- **Lemma 8.1**: a quantitative Theorem A (a Poisson defect on one Cohn-Elkies function).

**Decisive referee objections.**
1. Theorem D is Theorem A in explicit-formula coordinates, plus the classical Weil 1952 transport and strong
   multiplicity one. It adds no independent rigidity, and its novelty is exactly Theorem A's.
2. The literature half of the user's lead is only half-closed. KM58 was read only for its introduction, although
   its Thm 5 / Thm 10 extremal cases (the Dirac-comb pair) sit in Theorem A's exact setting. Meyer 2016's signed
   sqrt(n)-support measures were missed.
3. Theorem E and Lemma M are folklore grade. E.3 is tautological (a surgered factor's zeros sit on
   Re s = log|a| / log p).
4. Prop K's DH onset is COMPUTED, and its window convention and the Zhu normalization are unverified.
5. "Every zero-side positivity clause is RH" is a ledger over 15 examined forms, not a theorem.

**Salvage.**
- Keep Theorem D, adding the residue / kappa = -1 bookkeeping paragraph that the referee supplied.
- Keep Lemma M, with weaker hypotheses (rho >= 0, P2 >= 0; mu1 >= 0 is not needed).
- Keep Cor D2 (the cleanest new certified fact), Theorem E stated as folklore, and Lemma 8.1.
- Retitle to "every clause EXAMINED".
- Add Meyer 2016 as the sharp positivity-necessity witness.
- Add Ftwin as the explicit stress test for the no-atom hypothesis.
- O1 (non-integer positive partners) is well posed but cannot become a route: at full strength it must reproduce
  Cor D1's "iff RH".

### 3.3 Negative-control seat (score 6.3; 0 kills)

**Claims.**
- **Exact Guinand-Weil formulas** for DH, W1, W2, Epstein x^2+5y^2, the golden fake and E_theta (THEOREM-paper-proof
  + COMPUTED; residuals 1e-15 to 1e-31; zero counts reconciled with argument-principle counts).
  - Off-line zeros enter at complex gamma on the same footing as real ones.
  - DH's Lambda_D is signed and not prime-power supported: Lambda_D(6) = +1.93636, Lambda_D(3) = -0.31209.
  - Substituting zeta's Lambda leaves a residual of 0.41.
- **Claim 2** (THEOREM-paper-proof; classical, see attribution below): for every F with an FE and a Dirichlet
  series, distributional temperedness of the dual is equivalent to RH_F. Temperedness of the ABSOLUTE dual (the
  KS/ACV FQ axiom) fails for zeta unconditionally.
- **E_theta = zeta(s+theta)zeta(s-theta), the shift control** (THEOREM-paper-proof, elementary).
  - mu_E = mu_zeta * (delta_{i theta} + delta_{-i theta}), and the dual is 2cosh(theta x) nu_zeta.
  - E_theta has an Euler product, Lambda >= 0, a pure-point dual on prime-power logs, and T log T density.
  - It has infinitely many off-line zeros unconditionally, and ALL zeros are off-line under RH.
  - Hence no shift-invariant property of the pair can force real support. AFQ clauses (i), (ii) and (iv) accept
    E_theta; (iii) rejects it only by identifying the dual with zeta's.
- **The golden fake** satisfies every structural FQ axiom (periodic support in C, lattice spectrum, positive dual)
  except temperedness. At finite rank, temperedness = real-rootedness = Lee-Yang.
- **The Epstein lattice** is a positive, periodic, self-dual FQ in R^2 with off-line zeros. A second off-line zero
  was found at 0.937666906700399 + 29.9833952351555i (COMPUTED; independently re-found by two referees).
- **W2**: a finite window of real zeros cannot certify Lee-Yang. All zeros below height 150 are real
  (the argument-principle count of 330 equals the 330 sign changes), and the first off-line zero is at
  0.501942745874 + 162.69048446i.
- **P_min** = FE + Euler product + Lambda >= 0 + a single pole at 1 is the only separator. In degree one it is
  class P = {zeta}, so "P_min implies reality" is RH verbatim (CIRCULARITY).

**Decisive referee objections.**
1. W2 Lee-Yang is stated wrongly. P = 1 + a(z1 + z2) + z1 z2 is Lee-Yang iff |a| <= 1, not iff a = 1. The W2
   conclusion survives because a > 1.
2. F_t has a(1) = 2t; normalize by 2t.
3. BRS 5.3.3 is an unproved remark, and DH's zeros with Re > 1 fall outside BRS's H1 strip.
4. Claim 2 is Arias de Reyna 2024 Thm 3 (for zeta) plus a routine extension. The absolute-dual failure is the
   Kurasov-Sarnak remark. Both need attribution; neither is new.
5. "Every property" should read "every property examined". The 31 vs 29 on-line zero count is cosmetic.

**Salvage.**
- Promote E_theta to the standing zoo as an automatic pre-screen: any clause invariant under
  (mu, nu) -> (mu * (delta_{i theta} + delta_{-i theta}), 2cosh(theta x) nu) is dead on arrival.
- Keep the six verified formulas as a regression harness.
- Discharge `hzero` on `eisShift_violates_RH_analogue'` via Zeta23's `exists_nontrivial_zero_above`, using the
  parity argument (rho +- theta cannot both lie on the line).

### 3.4 Kernel seat (referee reports not received; writer-reverified)

**K1, Theorem A in crystalline form** (THEOREM-kernel-checked; `CruxFQ.poisson_rigidity`, `selfDual_rigidity`).
- Hypotheses: nu >= 0 locally finite, nu((-1,1) \ {0}) = 0, sinc^2(pi x) integrable, and
  `IsPoissonPair nu beta` (for every continuous compactly supported f with nu-integrable transform,
  int F f dnu = int f dnu + beta (f(0) - int f)).
- Conclusion: nu is carried by Z, with nu{m} = nu{0} + beta for m != 0.
- No discreteness is assumed. The proof uses only the translated Fejer pair F tri = fej; neither Cohn-Elkies nor
  Hamburger is needed at this stage.
- Also proved:
  - `gap_gt_one_forces_zero` (the gap is sharp);
  - `translation_bounded_of_poissonPair`;
  - `poissonPair_realizable` (r delta_0 + c sum_{n != 0} delta_n has beta = c - r).

**K2, the fooling family** (THEOREM-kernel-checked; `fq_rigidity_is_rh_blind`).
- nu_{p,c} = p^{-1/2} comb(1/p) + c comb(1) + p^{1/2} comb(p) is positive, exactly self-dual, uniformly discrete
  (a Lev-Olevskii periodic comb), and fej-integrable, with an atom at 0 and an atom at 1/p inside the gap.
- Its completed Mellin transform is Lambda_zeta(s) Q_{p,c}(s), with zeta's exact FE.
- `Qp_zero_re_of_le_two`: for c <= 2, all zeros of Q lie on the line.
- `Qp_offline_zero_in_strip`: for 2 < c < sqrt(p) + 1/sqrt(p), Q has a zero with 1/2 < Re s < 1.
- `satake_ramanujan_iff`: the onset c = 2 is exactly where local Ramanujan fails.
- `W1_as_crystalline`, `golden_as_crystalline`: W1(29,11) (c = 11/sqrt 29) and the golden fake (p = 5, c = sqrt 5)
  are members.
- The crystalline data are identical across c = 2. In the crystalline form, the only hypothesis of K1 violated is
  the gap. In the Dirichlet form, N({1}) = 1 also fails; this is the literature referee's objection 3.

**Builder (round 2, `CruxFQ_kernel.lean`).**
- `isPoissonPair_of_theta`: the Gaussian (theta) modular relation implies the C_c Poisson identity, via a
  Weierstrass density argument that avoids translation boundedness (Gaussian determination).
- `thmA_theta`: Theorem A from the modular relation.
- `theta_rigidity_is_rh_blind`: the fooling family, in theta form.
- `classP_collapse_beurling_q1_of_hamburgerConverse`: round 1's registry statement
  `RH_classP_collapse_beurling_q1`, with its `BeurlingNormalized` / `ZetaShapeFE` definitions verbatim, now follows
  from ONE classical hypothesis, `HamburgerConverse`: "zeta-shape FE implies the theta relation or the anti-theta
  relation for symmExt N".
- `no_antiTheta` (root number epsilon = -1 excluded for positive gap measures). This is a new finding: Theorem A's
  Fejer argument is silent on the anti-modular relation, and the Gaussian test
  K = 2G_1 - G_4 - G_{1/4}/2 closes that case.

**Zero side (`CruxFQZeroSide.zero_side_fejer`, THEOREM-kernel-checked).**
- For a Weil test in the prime gap (-log 2, log 2), the sum over ALL zeros, off-line ones included, equals
  archSide.
- So Theorem A's mechanism, transported to the zero side, sees only Gamma-factor and pole data. This is FE-uniform
  and fails test (b).

**Dimension ladder.**
- d = 2 (Arb-certified; re-run by this writer): the Theorem-A package (positive, self-dual, gap) is not rigid.
  The covolume-1 form 3m^2 + mn + 3n^2 (disc -35, min sqrt(6/sqrt 35) > 1) has an Epstein zeta
  Z = zeta L(chi_-35) - L(chi_-7) L(chi_5) with certified off-line zeros near 0.777 + 19.324i, 0.650 + 55.895i,
  0.628 + 78.651i, 0.828 + 92.424i and 0.575 + 101.134i, plus the FE partner of the first.
- d = 8 (paper sketch, not refereed): the package is rigid (Viazovska; CKMRV for masses). The pinned Mellin
  transform 240 * 2^{-s} zeta(s) zeta(s-3) has no zeros on its centre line, unconditionally (round-1 kernel
  `XiE8_offline_zeros`).
- Rigidity and zero location are logically independent.

**Salvage.** All of it, as prime-side and no-go infrastructure. The only open step to full kernel Theorem A is
`HamburgerConverse` (Mellin inversion, Phragmen-Lindelof, rectangle Cauchy; the residue-free route is sketched in
the kernel NOTES B5).

## 4. Property-by-control table

Symbols:
- H = holds; F = fails; H* = holds for zeta under RH / on verified zeros; n.c. = not checked.
- The W1 column also covers nu_{p,c} with c > 2 (the same object up to scaling).

| # | Property | zeta | DH | Epstein x^2+5y^2 | golden (lattice / H4) | W1 / nu_{p,c} | W2 (a > 1) | E_theta | Verdict |
|---|---|---|---|---|---|---|---|---|---|
| 1 | zero measure positive | H | H | H | H | H | H | H | blind |
| 2 | real support (RH_F) | H* | F | F | F | F | F (H below 150) | F | the target |
| 3 | exact Guinand-Weil pair | H | H | H | H | H | H | H | blind (verified numerically) |
| 4 | pure-point regularized dual, almost periodic | H | H | H | H | H | H | H | blind |
| 5 | BRS uniqueness pair | H | H (remark) | H (remark) | Poisson | H (remark) | H (remark) | n.c. | blind |
| 6 | zero measure translation bounded / FT a measure (Theorem G) | F | F | F | F (H4) | F | F | F | vacuous for all |
| 7 | u.d. support or spectrum | F | F | F | H lattice only | F | F | F | zeta fails |
| 8 | FQ (abs. dual tempered) | F uncond. | F | F | F | F | F | F | zeta fails, even under RH |
| 9 | pure-point diffraction (AFQ i) | F (Montgomery) | n.c. | n.c. | n.c. | n.c. | n.c. | n.c. | ill-posed |
| 10 | finite Lee-Yang representation | F | F | F | F | F | F | F | zeta fails |
| 11 | distributional temperedness of the dual | H* | F | F | F | F | F | F | CIRCULARITY |
| 12 | Weil positivity | H* | F | F | F | F | F | F | CIRCULARITY (E6Bridge9) |
| 13 | Lambda_F >= 0 | H | F | F | H | F (W1: Lambda(29^2) < 0) | F | H | partial |
| 14 | Euler product (Bragg on prime powers) | H | F (Lambda_D(6) = 1.936) | F | H | H | F | H | partial |
| 15 | local Ramanujan / local Lee-Yang at every p | H | n/a | n/a | F | F (onset c = 2, kernel) | F | F | separates the Euler controls only |
| 16 | only pole at s = 1, Gamma_R arch | H | F | F (deg-2 arch) | F | H | H | F | partial |
| 17 | Theorem-A package in 1D (positive self-dual comb, gap, zeta FE) | H | F (signed, cond. 5) | F in 1D; H for its d = 2 analogue | F (gap) | F (gap only, crystalline form) | n.c. | F (Gamma shape) | zero-blind (K1, K2) |
| 18 | invariant under the E_theta shift | -- | -- | -- | -- | -- | -- | -- | any such property is dead |
| 19 | P_min / class P / Selberg S | H | F | F | F | F | F | F | separates, but "=> real" is RH / GRH verbatim |

**Reading.** The separators are rows 2, 11 and 12 (RH_F itself) and row 19 (arithmetic identification of zeta).
Row 15 separates the Euler-product controls but is blind to DH and Epstein, and adding "Euler product" to it lands
in row 19. No row is simultaneously non-circular, a separator, and backed by an FQ mechanism. This last sentence is
HEURISTIC as a meta-claim over the rows examined.

## 5. Verified builds

### 5a. Skeptic-unrefuted (a referee recomputed them; no referee refuted them)

- **Literature numerics** (`literature/fq_numerics.py`; re-run by this writer, under 1 s):
  - S(15) = 15.4947;
  - zero window counts 0.40 -> 1.00 for T = 100 -> 2400;
  - Bohr coefficients m = 2, 3, 5: -0.487, -0.630, -0.714, against -0.490, -0.634, -0.720; m = 6, 10, 12, 15
    give below 0.01;
  - off-line injection: alpha_fake = +18.193 against an envelope of 21.852 at x = 16.8.
  - CORRECTION: the true-prime alpha range is [-3.39, -1.91] (dense), and its sign is -mu_AdR.
- **Rigidity N1-N4** (ref-rigidity):
  - GW normalization residuals 1e-22 to 1e-31;
  - local lines: golden 0.798994, W1 0.561221;
  - Arb: mu_cont < 0 on [1, 5.8], with mu_cont(3) = -0.0840382413870272863356 +/- 1e-36.
- **Negative-control harness** (ref-negative-control):
  - DH GW residual 4.62e-29 with the off-line quadruple, whose contribution is 4.0855;
  - golden Poisson residual -1.97e-31;
  - E_theta residuals -2.4e-15 (theta = 0.2) and -1.97e-31 (theta = 0.45);
  - W2 counts 72 = 66 + 6, and 330 = 330 below height 150;
  - both Epstein off-line zeros re-found (COMPUTED).

### 5b. Writer-reverified kernel artifacts (kernel-seat skeptic status UNKNOWN)

All three files are UNTRACKED under `/Users/peterwmurphy/arda-crux-fq/telperion/examples/`. They are not
committed, not in CI, and not in AxiomGuard. Their hashes match the seat notes. A token scan for
sorry / admit / native_decide / axiom / opaque / unsafe / partial / set_option / macro / elab / #eval in code was
clean. Each was rebuilt by this writer with `lake env lean` (single process):

| file | lines | sha256 (prefix) | rebuild | `#print axioms` |
|---|---|---|---|---|
| `li_positivity/lean/Crux/CruxFQ_PoissonRigidity.lean` | 1523 | d1c5ab5c | exit 0, 41 s | 30/30 [propext, Classical.choice, Quot.sound] |
| `li_positivity/lean/Crux/CruxFQ_kernel.lean` | 2958 | 03a8e42b | exit 0, 18 s | 37/37 standard |
| `rvm_bridge/lean/Crux/CruxFQ_ZeroSideFejer.lean` | 75 | 854fada3 | exit 0, 16 s | 4/4 standard |

Also re-run:
- `ref-kernel/ref.py`: |W1(s*)| = 7e-47; 29^{-s*} = (-11 + sqrt 5)/58; nu_{7,3} Gaussian self-duality residual
  2e-25; Satake roots of modulus 1 at c = 1.9 and 2.0, and 1.370 / 0.730 at c = 2.1.
- `research/crux_fq_kernel/epstein_d2_arb.py` (37.9 s): six certified winding-1 boxes; completed FE defect
  [+/- 9.07e-40].

Rebuilding does not audit statement fidelity. The key statements were read (`IsPoissonPair`, `poisson_rigidity`,
`fq_rigidity_is_rh_blind`, `theta_rigidity_is_rh_blind`, `HamburgerConverse`, `no_antiTheta`) and match the prose.
A blind read-back audit is still required before any grant.

## 6. Verdict

**Zero side: blocked, and a relabeling where it is not blocked.**
- Every positive-measure FQ structure theorem is vacuous for zeta and all controls. This is Theorem G, via the
  gamma factor's log density, and it holds unconditionally.
- Every zero-side positivity / temperedness / Hermite-Biehler / eta >= 0 clause is RH:
  - the Arias de Reyna + Bochner-Schwartz triangle;
  - E6Bridge9;
  - Vedana;
  - Goncalves.
- The FE-uniform certificates (Miller-type LP, `zero_side_fejer`, BRS) are blind to DH and the golden fake.
- The only reality-forcing FQ mechanism (Lee-Yang) is local. It equals local Ramanujan: Theorem E, K2's
  `satake_ramanujan_iff`, and Theorem L all say the same thing.
- E_theta kills every shift-invariant property outright.

**Prime side: a genuine lever, but not an RH lever.**
- Theorem A is literally an FQ (crystalline) rigidity theorem, and it is now kernel-checked in crystalline form.
- The full Dirichlet-series form is reduced in the kernel to one classical analytic input, `HamburgerConverse`.
- K2 proves in the kernel that this rigidity is zero-blind: the crystalline data are identical across the zero
  transition c = 2.
- The d = 2 / d = 8 ladder shows that rigidity and zero location are independent.
- Theorem D shows the prime side is rigid given the zero side's archimedean data, but it inherits all of its content
  from Theorem A.

**Classification.** A lever for the prime-side program (NT4 and the twisted Beurling cell), a relabeling on the zero
side, and blocked by the controls (E_theta, nu_{p,c}, and d = 2 Epstein) for any route from FQ rigidity to zero
location. The FQ angle is closed as an RH route. This is CONJECTURE-with-evidence that no FQ-type separator exists
beyond those examined.

**Precise next theorems** (none bears on RH):
1. **HamburgerConverse in the kernel.** For N satisfying `BeurlingNormalized` and `ZetaShapeFE 1`, symmExt N
   satisfies ThetaRelation or AntiThetaRelation.
   - Route: L = (t d/dt)(4 t d/dt + 2); Mellin(L theta_N) = xi(2s); Mellin inversion, Phragmen-Lindelof, and
     rectangle Cauchy with no poles; ker L = {A + B t^{-1/2}}.
   - Payoff: `classP_collapse_beurling_q1` (NT4) becomes an unconditional kernel theorem.
2. **The twisted Beurling cell R4, u.d. subcase** (CONJECTURE). For conductor q > 1, nu^ is a dilate of nu. With
   u.d. support, Lev-Olevskii 2015 Thms 1+3 or Baake-Spindeler-Strungaru Thm 6.3 give finitely many lattice cosets,
   and a Pisot / integrality argument then closes via round 1's R2. This is the only FQ-powered target with content.
3. **The novelty check for Theorem A** in the correct lineage, BEFORE any external claim:
   - Hamburger 1921/22;
   - Bochner 1951;
   - Bochner-Chandrasekharan, Ann. Math. 63 (1956);
   - Chandrasekharan-Mandelbrojt;
   - KM58 Thms 4, 5, 10;
   - Knopp;
   - Kaczorowski-Perelli;
   - Cordoba 1989;
   - Cohn-Elkies 1D / Cohn-Goncalves 2019.

   The crystalline argument is short (it tests against tri and its translates), so HEURISTIC: the measure-level
   statement may be folklore. What may be new is "positivity replaces discreteness".

## 7. Proposed draft nodes

Every node below is NOT proved as RH progress.

**Before any `mission add` or `grant`:**
1. Commit the untracked Crux files.
2. Add every theorem to an AxiomGuard target.
3. Put a skeptic on the kernel seat. Its referee reports were not received.
4. Run a blind read-back audit.
5. Wire cross-island CI for the rvm_bridge node.

| node | kind | status | content |
|---|---|---|---|
| `MM_fq_thmA_crystalline` | lemma | proved (kernel artifact) | `CruxFQ.poisson_rigidity` / `selfDual_rigidity`. Title must say "prime side; zero-blind" |
| `MM_fq_rigidity_rh_blind` | no-go lemma | proved | `fq_rigidity_is_rh_blind` + `theta_rigidity_is_rh_blind`: the Theorem-A package minus the gap admits nu_{p,c} with zeta's FE and a zero in 1/2 < Re s < 1 |
| `RH_classP_collapse_beurling_q1` (existing draft) | milestone | reduce | attach `classP_collapse_beurling_q1_of_hamburgerConverse`; new dependency below |
| `RH_hamburger_converse` | milestone | STATED ONLY | `HamburgerConverse` (registry defs verbatim); classical (Hamburger / Kahane-Mandelbrojt); not RH |
| `MM_fq_zero_side_fejer` | no-go lemma | proved (rvm_bridge) | `zero_side_fejer`: prime-gap tests see only archSide, off-line zeros included (FE-uniform) |
| `MM_fq_archimedean_obstruction` | no-go | paper; substrate-blocked | Theorem G via Favorov-Deger Thm 1 + RvM. Needs FT of tempered measures in Mathlib |
| `MM_regularized_prime_measure_tempered_iff_rh` | dictionary | paper | Arias de Reyna Thm 3. Tag CIRCULARITY; never an edge toward the goal |
| `MM_negctl_etheta_shift` | control | kernel target | E_theta: Lambda >= 0, FE, and off-line zeros above every height via `exists_nontrivial_zero_above` + parity; replaces the scratch EisensteinShiftControl |
| `MM_negctl_epstein_d2_offline` | control atom | Arb-certified | disc -35 covolume-1 lattice: positive, self-dual, gap > 1, certified off-line zeros |

**Text-only doc fixes.**
- `DYSON_QUASICRYSTAL_CERTIFICATES.md`:
  - Kurasov-Sarnak is arXiv:2004.05678 (2006.12037 is Olevskii-Ulanovskii).
  - Untangle Alon-Cohen-Vinzant (JFA 286 (2024) 110226, arXiv:2303.03201) from Alon-Vinzant (Rev. Mat. Iberoam.
    40 (2024), arXiv:2307.13498) and Alon-Kummer-Kurasov-Vinzant (Invent. Math. 239 (2025) 321-376).
- `QC_RIGIDITY_MEMO`:
  - Favorov arXiv:2408.09563 is sole-author; Favorov-Deger is arXiv:2605.10766.
  - Retire R1 as a proved relabeling, and mark the literal (H-temp) false for zeta.
- `QC_LITERATURE` section 2: the RH-sensitive grade is the signed / distributional one (Arias de Reyna), not the
  absolute one.
- AFQ spec:
  - Replace clause (i) with "Bohr-Fourier coefficients supported on log p^k" (unconditional; separates only the
    non-Euler controls).
  - Record E_theta as the requested negative control.
  - Close A0 as done in print (Guinand 1959, Arias de Reyna 2024, Vedana 2026).
- Lev-Olevskii 2017 is Adv. Math. 315.
- Shaughnessy arXiv:2410.03673 v12: its self-duality step would prove GRH for DH, which is false.

## 8. What was not checked

- **The kernel seat's referee reports.** The payload was truncated. The kernel artifacts are writer-rebuilt, but
  not skeptic-audited or blind-read-back-audited here.
- **Theorem A's novelty** against the Hamburger / Bochner-Chandrasekharan / KM58 / Cordoba / Cohn-Elkies lineage.
  All three literature-facing referees flagged this. The WebSearch budget was exhausted in the seats.
- **The Kahane-Mandelbrojt / Bochner growth hypotheses** against the "finite order" in `ZetaShapeFE`
  (HamburgerConverse). The C_c-vs-Schwartz caveat on `IsPoissonPair` is not formalized.
- **Unread sources:** Goncalves Remark 5 (Theorem L's N-valued completeness), Tselishchev, Favorov arXiv:2311.02728,
  Alon-Vinzant, Guinand 1948/1959, Cordoba, Meyer 2017/2022, and Landau 1912.
- **Unrefereed or uncertified pieces:**
  - The generalization of the Arias de Reyna equivalence to DH (writer's check, unrefereed).
  - The writer's completion of Arias de Reyna's converse is referee-checked but not written out in full.
  - The BRS 5.3.3 extensions (a remark in the source).
  - Prop K's normalization, and its DH onset at log 30.5 (COMPUTED).
  - The second Epstein x^2+5y^2 zero (COMPUTED, not Arb-certified).
  - The d = 8 mass-determination step (paper sketch).
  - d = 24 zero location (not examined).
- **Theorem E stability (O3), O1 (non-integer positive partners), and O2 (the dual of R4)** are open.
- **Left uncorrected:** the rigidity seat's Ftwin parameterization (c < -2 sqrt p in its normalization) was not
  reconciled with the kernel's nu_{p,c} (c > 2).
- **Not run by this writer:** the Epstein x^2+5y^2 root-finding scripts and the DH / W1 / W2 scripts. These rely on
  the referees' recomputation.

`conjecture1_proved = False`.
