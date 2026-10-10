# Skeptic verdicts (missing-Frobenius research, 2026-09-24)

Each angle was reviewed by an adversarial skeptic that checked citations, novelty and the Davenport-Heilbronn control.

## connes
- proposal survives: False; novelty: partially known; DH control holds: True

**Reason.** I reran the numerics independently with a convergence check over N in {60, 90, 120, 160} and M up to 800 (connes_skeptic/conv.py, defect_all.py). They largely confirm the core D-control facts:
- D's least even eigenvalue at x=35 is -3.5e-11, stable in N.
- At x=40 it is -2.5e-2.
- L(chi_5), with the same Gamma factor and conductor, stays positive at x=40 (+1.11e-9, converged). On D's negative vector it gives +2.154 against D's -0.025.
- The composite-n dominance in the defect is real on that vector.

So the D control is genuine in the sense that D does fail, but only via window Weil positivity (the A4/Hodge-index input) at D's horizon. Crux3 and the CCM criterion already contain that. The proposal is a well-executed calibration study showing that the realness theorem and the numerical zero accuracy in the CCM/Connes-letter program are D-blind. It is not a step toward RH.

The float64 claims near the roundoff floor (x=17, x=31-34, second eigenvectors) are unsupported. Lemma H and the 'RH iff index (1,0)' statement need correcting. The 'x >~ 31' prescription is specific to D.

The honest-odds figure of well under 1% is calibrated; if anything it is generous for a positivity mechanism, and the report correctly identifies A4 as the whole problem.

**Errors found:**
- Nothing in the proposal bears on RH. P1 and P2 are satisfied by D by design; the proposer says so, and I confirm it. P3 and P4 separate zeta from D only through the sign of lambda_0(x), i.e. window Weil positivity. That is the criterion already stated in CCM Cor. 3.8, and D's negativity beyond x~31 is already the project's Crux3 result. The only new element is a numerical calibration.
- P1 is essentially stated by the authors. CCM 2511.22755 says verbatim: 'The method we use is general as well as the proof that all the approximating values lie exactly on the critical line.' The CvS 2511.23257 hypotheses (real even distribution, lower-bounded, simple isolated lowest eigenvalue, even eigenvector) contain no arithmetic by construction. Applying it to D is a correct observation, not a discovery.
- P3 uses float64 eigenvectors that are ill-defined. I reran the convergence check (connes_skeptic/conv.py) for D at x = 31, 33 and 35: the second even eigenvalue is about 1e-15 at every N, i.e. a roundoff-degenerate near-null cluster. So the claims 'median error ~1e-13 at x=34' and 'the 2nd eigenvector (lambda ~ +1e-15) reproduces D zeros to 1e-11' refer to an arbitrary vector in a numerically degenerate subspace, not a specific eigenvector. The lambda_0 sign at x = 31 and 33 is also undetermined in float64: it flips between +4e-16 and -1e-14 as N changes. Only x = 35 (lambda_0 = -2.3e-11 to -3.5e-11, stable in N) and x = 40 are sign-resolved.
- P2's 'at least as well at matched lambda_0' compares different windows and different archimedean data: zeta at x=4 against D at x=15-17, with conductor 5 and an odd Gamma factor. D at x=17 has lambda_0 = 5e-15, at the float64 roundoff floor the report itself sets (below ~1e-14). The claimed 6.6e-14 zero accuracy there is not trustworthy without Arb.
- Lemma H is misstated. Q0 - 2vv^T >= 0 does NOT require Q0 > 0. The correct condition is Q0 PSD, v in range(Q0), and 2 v^T Q0^+ v <= 1. 'RH iff for every x: ind Q0_even = 1, ind Q0_odd = 0, ...' is an overstatement: the even-sector condition is [Q0_even PSD] OR [ind = 1 and sigma_+ <= -1], and singular or edge cases are dropped. Counting the index as (e0 < 0).sum() on a Galerkin matrix is also fragile near zero.
- '1 + sigma_+ = -0.0012 is exactly the slack of KWin's 1.33e-3 margin' is not an identity. The Schur scalar and the least eigenvalue are different quantities that happen to be of similar size (1.20e-3 vs 1.33e-3).
- 'Any Connes-type positivity proof must use prime-power support at windows x >~ 31' overgeneralizes one control. 31-35 is D's horizon, set by the height 85.7 and offset of its off-line zero and by its conductor. Other non-Euler controls could fail at different x. The matched control for zeta itself (degree 1, conductor 1, pole) cannot exist in the Selberg class, which is the project's known class-P = {zeta} barrier.
- P4's 'composite-n pinpoint' depends on the choice of vector and of comparison function. I confirm the numbers: on D's negative vector at x=40, D minus L(chi_5) splits as composites -1.544, prime powers -0.438, primes -0.197. So D also differs at the primes themselves (c_D(p) = a(p) log p, while Re chi(p) Lambda(p) = 0 for p = 2, 3 mod 5). Composites dominate on this one vector. That supports a heuristic, not a structural statement that positivity must come from composite vanishing.
- 'Convergence of the determinants to Xi is equivalent to mu_lambda >= 0 for all lambda' is loose. CCM Cor. 3.8 gives only lim mu_lambda = 0 => RH; that determinant convergence is equivalent to it is not established.

**Citation problems:**
- The 'CMP 2025' journal reference for Connes-van Suijlekom 2511.23257 is unconfirmed; the arXiv abs page shows no journal reference. The paper itself exists (28 Nov 2025), and the real-zeros theorem and its hypotheses are as stated.
- Connes-Moscovici 2112.05500's arXiv title is 'Prolate spheroidal operator and Zeta' (10 Dec 2021). The report's pairing with 'PNAS 2022' (published as 'The UV prolate spectrum matches the zeros of zeta') is plausible but I did not verify it.
- Connes-Consani 2006.13771 exists (24 Jun 2020); arXiv lists no journal reference. I could not verify the specific window [2^{-1/2}, 2^{1/2}] or the 'Theorem 1 needs g-hat(0) = 0' detail from the abstract.
- Verified: CCM 2511.22755 'Zeta Spectral Triples' (27 Nov 2025). Cor. 3.8 is quoted correctly, and the paper does not mention Davenport-Heilbronn.
- Verified: Connes 2602.04022 (3 Feb 2026): primes < 13, first 50 zeros, 2.6e-55 to 1e-3.
- Verified: Connes-Consani 2606.06604 (4 Jun 2026) and 2205.01391 (May 2022).
- Verified: CCM 2310.18423 (v1 Oct 2023, v2 4 May 2024).
- 'lambda_0 ~ 1e-150 for zeta at x = 57' is cited from project round 2 and was not independently checked.
- I could not run a novelty search for a DH control of CCM zeta-cycles: the session web-search budget was exhausted, so novelty rests on the CCM text alone.

**Salvage.** What can be kept:

(1) Publish-quality negative control, once certified in Arb/high precision:
- CvS realness and CCM-style zero approximations hold for D below its horizon.
- D's lowest-eigenvector approximation collapses at x of about 31-35.
- A false real zero shadows the off-line quadruple at 85.70.

It should be stated as a calibration of the CCM/Connes-2026 numerics, citing CCM's own 'the method is general'. Redo it at high precision with gap-aware eigenvector selection. Drop the 2nd-eigenvector and x=17 claims unless Arb confirms them.

(2) A corrected Lemma H as a small Mathlib lemma:
- Rank-one update of a PSD matrix, with the pseudo-inverse and range condition.
- The one-negative-direction case via the determinant (Q0 + 2vv^T has det = det(Q0)(1 + sigma)) plus interlacing.
- Present it as a relabeling (Castelnuovo shape), not new RH content.

(3) Kernel witness 'ind Q_D,x >= (1,1)' at x=40 or 57: an odd-sector negative vector for D alongside Crux3's even one. It is cheap and certifiable.

(4) The next informative control is a pole-bearing, degree-matched fake: an Epstein zeta of class number > 1 (e.g. x^2 + 5y^2), or a linear combination of zeta-like L-functions sharing Gamma factor and pole. That tests Lemma H's pole/Hodge structure, which D cannot.

## deninger
- proposal survives: False; novelty: partially known; DH control holds: True

**Reason.** The numerics and algebra are correct, and I reproduced them. The minimal polynomial x^4+2x^3-6x^2-2x+1 checks out. (1+i kappa)/(1-i kappa) equals the Gauss-sum root number to 30 digits, and -1/kappa gives the negative of it. b(6) = 1+kappa^2. The failure of D is real: D fails C1 and fails G.

The GCE proposal is still not a worthwhile deliverable. Its content is a counting triviality: the FE set is 2 points of a Mobius pencil, and the Galois orbit has 4 points. It is redundant with the classical absence of an Euler product (C1), which already excludes D before holonomy can even be defined. It is not robust either, because every rational-coefficient off-line fake (Epstein, rational combinations of newform L-functions) passes G. So it exposes nothing about the mechanism that puts zeros off the line.

That Galois conjugates of motivic L-functions keep an FE is classical (Shimura, Deligne rationality). The DH-specific failure is probably unrecorded, but only because it is immediate. The period and volume lemmas are correct and essentially known.

The honest-odds assessment (well below 1%) is calibrated, and if anything generous. The overall diagnosis is sound and matches the literature: compact Riemannian systems force alpha=0, solenoidal/Witt models have no Hodge theory, and D6 is a restatement of RH.

**Errors found:**
- GCE is close to a tautology. I checked this independently (/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/frob/deninger_skeptic/check.py). The FE condition on the pencil D_y is exactly (1+iy)/(1-iy) = w*eps(chi), where eps = tau(chi)/(i sqrt5) = 0.850650808+0.525731112i. A real Mobius parameter hits a given unimodular value exactly once, so the FE set is always the two points {y0, -1/y0}. kappa has degree 4, so its Galois orbit has 4 elements, and 2 conjugates must fail the FE. That counting argument is the whole content. The mpmath defect table (0.05 to 4.1) only confirms it and adds nothing.
- GCE-1 claims that D's own FE 'pins y0 = kappa without evaluating a Gauss sum'. That is circular. To prove in Lean that D satisfies the FE, you need (1+i kappa)/(1-i kappa) = eps(chi), and that is the explicit value of the mod-5 Gauss sum. So the Lean cost is understated: GCE-1 needs the Gauss sum value in Q(zeta_20), which involves sqrt(10-2sqrt5), and not only rootNumber as an opaque constant.
- Condition (G) is vacuous for D. (G) talks about holonomy local factors det(1 - rho(gamma) e^{-sl})^{-1} of an Euler product over closed orbits. D has no Euler product, and C1 already excludes it: b(6) = 1+kappa^2 is nonzero, and I verified c6 = k^2+1 symbolically. So 'no Galois-coherent Deninger system realizes D' follows from C1 alone. The conditional corollary adds no exclusion power beyond the classical reason, which is the lack of an Euler product.
- (G) does not track the Davenport-Heilbronn phenomenon, only this particular D. The report admits (G) is automatic for rational coefficients. The Epstein zeta for x^2+5y^2, and rational linear combinations of Hecke/newform L-functions with the same FE (Bombieri-Hejhal-type zeros off the line), have rational coefficients, pass G, and violate RH. So G is not a structural filter against off-line zeros. The claim that it is 'the program's first structural (not windowed) exclusion of D' is overstated: the Euler-product/C1 exclusion is classical and already sits in the kernel data (Crux3 dtab 6).
- The period-group and volume lemmas are correct. I checked the normalization omega(Y)=1: omega(Y) is basic, so omega/omega(Y) is closed, and L_Y omega = d(omega(Y)) = 0. But they are not new. AKM line 82 already states that Spec(O_k) 'must be infinite dimensional', and AKM Lemma 2.3 plus Remark 1.2(1) record that there are no fixed points without preserved leaves. The fact that alpha must be 0 on a compact system without fixed points (volume preservation), so the alpha=1 case needs the archimedean fixed leaves, is to my knowledge a standing remark in Deninger's surveys. They are fine as background but should not be presented as findings.
- 'D6 is equivalent to Weil positivity for all L, hence RH' is a heuristic identification, not a theorem, because the Hilbert space realizing it does not exist. The report's own conclusion ('building it would restate RH') is right, but the axiom list states the equivalence as if proved.
- The tensor-power paragraph is loose. The two-parameter trace on H^1 tensor H^1-bar is sum_{rho,rho'} e^{t1 rho + t2 conj(rho')}, not |sum e^{t rho}|^2 at a single t. The link to Montgomery pair correlation beyond |alpha|=1 is suggestive, not derived. It is fine as a pointer, not as a located failure point.

**Citation problems:**
- The ICM 1998 citation (Doc. Math. Extra Vol. ICM I, 23-46) is copied verbatim from the AKM bibliography [D6]. I could not verify the page range independently: the Documenta links redirected and the web search budget was exhausted. My recollection is that the Vol. I plenary pages are different (around 163-186). Treat this as unverified.
- Verified on arXiv: 2402.06671, Alvarez Lopez-Kordyukov-Leichtnam, 'A Trace Formula for Foliated Flows', submitted 7 Feb 2024, handles finitely many preserved compact leaves. 2508.15971, Morishita, v5 revised 21 Jan 2026, to appear in Munster J. Math. 1906.02424, Kim-Morishita-Noda-Terashima, Munster J. Math. 14(2) 2021. AKM 2410.20758: Theorem 1.8, Theorem 2.5(1)-(3) and Lemma 2.3 are quoted accurately from the extracted text (Thm 2.5(3) is 2 - sum e^{rho x} = sum l(gamma) sum eps_gamma(k) delta_{k l(gamma)}).
- Not re-verified (the report also flags these as from memory): Lafforgue Invent. Math. 147 (2002); Drinfeld Moscow Math. J. 12 (2012); Weil II Conj. 1.2.10; Kopei Abh. Hamburg 81 (2011); Leichtnam math/0603576 and 1307.3851; Morin 1006.0527; Connes-Consani 2006.13771. They look standard and plausible, but I did not check them this session because the arXiv API returned nothing and the search budget was exhausted.
- The Jber. DMV 103 (2001) 79-100 Theorem 2.1 and Progr. Math. 171 (2000) 29-87 citations match the AKM bibliography [D7] and [D8].

**Salvage.** 1. Keep the axiom checklist (C1 Euler product / G Galois coherence / P purity / D6 Kahler) as a way of sorting the project's fakes: D fails C1, Epstein fails C1, W_{p,c} fails P. It is a useful organizing table, but label G as redundant with C1 for D and as powerless against rational fakes.

2. The C1 certificate (b(6) = 1+kappa^2, meaning an orbit at log 6 would be needed) is the real DH control. It is cheap and nearly in the kernel already (Crux3 dtab 6). A small Lean lemma, 'the formal Euler exponent of D at 6 is 1+kappa^2, which is nonzero', is honest and checkable.

3. If GCE is formalized at all, state it as the Mobius fact: the FE set of the pencil {y : Lambda_y has an FE} equals {y0, -1/y0}, with (1+iy0)/(1-iy0) = eps(chi). Budget for the explicit mod-5 Gauss sum. Do not advertise it as a new structural exclusion.

4. The survey value stands. ALKL 2024 has a trace formula with preserved leaves but no Hodge theory. AKM 2024 gives the determinant formula with alpha=0 forced. Morishita 2025/26 connects to the Connes-Consani adelic spaces. The missing object is a non-compact or solenoidal system with an archimedean fixed leaf and a leafwise Hodge theory with alpha=1. Present this as literature positioning, not as a new result.

5. Drop the D6-equals-RH 'equivalence' wording, and the |sum|^2 / pair-correlation 'exact failure point', or mark both as heuristic.

## hilbertpolya
- proposal survives: False; novelty: known; DH control holds: True

**Reason.** I independently reproduced everything that matters (scripts in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/frob/hilbertpolya_skeptic/check.py and gapcheck.py).
- kappa = 0.2840790438.
- The off-line zero 0.808517182456637 + 85.699348485377592i, with |D| = 6e-26 there.
- c_D(6) = (1 + kappa^2) log 6 = 1.936356. I also derived it by hand from the recursion a(n) log n = sum_{d|n} c(d) a(n/d), using a(6) = a(1) = 1.
- Argument-principle count on the box [-1,2] x [83.2,87.6]: 2.0 zeros.
- Z_D is real on the line (relative imaginary part 3e-24), changes sign only at 83.12 and 87.66 in [83,87.8], and has min |Z_D| = 0.357 on [83.3,87.5].

So the D control holds, for a genuinely arithmetic reason: the coefficients are not multiplicative, and a composite orbit length log 6 appears.

The deliverable still does not survive as a new proposal:
- Lemma O (c is supported on prime powers if and only if a is multiplicative) is the textbook equivalence 'Euler product iff log F is supported on prime powers'. A Lean port is small, useful plumbing, not research.
- OHT-1(c) rebrands 'Euler product + functional equation + growth => zeta' (Hamburger-type, already classP_eq_zeta in the project) plus 'Weil positivity' as the Hilbert-Polya axioms. The author admits the residual obligation is exactly the open KWin-for-all-L problem, so nothing narrows.
- OHT-2 re-certifies D zeros that Spira (1994) and Balanzario and Sanchez-Ortiz (2007) already computed.
- The Weyl-deficit reading of D's off-line zeros is already in LeClair-Mussardo, JHEP 2024.
- Prediction 1 is miscalibrated and will be falsified by L5 itself at 10^4 spacings.

The honest-odds statement (below 1%, nothing narrows RH) is well calibrated, arguably still generous for a program that has made no positivity progress since 1999. The BBM trap (the periodic-coefficient embedding H_a = A(xp+px)A^-1, which carries Bender-Brody-Muller over to D with complex eigenvalue -171.3987 + 0.6170i) is correct and a clean, checkable negative control. It is the most valuable concrete item here, but the idea that the BBM construction does not use the Euler product is the substance of existing criticism, so it is at most partially new.

**Errors found:**
- HP1 misstates Connes 1999. The report says Connes (Selecta 1999), like Meyer, realizes ALL zeros, off-line ones included, as a spectrum. That is wrong. The arXiv:math/9811068 abstract (checked) says: 'spectral interpretation of the critical zeros ... as an absorption spectrum, while eventual noncritical zeros appear as resonances.' Only Meyer (Duke 127, 2005) realizes all zeros as a spectrum. Connes' L^2_delta construction sees only the critical zeros, and RH becomes the validity or positivity of his trace formula.
- HP4 uses the wrong name for the symmetry class. An antiunitary C with C H C^-1 = -H is a particle-hole symmetry (Altland-Zirnbauer class D or C, depending on C^2). A chiral symmetry is a UNITARY operator that anticommutes with H. The spectral symmetry gamma -> -gamma of xi can be implemented either way, so it constrains nothing locally, because it pairs eigenvalues that are far apart. Calling time reversal on xp 'chiral in exactly the right way' is therefore mislabeled. The report itself flags HP4 as a heuristic.
- Prediction 1 will fail at scale ('every hole > 2.2 unfolded spacings contains an off-line pair'). At T <= 1200 it holds: I recomputed 36 gaps > 2.2 against a count deficit of -72.0, i.e. 36 pairs, and there is a clean break between 2.02 and 2.32. But the GUE Wigner tail is P(s > 2.2) = 0.0063, so the proposed test on 10^4 spacings should show about 60 gaps above 2.2 in L5, which has no off-line zeros. The threshold is not scale-invariant. At T = 1200, L5's maximum gap of 2.16 reflects low-height rigidity, not a law. The claim that every off-line pair produces a hole of at least 2 is also unproven, and can fail when two off-line pairs sit close together or when fluctuations shrink the gap.
- N3 overstates its conclusion. After the holes are removed, the spacing test still gives KS p = 0.015, with variance 0.105 for D against 0.129 for L5. The truncation (dropping gaps > 2.2) lowers the variance mechanically, so the claim that D is 'marginally MORE rigid' is at least partly an artifact of that cut. The qualitative point stands: small-gap repulsion is the same for D and L5. But 'DH-blind' is close to a tautology (off-line zeros simply are not in the line spectrum), not a finding.
- Minor: 'Ramanujan-type bound' is the wrong name for |c(n)| <= log n, which is a von Mangoldt-type bound. The reported slope of 0.069 and '35 pairs' should read about 36 pairs at T = 1200: I measured a deficit of -72.03 at the last zero. Proposition T is a meta-statement, not a theorem; it restates the project's existing fooling lemma for Hamiltonian proofs.

**Citation problems:**
- Connes 1999 is cited correctly, but the report misreads what it realizes (see errors). Checked against arXiv:math/9811068.
- LeClair-Mussardo, JHEP April 2024 (arXiv:2307.01254): I VERIFIED it exists. It already uses the Davenport-Heilbronn function as a control: D satisfies the symmetry but has no Euler product, and its solutions 'deviate from the critical line', which they read as incompleteness of the Bethe-Ansatz quantization. That is essentially the report's 'silently drops each off-line pair' observation, and the zero-side DH control behind OHT-2 and N1. The report marks this paper '[memory, not verified]' and does not credit the overlap.
- Connes-Consani-Moscovici, arXiv:2310.18423: VERIFIED (submitted 27 Oct 2023, revised 4 May 2024). The description is accurate: the positive spectrum tracks low-lying zeros, and the Sonin space (negative spectrum) gives the ultraviolet behavior. No positivity proof is claimed.
- Bellissard, arXiv:1704.02644 (Apr 2017): VERIFIED, and the quote 'does not actually work' is accurate.
- Conrey-Li, arXiv:math/9812166 (Dec 1998): VERIFIED. The abstract says they document the difficulty of de Branges' positivity conditions. The stronger reading, that the positivity condition is FALSE for zeta, matches the published IMRN 2000 content as I recall it, but I could not confirm it from the abstract.
- Not verified (search budget exhausted): Meyer Duke 2005; Sierra 2007/2008/2019; Lagarias 2005/2006; Saias-Weingartner, Acta Arith 140 (2009); Trudgian, JNT 2014 (constants 0.112/0.278/2.510 agree with my recollection); Bombieri-Hejhal, Duke 80 (1995). None looks suspicious, but all are from memory.
- Missing prior art for OHT-2: rigorous computations of D's off-line zeros already exist. Spira, Math. Comp. 1994 ('Some zeros of the Titchmarsh counterexample') and Balanzario and Sanchez-Ortiz, Math. Comp. 2007 ('Zeros of the Davenport-Heilbronn counterexample') locate the zero at 0.8085 + 85.699i and the others. Both references are from memory, as I could not search. OHT-2 is a re-certification, not new.

**Salvage.** Worth keeping:
1. The BBM/D trap as a reusable, mechanical sanity check. It is correct: for any periodic a, phi_z(u) = -A(e^{ip}) u^{-z} gives eigenvalue i(2z-1), and D's off-line zero yields the non-real E = -171.3987 + 0.6170i. It belongs in project docs as the 'run any Hamiltonian claim on D' test.
2. Lemma O in Mathlib ArithmeticFunction form, plus the concrete witness c_D(6) = (1 + kappa^2) log 6. It is cheap, kernel-checkable plumbing that ties classP_eq_zeta to an explicit, orbit-level failure point for D. Present it as infrastructure, not as progress.
3. The quantified observation that D's count deficit is about 2 per off-line pair, 36 pairs by T = 1200 (measured deficit -72.0), with a clean gap separation at low height. Report it as low-height data, and cite LeClair-Mussardo 2024 and Spira / Balanzario-Sanchez-Ortiz as prior art.
Drop prediction 1, or restate it with a height-dependent threshold compared against L5's empirical gap tail. Drop the claims that D is more rigid than L5 and that local GUE statistics are DH-blind; the first may be a truncation artifact and the second is nearly tautological. Correct the Connes 1999 description (critical zeros form the absorption spectrum, non-critical zeros appear as resonances) and rename HP4's antiunitary anticommuting symmetry to particle-hole. Put the effort on KWin toward all L, as the report itself concludes.

## geometry
- proposal survives: True; novelty: partially known; DH control holds: True

**Reason.** I recomputed the key numerics myself. The scripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/frob/geometry_skeptic/: check.py and z2.py use sympy Kronecker symbols and a direct lattice count, and share no code with the original angle.

- **The Dirichlet identity holds** for n <= 200, up to the factor-2 normalization error above.
- **The weights are exact as reported.** c_E(n) >= 0 for all n < 36; the first negatives are at n = 36, 54, 84, 126, 189, 196; c_E(36) = -7.167 and c_E(6) = 3.584.
- **The off-line zeros are confirmed** to 25 digits: 0.9329696974854 + 15.66824953128i and 0.9376669067 + 29.98339523516i, with |E| ~ 1e-26. zeta_K is nonzero there (|zeta_K| = 0.93).
- **The certificate checks out.** In the angle's own zside.txt, arithmetic side = zero side for E (-0.450712 vs -0.45073) and for zeta_K (13.5393 vs 13.5389). This is an independent-method cross-check of the x = 28 certificate, and it supports Q_E < 0 with a large margin.
- **The threshold is not converged.** The weak point is the full-window value at x ~ 20: it keeps decreasing as more modes are added.

The DH control holds in the sense required. The positive side depends on the Lambda-supported weights Lambda(n)(1 + chi_-20(n)), which come from the Euler product. D and E lack those weights, and both actually have indefinite Weil forms. E is a legitimately stronger control than D: its first off-line zero is at height 15.7 against 85.7, and it keeps a_n >= 0, the pole, the Gamma_C functional equation and nonnegative weights on the window.

But none of this is a Frobenius or a positivity mechanism. It is a better counterfeit plus a finite certificate of the Crux3 type, and the certification method itself does not care about the Euler product. The survey part (A1-A6, the Borger square collapsing to Spec Z, the FF curve being genus 0, Habiro/mu_n adding H^1 rather than amplifying) is standard and correct as heuristics. The honest odds (< 1% for this angle reaching RH) are well calibrated, arguably generous.

It survives narrowly, as a diagnostic/barrier deliverable with the corrections above, not as progress toward RH.

**Errors found:**
- Normalization is off by a factor of 2. I checked coefficients up to n = 200 by direct representation counts: sum' (x^2+5y^2)^{-s} itself equals zeta(s)L(s,chi_-20) + L(s,chi_-4)L(s,chi_5), so a(1) = 2. The report's E = (1/2)sum' is therefore half of that expression, and by the same count (1/2)sum' Q1^{-s} = (zeta_K + L(chi_-4)L(chi_5))/2. This does not affect the zeros, the weights c_E or the signs, but P1 must fix one normalization before any Lean statement is written.
- The claim that 'the values are converged in the number of modes' is false near the threshold. thresh2.txt gives x = 20: M = 14 gives +0.001095, M = 22 gives +0.000151, M = 31 gives -0.000044. At x = 19: +0.0042, +0.0028, +0.0024. Both are still decreasing monotonically with M. So 'indefinite at x ~ 20' is only an upper bound: the true E threshold may be at or below 19, and 'lambda_min(19) = +0.0024' is not established. The x = 28 certificate is unaffected, because Q_E/|v|^2 = -0.165 is far from 0.
- 'KWin is Yoshida's theorem' is slightly overstated. I read the PDF: Connes-Consani, arXiv:2006.13771, p. 2 state Weil's inequality for support in (1/2, 2) only for f whose Fourier transform vanishes at +-2i (pole terms removed), and say it 'was proved in [34] by reducing it to an explicit computation', where [34] = Yoshida 1992. The project's KWin keeps the pole terms and works on the full space. It is the same window and the same mathematics up to a rank-2 pole correction, so 'essentially Yoshida, pole-kept variant, newly kernel-checked' is the accurate wording.
- 'E fails ONLY A6' is imprecise. E is not an arbitrary non-Euler series: it equals (zeta_K + L_genus)/2, a sum of two Euler products with the same gamma factor. Beyond the Euler product itself, it also lacks the Hecke eigen-property / primitivity, which is the Selberg-class axiom it fails. So 'isolates A6 as the only separating input among the listed properties' holds only relative to the report's own list.
- P2 is a heuristic filter, not a theorem. 'Any positivity mechanism whose inputs are only FE + growth + pole + a_n >= 0 + one-class theta + nonnegative window weights is refuted' has no precise statement. It is also a category error for Connes-Consani Riemann-Roch, which yields no positivity to refute. What E really shows is the concrete fact: a function with all those properties has an indefinite Weil form at x <= 20.
- The positive half of P1 (zetaK_window_pos at x = 28) is a finite-window numerical fact, implied by RH for zeta_K. It is not a positivity mechanism. The certification method (evaluate the arithmetic side and check the sign) is just as happy to certify E's positivity for x < 19. So the method is not D- or E-sensitive; only its numerical output is. This limits P1 to a barrier/diagnostic result of the same type as Crux3, not RH progress.

**Citation problems:**
- arXiv:2006.13771 (Connes-Consani, 24 Jun 2020): the paper exists. The Yoshida attribution and the (1/2, 2) interval are confirmed in the PDF text, but Yoshida's statement is under the extra condition fhat(+-2i) = 0 (pole-free subspace). The report omits that condition.
- arXiv:2605.03655: this is Scholze, 'Lectures on Analytic Geometry' (5 May 2026). It is 2019/20 lecture notes with Clausen credited as joint, and it is foundational. The report's characterization 'local or foundational' is fine.
- arXiv:2605.11731: Clausen-Scholze, 'Condensed Mathematics and Complex Geometry' (12 May 2026). Confirmed.
- arXiv:2510.15196: Anschutz-Bosco-Le Bras-Rodriguez Camargo-Scholze, 'Analytic de Rham stacks of Fargues-Fontaine curves' (16 Oct 2025, revised 3 Mar 2026). Confirmed.
- arXiv:2501.07944: Scholze, 'Geometrization of the local Langlands correspondence, motivically' (14 Jan 2025). Confirmed.
- Not independently rechecked by me (the report marks them 'from memory'): Borger 0906.3146, 2205.01391, 2412.04241 GSWZ, Faltings/Hriljac, Deninger ICM 1998. These are standard and plausible.
- Missing classical attribution: off-line zeros of Epstein zeta functions of class number > 1 forms go back to Potter-Titchmarsh (1935), Davenport-Heilbronn (1936) and Stark's computations (1967). Epstein zeta functions are the textbook 'FE without Euler product fails RH' example (e.g. Bombieri's Clay problem description). Using E as a counterfeit is therefore classical. Only the Weil-form threshold and the certificate numbers are new.

**Salvage.** (1) Adopt E = (zeta_K + L(chi_-4)L(chi_5))/2 = (1/2)sum'(x^2+5y^2)^{-s} (a(1) = 1) as the project's standard second counterfeit, next to D. The verified zeros and weights are ready to use.
(2) Pin down the E threshold properly. Push M until lambda_min stabilizes at x in {18, 19, 20}, or bound it by Richardson extrapolation in M. Report it as a certified interval, not '~20'.
(3) Formalize P1 via the Crux3 FWindow infrastructure with conductor 20 and Gamma_C arch, at x = 28 (large margin). Label it a barrier certificate ('E-blindness of all windows x <= 19' and 'separation at 28'), not progress toward RH.
(4) Restate P2 as a precise, testable filter: 'any candidate positivity statement must fail for E at x = 28'. Drop the claim that it refutes Riemann-Roch.
(5) Fix the KWin attribution: Yoshida 1992 proves it on the pole-free subspace (fhat(+-i/2) = 0; the +-2i in CC's multiplicative convention); the project's pole-kept, kernel-checked version is a variant.
(6) Cite Potter-Titchmarsh 1935, Davenport-Heilbronn 1936 and Stark 1967 for E's off-line zeros.
