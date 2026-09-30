# Hodge engine wave 6

conjecture1_proved = False.

## Portfolio

- **cascade_L1_guardband** (survivor_refinement): This is the ledger's highest-information priority (P1). R13 and the whole cascade side of R4/R17 currently rest on a numeric law plus an unproved lemma. Wave 5's cascade theorem was refuted precisely at L1 and at the misplaced M_L (C26). Proving or refuting L1 is the cheapest way to upgrade the project's main quantitative barrier to a kernel-certifiable theorem, or to learn exactly how much weaker it is.
- **period_height_positive_cone** (hybrid): P4 and Q11 have promoted central_value_nonnegativity_families and arithmetic_siegel_weil_heights_to_L as the only fresh numerator-in-strip automorphic leads, and neither has been screened. A one-line lemma probably kills both against the E ladder: period positivity is linear in L-values, and the E ladder is a positive cone. That would free future waves from them, while the GKZ Gram question keeps the one genuinely Hecke-quadratic sub-lead alive for a sharp test.
- **ff_theta_char_counterfeit_lab** (wildcard): P3/Q16 asks for a proof-carrying solved-world calibration, and the Ihara wave was criticized (C29, K12) for using a world without a proof. Curves over F_q have proofs AND, via theta-characteristic partial zetas, genuine FE-satisfying counterfeits computable in exact integers. So this is the first solved world where the ledger's E-type counterfeit exists. We can see exactly which proof step E-type objects break, and test the barrier_hunt's cumulant/ID finding in a second world.
- **id_cumulant_pringsheim** (barrier_hunt): Q7 has been open since wave 1, and the knowledge map rates global ID as MEDIUM-HIGH. The planner's pre-check shows log-coefficients of the E ladder are exact random-character cumulants, and that turns Q7 into an elementary, kernel-certifiable theorem via Pringsheim. That closes a standing lead with a precise barrier (ID is an Euler gate, not a source; B9/R6) at the kind of cost that Lean can certify, which is what barriers are for in this project.
- **siegel_segment_horizon** (micro_experiment): This is a sharp, harness-native question that joins three ledger items that have never been measured together: the B7/B8 pole-residue floor (w -> 0, via a Siegel-type real zero), the reference counterfeit E (w = 1/2), and genuine zeta_K (w -> 1). The barrier_hunt's cumulant finding makes n_neg(w) exactly predictable, so for the first time a counterfeit family can test whether an Euler-product defect ever precedes the Weil horizon. That is the R1 scale-location question that B5 answered only at the single point w = 1/2.

## Results

### cascade_L1_guardband (survivor_refinement)
- survives adversarial review: False; prediction matched: False; claimed barrier: L1 IS FALSE, in both the literal guard-band form and the same-edge form. Numeric; own arb code at dps up to 397; cross-checked by an independent direct quadrature.
(i) Literal form: band-T prolates, tail beyond T-r, right side C e^{2A|eta|}(1-mu). It fails already at eta = 0, with rho ~ exp(kappa 2A sqrt(2rT)), kappa = 0.82-0.88: log10 rho = 12.0 at x=20 and 20.6 at x=36 for r = 1/2. The index guard G is irrelevant.
(ii) Same-edge form: it fails with rho ~ exp(kappa0 2A sqrt(T|eta|) - 2A|eta|): log10 rho = 7.4 / 13.3 at eta = 1/2 and 10.9 / 19.2 at eta = 1, for x = 20 / 36.
Cause: the identity F_k(z) = A lambda_k psi_k(z/T) and the prolate's edge-layer local wavenumber c t/sqrt(t^2-1). It is not edge-phase cancellation.

CORRECTED LEMMA L1* (numeric, 60/60 points at x = 20 and 36 with constant 1). For any f in the span of band-T prolates (any size, both parities), g > 0, delta = g/T, |eta| <= 1:
(1/2pi) int_{|xi|>T+g} |F(xi+i eta)|^2 <= exp( 2A|eta| (1+delta)/sqrt(2 delta + delta^2) ) * (1/2pi) int_{|xi|>T} |F(xi)|^2.
The observed exponent ratio is 0.63-0.89.

WEAKER R13 (a THEOREM only modulo L1* and the RvM local count L2; my derivation, heuristic in its constants). Optimising g* ~ (eta0 ln c/2pi)^{2/3} (T/2)^{1/3} gives
#{lambda_k(Q_x) <= eps} >= e*(x) - C1 x^{1/3} (log x)^{5/3} - C2 log x log(C/eps) per sector.
Any split with ample/pole rank k below that has primitive margin <= eps. At fixed x the explicit inequality with M_L inside still certifies counts within 1 of S20 (3/3, 7/7, 15/15, 31/30 at x = 8/12/20/36).

Lean target (a), finite-dimensional Gram inequality only:
theorem cascade_gram_count {n m : Nat} (Q : Matrix (Fin n) (Fin n) Real) (hQ : Q.IsHermitian) (N : Matrix (Fin n) (Fin m) Real) (hN : N.transpose * N = 1) (U : Real) (hU : forall v : Fin m -> Real, v dotProduct ((N.transpose * Q * N) mulVec v) <= U * (v dotProduct v)) : m <= (Finset.univ.filter (fun i => hQ.eigenvalues i <= U)).card
This is Courant-Fischer; the analytic disk/zero-sum steps stay outside Lean.; barrier confirmed: False

WAVE 6 - cascade_L1_guardband. conjecture1_proved = False. Class-7 archimedean, count-only work. It holds verbatim for E and DH (S21, re-confirmed), the battery does not apply, and no RH progress is claimed. Prior (K11) was 15-30%. The outcome is a NEGATIVE result on L1 plus a corrected lemma and a weaker R13.

**Files** are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/cascade_L1_guardband/:

| file | what it is |
|---|---|
| PREREG.txt | timestamped before any script |
| l1core.py, l1run.py | arb prolate and strip-tail Gram engine |
| l1anal.py, l1fit.py | analysis and growth-law fit |
| l1_x8test.pkl, l1_x20.pkl, l1_x20conv.pkl, l1_x36.pkl and .log files, l1fit.log | L1 test data and fits |
| xcheck.py | independent direct-quadrature cross-check |
| q8own.py, q8.log, q8_36.log | Q8, own Legendre explicit-formula code |
| q5.py | Q5a regression |
| counts.py, counts.log | E and DH counts |
| strip.py, strip12.log, strip20.log, strip36.log | deliverable (b) |
| cc2023.txt | Connes-Consani full text |
| pylib/ | python-flint and gmpy2 installed with pip --target |

Environment note: python-flint was NOT in venv312 despite the brief, so I installed it privately into pylib/. Harness and git were untouched. No harness bugs found. All processes are finished.

**1. Decisive test.** L1 as posed is FALSE.
- Key identity: the finite Fourier transform of a prolate is the prolate itself, F_k(z) = A lambda_k psi_k(z/T) for all complex z. So the strip tail is the entire prolate evaluated just off the real axis near t = 1.
- There psi has two regimes:
  - inside the band it grows exponentially, like exp(c sqrt(2s));
  - outside the band it oscillates with local wavenumber c t/sqrt(t^2-1), which diverges at the edge.
- Three consequences:
  - (i) The guard T-r vs T costs exp(~2A sqrt(2rT)) already at eta = 0: log10 rho = 12.0 (x=20) and 20.6 (x=36).
  - (ii) Even with the same edge, the eta-shift costs exp(~2A sqrt(T eta)) instead of e^{2A eta}.
  - (iii) The index guard G is irrelevant (identical to 4 digits for G in {0, A/4, A/2, A, 2A}).
- The adversarial worst case over the mixed-parity span, with eta of both signs, is only 2.5-7x the worst single prolate. The rigorous bound is dim V.
- The crude bound is vacuous for top prolates, up to 1e161 at x=20 and beyond 1e300 at x=36.
- The brief's "jump expansion + three lines" proof route fails for a structural reason: near xi ~ T the jump series converges only like (T/xi)^k, and the L2-log-convexity (three lines) holds for the full line but not for the band-restricted tail.

**2. Corrected lemma and weaker R13.**
- L1* (numeric): for a frequency guard g > 0,
  Tail_{T+g,eta} <= exp(2A|eta|(1+delta)/sqrt(2 delta + delta^2)) * (1-mu)-energy, with delta = g/T.
  It holds with constant 1 at all 60 (g, eta) points at x = 20 and 36. The fitted exponent ratio is 0.63-0.89, rising with x.
- R13 therefore survives modulo L1* and L2, but weaker: rank >= e*(x) - O(x^{1/3} log^{5/3} x) - O(log x log 1/eps). The leading x term survives.
- At fixed x the direct inequality with M_L(|xi|) inside the integral certifies 3/3, 7/7, 15/15, 31/30 at x = 8/12/20/36, all within 1 of S20. C26's point stands: at fixed x this is Galerkin min-max.
- A likely proof route for L1*: Olver-type error bounds for the prolate ODE, plus the dim-V span bound.

**3. Q8.** My own code path (Legendre basis, u-space arch kernel, arb) gives -ln lambda_1 = 74.60 / 122.95 / 171.70 / 220.79 at x = 8 / 12 / 16 / 20.
- x = 20 needed N = 200. At the brief's cap of N = 160 it reads 218.5 and is still rising.
- The prior values 74.5 / 122.8 / 171.5 / 220.5 are reproduced within 0.3.
- This is now skeptic-grade (independent code). Zhu 2608.24827 is prior art for the law.

**4. Q5a/Q5b.**
- The regression slope is 3.0 at offset N(T*), and 2.6-3.8 for offsets -6..+6. Local slopes run 2.5-4. So the (1-mu)^2 mechanism is refuted as a pairing.
- The 1/(4pi^2) ln(AT*) width is nevertheless confirmed empirically to 4-10%: the continuous-count offset is tau-independent.
- The 7/8 offset is not resolvable (convention +-1/2, and it drifts with x).
- NEW robust regularity: odd offset = even offset + 0.50 +- 0.06 at all x and tau.

**5. Counts.** E at x=128: 9/8 with index 7/7, non-negative part 2/1 = zeta_K(-20)'s 2/1. DH at x=64: non-negative part 10/9 = L(chi_5)'s 10/9. Both confirmed and stable in N.

**6. Literature.**
- Connes-Consani 2023 (full text read) already states numerically that the small-eigenvalue count grows like x per even sector, with odd one less, plus a 2 lambda^2 prolate heuristic.
- So the novelty left in the cascade law is: the tau-width 1/(4pi^2), counterfeit-twin equality, the 1/2 sector shift, and now the falsification of L1 and the L1* law.
- Slepian 1965 and Landau-Widom 1980 are backfilled into the lit cache (metadata verified via Crossref; full texts not read).

**7. Ledger recommendations.**
- Replace Q5/L1 with L1*.
- Downgrade R13's theorem form to e* - O(x^{1/3} log^{5/3} x).
- Add a correction: CC2023 is prior art for the leading count.
- Close Q8 as reproduced.
- Close Q5b as unresolvable, adding the 1/2 sector-shift fact.
- Add the Lean target cascade_gram_count to Q12.

**Skeptic:**

```json
{
 "angle": "cascade_L1_guardband, wave 6 skeptic. This is class-7 archimedean, count-only work that tests the guard-band strip-leakage lemma L1 behind R13. It is not a positivity mechanism and does not use the Euler product. conjecture1_proved = False.",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "NOT A MECHANISM, BY DESIGN. Class 7 (R12): only A, T, the prolate spectrum, known zeros and M_L enter, with no Euler product at any step. It goes through verbatim for E and DH (S21; the counts were re-run: E x=128 is 9/8 with index 7/7, DH x=64 leaves 10/9). The default survives=false applies.",
  "THE CLAIMED BARRIER 'L1 IS FALSE' REFUTES THE WRONG FORM OF L1. What was tested is the per-direction (Gram-diagonal) inequality Tail_{S,eta}(f) <= C e^{2A|eta|} sum_k |a_k|^2 (1-mu_k), with rho = lambda_max(Tail, e^{2A|eta|} diag(1-mu)). The cascade count only needs the operator-norm form: for K = Sh - G, sup over the span V_K of Tail_{T-r,eta}(f)/||f||^2 <= C e^{2A|eta|} (1-mu_{K-1}). Wave 5 set it up as exactly this count on the operator R, and it is the form under which Q5's index guard G means anything. In that form L1 is NOT refuted. My own independent code at x=20 gives rho_sup = 3.4 (G=A), 11 (2A), 67 (4A) and 380 (6A) for the literal case (S=T-1/2, eta=0), and at most 6.1e2 for |eta| <= 1. The same-edge case gives 0.6-44. The proposer's own saved x=36 data give 4.0, 13, 157 and 856, with at most 1.1e3.",
  "'THE INDEX GUARD G IS IRRELEVANT' IS AN ARTEFACT OF THE METRIC. In the per-direction metric the top prolates dominate, since 1-mu_0 ~ 1e-161 is multiplied by the edge-layer growth, so G cannot matter. In the sup form G is the controlling parameter: rho_sup rises from about 2 to about 1e3 as G goes from 0 to 6A.",
  "FOR FIXED G = kappa*A THE SUP-FORM L1 IS ALMOST TRIVIAL. Tail <= Tot <= e^{2A|eta|}||f||^2 gives C <= 1/(1-mu_{Sh-kappa A}), which is about exp(2 pi^2 kappa A/ln c). That tends to about e^{pi^2 kappa} because ln c ~ 2A, so it is bounded in x. This still needs a non-asymptotic plunge bound; the references for that are recalled from memory and are UNVERIFIED. The real open content is how C grows with G, which is where small tau lives.",
  "THE RECOMMENDED LEDGER DOWNGRADE IS UNJUSTIFIED. The proposal would change R13 to e*(x) - O(x^{1/3} log^{5/3} x) because L1 is false. That follows only if the per-direction form is used. Under the sup form, the cost of C(G) against the Landau-Widom width-1/(2 pi^2) count is ln(rho_sup) ln c/(2 pi^2). That is 0.3-1.2 dimensions at 1-mu = 1e-3..1e-10 and 1.6-2.3 dimensions at 1e-15..1e-16, at both x=20 and x=36 (supcurve.log). It grows sublinearly in G.",
  "MINOR: P4 was scored BORDERLINE but is a miss. The measured slope is 3.02, and 3.1 at N=160, outside the preregistered [1.5,3]. Separately, the report's 'worst-case span vs single prolate 2.5-7x' is exceeded: 9.5x at x=20, g=A, eta=0.5 (my run).",
  "MINOR: the Q8 'reproduction within 0.3' at x=20 compares two unconverged numbers. N=160 -> 200 still moves +2.3, as the proposer discloses, so 220.5 vs 220.8 is not a convergence check. Also, the proposer's own code is not skeptic reproduction; it is independent only of the wave-5 code."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Not applicable as a detector: the object is archimedean. I did not re-run E and DH myself. The proposer's harness counts in counts.log match S21: E[1,0,5] at x=128 is 9/8 with index 7/7, leaving 2/1, equal to zeta_K(-20); DH at x=64 is 12/11 with index 2/2, leaving 10/9, equal to L(chi_5). Both are stable over N = 128-256. The strip-tail quantities involve no L-data at all, so they are identical for zeta, E and DH by construction. That confirms class 7 and R17: nothing here can separate genuine from counterfeit.",
 "numerics_reproduced": "INDEPENDENT CODE in hengine/w6/cascade_L1_guardband_skeptic/: sk_l1.py, sk_anal.py, supcurve.py, supform_from_pkl.py; logs sk_x8_anal.log, sk_x20_anal.log, supcurve.log, supform_x20/x36_fromprop.log.\n\nHow it differs: the proposer computes the in-band energy on the time side with a double sinc kernel. I compute it on the frequency side. I evaluate F_n(xi+i eta) = A^{1/2} sqrt((2n+1)/2) 2 i^n j_n(A(xi+i eta)) directly (spherical Bessel, arb acb), and integrate with composite Gauss-Legendre panels in xi on [0,S] using conjugate symmetry. Prolates come from my own tridiagonal LDL inverse-iteration code. Precision was 820 bits at x=20 (Nmax=420, last coefficients 1e-102) and 420 bits at x=8.\n\nConsistency checks:\n- My frequency-side real-tail Gram is diagonal in my prolates: off-diagonal (scaled) 6.6e-55 at x=20 and 7.8e-78 at x=8.\n- 1-mu_0 = 3.124e-162, against the asymptotic 3.131e-162 (x=20); 2.05e-44 at x=8.\n- The full 1-mu spectrum matches the proposer's log (-161.5, -155.5, ...).\n\nPer-direction log10 rho REPRODUCED to within 0.01-0.03 (mine vs claimed), x=20:\n- S=T-1/2: eta=0 12.00 (12.0); eta=0.5 12.80 (12.8); eta=1 14.67 (14.7)\n- S=T-1/4: eta=0 7.89 (7.9); eta=1 12.72 (12.7)\n- S=T: eta=0.5 7.42 (7.4); eta=1 10.91 (10.9)\n- g=A, eta=0.5: 2.36 (2.4)\n- g=2A: eta=0.5 1.54 (1.5); eta=1 3.34 (3.3)\nAt x=8 I get 4.23 (4.2) and 2.29 (2.3). x=36 was NOT recomputed independently; I used the proposer's saved Gram data.\n\nNEW, sup form (operator norm on V_{Sh-G}, against 1-mu_{Sh-G}), agreeing between my code and the proposer's data at x=20:\n\n| case | G=A | 2A | 4A | 6A |\n|---|---|---|---|---|\n| literal S=T-1/2, eta=0 | 3.4 | 11 | 67 | 380 |\n| same-edge, eta=1 | 0.86 | 2.0 | 9.1 | 44 |\n\nAt x=36 the literal case (proposer's data) gives 4.0, 13, 157, 856.\n\nThe additive form ('+ exponentially small term') does not rescue the per-direction version over the full Shannon span: with C=10 it needs eps ~ 1e-3.5 at x=20. So the sup form is the right statement.\n\nNot reproduced: Q5a slopes, Q5b offsets, deliverable (b) counts, and the Q8 values (my check was limited to reading the proposer's q8.log).",
 "novelty": "Low.\n- The identity F_k(z) = A lambda_k psi_k(z/T) is classical Slepian duality. The edge-layer WKB growth exp(c sqrt(2s)) is standard prolate asymptotics (e.g. Dunster-type uniform asymptotics, recalled from memory, UNVERIFIED).\n- So the per-direction failure is close to a textbook consequence. At eta=0 it just says that a top prolate carries far more energy in [T-r,T] than beyond T.\n- Connes-Consani 2023 (Enseign. Math. 69; full text in cc2023.txt; I grepped the quotes at lines 1738, 1873 and 4353) is prior art for the leading small-eigenvalue count. It has 'one less' in the odd sector and 'k ~ 2mu up to a log mu term'.\n- Zhu arXiv:2608.24827 is prior art for Q8.\n- What is new and real:\n  - the independent confirmation that the per-direction L1 fails, with its sqrt-growth law;\n  - the numeric L1* envelope with a frequency guard;\n  - the regularity that the odd offset exceeds the even offset by 1/2 (not reproduced by me);\n  - from this skeptic pass, that the operator-norm L1 holds numerically with C = O(1-1e3), at a cost of 1-2 dimensions at practical tau.",
 "what_is_real": "1. The per-direction guard-band inequality really is false, by a superpolynomial factor. Precisely: Tail_{T-r,eta}(f) <= C e^{2A|eta|} sum|a_k|^2(1-mu_k) on band-T prolates fails with rho ~ exp(kappa 2A sqrt(2rT)). At x=20 log10 rho = 12.0 (r=1/2, eta=0) and 14.7 (eta=1); in the same-edge form it is 7.4 (eta=1/2) and 10.9 (eta=1). The cause is prolate edge-layer growth through the entire continuation F_k(z) = A lambda_k psi_k(z/T). Independently reproduced (frequency-side Bessel code). It is a narrow, nearly classical fact about the WRONG FORM of L1.\n2. The form the cascade needs, sup over V_{Sh-G} of Tail_{T-r,eta}/||f||^2 <= C(G) e^{2A|eta|}(1-mu_{Sh-G}), holds numerically with modest C:\n   - at x=20: 3.4 / 11 / 67 / 380 for G = A / 2A / 4A / 6A (literal, eta=0); at most 6.1e2 for |eta| <= 1;\n   - at x=36: 4.0 / 13 / 157 / 856 (proposer's data).\n   For fixed G = kappa*A it holds almost trivially (crude bound plus a non-asymptotic plunge bound). The cost against the width-1/(2 pi^2) count is 0.3-2.3 dimensions per sector at x = 20 and 36 for 1-mu between 1e-3 and 1e-16.\n3. R13 should NOT be downgraded to e* - O(x^{1/3} log^{5/3} x). The right open lemma is the growth of C(G), which is sublinear in G in the data. With it, R13 would be e*(x) - ln(1/eps) ln c/(2 pi^2) - (loss from C(G)) - O(1). Width 1/(2 pi^2), not the empirical 1/(4 pi^2), which still needs a constraint-assisted lemma.\n4. The numeric L1* (frequency guard) envelope is consistent with my data at g = A and 2A.\n5. PREREG timestamps are genuine: 08:46:17, before the first script at 08:49:31. prediction_matched=false is honest; P4 is mildly soft-scored.\n6. Counterfeit-blind by construction (class 7, R17). No RH content.\n\nRecommended ledger wording: 'Q5 narrowed. The per-direction (Gram-diagonal) guard-band L1 is FALSE (rho ~ exp(0.8-0.9 * 2A sqrt(2rT)), reproduced by two codes). The operator-norm L1 needed for R13 holds numerically with C(G) <= 1e3 for G <= 6A at x = 20, 36. Open: the growth law of C(G). Do not downgrade R13 to x^{1/3}.'",
 "next_step_if_survives": "It does not survive as a mechanism. The most informative next step for the barrier program is to prove the operator-norm lemma with an explicit G-dependence: sup over V_{Sh-G} of Tail_{T-r,eta} <= C(G) e^{2A|eta|}(1-mu_{Sh-G}), with ln C(G) = o(G/ln c).\n\nRoute:\n1. Bound the tail by the trace, sum over k < K of Tail(psi_k). That loses at most dim V, which is harmless.\n2. For each k, bound Tail(psi_k)/(1-mu_k) with Olver-type Liouville-Green bounds on psi_k(z/T) near t=1.\n3. Combine with a verified non-asymptotic plunge bound for 1-mu_k (backfill the lit cache first; the candidate references recalled from memory are all UNVERIFIED).\n\nNumerically, first measure ln C(G) against G at x = 36, 64 and 100 with the frequency-side code (sk_l1.py) to fix the growth law: sqrt(G*A) as WKB predicts, or linear. Then restate R13 as e*(x) - ln(1/eps) ln c/(2 pi^2) - (loss from C(G)) - O(1). The 1/(4 pi^2) width stays a separate constraint-assisted question."
}
```

### period_height_positive_cone (hybrid)
- survives adversarial review: False; prediction matched: True; claimed barrier: B28 LINEAR-CONE BLINDNESS (conditional closure of Q11 leads 1-2). Let Lambda be any linear functional on the coefficient sequences a(n) with a FIXED genuine twisting or Rankin-Selberg partner: a central value L(1/2, f x chi_d), a height or L'(1/2) at a sign -1 point, or a Waldspurger / Gross-Zagier period. If GRH for the genuine constituents (no real zero in (1/2,1)) makes Lambda >= 0 on each, then Lambda >= 0 on every nonnegative mixture, including E = (zeta_K + L(chi_-4)L(chi_5))/2. So the positivity is E-blind at every scale x, while E is Weil-negative from 19.8225.

Numerics: 676/676 E-twists are positive (min 0.6917), and the battery gives useful=False (13 misses).

Delimiters:
(i) Complex weights (DH) escape the cone. The sign of DH_d(1/2) is +-sec(theta)|Lambda(1/2, chi chi_d)|, which is uncontrolled: 18/168 canonical twists are negative, first at d = 61, each carrying a real off-line zero (sigma = 0.8037). This is a zero readout (B2).
(ii) Quadratic positivity (|.|^2, Hecke-defect Grams) is trivially PSD. For E the defect Gram is exactly (1/4)(a_K - a_LL)(a_K - a_LL)^T, rank 1.
(iii) At a sign -1 point the lemma still covers L'(1/2).

D-KILL: over Cl(-20), G_s[A,B] = Z(s; A^{-1}B) is circulant, with eigenvalues zeta_K and L(chi_-4)L(chi_5), and E is the diagonal entry.
- At s = 1/2 it is indefinite before pole removal (-3.668, +0.231) and PSD after (0.332, 0.231).
- At s = 1 its finite part is PSD.
- On the line it is only a pointwise zero readout: PSD on 25% of t in [0,50].
- No E-own Gram fails PSD, and no x-scale enters.; barrier confirmed: True

WAVE 6 / period_height_positive_cone. Artifacts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/period_height_positive_cone/:
- PREREG.txt
- twists.py and twists.json (all 676 E and DH values, dps 30, with the FE class of each d)
- realzero.py and dh_real_zeros.json
- gram_and_battery.py and gram.json (critical-line circulant rows, the s=1 Gram, the Hecke-defect spectrum)
- battery_cv.py, battery_cv.json and battery_cv.log
- results_summary.json
Every process has exited. The two other venv312 pythons on the machine belong to other sessions.

(A) LEMMA AND LEAN. The abstract cone statement below is NOT compiled; nothing was built or run here, and no repo was touched:
theorem linear_positivity_cone {V : Type*} [AddCommGroup V] [Module ℝ V] (Λ : V →ₗ[ℝ] ℝ) {a₁ a₂ : V} {w₁ w₂ : ℝ} (h₁ : 0 ≤ Λ a₁) (h₂ : 0 ≤ Λ a₂) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) : 0 ≤ Λ (w₁ • a₁ + w₂ • a₂) := by simp only [map_add, map_smul, smul_eq_mul]; positivity
(Equivalently, {a | 0 ≤ Λ a} is a PointedCone ℝ V.)

E-instance: for fundamental d with gcd(d,20)=1, write cv_D := L(1/2, chi_D). Then
(hK : 0 ≤ cv_d * cv_{-20d}) (hL : 0 ≤ cv_{-4d} * cv_{5d}) ⊢ 0 ≤ (1/2)*(cv_d*cv_{-20d}) + (1/2)*(cv_{-4d}*cv_{5d}).
Each hypothesis follows from 'L(sigma, chi_D) has no zero in (1/2,1)', since L(1,chi_D) > 0 and the function is real-analytic in sigma. This is GRH for the pieces. For |D| up to about 3e8 it is believed to be an unconditional computation (Watkins 2004, UNVERIFIED citation).

Precise caveat: linearity requires a FIXED genuine partner, and the twisted central value must be FE-canonical. For DH, twists with d = +-2 mod 5 break the FE (eps ratio +-i), so the 'central value' there is only a number, not an invariant.

(B) RESULTS. The method is the smoothed exact AFE, validated against Hurwitz zeta to 1e-31.
- E x chi_d: 676 twists, 0 negatives, min 0.6916930812671098 at d = -3. Among the four L constituents the smallest single value is 0.003608 (D = 13340). Prediction matched.
- DH x chi_d splits cleanly by d mod 5:
  - d = 1: FE holds with sign +1; 18/168 negative, first d = 61 (-0.2711), min -1.39665 at d = 1741;
  - d = 4: FE holds with sign -1; the value is identically 0;
  - d = 2, 3: FE fails; 78/341 negative, first d = 13.
  - Overall 96/676 = 14.2% negative. First negative d = 13 (flagged non-canonical); first canonical negative d = 61.
- Structural reason: for FE+ twists, Lambda(1/2, psi) lies on the line e^{i theta}R, so DH_d(1/2) = +-sec(theta)|Lambda|. The sign is a free square-root-of-root-number sign.
- A canonical negative forces a real zero off the line. I located them: sigma = 0.803665 (d = 61), 0.905307 (901), 0.923939 (1741), with FE check 1e-23.
- The prediction scored at 60% (or 50%) is MATCHED, and the result is stronger than predicted: canonical negatives exist.

(C) ONE-LINE VERDICTS.
- R12-7/8/9: everything in (B) is class 8, a special-point evaluation (s = 1/2, sigma in (1/2,1)). It is not class 7, and not class 9 unless one adds Hodge-index finite rank.
- R15: the evaluation is only at s = 1/2 (or 1). It is strip-blind at every t != 0. The line version (D) is a pointwise zero readout.
- R17: the partner must be genuine. With a counterfeit partner, linearity in the counterfeit is lost, which is case (ii).
- R18: in the solved worlds (Weil curves, Yun-Zhang shtukas), positivity came from finite-rank Hodge index on NS or J, not from the sign of central values. Central values there are consequences of that positivity, not its source.
- B24: differences of linear functionals are zero-mean, so no comparison can extract a sign.
- R13/R9: the Heegner/CM span has rank <= the MW rank or dim J_{2,N}, fixed in x, while the cascade grows like e*(x). It is dead.

(D) DECISIVE CHECK (D1).
- The circulant decomposition is verified to 2.3e-15 on t in [0,50], using a Chowla-Selberg Epstein evaluator I derived and checked (prefactor 2^{s+5/2}; direct lattice sum agrees to 3e-10).
- Correction to the assignment's premise 'PSD(G_s) = both genuine L >= 0': the raw completed Gram at s = 1/2 is INDEFINITE for genuine data. The zeta_K eigenvalue is -3.66796 because of the pole: zeta(1/2) < 0, the same sign as xi-normalization issues.
- Removing the rank-1 polar block (R = 1/2 per entry, contributing -2 per entry at s = 1/2) gives the pole-free Gram, which is PSD (0.33204, 0.23139). The E entry is 0.28171 > 0.
- On the line the Gram is PSD at only 24.9% of grid heights. It fails at t ~ 2.5 (zeta_K / L(chi_-20) zero) and at t ~ 6.02 (the first zero of L(chi_-4)). So the only height it sees is pointwise zero readout (B2), not the e*(x) cascade.
- Kronecker at s = 1: the finite-part Gram [[0.351456, 0.013414], [0.013414, 0.351456]] has eigenvalues 0.364871 and 0.338042 = L(1,chi_-4)L(1,chi_5). The ratio to the Kronecker difference is pi/sqrt5 = 1.404963. It is PSD. The residue Gram is rank-1 PSD.
- E-own Gram: M_E = (1/4)(a_K - a_LL)(a_K - a_LL)^T exactly (numerically 1 positive and 0 negative eigenvalues; 0 for genuine forms). It is PSD, catches E only as an identity defect (R2), has no x, and is not a period.
- Verdict: 'PSD-for-both (after pole removal) / ill-posed for E'. Success (ii) fails, so this records B28 plus the D-kill. Prediction matched.

BATTERY (x-blind predictor: the sign of the member's own pole-corrected central value, eps = +1, with residue fitted from AFE consistency). Agree 117, catches 0, false alarms 0, misses 13 (E[1,0,5] at x >= 20, E[1,1,6] at x >= 28, E[1,0,6] at x >= 32, DH at x >= 32), abstain 60 (the no-FE members, where the FE residual flags a non-canonical value). useful=False.

Harness note, not a bug: the E[1,0,5] central value from the predictor, -1.718288, matches the independent Chowla-Selberg value -1.718288, which cross-checks both codes.

NET: Q11 leads 1 (central_value_nonnegativity_families) and 2 (arithmetic_siegel_weil_heights_to_L) are closed by B28 and R13. The only arithmetic positivity that detects anything here (DH twists) does so by reading an off-line real zero at a special point.

**Skeptic:**

```json
{
 "angle": "period_height_positive_cone (hybrid). The proposal claims that central values, heights and periods are linear functionals of the coefficients a(n) with a fixed genuine partner. Any such functional that GRH makes nonnegative on the genuine pieces is therefore nonnegative on every nonnegative mixture, including E = (zeta_K(-20) + L(chi_-4)L(chi_5))/2. That makes it blind to E at every scale x (claimed barrier B28). DH escapes the cone only through complex weights, and DH twists are caught only by reading off real zeros.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "The mechanism is x-blind by construction. On the battery (x = 4..36), the proposer's central-value predictor gives the same verdict as the constant '+' predictor on all 130 FE-member cells. That includes the 13 misses: E[1,0,5] from x=20, E[1,1,6] from x=28, E[1,0,6] and DH from x=32. On the 60 no-FE cells it abstains, and under R11 an abstention counts as a miss. So it carries zero information. I reproduced this with lambda ld,x: 1 (battery_const.py).",
  "The Euler product is used only pointwise and linearly: 'no real zero in (1/2,1)' for the constituent real L-functions, i.e. R12 class 8 plus R15. It never acts on the mixture. This fails the survival requirement that the Euler product be used nonlinearly and globally in an essential step.",
  "Overclaim in the barrier's framing: not every central-value, height or period positivity has the linear form. Rankin-Selberg self-products L(1/2, E x E), Sym^2 values and Petersson norms are quadratic in a(n), and they are not trivial squares |.|^2 as delimiter (ii) says. The skeptic's fix, which only strengthens B28: sum a_E(n)^2 n^{-s} = (1/4) sum_{i,j} L(f_i x f_j, s) / L(2s, omega). For the constituents here, every monomial is a product of squares of Dirichlet L-values (for example the cross term is ~ L(chi_-4)^2 L(chi_5)^2), so the quadratic route is also E-blind. The correct barrier is a tensor-cone statement: any functional polynomial in a(n) whose monomials are nonnegative on genuine tuples is E-blind.",
  "Sign error in delimiter (ii). In the natural convention H(m,n) = a(m)a(n) - sum_{d|(m,n)} chi_-20(d) a(mn/d^2), which is 0 for normalized eigenforms, E's Hecke-defect Gram is -(1/4) v v^T with v = a_K - a_LL. That is NEGATIVE semidefinite, not PSD: at 24x24, min eigenvalue -32, max ~3e-15, and ||H_E + vv^T/4|| = 0 exactly (hecke_sign.py). Structurally it is -Cov_w for a convex mixture (Jensen). It is still x-free and not a scale mechanism, so the kill stands. But calling it 'PSD' depends on the sign convention.",
  "The (D) preregistration was scored generously. PREREG predicted a class-group Gram that is PSD for both genuine eigenvalues at s=1/2, at 80%. The raw completed Gram is INDEFINITE: eigenvalues -3.66796 and +0.23139, reproduced by Hurwitz. PSD holds only after removing the pole, which the prediction never mentioned. Honest scoring: (D) as written was WRONG, not 'correct with a correction'.",
  "Literature: the Waldspurger/Kohnen-Zagier citation does not apply to these constituents. At h(-20)=2 both weight-1 constituents, zeta_K = theta_A + theta_B and L(chi_-4)L(chi_5), are EISENSTEIN series, not cusp forms. Nonnegativity of L(1/2, chi_D) is itself open unconditionally (Chowla's conjecture; Conrey-Soundararajan give a positive proportion). The claim that 'Watkins 2004 makes it unconditional in our range' covers only ODD real characters, while half the constituents (chi_d and chi_5d with d>0) are even. For the tested finite range, positivity is simply the computed values: a margin of 0.0036 against a float error of 5e-15. No zero-free input is needed there."
 ],
 "prereg_honored": true,
 "counterfeit_check": "By design the mechanism goes through verbatim for the counterfeit E, and that is the point of B28. My independent code gives E x chi_d > 0 for all 676 fundamental d with |d| <= 2000 and gcd(d,20) = 1, while E is Weil-negative from x = 19.8225.\n\n- E's own pole-kept completed central value is -1.71829, and after removing the pole it is +0.28171 > 0, so it predicts '+' at every x.\n- DH is 'caught' only by its twisted functions' real off-line zeros. This is B2 zero readout of DH x chi_d, not of DH's own Weil form at any scale.\n- The no-FE members (LEB, euler-rand, a2-flip, DH kappa=0 and kappa=1) get abstentions, which R11 counts as misses.\n\nSo every member of the zoo is either missed, or caught only through a zero located at a special point.",
 "numerics_reproduced": "Everything was recomputed with independent code in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/period_height_positive_cone_skeptic/. The twist code is numpy/scipy float64 with sympy Kronecker symbols and numpy Gauss sums. It uses an AFE with a free theta-split parameter T in {1, 1.7}, so dependence on T serves as an FE test. The checks at special points (d=61 and 901, s=1/2) use mpmath Hurwitz zeta, a method with no AFE at all.\n\n(1) E twists (twists_indep.py): 676 d, 0 negatives, min 0.6916930812671097 at d=-3. The smallest constituent is L(1/2, chi_13340) = 0.0036081401702953 at d=-667. The T-dependence error is at most 5e-15. This matches the proposer exactly.\n\n(2) DH twists:\n- d = 1 mod 5: 168 cases, Gauss-sum ratio eps(psi)/eps(chi5) = +1. 18 are negative, the first at d=61 (-0.2711197183). The min is -1.3966476700 at d=1741.\n- d = 4 mod 5: 167 cases, ratio -1, and the value is identically 0 to 9e-16.\n- d = 2 mod 5: ratio -i, 24 of 172 negative. d = 3 mod 5: ratio +i, 54 of 169 negative. The first negative in these classes is d=13 (-0.5578557412).\n- Total 96/676 negative. The count is 164 if float noise (~-6e-16) in the d = 4 mod 5 class is counted as negative, so a threshold is needed.\n- All matched. I also confirmed the delimiter (i) algebra: canonical twists satisfy DH_d(1/2) = +-sec(theta)|Lambda|.\n\n(3) Real zeros by Hurwitz (hurwitz_checks.py): DH_61 has sigma = 0.80366529854015 and DH_901 has sigma = 0.90530741153548. Both match to all printed digits, and DH_d(1/2) agrees with the AFE to 1e-16.\n\n(4) Class-group central values by Hurwitz:\n- Lambda_zetaK(1/2) = -3.667963875973115 and Lambda_LL(1/2) = 0.231387470880022.\n- Lambda_E = -1.718288202546546 and Lambda_B = -1.949675673426568.\n- With residue R = 1 per zeta_K, the polar part at s=1/2 is -4, i.e. -2 per E entry, which gives the pole-free 0.28171.\n- L(1,chi_-4)L(1,chi_5) = (pi/4)(2 log(phi)/sqrt5) = 0.338042 (by hand).\nAll matched.\n\n(5) Battery: the constant '+' predictor reproduces the proposer's agree and miss pattern cell for cell on the FE members (13 counterfeit misses, useful=False). The harness reports a conflict at DH, x=32: metadata says -1, measured +1.7e-26 (known ledger Q9). The proposer's count of 13 misses leans on the metadata there.\n\nNot reproduced (decorative, not load-bearing): PSD on 24.9% of the critical-line grid; the 2^{s+5/2} Chowla-Selberg prefactor; the Lean snippet (NOT compiled).",
 "novelty": "Low. B28 is the inequality/convex-cone corollary of ledger B1: E satisfies every identity linear in a(n) on the Hecke-stable space, so it also satisfies every inequality that is linear in a(n) and valid on the genuine pieces. The convexity lemma is a two-line fact.\n\nMildly new:\n(a) the clean d mod 5 root-number classification of DH twists. Canonical negatives at d=61, 901 and 1741 force real zeros of DH x chi_d at sigma = 0.8037, 0.9053 and 0.9239. This is a new explicit family of real off-line zeros, but a classical kind of phenomenon: DH has no Euler product.\n(b) The skeptic's strengthening: E-blindness extends from linear functionals to every polynomial (tensor-power) functional whose genuine monomials are nonnegative, including Rankin-Selberg self-products. So only non-polynomial dependence on a(n), through log L / c(n) or Euler factorization, can see E.",
 "what_is_real": "1. B28 as a precisely stated lemma is correct, and the numerics behind it reproduced: 676/676 E twists are positive, with min 0.69169 at d=-3. Statement: if Lambda is linear in a(n), or more generally polynomial with nonnegative genuine monomials, and nonnegative on the genuine constituents, then it is nonnegative on E at every x. So no central-value, height or period positivity of that form can see E's Weil failure at 19.8225.\n\n2. This closes Q11 leads 1-2 (central_value_nonnegativity_families, arithmetic_siegel_weil_heights_to_L) as E-blind. The scope must be narrowed: it is a corollary of B1, it is conditional on GRH for the constituents to cover the infinite family, and delimiter (ii) must be corrected. Quadratic Rankin-Selberg functionals are also blind, by tensor-cone positivity rather than by being trivial squares. The natural-sign Hecke defect is H_E = -(1/4)vv^T <= 0.\n\n3. The DH twist family: a real-coefficient Dirichlet series with DH_d(sigma) -> 1 as sigma grows and a negative canonical central value must have a real zero at sigma > 1/2. There are 18 canonical negatives among the 168 d = 1 mod 5 twists. This is a genuine but pure zero-readout detector (B2): all-x for DH, and blind to E.\n\n4. The x-blind central-value predictor is informationally identical to the constant '+' predictor. That is a clean battery calibration datum for R12 class 8.\n\n5. Structural takeaway for the ledger: the Weil functional is linear in c(n) = coefficients of -L'/L, which is NON-polynomial in a(n). E is a positive mixture in a-space but not in c-space (c_E(36) < 0, B5). This is exactly the gap every a-polynomial positivity cannot cross.",
 "next_step_if_survives": "The proposal does not survive, so this is the most informative follow-up.\n\n1. Record B28 in the ledger in its tensor-cone form: any functional polynomial in a(n) whose genuine monomials are nonnegative is E-blind.\n2. Add a requirement R19: the essential step must be non-polynomial in a(n), i.e. it must act on c(n) = coefficients of -L'/L or on the Euler factorization.\n3. Then run the one quantitative test this points to, in c-space, where the Weil functional is linear. For each window x, solve an LP (cvxpy/CLARABEL, with signs certified separately) for the scale x_c(E) at which E's truncated vector c_E|_{n <= x} leaves the closed convex cone generated by the truncated c-vectors of genuine conductor-20 data with the same Gamma factor and pole data (zeta_K(-20), L(chi_-4)L(chi_5), and their Satake-positive neighbours).\n4. Compare x_c(E) with the Weil horizon 19.8225:\n- If x_c(E) is well below 19.82, the obstruction lives in c-space geometry (the log map), not in zeros. That would be a genuinely new non-readout handle, which must then be tested against B24 (no comparison) and B19/B22 (Euler data without FE).\n- If x_c(E) is about 19.82, it is the Weil form in disguise (B2/B25).\n5. Housekeeping: correct the Waldspurger citation (the constituents are Eisenstein), and verify Watkins 2004 (odd characters only) plus Platt's GRH verification for the even ones before either enters the lit cache."
}
```

### ff_theta_char_counterfeit_lab (wildcard)
- survives adversarial review: False; prediction matched: True; claimed barrier: TRANSFER BARRIER (SOLVED-WORLD, EXACT). In a world where RH is a theorem, partial class zeta functions Z_c of hyperelliptic curves have all of the following: finite rank (degree 2g-2d), integrality (N_c in Z[T], N_c(1)=1, no 1/h), an exact FE (a palindrome with no pole correction), the correct pole terms, and positive log-derivative counts (N_c(n) >= 1 for n <= 80). Yet they violate RH universally. The principal class c=0 is a counterfeit on EVERY odd-model curve with g>=2 and p>=3, via Z_0 = Phi_g/((1-T)(1-pT)), which is off the circle iff p > (1+1/g)^2. Detection is by exactly one added negative Toeplitz index at M* <= 2g-1 (R17). Rosati-positivity of the class weighting is also not separating: for c=0 the weight (1/h)Id is positive.

One-sentence transfer theorem: finite rank + integrality + FE + positive counts do not separate genuine from counterfeit; the separating input is determinantal (Euler-product) structure with a polarization, i.e. Z = det(1-FT | H^1) for a single Frobenius F acting on a polarized H^1 with FF^dagger = q, so that N(n) = Tr-type cardinalities of ONE curve over every F_{q^n}. Castelnuovo-Severi, Rosati and Bombieri-Stepanov all consume this, and zeta has no finite-rank version of it (B17/R9/R18).; barrier confirmed: True

WAVE 6 / ff_theta_char_counterfeit_lab: proof-carrying solved-world calibration. Not a mechanism.

SETUP. The curves are y^2 = f(x) with deg f = 2g+1 over F_p, with base point P0 = inf (a rational Weierstrass point). This gives K = (2g-2)inf, so kappa = 0 and the self-dual classes are exactly J[2](F_p), of which there are 2^(r-1), r = number of irreducible factors of f. Scope limitation: curves without a rational Weierstrass point (even models) are not covered.

MAIN EXACT RESULT. Every effective divisor decomposes uniquely as D = D_sr + pi^*E + k*inf. With uniqueness of reduced Mumford representations and Riemann-Roch at n >= 2g-2, this gives for g <= 3:
Z_c(T) = T^{d(c)} Phi_{g-d(c)}(T) / ((1-T)(1-pT)),
Phi_k(T) = sum_{j<=k} p^j T^{2j} - pT sum_{j<k} p^j T^{2j},
(1 - pT^2) Phi_k = (1-pT) + p^{k+1} T^{2k+1} (1-T).

- Phi_k is off the circle iff p > (1+1/k)^2, with exactly one real reciprocal pair off. This follows from the slope sign (2k+2) - 2k sqrt(p) at u=1, and is checked exactly for k <= 7 and p <= 13.
- So the self-dual partial zeta functions are UNIVERSAL: the curve is irrelevant.
- c=0 is always a counterfeit for g >= 2, p >= 3.
- For g=2: the d=1 class is RH-true at p=3 and a counterfeit at p >= 5; d=2 gives Z_c = T^2/((1-T)(1-pT)), which has no zeros.
- Corollary: h > 1 always. If h were 1, then Z_X = Z_0 would violate Weil.

T1 normalization answer. N_c = (1-T)(1-pT)Z_c is integral, with N_c(1) = 1. It satisfies the exact palindrome p^g T^{2g} N_c(1/(pT)) = N_{-c}(T). The class number h appears only through sum_c N_c = P_X and P_X(1) = h. The '1/h residue' creates no correction and no integrality defect.

T0 PASS (exact), on 7 sample curves:
- Cantor enumeration gives h = P_X(1), and sum_c N_c = P_X.
- Brute-force divisor counts per class, obtained by enumerating semireduced divisors and Cantor-reducing, match the formula for all n <= 2g-2.
- Every character-orbit norm of L(psi) is divisible by the pole factor, has degree (2g-2) times the orbit size, and is exactly on the circle by a Sturm count on E(Y) = H(sqrt Y)H(-sqrt Y) over [0, 4p]. Each is also Toeplitz-PSD.
- P_X is on the circle for all 7778 swept curves.
- Correction to the brief: an unramified nontrivial psi gives L of degree 2g-2, not 2g.

T2. Full sweep of all monic squarefree f up to x -> lam*x + b with lam a square. These are affine-orbit classes, so they upper-bound true isomorphism classes.
- Class counts: 54 / 260 / 686 (g=2, p = 3/5/7) and 486 / 6292 (g=3, p = 3/5).
- Every curve carries a counterfeit.
- Counterfeit fraction of self-dual classes: 45%, 72%, 71% (g=2) and 63%, 78% (g=3).
- The prior (65% that counterfeits exist) is confirmed, and more strongly than expected. There is no psi=1-dominance explanation, since the counterfeits are universal.

T3. N_c(n) >= 1 for all n <= 80 in every class, counterfeit or not. max|alpha|/p runs from 0.72 to 0.9975. Positivity of the counts never fails, so it is not the separating input (a sign barrier, B5, in a solved world).

T4. Exact inertia via characteristic polynomial plus Descartes' rule, on G_ij = p^{min(i,j)} s_{|i-j|} (congruent to the p^{-n/2}-weighted Toeplitz form).
- M* <= 2k-1 <= 2g-1 in every case. Examples: c=0 at g=2, p=3 gives M* = 3; at g=3, p=3 it gives M* = 4. d=1 at g=2, p=5 gives M* = 1.
- After M* the inertia is (n_on + 1, 1, rest): exactly one negative direction per off-circle pair, consistent with R17.
- Genuine Z_X and L(psi) are PSD for every M checked.

T5. See test_and_outcome for the row-by-row table. Rows (1)-(3) and positive counts are KEPT by the counterfeit. Rows (4)-(6) are LOST: the correspondence realization, Castelnuovo-Severi/Rosati, and Bombieri-Stepanov.
KEY CORRECTION to the brief's expectation: (1/h) sum_psi psibar(c) e_psi = (1/h) tau_{-c}. It is Rosati self-adjoint for self-dual c, and POSITIVE for c=0, yet Z_0 is a counterfeit. So the failure is not 'the projector is not Rosati-positive'. It is 'sum of determinants rather than determinant of a sub-motive'. An idempotent in Q[G] gives a product of L(psi), each on the circle.

TRANSFER THEOREM (one sentence). Finite rank + integrality + FE + positive counts do not separate genuine from counterfeit; the separating input is a determinantal Euler structure with a polarization: Z = det(1-FT | H^1) with FF^dagger = q, i.e. N(n) are cardinalities of one curve over every F_{q^n}. This answers Q16/P3 for curves: every separating proof step uses a finite-rank polarized Frobenius module, which zeta lacks (B17/R18).

LEAN FiniteDecide CANDIDATES:
(a) N_0 = [1, -3, 3, -9, 9] for g=2, p=3. It equals A-counts times (1-T)(1-3T) with A = 1, 1, 4, 13, 40, ... .
(b) Off-circle certificate: H(V) = V^2 - pV - p, E(Y) = Y^2 - (p^2+2p)Y + p^2, and E(4p) = p^2(9-4p) < 0 for p >= 3. At p=3: E(12) = -27 < 0 with positive leading coefficient, so there is a root Y > 12 = 4p, hence a zero off |T| = 3^{-1/2}.
(c) Toeplitz at M* = 3 for g=2, p=3: G = [[4,3,3,27],[3,12,9,9],[3,9,36,27],[27,9,27,108]], leading minors 4, 39, 1134, -107163, so the inertia is (3,1,0). Also g=2, p=5, d=1: [[2,5],[5,10]], det = -5. And g=3, p=3, c=0: a 5x5 matrix with leading minors 6, 99, 4860, 166941, -214820262.
(d) The integer identity (1-pT^2) Phi_k = (1-pT) + p^{k+1} T^{2k+1} (1-T).

PREREG AUDIT. Matched: P1, P2, P3, P4, P5, P6, P7 (M* <= 2g).
Misses:
- P7 detail: M* took values 1-4, not only {2,3}.
- P8: I predicted 'not Rosati-positive', which is wrong for c=0.
- Not preregistered at all: g=3, d=1 is a counterfeit even at p=3.
- The brief's L-degree statement (2g) was wrong; the correct value is 2g-2.

Harness: battery() does not apply, because there is no function-field LData. No harness bugs found. All processes were killed; the first T0 run hung on large-m resultants and was killed.

**Skeptic:**

```json
{
 "angle": "WAVE 6 SKEPTIC for ff_theta_char_counterfeit_lab. This is a solved-world calibration: partial class zeta functions Z_c on odd hyperelliptic curves over F_p. By the proposer's own statement it is not a mechanism. I reproduced everything independently, strengthened the math (it holds for every genus and every class, and the threshold is now proved for all k), and found one real error in how the result was read. The counterfeit Z_c does have a formal Euler product with nonnegative integer place counts. So \"the Euler product is the separating input\" is false in this world. What actually separates genuine from fake is a geometric or cohomological realization by one curve.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "It is not a mechanism, by design: it gives no route to W(x) for Spec Z. It also does not use the Euler product nonlinearly or globally in any step that could transfer. It survives only as a calibration or barrier.",
  "The euler_product_usage claim is WRONG as stated. Z_c has no Euler product over the places of X, but Z_c/T^d = Phi_k/((1-T)(1-pT)) IS a formal Euler product prod_d (1-T^d)^{-a_d}. The a_d are integers for all d, and nonnegative for every d <= 150, k <= 8, p <= 13 (s4.log). Through degree 2k it is literally 1/((1-T)(1-pT^2)): a 'virtual curve' with one rational point and all affine places inert (a_1=1, a_2m = number of degree-m irreducibles over F_p, a_odd=0). So a rational function with finite rank, integrality, an exact FE, the correct poles and a nonnegative-integer Euler product still violates RH. The separating input is that the counts are counts of ONE curve over every F_{p^n} (Riemann-Roch, polarized H^1), not the Euler product. The one-sentence 'transfer theorem' clause naming the 'determinantal Euler structure' as the separator is therefore half wrong. It is also not a theorem: no necessity is proved; it restates the architecture of Weil's proof.",
  "Transfer to Spec Z is weaker than claimed. In F_q[T] the zeta is univariate in T, so every series in 1+T Z[[T]] is a formal Euler product and only the signs of the a_d carry content. The Hecke multiplicativity across different primes (R2) cannot be modelled here. The FF FE is also non-rigid: a genus-g rational Z has about g free parameters. Over Q, a degree-1 FE plus finite order forces c*zeta (Hamburger; the analogue of ledger B9). So FF counterfeits that 'keep the Euler product' have no degree-1 Spec Z analogue.",
  "Scope is mis-framed, which is cosmetic rather than fatal. The Riemann-Roch argument gives Z_c = T^d Phi_{g-d}/((1-T)(1-pT)) for EVERY class c, not only J[2]. Since d(-c) = d(c), every Z_c satisfies the FE with itself. 'Self-dual classes = J[2]' is therefore irrelevant, and the counterfeit statistics restricted to J[2] are an arbitrary slice. Over all classes the counterfeit fraction is (h - n_g)/h, which is small: for g=2, p=7, 42 of 50 classes have d=2 and no zeros at all.",
  "The Rosati-positivity remark is correct but vacuous. Z_c = (1/h) sum_psi psibar(c) L(psi) is ledger B1/S4 (E_Q = (1/h) sum L(psi)) in solved-world form, and positivity of a weighting was never a serious candidate separator.",
  "The literature novelty check was not done. The web budget is exhausted: I confirmed my own WebSearch call was refused at 200/200. The c=0 case is exactly the zeta of the Weierstrass semigroup <2,2g+1>, i.e. A_n = #|n*inf|. That very likely overlaps existing literature on numerical-semigroup and class zeta functions and their RH (Pellikaan's two-variable zeta, Duursma, Stohr, Zuniga-Galindo, Moyano-Fernandez/Tenorio/Torres). All of these are UNVERIFIED and not in the lit cache."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Circularity: none, since this is a calibration. \"Would it go through verbatim for a counterfeit?\" The object IS a counterfeit. The genuine/counterfeit split is exact and zero-readout-free: Z_X and each L(psi) come from one curve or cover, and Z_c from a linear combination. My check S3(a) rebuilt P_X = sum_d n_d T^d Phi_{g-d} from my own class census; it is on the circle with P_X(1) = h for all 12 curves. The inertia claim (exactly one added negative Toeplitz direction per off-circle pair, M* <= 2k-1) reproduced exactly. It extends to g=4: M*=4/4/3 at d=0/1/2, p=3, and inertia (n_on+1, 1, rest) at M = 4g+2. That is R17 reproduced in the solved world. The proposer's own detector (\"determinantal Euler structure\") would NOT exclude Z_0 if Euler means the formal product with nonnegative integer places (S4). The detector that works is \"counts of one curve over all F_{p^n}\", i.e. geometry, which zeta lacks (B17/R18).",
 "numerics_reproduced": "All independent code is in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/ff_theta_char_counterfeit_lab_skeptic/. None of the proposer's ffcore was used. python-flint is not in venv312, so s2_bruteforce_sympy.py runs my own Cantor code through a sympy Poly shim.\n\n(S1, s1_rr_closed_form.py / s1.log) I derived A_n(c) from Riemann-Roch. For j = 2g-2-m >= 0, l(E + m*inf) = d + m - g + 1 + max(0, floor(j/2) + 1 - d); for j < 0 the last term is 0. L(j*inf) contains only polynomials in x when j <= 2g-2. The condition u | h handles multiplicities because x - a is a uniformizer at non-Weierstrass points. This matches T^d Phi_{g-d}/((1-T)(1-pT)) for ALL g <= 10, d <= g, p in {2, ..., 13}, together with the identity (1-pT^2) Phi_k = (1-pT) + p^{k+1} T^{2k+1} (1-T). So it is a theorem for every g; the proposer's 60% for g >= 4 is resolved. Minor typo: for g=2, p=3, c=0 the sequence is A = 1,1,4,4,13,40,..., not 1,1,4,13,40.\n\n(S2, s2.log) Brute force over all effective divisors as multisets of places (split, inert and ramified), class by my own Cantor reduction, n <= 2g-1. 0 mismatches for EVERY class, including non-2-torsion ones, on 12 random curves: g=2 at p=3,5,7 and g=3 at p=3. Example h values: 9, 8, 4 / 31, 35, 22 / 50, 65, 39 / 24, 41, 12.\n\n(S3, s3.log) Threshold: Phi_k is off-circle iff p > (1+1/k)^2, with exactly one real pair, for all k <= 12 and primes <= 31 (mpmath, dps 50): 0 mismatches. PROOF FOR ALL k. With u = sqrt(p) T, on |u| = 1, (1-u^2) F(u) = 0 iff sin((k+1)theta) = sqrt(p) sin(k theta). At theta = j*pi/k the sign alternates, which gives k-2 roots. One more root lies near pi always, since F(-1) > 0. One more lies in (0, pi/k) iff k+1 > k*sqrt(p). When F(1) = k+1 - k*sqrt(p) < 0 there is a real root with u > 1.\n\nThe proposer's matrices are exact: G(g=2, p=3) minors 4, 39, 1134, -107163; [[2,5],[5,10]] with det -5; the g=3, p=3 minors 6, 99, 4860, 166941, -214820262. The M* table matches theirs. N(n) >= 1 for n <= 200, k <= 7, p <= 11.\n\n(S4, s4.log) The formal Euler place counts a_d are integers and nonnegative for d <= 150 in all 40 (k, p) cases.",
 "novelty": "Low to moderate, and literature-unverified. The qualitative phenomenon (partial class zetas are linear combinations of L-functions that keep the FE and fail RH) is the function-field twin of Potter-Titchmarsh/Davenport-Heilbronn Epstein zetas, and it is already ledger B1/S4 (E_Q = (1/h) sum L(psi)). The graph analogue E_G (S23/B5) already covered finite rank, FE and positive counts.\n\nGenuinely new for the ledger:\n(i) An exact, curve-independent closed form Z_c = T^d Phi_{g-d}/((1-T)(1-pT)) for every class and every genus, with an analytic all-k threshold p > (1+1/k)^2.\n(ii) The counterfeit is integral with N_c(1) = 1, and, per the skeptic's addition, it is a formal Euler product with nonnegative integer place counts.\n\nThe c=0 case equals the zeta of the Weierstrass semigroup <2,2g+1> and is probably known in the numerical-semigroup and singular-curve zeta literature (Stohr; Zuniga-Galindo; Moyano-Fernandez/Tenorio/Torres; Pellikaan; Duursma). All are UNVERIFIED because the web budget was exhausted and these are not in the lit cache. Do not claim novelty before checking.",
 "what_is_real": "Confirmed barrier, narrowed and in the skeptic's wording:\n\nSOLVED-WORLD COUNTERFEIT (exact, all g >= 1, all p). On any odd hyperelliptic curve over F_p with base point inf, every divisor class c has Z_c = T^d Phi_{g-d}(T)/((1-T)(1-pT)), where d = deg u(c) and Phi_k = sum_{j<=k} p^j T^{2j} - pT sum_{j<k} p^j T^{2j}. The proof is Riemann-Roch plus uniqueness of the reduced Mumford representation. Phi_k has exactly one real reciprocal pair off |T| = p^{-1/2} iff p > (1+1/k)^2, proved for all k by the sin((k+1)theta) = sqrt(p) sin(k theta) interlacing.\n\nThe objects Z_c (c = 0 always when g >= 2, p >= 3) have all of the following and still violate RH: finite rank; integral numerator with N(1) = 1; an exact FE with no pole correction; the correct pole terms; log-derivative counts N(n) >= 1 (checked n <= 200); and a formal Euler product with nonnegative integer place counts (checked d <= 150). This happens in a world where RH is a theorem. Detection is exactly one added negative Toeplitz index at M* <= 2k-1 (R17 reproduced).\n\nConsequences:\n- Corollary: no odd-model curve with g >= 2 over F_p, p >= 3, has h = 1.\n- In function fields, positivity of counts, formal Euler nonnegativity, the FE and rationality do NOT separate. Only the realization of the counts as counts of ONE curve over every F_{p^n} (Riemann-Roch / polarized H^1 / Castelnuovo-Severi / Bombieri-Stepanov) separates.\n- R3 (\"FE and Euler jointly\") is insufficient in the solved world when \"Euler\" means univariate nonnegative place counts. Only multi-prime Hecke multiplicativity (R2), which the function-field world cannot model, stays a candidate.\n- This answers Q16 for curves: every separating step consumes finite rank plus a geometric realization (death class 9).\n- The \"Euler product is the separator\" reading and the \"transfer theorem\" as a positive characterization are NOT confirmed.\n\nKernel-decidable Lean items: (a)-(d) from the proposal, plus the Riemann-Roch closed form and the all-k threshold as candidates. The identity (1-pT^2) Phi_k = (1-pT) + p^{k+1} T^{2k+1} (1-T) and the minors listed above are sound integer facts.",
 "next_step_if_survives": "It does not survive as a mechanism. Next steps, most informative first:\n\n1. Run the rigidity-gap test that this calibration points to: which extra axiom on a rational, FE-satisfying, nonnegative-Euler Z in F_q-land excludes Phi_k? Candidates are base-change compatibility, effectivity or Riemann-Roch-shaped counts A_n being p-power projective counts of ONE linear-system tower, and Jacobian cardinality signs. Then ask whether that axiom has any degree-1 Spec Z counterpart beyond Hamburger rigidity (B9). If the only excluding axiom is a geometric realization, record it as a closed transfer barrier under R18/class 9, and retire function-field transfer as a mechanism source.\n\n2. Add S4 (the formal-Euler counterfeit) to the ledger as a correction to R3's scope.\n\n3. Backfill the lit cache for semigroup/class-zeta RH (Pellikaan 1996; Duursma; Stohr; Zuniga-Galindo; Moyano-Fernandez/Tenorio/Torres) before any novelty claim.\n\n4. Optionally make the RR closed form, the Phi_k identity and the Toeplitz minors a FiniteDecide showcase."
}
```

### id_cumulant_pringsheim (barrier_hunt)
- survives adversarial review: False; prediction matched: True; claimed barrier: B28 'ID IS A GATE'. There are four parts.

(a) Finite combinations. Let L = sum_{j<=k} w_j L_j with distinct Euler products L_j and nonzero weights. Assume (H): some prime-coefficient vector v, with infinitely many primes arbitrarily near it, makes M_v(t) = sum_j w_j e^{t v_j} have >=2 exponents with nonzero merged weights. Then Re b(n) < 0 for infinitely many squarefree n. Hence ID => k = 1.
- (H) is unconditional for finite-order Hecke characters (Chebotarev) with positive weights, and for DH (verified directly).
- For GL(2) holomorphic forms, (H) follows from Deligne plus Rankin-Selberg orthogonality.
- For general GL(n) or the Selberg class, (H) needs Ramanujan or a fourth-moment bound plus Selberg orthonormality. This is UNPROVED and flagged.
- CORRECTION to the assignment wording: the converse fails. 'ID <=> single Euler product' is false, since L(chi_-4) is a single Euler product and is non-ID.

(b) ID is not necessary for W. L(chi_-4), L(chi_5) and L(chi_-20) are GRH-positive and non-ID.

(c) ID + Euler + FE + pole at 1 is not sufficient without entireness. zeta^2 L(chi_-4)/L(chi_-3) has a genuine Gamma_R^2 and is Weil-negative from x* = 2.4695. With entireness added, sufficiency is RH itself.

(d) Detection scale. The ID gate fires on the E ladder only after the Weil horizon (n_neg = 36/36/48/196 against 19.82/31.77/27.63/94.44), and it false-alarms on control+. There is no uniform r-bound for general combinations (the FE-mismatched Bernoulli example has first negative r ~ log2(1/w)).

Class: converse-type (4 / B9 / R6). The residual open question is at degree 2 (S#_2 has no classification): is there an ID, FE, pole-at-1, entire Dirichlet series that is not a finite combination of Euler products and is Weil-negative? Irrational Epstein zetas are not counterexamples: they are non-ID at frequency c^2, with b = -1/2 at frequency 2 for c = sqrt2, and they lie outside the integer-frequency setting of Hamburger and Selberg.; barrier confirmed: True

## ID is a gate, not a positivity source

Global infinite divisibility (ID, all log-coefficients b(n) = c(n)/log n >= 0) turns out to be a converse-type gate. Among finite combinations it forces a single Euler product, but it is neither necessary nor sufficient for W(x). It never acts in the critical strip, so it cannot be a positivity source (R2). This answers Q7 and closes the Q11 lead `infinite_divisibility_levy`. conjecture1_proved = False.

All artifacts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/id_cumulant_pringsheim/`. That folder holds `PREREG.md` (mtime earlier than every script), scripts `t0`-`t10` with their json/log outputs, and `IDGate.lean`.

### 1. The identity (test 0 and T1)

Take a finite combination L = sum_j w_j L_j of distinct Euler products, and distinct primes p_1..p_r.
- b(p_1...p_r) is the multilinear coefficient of log E_w[prod_i local factors].
- Working modulo t_i^2, that coefficient is the joint cumulant kappa(X_1,...,X_r) with X_i = a_J(p_i).
- If every p_i has the same local vector v, it equals kappa_r of X_v, and the generating function is M_v(t) = sum_j w_j e^{t v_j}.
- For class-group mixtures, X_C = 2 Re psi(C).

**Pre-check reproduced exactly** (harness value, exact rational value, and cumulant all agree):

| n | primes | b(n) | cumulant of X = +-2 fair |
|---|---|---|---|
| 21 | 3·7 | 4 | kappa_2 = 4 |
| 483 | 3·7·23 | 0 | kappa_3 = 0 |
| 20769 | 3·7·23·43 | -32 | kappa_4 = -32 |
| 36 | 2²·3² | -2 | (mixed term, see section 3) |

3, 7, 23 and 43 are represented by the non-principal form 2x²+2xy+3y² and not by x²+5y².

**Identity checks: 25 of 25 exact** (r = 1..5, five class structures, n up to 2.3e10). First negative cumulant r per class:

| member | class | cumulants | first negative r |
|---|---|---|---|
| E[1,0,5], D=-20 | order 2 | 0, 4, 0, -32 | 4 |
| E[1,0,6], D=-24 | order 2 | 0, 4, 0, -32 | 4 |
| E[1,1,6], D=-23 | order 3 | 0, 2, 2, -6, -30 | 4 |
| E[1,0,14], D=-56 | g (order 4) | 0, 2, 0, -4 | 4 |
| E[1,0,14], D=-56 | g² (order 2) | 0, 4, 0, -32 | 4 |

**Pringsheim lemma (general form).** Let F be entire and real on R, with F(0) = 1 and at least one zero. Then log F has infinitely many negative Taylor coefficients.
- Let R be the smallest modulus of a zero of F. This is the radius of convergence of log F, and it is finite.
- Suppose only finitely many coefficients were negative, and let P be the polynomial collecting them. Then G = log F - P has nonnegative coefficients and radius R.
- Pringsheim's theorem makes t = R a singular point of G.
- But G >= G(0) = 0 on [0, R), so F(t) >= e^{P(t)} there. Hence F(R) != 0, so log F is analytic at R. That is a contradiction.
- log F cannot be entire either, since then F = e^{log F} would have no zeros.

**Exponential polynomials have zeros.** Take >=2 distinct exponents with nonzero merged weights. Such an M has order 1, so if it had no zeros, Hadamard's theorem would give M = e^{a+bt}. That contradicts the linear independence of distinct exponentials.

**Complex weights (the DH case).** Apply the lemma to M·M*, where M*(t) = conj M(conj t). Its log-coefficients are 2 Re kappa_r, which is the real part the harness uses.

**T1.** Distinct characters (up to conjugation) differ in Re psi(C) at some class C. Chebotarev gives infinitely many distinct split primes in C. So every non-degenerate class-group mixture has infinitely many negative b(n).

### 2. Extensions

**(a) DH.** The lemma above already covers complex weights. There are also direct negatives, matching the harness to 30 digits:
- b(3) = -kappa
- b(4) = -1 - kappa²/2
- b(14) = -(1 + kappa²)

**(b) General finite combinations.** T1 needs one input (H): some prime-coefficient vector v, with infinitely many primes arbitrarily close to it, for which M_v is non-degenerate.
- Unconditional for finite-order characters (Chebotarev).
- For GL(2) holomorphic forms it follows from Deligne's bound plus Rankin-Selberg orthogonality. Orthogonality gives a positive proportion of primes with |a_1(p) - a_2(p)| >= 1, and compactness then gives an accumulation point off the diagonal.
- For general GL(n) or the Selberg class it is **UNPROVED**: it needs Ramanujan (or a fourth-moment bound) plus Selberg orthonormality.
- If the coefficient difference is one-sided and the weight w is small, the first negative cumulant sits near r = log2(1/w), so there is no uniform r bound.

**(c) Prime-power slices.** For the uniform (Epstein) weights, every single-prime slice is ID.
- Split prime in a class of order m: the slice is (1+t^m)/((1-t²)(1-t^m)), whose log is -log(1-t²) + 2 sum over odd k of t^{mk}/k >= 0. Checked for m = 2..24.
- Ramified prime: -log(1-t^m) >= 0.
- Inert prime: -log(1-t²) >= 0.

Every one of the 14,492 negative b(n) up to 2e5 has at least two distinct prime factors. The first negatives are cross terms between two primes:
- E[1,0,6] at 36 and E[1,0,14] at 196 (both primes ramified): the slice is log(1+uv), coefficient -1/2.
- E[1,0,5] at 36: -2.
- E[1,1,6] at 48 = 2⁴·3: -2.

The Goldie-Steutel link is only an analogy here: the actual proof is the closed form above.

### 3. Harness results

**First negative n, up to 2e5, for every zoo member:**

| group | members | first negative n |
|---|---|---|
| controls, ID | zeta, zetaK(-4), zetaK(-20), zetaK(-23), zetaK(-163) | none (ID) |
| controls, not ID | L(chi_-4), L(chi_5), L(chi_-20) | 3, 2, 11 |
| counterfeits | E[1,0,5], E[1,0,6], E[1,1,6], E[1,0,14] | 36, 36, 48, 196 |
| counterfeit | DH | 3 |
| probes | DH(kappa=0), DH(kappa=1) | 4, 3 |
| barriers | LEB, euler-rand d1, euler-rand d2, a2-flip | 2, 4, 3, 2 |

L(chi_-4) is GRH-positive but not ID, so W does not imply ID.

**The ID gate fires late on the E ladder.** For every Epstein, the first negative n comes after the Weil horizon, later by a factor of 1.13 to 2.08 in x:

| member | Weil horizon | first negative n |
|---|---|---|
| E[1,0,5] | 19.82 | 36 |
| E[1,0,6] | 31.77 | 36 |
| E[1,1,6] | 27.63 | 48 |
| E[1,0,14] | 94.44 | 196 |

**Battery, blind, 14 xs, predictor "-1 iff some c(n) < 0 for n < x":**
- 71 catches.
- 62 false alarms: 37 on control+ and 20 on counterfeits below their horizon.
- 16 misses, 13 of them on counterfeits.
- useful = False.

The one conflict is the known DH x=32 case (ledger C11(c)).

### 4. B28, stated precisely

- **(a)** Among finite combinations with input (H), ID implies a single Euler product. The assignment's "iff" is **false**: L(chi_-4) is a single Euler product and is not ID.
- **(b)** ID is not necessary for W.
- **(c)** ID + Euler + FE + pole at 1 is not sufficient for W.
  - R = zeta² L(chi_-4)/L(chi_-3) has a genuine Gamma_R(s)² factor and b >= 0 (checked to 2e4), yet it is Weil-negative from x* = 2.4695.
  - Its x_N are 2.46986 / 2.46965 / 2.46958 at N = 64/128/256 (float), confirmed by mp60 at N = 24.
  - It is positive at x <= 2. By linearity of the explicit formula, its form is 2Q_zeta + Q_L4 - Q_L3.
  - zeta²/L(chi_-4) is negative at every x >= 1.5.
  - The hypothesis that matters is entireness (Selberg-class axiom: no pole other than s = 1). With entireness added, sufficiency is RH itself.
- **(d)** Late detection, false alarms on controls, and no uniform r bound.

Death class: 4 / B9 / R6 (converse-type), and it fails R2.

### 5. Residual: irrational Epstein zetas

These are not counterexamples, because they are not ID. For c = √2 the log-coefficient at frequency 2 is -1/2, since it equals -a(√2)²/2 and 2 is not a value of the form. More negatives follow at 2+√2, 3+2√2, and so on. They also lie outside the integer-frequency setting of Hamburger and Selberg (hamburger_selberg_class_rigidity#0-3).

In degree <= 1, Kaczorowski-Perelli (selberg_class_rigidity#2) plus T1 force an ID member of S# to be zeta. One gap: that step needs T1 extended to Dirichlet-polynomial coefficients, which is only sketched.

**The open question:** is there an entire (apart from s = 1), FE, pole-at-1, ID Dirichlet series in degree 2 that is not a finite combination of Euler products and is Weil-negative? S#_2 is unclassified.

### Kill condition

- **For T1 (class-group mixtures): not met.** Over m = 2..36, about 1e5 samples of nu plus hill-climbing, the largest first-negative r found is 4. This is proved for classes of order 2 and 3.
- **Literal wording: met outside T1's scope.** The mixture (1-w) zetaK(-4) + w zeta² with w = 1e-4 has all b(n) >= 0 for n <= 2e5 and all kappa_r >= 0 up to r = 14, with the first negative at r = 15. It does not satisfy the FE (its gamma factors and conductors differ), so it is not a class-group mixture or a counterfeit, and it does not contradict T1.

### Lean handover

`IDGate.lean` uses core Lean v4.32.0 and kernel `decide` only (no `native_decide`), is axiom-free, and checks in 18 s:
- `kappa4 0 1 0 1 = -2` (fair +-1 law)
- `kappa4 0 4 0 16 = -32` (fair +-2 law)
- `rep5 20769 = 32`, plus the full table of representation counts
- the non-principal witnesses for 3, 7, 23, 43
- `sixteenB = -512`, which is 16·b(20769) as a set-partition sum

The partition-lattice Möbius formula behind the last one is a paper-level step and is not formalized.

### Self-audit of the prediction

Matched: P0, P1, P2a, P2c, P3 values, P4, P5, and the class-group kill prediction.

Misses and unpredicted findings:
- The E[1,0,14] first negative (196) only just fit my "< 200" guess.
- The battery misses on E[1,0,6], E[1,1,6], E[1,0,14], DH(kappa=1), euler-rand d1, and the below-horizon false alarms on LEB and the a2-flip were not predicted.
- The clean ratio horizon of 2.47 was not predicted.
- The literal kill-condition hit from the FE-mismatched mixture was not anticipated.
- My first SLSQP kill-search objective (t4) was badly normalized and inconclusive; it was replaced by the direct search (t4b).

### Other issues

- **Literature:** the web-search budget was exhausted, so the classical citations in the literature field are UNVERIFIED, and T1's novelty relative to Nakamura's work is unconfirmed.
- **Harness:** there are no new harness bugs.

**Skeptic:**

```json
{
 "angle": "WAVE 6 SKEPTIC: id_cumulant_pringsheim, claimed barrier B28 \"ID IS A GATE\". I reproduced the key numbers with my own code, which does not use the harness. It is in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/id_cumulant_pringsheim_skeptic/ (scripts s1-s5 plus their json outputs):\n- s1: exact rational log-coefficients via an Omega-derivation recurrence.\n- s2/s3: a new Weil quadratic form built from the explicit formula in u-space on a Legendre basis.\n- s4: a minimax kill search that also covers non-cyclic groups.\n- s5: DH log-coefficients at 30 digits.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "As a positivity mechanism it is dead by construction, and the proposer says so (alive=false). The Euler product enters only as a sign pattern of the log-coefficients where the series converges absolutely. That is a gate, which fails R2 and falls in R12 class 4 (with class-8 flavour). Nothing acts in the critical strip.",
  "It fails verbatim on counterfeits. R = zeta^2 L(chi_-4)/L(chi_-3) is ID, an Euler product, satisfies an FE and has a Gamma_R(s)^2 gamma factor, yet it is Weil-negative from x ~ 2.4698. ID also fires only AFTER each Epstein horizon: first negative n = 36/36/48/196 against x* = 19.82/31.77/27.63/94.44. It false-alarms on the controls L(chi_-4), L(chi_5) and L(chi_-20). Battery useful=False (71 catches / 62 false alarms / 16 misses).",
  "Wording defect in B28(b): 'L(chi_-4) is GRH-positive' holds for ALL x only under GRH for L(chi_-4). Unconditionally it is W(x) at the tested windows. It should be stated that way.",
  "Wording defect in B28(c): 'with entireness added, sufficiency is RH itself' is loose. With entireness added, sufficiency is GRH for every ID member of the Selberg class (for example all Dedekind zetas and zeta^2). That implies RH but is strictly stronger than RH alone.",
  "(c) is structurally trivial. R's strip poles are the zeros of L(chi_-3), which enter the explicit formula as -ghat(gamma'), so Q_R = 2Q_zeta + Q_L4 - Q_L3 subtracts a positive form. Weil-negativity is therefore automatic once x is moderate. R also has the non-integral conductor 4/3, so it lies outside any automorphic or integer-conductor class. The counterfeit is correct but carries little information beyond 'poles in the strip break W'.",
  "The general form of B28(a) is conditional on hypothesis (H). For general GL(n) or Selberg-class data, (H) needs Ramanujan or a fourth-moment bound plus orthonormality, which is unproved. This is flagged correctly. It is unconditional only for finite-order Hecke/class-group characters with positive weights, for DH, and (sketched) for GL(2) holomorphic forms.",
  "The side claim 'first negative cumulant r <= 4 for every positive-weight class-group mixture' is proved only for element orders 2 and 3. My minimax search (SLSQP multistart over 16 groups, including (2,2), (2,4), (3,3), (2,2,2), (4,4)) found max over w of min(k1,k3,k4) < 0 everywhere. That supports the claim but does not prove it. The optimum always sits at the non-degeneracy boundary (trivial weight 0.999), where k3 < 0 because the law X = 2 - Y is left-skewed.",
  "Novelty is unconfirmed. The Pringsheim lemma is classical in spirit (Lukacs: bounded non-degenerate laws are not ID). T1 may be folklore or may already be in the Nakamura / Aoyama-Nakamura line (infinite_divisibility_levy#2 in the cache covers only the ID <=> b >= 0 dictionary). My web budget is also exhausted, so I could not check this."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Would the argument go through verbatim for a counterfeit? Yes, which is why ID is only a gate.\n\nR = zeta^2 L(chi_-4)/L(chi_-3) passes every ID, Euler and FE input and is Weil-negative. I confirmed this with my own form.\n- The crossing (min over sectors) is 2.4713 / 2.4704 / 2.4700 / 2.4698 at N = 24/32/48/64. It decreases monotonically in N, as expected for a one-sided Ritz bound.\n- The proposer's harness gives 2.46986 at N=64, which agrees with mine at equal N to 2e-5. Their Richardson estimate is 2.4695.\n- At x=2, my even/odd lambda values are 0.290341 / 0.43393. The harness gives 0.290344 / 0.43408 (N=64) and mp60 gives 0.290360 / 0.43469 (N=24). These agree to about 1e-4 at x=2, with the odd sector as the loosest.\n- Linearity check: Q_R = 2Q_zeta + Q_L4 - Q_L3 holds to 2e-16, with L4 and L3 each positive.\n- Sanity checks: zeta stays positive (1.5e-5 at x=2.47, 3.7e-11 at x=5).\n- The Epstein horizon trends toward the ledger value: 20.56 / 20.25 / 20.12 at N = 24/32/40, against the ledger's 19.8225. It is slowly converging downward through a near-null even sector (lambda = 2.7e-4 at 19.9, N=40), so N=40 does not yet reach 19.82.\n\nOther checks:\n- The Epsteins pass ID up to n = 36/36/48/196 while their Weil horizons come earlier. This matches the ledger's sign barrier (c_E(36) = -2 * log 36 = -7.167).\n- The controls L(chi_-4), L(chi_5) and L(chi_-20) are non-ID but W-positive at the tested windows.\n- So ID is neither necessary nor sufficient, and it detects too late.",
 "numerics_reproduced": "Everything below is my own code; nothing depends on the harness.\n\n**s1: exact Fractions via the Omega-derivation recurrence.** For E[1,0,5] (normalised a(n) = r(n)/2):\n\n| quantity | reproduced value |\n|---|---|\n| b(21) | 4 |\n| b(483) | 0 |\n| b(20769) | -32 |\n| b(36) | -2 |\n| r(20769) | 32 |\n| primes 3, 7, 23, 43 | represented 0 times by x^2+5y^2 and 4 times by 2x^2+2xy+3y^2 |\n\nFirst negative n, with its b value:\n\n| member | first negative n | b there | negatives counted |\n|---|---|---|---|\n| E[1,0,5] | 36 | -2 | 319 negatives up to 21000, none at a prime power |\n| E[1,0,6] | 36 | -1/2 | none at a prime power, up to 2000 |\n| E[1,1,6] | 48 | -2 | none at a prime power, up to 2000 |\n| E[1,0,14] | 196 | -1/2 | none at a prime power, up to 2000 |\n| zeta_K(-20) | none up to 3000 | \u2014 | \u2014 |\n\nExact sympy cumulants:\n\n| law | cumulants from r = 1 |\n|---|---|\n| fair +-2 | 0, 4, 0, -32, 0, 1024, 0, -69632 |\n| fair +-1 | 0, 1, 0, -2 |\n| {2,-1,-1} | 0, 2, 2, -6, -30 |\n| {2,0,-2,0} | 0, 2, 0, -4 |\n\n**s5: DH at 30 digits.**\n- kappa = 0.284079...\n- b(3) = -kappa\n- b(4) = b(9) = -1 - kappa^2/2 = -1.04035\n- b(14) = -(1 + kappa^2) = -1.08070\n\n**s2/s3: independent Weil form.**\n- The R crossing is 2.4698 at N=64. The proposer's harness gives 2.46986 at N=64 and a Richardson value of 2.4695.\n- Linearity check to 2e-16.\n\n**Battery.** I did not re-run it. Its table is consistent with my independently computed n_neg values under the predictor '-1 iff some c(n) < 0 for n < x' (71 catches / 62 false alarms / 16 misses; the DH x=32 conflict is the known ledger item C11(c)).\n\n**s4: kill search.** Over 16 groups, including non-cyclic ones, I found no positive-weight class-group mixture with k1, k3, k4 all >= 0 at every split class. So the class-group kill condition is not met.\n\n**Proof audit, done by hand.**\n- The Pringsheim lemma is correct. F(R) >= e^{P(R)} > 0, and log F continues analytically along [0, R], which contradicts Pringsheim's theorem.\n- The Hadamard zero-existence step for exponential polynomials is correct.\n- The M M* extension to complex weights is correct: the coefficients are 2 Re kappa_r and F(0) = |a(1)|^2 = 1.\n- Linear independence of characters gives a class C with differing Re psi(C) (up to conjugation). Chebotarev then gives infinitely many n. T1 holds as stated for class-group and finite-order characters with positive weights.",
 "novelty": "Low to moderate.\n- The Pringsheim/cumulant lemma is a restatement of classical facts: bounded non-degenerate laws are not ID, and the cumulants of Bernoulli laws change sign infinitely often.\n- The dictionary 'b = joint cumulant' is elementary.\n- T1 (a non-degenerate combination of distinct Euler products is never ID) is a clean, correct statement. Its novelty relative to Aoyama-Nakamura (cached as infinite_divisibility_levy#2), Nakamura arXiv:2209.13257 and Kaczorowski-Molteni-Perelli-type linear independence results is UNVERIFIED. Both the proposer's and my web budgets are exhausted, so queue this for the lit cache.\n- The counterfeit zeta^2 L(chi_-4)/L(chi_-3) is new to the zoo but conceptually trivial (poles in the strip).\n- The Lean integer instances are kernel-checkable facts, not new mathematics.",
 "what_is_real": "Confirmed in narrowed wording, as B28 \"ID is a converse-type gate\":\n\n**(a) T1.** For finite-order Hecke/class-group characters with positive weights, and for DH, every non-degenerate finite combination has infinitely many squarefree n with b(n) < 0. The proof is correct: cumulant dictionary, then the Pringsheim lemma, then Chebotarev. So ID forces a single Euler product among such combinations. For general Euler products the same holds modulo (H), which is proved for GL(2) holomorphic forms (sketch) and open beyond that. The converse is false, since L(chi_-4) is a single Euler product and is not ID.\n\n**(b) ID is not necessary for W(x).** L(chi_-4), L(chi_5) and L(chi_-20) are W-positive at every tested x, and for all x under their GRH, yet are non-ID.\n\n**(c) ID + Euler + FE + pole at 1 is not sufficient without entireness.** The witness is R = zeta^2 L(chi_-4)/L(chi_-3): conductor 4/3, gamma factor Gamma_R^2, Weil-negative from x ~ 2.4698. This is independently reproduced. With entireness added, sufficiency becomes GRH for the ID members of the Selberg class, not 'RH itself'.\n\n**(d) Detection scale.** ID detects the E ladder only after its Weil horizons (36/36/48/196 against 19.82/31.77/27.63/94.44). There is no uniform r bound outside class-group mixtures: the FE-mismatched (1-w) zeta_K(-4) + w zeta^2 has its first negative cumulant at r ~ log2(1/w).\n\n**Survivor facts.**\n- Every single-prime slice of the uniform Epsteins is ID. Every negative b(n) has at least two distinct prime factors (reproduced for all four Epsteins in my ranges: up to 21000 for E[1,0,5], up to 2000 for the others).\n- The side claim that the first negative cumulant is at r <= 4 for positive-weight class-group mixtures is proved for element orders 2 and 3, and supported numerically for 16 groups including non-cyclic ones.\n\n**Preregistration.** PREREG.md (mtime 08:45:20) predates the first script (t0, 08:45:49). All P0-P5 items matched. Misses were self-listed, including the SLSQP t4 mis-normalisation and the literal-kill hit by an FE-mismatched mixture. That hit was correctly judged not to meet the preregistered class-group kill condition.",
 "next_step_if_survives": "B28 does not survive as a mechanism, but it is confirmed as a narrowed barrier. The most informative next steps, in order:\n\n1. Close Q7 and the infinite_divisibility_levy lead in the ledger. Record B28 in the narrowed wording above: the (b) GRH qualifier and the (c) 'GRH for ID Selberg-class members' correction.\n2. Settle novelty once the web budget allows: check Aoyama-Nakamura (Tokyo J. Math. 2013), Nakamura arXiv:2209.13257, Kaczorowski-Molteni-Perelli on linear independence, and Lukacs on non-ID bounded laws.\n3. The only residual open question with content is in degree 2. Is there an entire (apart from s=1), FE, pole-at-1, ID Dirichlet series that is not a finite combination of Euler products and is Weil-negative? This is worth one cheap experiment: take a DH-type combination at degree 2 with complex weights tuned so that every Re kappa_r >= 0 up to a large r. T1 forces eventual negatives, but the scale may be pushed arbitrarily far, which would sharpen (d).\n4. Optional Lean work: formalise the Pringsheim lemma (Mathlib has Pringsheim-type results for power series with nonnegative coefficients). It is a cheap, reusable kill-switch lemma for any future 'positivity of log-coefficients' proposal."
}
```

### siegel_segment_horizon (micro_experiment)
- survives adversarial review: False; prediction matched: False; claimed barrier: B5 REFINED ("sign and horizon are decoupled in both directions; E's sign pattern is an involution-fixed-point accident"). Along the FE-exact genus segment E_w = Z1 + (2w-1)Z2 (q = 20, Gamma_R(s)Gamma_R(s+1)), n_neg(w) (exhaustive over n <= 1e5) is:
- 2 on (0, 1/2);
- 36 only at w = 1/2;
- 12 on (1/2, 1);
- inf at w = 1.
Meanwhile x_h(w) ranges over [5.07, >110], so n_neg < x_h for every w != 1/2. B5 ("no negative coupling before the horizon") is therefore NOT family-uniform. It holds only at the fixed point u = 0 of the exact genus-twist involution c_{-u}(n) = gamma(n) c_u(n), where every gamma-odd coupling vanishes. With a magnitude threshold tau = 0.5 it holds on the exact interval w in [0.375, 0.5635], which shrinks to {1/2} as tau -> 0.

The negative couplings off u = 0 come far before the horizon: n = 2 vs 5-33, and n = 12 vs 19.8-101. So coupling signs neither detect (at w = 1/2) nor locate (w != 1/2) the Weil horizon. This strengthens B5's intended lesson, that sign information is not a mechanism, while the literal "36 > 19.82" statement turns out to be non-generic.

B7/B8 quantified: the pole-residue floor is the right limit of the family's odd horizon. x_h(0+) = x_h(L_G + pole) = 5.0716 +- 4e-4 (ledger: 5.0748), slope ~14 per unit w. Its growth follows the Siegel-pair law x_h,odd ~ 2.65 + 2.97 log(1/(beta - 1/2)) up to w_c = 0.05934, where a complex off-line zero (born w ~ 0.022, t ~ 16.1) has already set an even-sector horizon near 32.7.; barrier confirmed: True

SIEGEL_SEGMENT_HORIZON (wave 6 micro_experiment). conjecture1_proved = False.

Directory: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/siegel_segment_horizon/
- PREREG.md predates every script.
- fam.py: family constructor on the harness LData.
- s1: exact c(n) in Q[u] for n < 40.
- s2 / s7: Siegel pair and zero flow.
- s3 / s3b / s3c: argument-principle census, Re > 0.505, t in [0.25, 60].
- s4 / s6 / s10: horizons.
- s5: exhaustive n_neg to 1e5.
- s8: regime fits.
- s9: window-ID scoring and battery.
Every number below has a .json or .log beside its script. No process is left running.

FAMILY
E_w = w*zeta_K(-20) + (1-w)*L(chi_-4)L(chi_5) = Z1 + u*Z2, with u = 2w-1.
- Genus identities (r1 +- r2)/2 = sum chi_-20(d) and sum chi_-4(d)chi_5(n/d) are verified to n = 60.
- The FE holds exactly for all w. The pole at 1 has order 1 for w > 0 (residue proportional to w) and vanishes at w = 0.

EXACT COUPLINGS (c(n)/log n as polynomials in u; negative sets as w-intervals)
The brief's "affine in w" claim is FALSE beyond primes. The degree is Omega(n) in general.

| n | c(n)/log n | negative for |
|---|---|---|
| 2 | u | w < 1/2 |
| 3 | 2u | w < 1/2 |
| 7 | 2u | w < 1/2 |
| 23 | 2u | w < 1/2 |
| 4 | (2-u^2)/2 | never |
| 5 | 1 | never |
| 25 | 1/2 | never |
| 29 | 2 | never |
| 6 | 2(1-u^2) | never |
| 14 | 2(1-u^2) | never |
| 21 | 4(1-u^2) | never |
| 8 | u^3/3 | w < 1/2 |
| 9 | 3 - 2u^2 | never |
| 12 | 2u(u^2-1) | w in (1/2, 1) |
| 28 | 2u(u^2-1) | w in (1/2, 1) |
| 18 | 4u(u^2-1) | w in (1/2, 1) |
| 16 | (2-u^4)/4 | never |
| 24 | 2u^2(1-u^2) | never |
| 27 | 2u(4u^2-3)/3 | w in (0, 0.0670) and (0.5, 0.9330) |
| 32 | u^5/5 | w < 1/2 |
| 36 | -2(u^2-1)(3u^2-1) | w in (0.2113, 0.7887) |

c = 0 identically at n = 10, 11, 13, 15, 17, 19, 20, 22, 26, 30, 31, 33-35, 37-39.

Structure: c_{-u}(n) = gamma(n) c_u(n), where gamma is the completely multiplicative genus sign (gamma(2) = gamma(3) = gamma(7) = -1, gamma(5) = +1). The gamma-odd couplings vanish at u = 0, which is E. E is the fixed point of the genus-twist involution, and that is the whole reason c_E >= 0 for n < 36.

n_neg(w), exhaustive over n <= 1e5
- n_neg = 2 on (0, 1/2), then 3, 7, 8, 23, ...
- n_neg = 36 at w = 1/2 exactly, then 54, 84, 126, 189, ...
- n_neg = 12 on (1/2, 1), then 18, 27, 28, ...
- n_neg = inf at w = 1.

The first negative is set by the prime 2 (ramified, non-principal) for w < 1/2; by the 2^2*3 structure (c(12) = 2u(u^2-1) log 12) for w > 1/2; and by 36 = 2^2*3^2 (a gamma-even ramified-2 structure) only at u = 0. None of 483 or 20769 is ever first. max |c(n)|/sqrt(n) over n <= 1e5 is symmetric under w <-> 1-w, as the involution predicts.

ZEROS
- (b) w_c = 0.0593400: Lambda_w(1/2) changes sign, with A(1/2) = zeta*L(chi_-20) = -2.45292 and B(1/2) = 0.154738. W(s) = B/(B-A) is monotone on (1/2, 1), so there is exactly one real pair. beta(w):

| w | beta |
|---|---|
| 0.001 | 0.99583 |
| 0.005 | 0.97874 |
| 0.01 | 0.95645 |
| 0.02 | 0.90804 |
| 0.03 | 0.85279 |
| 0.05 | 0.69951 |
| 0.058 | 0.57564 |
| 0.0593 | 0.51307 |
| 0.05933 | 0.50653 |

  Slope: (1-beta)/w -> L(1,chi_-20)/L_G(1) = 4.156.
- (c) Census of off-line zeros, Re > 0.505, t < 60 (step 0.01; max arg step < pi/2 except one w = 0.52 segment, whose count still came out an integer):

| w | count |
|---|---|
| 0.001 | 0 |
| 0.01 | 1 (t ~ 28-30) |
| 0.05 | 3 |
| 0.1 | 6 |
| 0.25-0.55 | 7-8 |
| 0.6-0.7 | 6 |
| 0.9-0.95 | 4 |
| 0.98 | 1 |
| 0.99 | 0 |

  Lowest off-line zero:
  - Born at w ~ 0.022 near t = 16.2. Positions: w = 0.03: 0.590 + 16.150i; w_c+: 0.688 + 16.114i; w = 0.1: 0.761 + 16.067i; w = 0.3: 0.907 + 15.861i; w = 0.45-0.48: Re peak 0.934; w = 0.5: 0.93297 + 15.66825i; w = 0.8: 0.777 + 15.346i; w = 0.87: 0.592 + 15.250i. It returns to the line at w ~ 0.877.
  - After that, the t ~ 30.5 zero is lowest: w = 0.9: 0.822 + 30.419i; w = 0.95: 0.725 + 30.503i; w = 0.98: 0.567 + 30.566i. It dies at w ~ 0.982.

HORIZONS (a): x_h even / odd, float, N = 64/128/256, Richardson, uncertainty ~0.002-0.02 unless stated

| w | even | odd |
|---|---|---|
| 0.0005 | - | 5.0784 |
| 0.001 | - | 5.0853 |
| 0.005 | unresolved (float noise ~1e-14) | 5.1430 |
| 0.01 | ~101 +- 2.5 (near-noise) | 5.2232 |
| 0.02 | ~115 +- 24 (near-noise) | 5.4170 |
| 0.03 | 43.17 | 5.675 |
| 0.04 | 37.50 | 6.052 |
| 0.05 | 34.61 | 7.238 |
| 0.055 | 33.54 | 8.691 |
| 0.057 | - | 9.406 |
| 0.058 | - | 10.167 |
| 0.059 | 32.78 | 12.307 |
| 0.0592 | - | 13.658 |
| 0.0593 | - | 15.363 |
| 0.05933 | - | 17.636 |
| 0.05936 | - | 37.08 |
| 0.06 | 32.60 | 36.97 |
| 0.065 | 31.84 | 36.18 |
| 0.08 | 30.24 | 34.25 |
| 0.1 | 29.05 | 32.69 |
| 0.15 | 27.68 | 30.77 |
| 0.2 | 26.87 | 29.69 |
| 0.25 | 26.06 | 28.89 |
| 0.3 | 25.01 | 27.88 |
| 0.35 | 23.90 | 22.43 |
| 0.4 | 22.85 | 21.53 |
| 0.45 | 20.05 | 21.30 |
| 0.48 | 19.875 | 21.26 |
| 0.5 | 19.8231 | 21.267 |
| 0.51 | 19.812 | - |
| 0.52 | 19.8095 | 21.30 |
| 0.53 | 19.816 | - |
| 0.55 | 19.854 | 21.39 |
| 0.6 | 20.14 | 21.80 |
| 0.65 | 24.35 | 22.93 |
| 0.7 | 27.09 | 29.23 |
| 0.75 | 28.81 | 32.38 |
| 0.8 | 31.89 | 36.09 |
| 0.85 | 35.94 | 40.47 |
| 0.9 | 81.97 | 85.83 |
| 0.95 | 101.14 | 107.1 +- 0.15 |
| 0.98 | unresolved, > ~110 (float noise) | unresolved, > ~110 (float noise) |

Reading the table:
- The minimum of x_h over w is about 19.81, at w ~ 0.52, which is next to E.
- x_h = min over sectors is continuous at w_c, with a kink: the odd Siegel horizon diverges as eps -> 0, but the even sector (t~16 zero) caps x_h near 32.7.
- x_h is not symmetric under w <-> 1-w: the pole breaks the involution in Q.

SANITY CHECKS
- c at w = 1/2 equals the harness E[1,0,5] exactly.
- x_h(1/2) = 19.8231 vs 19.8225.
- w -> 0+: x_h(L_G + pole) = 5.0716 +- 4e-4 in this run, vs the ledger's 5.0748. The ~3e-3 gap probably comes from a different N; it is flagged, not resolved.
- x_h(0.02) = 5.417 and x_h(0.05) = 7.238 are both above the floor.
- x_h is CONTINUOUS from the right at 0+ (slope ~14 per unit w) and JUMPS at w = 0, where L_G has no pole and is GRH-positive.

TWO-REGIME LAW (held out: w = 0.03, 0.058, 0.0593 in regime I; w = 0.1, 0.5, 0.8 in regime II)
- Regime I (Siegel): x_h,odd = 2.652 + 2.971 log(1/(beta - 1/2)) for eps < 0.15. Training max residual 0.115; held-out errors 0.15 / 0.17. All-eps fit: 2.724 + 2.944 log(1/eps), max residual 0.35. Reading: the defect scales like eps^2 against a margin that decays like exp(-~0.67 x). This interpretation is not proved.
- Regime II (complex): FAILS as a single-zero law. With the t~16 zero's delta, a + b log(1/delta) gives training residual 3.2 and held-out errors of 2.1 (w = 0.5), 3.5 (w = 0.8) and 0.2 (w = 0.1). a + b/delta does no better. The horizon depends on several off-line zeros at once; for example it jumps from 36 to 82 when the t~16 zero dies at w ~ 0.877 and the t~30.5 zero takes over.

DECISIVE TEST: YES, n_neg < x_h on (0,1) \ {1/2}. No interval crossover w* exists, and B5 holds only at the involution-fixed point. With a magnitude threshold (tau = 0.5), B5 holds on w in [0.375, 0.5635] exactly; the edges are c(3) and c(18). B5 is therefore not "family-uniform" and not "refined to the residue-floor side". Both sides break it, and E is the unique exception.

B5's intended lesson, that coupling signs carry no horizon information, is strengthened. The sign-of-coupling window-ID predictor (negative iff some c(n) < 0 with n < x) scores:
- on the segment: 1144 false alarms and 33 misses (all at w = 1/2);
- on the zoo: useful = False, with 25 false alarms on controls (Dirichlet L's have negative c) and 6 counterfeit misses.

PREREG SELF-AUDIT (all misses listed)
- P1 PARTIAL. The pair, beta -> 1 and the merge onto the line all hold. The w_c prediction (0.2-0.45) MISSED badly: w_c = 0.0593.
- P2 PARTIAL. The limit 5.07 and the jump at 0 hold. The "within 0.2" claim MISSED: 0.34 at w = 0.02 and 2.2 at w = 0.05.
- P3 MOSTLY. Monotone growth on (0, w_c) holds. "x_h blows up at w_c-" holds only for the odd sector; the total is capped near 32.7 by an off-line zero that already exists (unpredicted). x_h -> large as w -> 1 holds. The minimum near w = 0.52 was not predicted.
- P4 PARTIAL. n_neg = 2 for w < 1/2 and non-affinity both hold. I MISSED n_neg = 12 on (1/2, 1).
- P5 FAILED. I predicted B5 holds on [1/2, 1); it fails there (12 < 19.8).
- Window-ID: false alarms for w < 1/2 as predicted. The false alarms on w > 1/2 were not predicted.
- prediction_matched = false.

HARNESS NOTES
- form.x_star raises "no sign change" when a larger N moves the threshold below lo. I worked around it by widening lo. This is an enhancement request, not a bug.
- The known DH x = 32 N_mp = 24 conflict reappears in the battery.

**Skeptic:**

```json
{
 "angle": "siegel_segment_horizon (wave 6 micro-experiment). The family is E_w = w*zeta_K(-20) + (1-w)*L(chi_-4)L(chi_5) = Z1 + u*Z2, with u = 2w-1. It uses the FE and has no Euler product for w in (0,1). Two claims were tested: B5 (sign before horizon) and the B7/B8 limit.\n- Skeptic directory: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w6/siegel_segment_horizon_skeptic/\n- No harness code was used. That directory holds my own lattice counts, an exact Q[u] recursion, a Legendre-basis Weil form with the u-space digamma-integral arch kernel (wform.py), and mpmath zero finding.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "Not a mechanism. The proposer says so (alive=false, Euler-product usage 'None'). The genus character enters only as an exact linear twist of the coefficients (B1 class), so the survives criterion (Euler product used nonlinearly and globally in an essential step) fails by construction.",
  "The barrier carries less new force than claimed. B5's logical content is 'c >= 0 before the horizon does not imply Weil positivity', and one witness (E) is enough; showing that E is non-generic does not strengthen or weaken it. The 'other direction' (negative couplings, yet positive to the horizon) was already in B5 via D, and in Q7 via L(chi_-4). So the genuinely new content is: (i) the involution explanation of E's sign pattern, (ii) the exact n_neg(w) map, (iii) the horizon profile along the segment.",
  "Wrong interpretive claim: 'x_h is not symmetric under w <-> 1-w because the pole breaks the involution in Q'. The Weil form sees only the pole ORDER, which is 1 at both w and 1-w, so the pole terms are identical. The real reason is that twisting the coefficients by gamma is not an isometry of the Weil form: L_u and L_{-u} are different functions with different zeros. Harmless to the numbers, but it should not enter the ledger.",
  "The 'B7/B8 quantified' item is largely a continuity tautology. For w > 0 the pole order is 1, and the coefficients converge to L_G's, so Q_{0+} = Q_{L_G} + pole term = Q_{L_G+pole}; equivalently, the Siegel pair at (1-beta, beta) -> (0, 1) cancels against nothing. It illustrates B8 with FE-exact witnesses whose residue tends to 0, but it is not a new quantification of a residue floor.",
  "The tau-thresholded window claim ('B5 holds exactly on w in [0.375, 0.5635]') is correct only below w ~ 0.96. At tau = 0.5 the exact polynomials (n <= 200) give a second set, w in [0.9652, 1), where the first thresholded negative n is >= 42. The claim was stated as exact without noting this. There B5 fails anyway, since 42 < x_h ~ 100+, but the behaviour as w -> 1 (both quantities diverge) was not assessed.",
  "The positivity half of 'n_neg < x_h' rests on Ritz values: finite-Galerkin positivity, not certified. The margins are comfortable (min lambda >= 0.0188 on x <= 5 for small w, and >= 0.165 on x <= 12 for w in (0.5, 1), both at K=64), so this is a certification gap, not a doubt."
 ],
 "prereg_honored": true,
 "counterfeit_check": "The segment is itself a family of counterfeits: FE-exact, no Euler product for w in (0,1), and off-line zeros for all w in (0, ~0.982). Nothing in the proposal is a positivity mechanism that could 'go through verbatim for a counterfeit', because it makes no positivity claim.\n- The sign-of-coupling window-ID predictor is correctly reported as useless: 25 control+ false alarms (Dirichlet L's have negative c), and on the segment 1144 false alarms and 33 misses. I did not re-run the battery.\n- Circularity: none. The decisive statement uses exact coefficient polynomials plus independently computed horizons, not zero readout. The Regime I/II laws are zero-readout fits (B2 class), and the proposer presents them only as descriptive.\n- New observation worth keeping (B8-type, sharpened): at w -> 0+ the coefficients a(n), for any fixed range of n, converge to those of the GRH-positive Euler product L_G, yet x_h -> 5.0717. The horizon is DISCONTINUOUS at w = 0: it is infinite at w = 0 and 5.07 at 0+. So any predictor that is continuous in finitely many a(n) plus the pole order is dead at L_G. Euler input has to enter through the residue / pole-coupling identity, which acts on the whole Dirichlet series (the class-number-formula type), not through local Hecke defects, which are O(w) here.",
 "numerics_reproduced": "Everything decisive reproduced with independent code (skeptic dir above; logs and JSON beside each script).\n\n(1) EXACT (k1_coeffs.py, sympy, own lattice counts, derivation recursion with Omega)\n- b(n) = c(n)/log n in Q[u] matches the proposer's table for every n <= 40. Examples: b(12) = 2u(u^2-1), b(18) = 4u(u^2-1), b(27) = 2u(4u^2-3)/3, b(36) = -2(u^2-1)(3u^2-1), and zeros at 10, 11, 13, 15, ...\n- For n <= 200 every n is represented by only one genus, so a_{-u}(n) = gamma(n) a_u(n), and b(-u) = gamma(n) b(u) holds with zero violations for n <= 200. The proof is elementary: the class group has order 2, so conjugate primes lie in the same class.\n- n_neg is exact: 2 for u < 0, 36 at u = 0, 12 for all u in (0,1) (every b(n), n < 12, is >= 0 on [0,1]), and none at u = 1.\n\n(2) ZEROS (k5_zeros.py, mpmath dps 30)\n- zeta_K(1/2) = -2.452915, L_G(1/2) = 0.1547381, w_c = 0.05933999.\n- L(1,chi_-20)/L_G(1) = 4.156174.\n- beta(w) matches to all printed digits: w = 0.001: 0.995825; 0.01: 0.956447; 0.03: 0.852792; 0.05: 0.699513; 0.058: 0.575641; 0.0593: 0.513069.\n- Off-line zeros confirmed to 1e-31 residual: w = 0.03: 0.58993 + 16.1498i; w = 0.3: 0.90670 + 15.8612i; w = 0.5: 0.932970 + 15.668250i (equals C10); w = 0.8: 0.77671 + 15.3463i; w = 0.9: 0.82178 + 30.4189i.\n\n(3) HORIZONS (wform.py: Legendre basis, u-space Weil arch, float; K = 80/120/160 total degree, i.e. 40/60/80 per sector; power-law extrapolation)\nValidation: E even gives 19.8568 / 19.8398 / 19.8342 / 19.8287 at K = 80/120/160/240, converging toward 19.8225. zeta_K x=20 even gives 4.5406e-3 at K=240, against 4.5322e-3.\n\n| member | sector | my K=160 | my extrapolation | proposer |\n|---|---|---|---|---|\n| L_G + pole | odd | 5.07200 | 5.0719 | 5.0716 +- 4e-4 |\n| w = 0.0005 | odd | 5.07874 | 5.0786 | 5.0784 |\n| w = 0.02 | odd | 5.41727 | 5.4170 | 5.417 |\n| w = 0.05 | odd | 7.23867 | 7.2383 | 7.238 |\n| w = 0.0593 | odd | 15.3677 | - | 15.363 |\n| w = 0.1 | even / odd | - | 29.053 / 32.710 | 29.05 / 32.69 |\n| w = 0.3 | even / odd | - | 25.00 / ~27.8-27.9 | 25.01 / 27.88 |\n| w = 0.5 | even / odd | 19.834 / 21.278 | 19.828 / 21.25 | 19.823 / 21.267 |\n| w = 0.52 | even | - | 19.814 | 19.8095 |\n| w = 0.65 | even / odd | 24.370 / 22.950 | 24.367 / - | 24.35 / 22.93 |\n| w = 0.8 | even / odd | 31.913 / 36.127 | 31.86 / 36.04 | 31.89 / 36.09 |\n\n- The minimum of x_h over w sits near w ~ 0.52, below E: confirmed.\n- The ledger value 5.07476 (B7/B8) is about 3e-3 too high. The converged value from two independent codes is 5.0717 +- 3e-4, and the ledger should be corrected.\n\n(4) SCAN (k3_scan.py, K=64, x in [2,45] step 0.25, 25 values of w)\n- Every member is positive before its first negative x.\n- min lambda over x <= 5 is >= 0.0188 for all w >= 0; min lambda over x <= 12 is >= 0.165 for w in (0.5, 1). So n_neg(w) < x_h(w) for every w != 1/2 at the numeric level.\n- The small-w even sector is near-null (~5e-8), so the proposer's even horizons of ~101/115 at w = 0.01/0.02 are rightly flagged as unreliable.\n\n(5) THRESHOLD (k6_tau.py)\n- tau = 0.5 gives the window [0.3750, 0.5635] (edges c(3) and c(18)), confirmed.\n- There is an extra component at w in [0.9652, 1), omitted by the proposer.",
 "novelty": "Low to moderate.\n- E = (zeta_K + L_G)/2 and the genus-character twist are classical genus theory. That a class-group character twists the coefficients, so c_{-u} = gamma c_u, is elementary and almost certainly folklore, though no specific citation is in the cache. The proposer honestly flagged it as unverified.\n- Zeros of linear combinations and Epstein zetas are covered by verified cache entries: Davenport-Heilbronn 1936, Potter-Titchmarsh 1935, Stark 1967 (real zeros of Epstein zeta in (1/2,1)) and Bombieri-Hejhal 1995 (100% on the line).\n- From memory, UNVERIFIED and not in the cache: Bateman-Grosswald (Acta Arith. 9, 1964) on real zeros of Epstein zeta in (1/2,1); it is relevant to the Siegel-pair regime and should be queued for the lit cache.\n- New: the exact n_neg(w) map, the Weil-horizon profile x_h(w) along an FE-exact segment joining a counterfeit to two Euler products, the Siegel-regime horizon fit, and the explicit discontinuity of x_h at the Euler endpoint w = 0.",
 "what_is_real": "Confirmed in narrowed wording (B5 annotation, not a new barrier). Along the FE-exact genus segment E_u = Z1 + u*Z2 (q = 20, Gamma_R(s)Gamma_R(s+1), pole order 1 for u in (-1,1)):\n\n1. Exactly, b(n) = c(n)/log n lies in Q[u] with degree <= Omega(n), and b_{-u}(n) = gamma(n) b_u(n), where gamma is the completely multiplicative genus sign (gamma(2) = gamma(3) = gamma(7) = -1, gamma(5) = +1).\n\n2. Exactly, n_neg = 2 on u < 0, 36 only at u = 0, 12 on (0,1), and infinite at u = 1. E's 'c >= 0 for n < 36' is the fixed-point effect of this involution: every gamma-odd coupling vanishes at u = 0.\n\n3. Numerically (two independent codes), x_h(w) >= 5.07 on (0, 1/2) and >= 19.8 on (1/2, 1), so n_neg < x_h for every w != 1/2. The sign-before-horizon property therefore holds only at u = 0. B5's logical force is unchanged, and 'no sign information locates horizons' is re-confirmed.\n\n4. Numerically, x_h(0+) = x_h(L_G + pole) = 5.0717 +- 3e-4 (correct the ledger's 5.07476). x_h is discontinuous at the Euler endpoint w = 0, even though every fixed-range coefficient converges to L_G's. This is the most useful takeaway: horizon predictors continuous in finitely many a(n) plus the pole order are dead at L_G, so the residue coupling must be an essential input (a sharpened B8/R5).\n\n5. The Siegel-regime zero data (w_c = 0.0593400, beta(w), slope 4.1562 = L(1,chi_-20)/L_G(1)) and the lowest off-line zeros are exact to the printed digits. The horizon table matches within 0.01-0.05 everywhere I checked.\n\n6. The prereg (08:42:39) predates the first script (08:43:17), and the self-audit lists every miss honestly (P1 w_c, P2 within-0.2, P4 n_neg = 12, P5 failed). One small unlisted item: the tau-window omits the w > 0.965 component.",
 "next_step_if_survives": "The proposal does not survive, so this is the most informative follow-up rather than a next step. Turn the w = 0 discontinuity into a kill-switch lemma and a battery test.\n- State and prove (Lean candidate): for FE-exact data with pole order 1, if a(n) -> a_{L_G}(n) for every fixed n, the Weil form converges to Q_{L_G+pole}, not to Q_{L_G}. Consequently any horizon predictor that is continuous in (a(n) for n <= X, pole order) is wrong at L_G.\n- Then add the segment members w in {0.0005, 0.02, 0.05, 0.0593, 0.1, 0.52, 0.8} to zoo.py as counterfeits, with their horizons: 5.0786, 5.417, 7.238, 15.36, 29.05, 19.81, 31.86. This supplies a one-parameter family whose Hecke defect goes to 0 while the horizon stays at 5.07. Every future mechanism must say how its Euler-product input sees the residue, i.e. the class-number-formula coupling between Res_{s=1} and L(1,chi), rather than local Hecke defects.\n- Also correct B7/B8 to 5.0717 +- 3e-4."
}
```
