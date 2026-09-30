# Hodge engine wave 7

conjecture1_proved = False.

## Portfolio

- **l1op_cascade_growth** (survivor_refinement): Q5 is the ledger's P3 item. Everything that is 'theorem modulo L1op', including R13, S20 and S22, is capped at the lemma's odds (K11), and L1op is still unscored. The skeptic's w6 data suggest the operator-norm form is the easier route. The C(G) table is a lost-artifact item on the P0 list, so this angle also clears hygiene debt.
- **beurling_hamburger_frequency_rigidity** (hybrid): Q22 asks whether any axiom has a degree-1 Spec Z counterpart beyond Hamburger. General (Beurling) frequencies are exactly where Hamburger rigidity is not automatic, so this is the untested edge. beurling_generalized_primes is untried, and P5 already lists it as a new zoo family (Euler product without FE). Part B tests directly whether the R5 residue floor can carry positivity without the FE. B8 shows that the residue matters; this checks whether it suffices.
- **ahk_epstein_real_c_walls** (wildcard): This is the least-explored domain. The combinatorial and Lorentzian Hodge theory keys are untried, and P5 flags them 'check class 9 first'. This design avoids class 9 because it needs no solved world, only the AHK propagation logic tested directly. A continuous FE-exact family through the class-number-one arithmetic points and through E itself is the cleanest test of whether E's failure at c=5 is an accident of position. It is also the first zoo object in which Hecke multiplicativity turns on and off continuously while the FE and pole stay exact.
- **b8_pole_zero_cancellation** (barrier_hunt): B8 is the sharpest structural fact in the ledger. Q24 and P2 ask for the kill-switch lemma, and the planner found that the Siegel slope 4.156174 is exactly the residue ratio L(1,chi_-20)/(L(1,chi_-4)L(1,chi_5)). If this is proved it reshapes the requirements themselves. R5/R21 currently ask every mechanism for 'residue coupling', and T3 would show that, near L_G, residue coupling IS zero readout. That avoids a wave of futile attempts, and it is a finite, Lean-friendly negative theorem (the project's kernel-certification lane).
- **cspace_relaxed_hull_q21** (micro_experiment): Q21 is the ledger's top quantitative test (P1). Taken literally, it exits trivially at n=6 via the B6 non-prime-power block, which is a forbidden gate. The relaxed PSD-hull version with conductor slack is the correct object: it comes with a clean theorem x_c <= x_h under GRH for the pieces. It is cheap, it uses the harness FormSetup fast path, and it gives one sharp number (x_c(E) vs 19.8225) plus the w -> 0+ behaviour that R21 asks about.

## Results

### l1op_cascade_growth (survivor_refinement)
- survives adversarial review: False; prediction matched: False; claimed barrier: B-L1op(r) GUARD-SCALING BARRIER. Status: numeric, two independent codes at x=20, one code converged across two precisions at x = 36..150.

Claim 1 (fixed guard). For the literal fixed-guard form (S = T* - 1/2, eta = 0, band-T* prolate span V_K per sector), the sup-form constant C(G) is NOT uniform in x:
- ln C = a + s(Sh - K) with s = 0.58-0.60 per index, independent of x = 20..150. So C(G) grows like exp(0.59 G A) in G-units of A.
- The extra R13 dimensions needed are Delta_d(eps = 1e-10) = 1.34 -> 3.28 from x = 20 to 150, fitting ln c (0.045 sqrt(ln x ln(1/eps)) - 0.08).
- Via this route R13 therefore picks up a growing O(ln c sqrt(ln x ln(1/eps))) loss on top of the Landau-Widom width.

Claim 2 (scaled guard). With the scaled guard r = 1/(2A) the constant is x-uniform (G=1: about 2; G=6: 43-66 at x = 20..100). The loss is a constant fraction (about 12-15%) of the width ln(1/eps) ln c/(2pi^2); the strip factor 2/r^2 = 8A^2 costs only ln(8A^2).

Verdict. "R13 permanently conditional" is NOT the right conclusion. R13 stays conditional only on the open edge-energy lemma L-B, and the guard must scale like 1/ln x.

Side barrier (Hodge-split leakage). With P = zero-constrained prolates, the Schur leakage of the zeta Weil form exceeds lambda_max(PQP) by 6e4 at G=1 (x=20), and C_op >= 44 up to 2e20. The block split along the arithmetic cascade is lossy (B3/B25 instance).

Do not downgrade R13.; barrier confirmed: False

# W7 l1op_cascade_growth: report

conjecture1_proved = False. This is barrier and infrastructure work (class 7), not a mechanism.

Directory: /Users/peterwmurphy/hodge-engine/hengine/w7/l1op_cascade_growth/

| file | contents |
|---|---|
| PREREG.md | predictions; mtime 16:51:07, before every script |
| RESULTS.md | scored table |
| csup.py | Engine A |
| engB_sk_l1.py, engB_anal.py | Engine B (fixed copy of the w6 skeptic code) |
| fitgrowth.py / .log / .json | growth-law fits |
| dimloss*.py / .log / .json, dimfit.log | R13 dimension-loss tables and fit |
| wform.py (fixed copy of w6 q8own), q8inv.py | Legendre Weil matrices and lambda_1 |
| q8_partA.log, q8_nucheck.log | Q8 values and arch-node check |
| cop.py, cop_*.log / .json | Weil-form C_op |
| counts.py, counts.log / .json | P7 counts |
| csup_x{20,36,64,100,150}_*.log / .json, csup_x*_rA.* | C(G) runs, including the r = 1/(2A) guard |
| w6_*.py | verbatim copies of the w6 basis code |
| lit_index_backup_pre_w7.json | lit cache before this wave's write |

The directory is about 118 MB, mostly Weil-matrix pickles.

## 1. P0 reproduction: done exactly (odd sector)

Engine A uses the exact prolate duality identity. Engine B is the w6 skeptic's frequency-side code. The two agree to all printed digits at x=20:

- odd sector: C = 3.413 / 10.69 / 66.59 / 378.4 at G = A / 2A / 4A / 6A;
- x=36 odd: 4.001 / 13.44 / 157.2 / 856.2;
- the even sector is about 1.3x larger.

So the w6 numbers are the odd-sector (= global-index) values; the basis dependence is only the sector convention.

C50 is strengthened. Two bugs in the preserved w6 scripts:
- sk_l1.py uses cylindrical J_{n+1/2} without sqrt(pi/2w), which gives garbage Tail_T = -93.
- q8own.py uses float(A) in the constant term, which floors lambda at e^{-37.3}.

The preserved files are therefore not the code that produced the w6 numbers. Fixed copies are here.

## 2. Growth law (x = 20, 36, 64, 100, 150; converged in prec and Nmax)

- ln C is linear in the index deficit d = Sh - K, with slope 0.593 / 0.599 / 0.591 / 0.583 / 0.577 per index. That is x-independent to 3%.
- In G-units of A the slope is 0.89 / 1.07 / 1.23 / 1.34 / 1.45, tracking ln x. P5's ratio is 1.37: the failure branch.
- AIC prefers linear over sqrt(GA) and G ln G by dAIC 25 / 16 / 9 / 5.5 / 3.8. There are only 6 points, and at x=150 they are indistinguishable.
- The 1-mu decay per index is 3.62 to 2.48, matching 2pi^2/ln c (per-sector Landau-Widom width ln c/(2pi^2)). Keep in mind the factor 2 between the per-sector and global conventions.
- R13 cost: Delta_d(eps = 1e-10) = 1.34 / 1.85 / 2.39 / 2.84 / 3.28. The best law is ln c (0.045 sqrt(ln x ln(1/eps)) - 0.08), so the loss grows with x.

## 3. Scaled guard (exploratory, NOT preregistered)

A WKB reading says the fixed xi-guard r = 1/2 covers a growing fraction A/beta of the prolate evanescent edge layer (width beta/2c in t). With r = 1/(2A) (t-window 1/(2c)), that fraction is x-free.

Measured:
- C(G) is uniform: G=1 about 1.9-2.4, G=6 43-66, at x = 20 / 36 / 64 / 100.
- Delta_d / width is 3.08 to 2.84 at eps = 1e-10, a flat fraction of about 12-15% of the Landau-Widom width.
- The strip-to-line factor 2/r^2 costs ln(8A^2).

Candidate theorem (modulo L-B): #{lambda_k(Q_x) <= eps} >= e*(x) - (1+kappa) ln(8A^2 C/eps) ln c/(2pi^2) - O(1) per sector, with kappa about 0.15.

## 4. Proof attempt

- (A) Exact identity and trace bound: proved (see mechanism).
- (i) Plunge count: available from Karnik-Romberg-Davenport or Osipov (verified metadata, constants unread).
- (iii) Pure-archimedean lower bound: reduces to L-B, the edge energy of psi_k for chi_k < c^2 in a 1/(2c) window, bounded by (1-mu_k) exp(C sqrt(ln 1/(1-mu_k))). This is the exact open inequality; it needs Olver bounds through the turning point.
- (ii) For the Weil-form version the off-diagonal fails as predicted:
  - ||P_perp Q P|| = 5.5e-4, lambda_min(P_perp Q P_perp) = 1.24e-5 and lambda_max(PQP) = 4.1e-7 at G=1, N=200, even sector.
  - The Schur leakage is 0.025, which is 6e4 times lambda_max(PQP).
  - C_op runs 44 to 2e20 over G = 1..6, and is a lower bound because it is not N-converged.
  - The prime/pole part is not band-limited, so this cannot be a block certificate.

## 5. Q8

-ln lambda_1(zeta, 20) = 218.535 / 220.790 / 220.921 / 220.974 / 220.989 at N = 160 / 200 / 240 / 320 / 400 per sector (Legendre, even sector). dps 150 = 260, and arch nodes 349 = 500. Converged to about 221.0, and >= 220.99 as a Ritz bound. The odd sector gives 210.81. Q8 is closed at the 0.02 level.

## 6. Counterfeit blindness

The cascade equals the twin's +-1, and the index appears only past the horizons (table in counterfeit_control). DH is negative in both sectors at x=32, so the zoo's DH@32 conflict is resolved as an artefact. L1op does not exclude hyperbolic blocks; the Euler input must (R17).

## Ledger recommendations

1. Q5 / L1op: record B-L1op(r). The fixed guard is non-uniform in x. The scaled guard r = 1/(2A) is uniform, and L-B is the single open lemma. Do not downgrade R13.
2. C50: the preserved w6 scripts are buggy, so they are not the generating code.
3. Q8: closed at about 221.0.
4. The zoo DH@32 conflict is an N-artefact.
5. C(G) conventions: the w6 values are odd-sector.

## Harness bugs (reported, not edited)

- zoo DH@32 metadata versus measurement is resolved in favour of negative.
- No new harness bug was found. The two bugs are in the preserved w6 scripts, not in the harness.

**Skeptic:**

```json
{
 "angle": "Wave 7 skeptic review of l1op_cascade_growth, the operator-norm guard-band lemma L1op behind R13. This is class-7 archimedean barrier and infrastructure work, not a positivity mechanism. conjecture1_proved = False. I rebuilt the decisive numbers with my own code in /Users/peterwmurphy/hodge-engine/hengine/w7/l1op_cascade_growth_skeptic/:\n- skc.py, a fresh C(G) engine: float64 commuting-operator prolates, exact Gram V^T V, and the frequency-side tail (2/pi) int h_v h_u with arb spherical Bessel functions (Miller recurrence normalised by sum (2n+1) j_n^2 = 1);\n- q8sk.py, a separate Weil-form evaluator: exact rational Legendre polynomials, exact polynomial autocorrelation g, and a Gauss-psi archimedean constant that differs in form from the proposer's E1 split.\n\nLogs and JSON are in the same directory (anal.log, skc_x*.log/json, q8sk_*.log).",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "It is not a mechanism: purely archimedean, the Euler product is never used, and it holds verbatim for E and DH (their cascades equal their twins' +-1). Under the brief's default rule it cannot survive. The proposer says so too.",
  "The claimed barrier B-L1op(r), Claim 1 ('fixed-guard C(G) NOT uniform in x; grows like exp(0.59 G A)'), is not a correct precise negative result. Trivially Tail <= ||f||^2, so C(G) <= 1/(1-mu_{K-1}). By Landau-Widom, ln(1/(1-mu_{K-1})) ~ 2pi^2 (GA+1)/ln c < pi^2 G + O(1), since 2A/ln c < 1 (measured 0.57 to 0.645). So for each fixed G, C(G) is uniformly bounded in x (weakly: the cap at G=6 is about 1e16 while C is about 1e4). The fitted law ln C = a + 0.59 d exceeds that cap once the Landau-Widom per-index rate 2pi^2/ln c drops below 0.59. My fits put that crossing at ln c* = 33.2 to 34.5 (x ~ e^30), so the law cannot hold asymptotically.",
  "Most of the claimed 'non-uniformity in x' comes from measuring G in units of A. In index units the fixed-guard C is nearly x-independent. Even sector at deficit d ~ 8: 161 / 210 / 277 / 215 / 250 for x = 20 / 36 / 64 / 100 / 150. At d ~ 12: 1.5e3 / 1.9e3 / 2.5e3 / 2.0e3 / 2.35e3. The real content is the drift of kappa = ln C / ln(1/(1-mu)): 0.17-0.21 at x=20 up to 0.25-0.36 at x=150. That is a finite-range quantitative observation over ln x in [3,5], not a barrier.",
  "The R13 loss law Delta_d = ln c (0.045 sqrt(ln x ln 1/eps) - 0.08) is a two-parameter fit over x = 20..150 (ln x spans 3 to 5). It cannot tell apart growth, saturation, or the WKB-predicted collapse to the trivial bound. That collapse is expected once the turning point enters the fixed guard, at A >~ beta ~ (2/pi) ln(1/eps), i.e. x ~ e^30 at eps = 1e-10. None of this is established.",
  "Bug found in the proposer's wform.py, which built the Q8 matrices. The archimedean quadrature uses nu = Nmax//2 + 150 Gauss nodes, which is exact only up to polynomial degree 2nu-1. So the N=240/320/400 matrices are wrong in the high-degree corner (entries with deg_j + deg_k >~ 2nu). At N=400, a random vector over all degrees gives 150.6552984 with their matrix and 150.6556007 with my evaluator, a difference of 3.0e-4. My value is identical to 30 digits at 800 and 1300 nodes. Random vectors restricted to degree <= 500 or <= 300 agree to 1e-262. So this does not affect lambda_1, but the 'arch nodes 349 = 500' check tested lambda_1 only and did not validate the matrices."
 ],
 "prereg_honored": true,
 "counterfeit_check": "L1op concerns band-limited prolates and the archimedean near-null cascade only. By construction it is counterfeit-blind: the lemma holds identically for E[1,0,5] and DH, and it predicts no failure scale for any counterfeit. The proposer states this correctly.\n\n- P7 (the E/DH negative index appears only past the horizons 19.8225 / 30.571, on top of the twin's cascade +-1) is consistent with ledger B21/B25. I did NOT independently re-run it; it went through the harness mp/LDL path.\n- The circularity question does not arise, because no RH-type claim is made.\n- The only RH-relevant content is structural: L1op controls the positive cascade half of R17. The added hyperbolic negative index must come from an Euler input acting inside the inequality, not blockwise. That is correct but not new (B3/B25/R17).",
 "numerics_reproduced": "**C(G), my independent engine.** Every printed digit matches the proposer's at every x and G checked, in both guards and both sectors.\n\n| x | guard | odd sector | even sector |\n|---|---|---|---|\n| 20 | fixed, S = T - 1/2 | 3.413 / 10.69 / 19.71 / 66.59 / 120.4 / 378.4 (G = 1..6) | 4.452 / 14.5 / 26.8 / 89.7 / 161.1 / 499.7 |\n| 36 | fixed | G=1: 4.001, G=6: 856.2 | G=6: 1122 |\n| 64 | fixed | G=1: 4.855, G=6: 3238 | G=6: 4186 |\n| 100 | fixed | G=1: 6.501, G=6: 7316 | G=1: 8.99, G=6: 9383 |\n| 150 | fixed | G=1: 7.298, G=6: 1.391e4 | G=1: 10.18, G=6: 1.774e4 |\n| 20 / 36 / 64 / 100 | scaled, r = 1/(2A) | G=1: 2.094 / 1.941 / 1.86 / 1.886; G=6: 51.44 / 43.05 / 54.01 / 56.52 | |\n| 150 | scaled | (not run by the proposer) | G=1: 2.00, G=6: 64.6 |\n\n- **Sensitivity.** Changing precision (256 to 320 bits), Nmax (+80 to +140) and quadrature nodes (Q factor 0.75 to 1.0) leaves every printed digit unchanged at x=64. The Gram departs from the identity by at most 5e-15. The arb radius is about 1e-75.\n- **Fits.** The per-index slope of ln C is 0.594 / 0.591 / 0.588 / 0.579 / 0.573 for the fixed guard, reproducing the proposer's 0.59. The 1-mu decay per index is 3.62 to 2.48, against 2pi^2/ln c = 3.77 to 2.54; the Landau-Widom per-sector width is confirmed.\n- **New observation.** Under the scaled guard, the ratio of the ln C slope to the 1-mu decay rate is constant at 0.111-0.114 for x = 20..100, so kappa ~ 0.11 is flat. Under the fixed guard the same ratio rises: 0.164 / 0.186 / 0.207 / 0.219 / 0.231.\n- **Q8.** I evaluated the minimising N=400 vector (inverse iteration on their dump) with my own evaluator. I get Q(v) = 1.061335814e-96 (arb radius 1e-250, identical at 800 and 1300 archimedean nodes), against their v^T M v = 1.0613360e-96. So the Ritz bound -ln lambda_1(zeta, 20) >= 220.98864 is independently confirmed. That the limit is about 221.0 is still an extrapolation, since Ritz values only bound lambda_1 from above. The N=40 dump agrees to 6e-63.\n- **Not reproduced:** C_op, the Hodge-split leakage (the proposer says it is not N-converged, so it is a lower bound), and the P7 counts.\n- **Confirmed:** the preserved w6_sk_l1.py omits the sqrt(pi/2w) factor, as claimed.",
 "novelty": "- **Classical.** The Slepian duality identity Tail = (1-mu) delta + (c/pi) lam_k lam_l int psi_k psi_l, and the trace bound L-A, are classical prolate theory (Slepian-Pollak 1961; Osipov-Rokhlin-Xiao 2013; lit key prolate_time_frequency_limiting, metadata verified, full texts unread).\n- **Prior art.** Q8's law is Zhu arXiv:2608.24827 (weil_positivity_window_frontier_2026#4). The leading cascade count is Connes-Consani, and prolates already appear in their archimedean Weil-positivity work (2006.13771, #2).\n- **New but narrow.** Three pieces:\n  - measured guard-band sup constants C(G) for prolate spans;\n  - the scaled-guard observation (kappa ~ 0.11, flat in x);\n  - the index-unit near-uniformity.\n\n  No literature was found, so novelty is unverified. All three are technical infrastructure for R13 and carry no RH content.",
 "what_is_real": "**Real and verified by my independent code:**\n1. **The C(G) tables.** Fixed and scaled guards, both sectors, x = 20..150, all to every printed digit. The w6 values 3.4 / 11 / 67 / 380 are odd-sector values. Separately, the preserved w6 sk_l1.py omits the sqrt(pi/2w) factor, as the proposer says.\n2. **What actually happens to the fixed guard.** Measured per index, the fixed-guard C is almost x-independent (slope 0.57-0.60 per index, intercept drifting by about 0.7). Its usefulness still degrades because the Landau-Widom rate 2pi^2/ln c falls: kappa = ln C / ln(1/(1-mu)) rises from about 0.17 to 0.25-0.36 over x = 20..150. The dimension-loss values Delta_d(1e-10) = 1.34 to 3.28 are correct as measured numbers.\n3. **The scaled guard r = 1/(2A) (exploratory).** It gives an x-flat kappa of about 0.11: the ratio of slope to Landau-Widom rate is 0.111-0.114 at x = 20..100, and C(G=1) is about 2 at x = 20..150. It is the right form for a provable R13, at an added cost of ln(8A^2).\n4. **Q8.** Checked by my own evaluator: -ln lambda_1(zeta, 20) >= 220.98864 as a Ritz bound.\n5. **wform.py bug.** Under-resolved archimedean quadrature in the high-degree block of the N >= 240 Weil matrices. It is harmless for lambda_1 but should be fixed with nu >= Nmax + 150.\n6. **Prereg.** PREREG.md (16:51:07) predates every script, and the misses (P4, P5, the P1 convention, P2 convergence) are self-reported. P1 would be a strict MISS under the declared max-over-sectors convention; the proposer labelled it PARTIAL but disclosed it fully.\n\n**Not real:**\n- The claimed barrier as stated. For fixed G, C(G) is uniformly bounded by the trivial cap 1/(1-mu_{K-1}) <~ e^{pi^2 G + O(1)}.\n- The exp(0.59 G A) growth law, which must break by ln c ~ 34.\n- The Delta_d growth law, a five-point fit over a narrow ln x range.\n- Nothing here bears on positivity or RH.",
 "next_step_if_survives": "It does not survive, but the most informative next step for the R13 infrastructure is this.\n\n1. **Restate L1op in index units with the scaled guard.** The target form: sup over V_K of Tail_{T - 1/(2A), eta} <= C0 e^{2A|eta|} (1-mu_{K-1})^{1-kappa}, with kappa ~ 0.11 x-uniform.\n2. **Prove it via L-B.** L-B is the edge-energy bound in a 1/(2c) window through the turning point: Olver / Liouville-Green bounds plus the Karnik-Romberg-Davenport or Bonami-Jaming-Karoui non-asymptotic plunge count.\n3. **Test the kappa laws at large x.** Before any proof effort, run both kappa laws at x = 1e3..1e4 with skeptic skc.py, which does x=150 in 80 s per sector. Restricting the H columns to the plunge-region prolates keeps this cheap. Check that:\n   - the scaled-guard kappa stays flat;\n   - the fixed-guard kappa keeps rising toward the WKB saturation.\n4. **Fix the Q8 matrices.** Set wform.py arch nodes to nu >= Nmax + 150 before any further use of the N >= 240 Weil matrices."
}
```

### beurling_hamburger_frequency_rigidity (hybrid)
- survives adversarial review: False; prediction matched: True; claimed barrier: **B31 (converse; covered class stated exactly).** Degree 1, Gamma_R(s), conductor 1, simple poles at 0 and 1, FE Lambda(s) = Lambda(1-s), finite order. If the frequencies form a positive-mass, Euler-closed Beurling semigroup S (masses = factorization counts), then S uniformly discrete => S = Z_{>0} and zeta_B = zeta.
- Positivity is used only to make supp mu = S.
- NOT covered: non-u.d. S, which is the whole generic Beurling world and the Q22 gap, and signed or complex Euler data, whose support can lose multiplicative closure.
- Adversaries:
  - Guinand/Meyer sqrt(n) measures violate Euler closure: sqrt3 * sqrt5 = sqrt15 is not in the support, and the masses 4/3 are non-integral.
  - Finite-scale near-counterfeits exist at every X (residual ~ exp(-pi p^2/X)), so no finite-window FE certificate pins all primes. This is a visibility law: nu_vis ~ sqrt(X ln(1/delta)/pi).
  - The certified finite-scale rigidity holds for K=4 only: at X=10 and X=25, down to eps = 0.02.

**B31b (Weil side, class 11).** For a Beurling datum whose comb equals zeta's below p_d, with an off-integer atom at p_d (residue held at 1 or 1 +- 1e-3, DMV-type theta = 0.51 or 0.7), W(x) fails at x_B in [p_d, p_d(1 + 5e-4..1.3e-3)] (N=64 Ritz, mp-certified negative direction). x_B is independent of R and tracks P0 (7, 13, 31, 101 -> about 11, 17, 37, 103). Removed atom -> odd sector, added atom -> even sector. The residue is invisible to W(x): the window sees only atoms below x and the pole order, so no 'residue source' of positivity exists in this family. As a predictor it is a zeta-agreement lookup: battery useful=False, with 63 control+ false alarms.; barrier confirmed: True

WAVE 7: beurling_hamburger_frequency_rigidity. conjecture1_proved = False.

**0. Harness reproduction and feature request.**
- The harness Window stores the comb as W.terms. Overriding it with arbitrary atoms (base, k), where nu = base^k and c = log base, all evaluated at the working dps, reproduces form.Q for zeta EXACTLY (max|dB| = 0.0) on float and mp80.
- Feature request (the harness was not edited): add a `terms=` / `atoms=` argument to form.Q / Window for Beurling and generalized combs. The Loewner identity is per-term valid for any 0 < log nu < 2A.
- Footgun found: computing mp.log(p) outside workdps silently limits mp runs to 1e-16. Build the atoms inside workdps.

**1. Part A theorem: B31.**
- The proof is in the mechanism field. Its components:
  - Bochner (FE <=> modular relation);
  - a self-dual tempered measure mu = R delta_0 + sum m(delta_nu + delta_-nu);
  - Lev-Olevskii Theorem 1 (verified verbatim: dimension 1, complex measures, u.d. support AND spectrum give a finite union of lattice cosets);
  - a new elementary semigroup lemma (Euler closure + pigeonhole + denominators gives each nu in Z);
  - Hamburger.
- Positivity is needed only so that supp mu equals the full semigroup.
- Honest Q22 answer in degree 1: the residual class is positive, integer-mass, Euler-closed, self-dual crystalline measures with NON-u.d. support. Generic Beurling systems fall into this class (unbounded local counts). Kurasov-Sarnak and Meyer/Guinand show that non-u.d. positive or crystalline measures exist, but none is Euler-closed and self-dual.
- Adversarial test (a), signed coefficients: not covered. Cancellation breaks support closure.
- Adversarial test (b), Guinand: the support {sqrt n : r3(n) > 0} is not multiplicatively closed (15, 28, 39, 55, 60 missing), the masses r3/6 are non-integral and non-multiplicative (11 coprime violations for n, m < 9), and the gamma factor is Gamma_R(s+1) with a pole at s=2. So it carries no Euler structure. Artifact: a4_guinand.json.
- Frequency scaling: killed analytically (1 in S with mass 1; q=1 forces lambda=1) and numerically (residual 0.005 at lambda = 1.001).

**2. Part A certificate.**
- Setup: F(t;p) = R(p)(1 - sqrt t) + 2(S(1/t) - sqrt(t) S(t)) on a 24-point grid in (1, X]. R(p) is tied to the Euler product; primes above pi_K are fixed; p1 is in [1.05, 2.5]. The interval (1, 1.05) is not certified (a gap: the power count diverges as p1 -> 1).
- Bounds: exact monotone corner enclosures, plus a Taylor-model LP with rigorous termwise Hessian bounds. Outward margin 1e-12 * magnitude; 6/6 mpmath.iv spot-checks agree.
- K=4 certified at eps = 0.2, 0.1, 0.05, 0.02:
  - X=25: lower bounds 1.97e-3, 1.10e-3, 5.5e-4, 2.1e-4;
  - X=10: 2.1e-5, 1.0e-5, 4.9e-6, 2.0e-6.
  So the lower bound is about linear in eps, and the finite-scale rigidity radius is <= 0.02 at both X. The slope rises about 100x from X=10 to X=25, set by the weakest singular value (p=7): 4.4e-4 -> 0.038.
- K>=5: the Jacobian is numerically rank-deficient (sv 1e-7..1e-18), and K=5 at X=25 failed within 60k boxes. P2 is a MISS here.
- The true finite-scale law is a VISIBILITY law. Residue-preserving pair moves give residual ≈ exp(-pi p_a^2/X), measured in mp:
  - (11,13) at X = 10/25/50/100: 2e-16, 3.7e-7, 3e-4, 4.5e-3;
  - (13,17) at X=25: 8.6e-10.
  These are explicit off-integer finite-scale counterfeits. All die at large X, since the exact FE is rigid by B31.
- Degree 2 (P3): no off-ball near-solution below 1e-8; the best is 7.9e-7. Moving the two norm-p atoms of a split prime in opposite directions, p -> (p+d, p-d), is flat to second order. P3 did not occur.

**3. Part B, the decisive test.**
- 48 configs; x_B is in [p_d, p_d(1 + 5e-4..1.3e-3)], independent of R, tracking P0. The full table is in counterfeit_control.
- The failing sector obeys the edge-overlap sign lemma: a removed atom perturbs Q by +2c g(log p) with g ≈ -delta f(A)^2 < 0 for odd f; an added atom perturbs by -2c g with g ≈ +delta f(A)^2 for even f. Zeta's near-null margin (~e^{-12x}) then makes the failure immediate.
- Hence B31b: the residue is not a positivity source, and x_B grows with P0 only because the datum agrees with zeta below P0 (class 11).
- The Weil window is far more frequency-sensitive than the finite-scale FE: it sees p at x ≈ p, whereas the theta-FE needs X ~ pi p^2/ln(1/delta). But that sensitivity IS zeta's near-nullness (R17/B25), not an Euler-sourced positivity.

**4. Classes evaded or hit.**
- B31 is class 4 (converse theorem; R6 circular as a mechanism). It is silent on every zoo counterfeit, since all have integer frequencies (battery: all abstain).
- B31b is class 11. As a predictor it is useful=False.
- It is not an RH mechanism; the angle is closed as a positivity route. What it contributes:
  - a clean degree-1 frequency-rigidity theorem for u.d. Beurling data;
  - an exact statement of the non-u.d. gap;
  - a finite-scale visibility law.

**Provenance and verification.** Everything here is same-session work with no skeptic or peer (C39 applies). Nothing is interval-certified except the Part A box bounds, whose rigor rests on the float64 margin plus the iv spot-check. The Part B negatives are mp LDL inertia at N=64, stable under dps+60.

Sources: [Lev-Olevskii arXiv:1312.6884](https://arxiv.org/abs/1312.6884); [Bochner 1951 / modular relation](https://link.springer.com/chapter/10.1007/0-387-30829-6_9); [Chandrasekharan-Narasimhan 1961](https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/arithmetical-identities-and-heckes-functional-equation/4FD5F3F91459276D69A279253BFC72A1).

**Skeptic:**

```json
{
 "angle": "beurling_hamburger_frequency_rigidity (w7 skeptic). The proposal has two parts. Part A is B31: a degree-1 converse theorem saying that a u.d. Euler-closed Beurling semigroup with the Riemann FE must be zeta, plus finite-scale FE certificates. Part B is B31b: Beurling combs with residue held fixed fail W(x) at the first moved atom p_d.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "As an RH mechanism it has no content. B31 is a converse/uniqueness theorem (class 4, R6). It says which data IS zeta, not WHY zeta's window form is positive. It is silent on every zoo counterfeit: E, DH, LEB, a2-flip and E_w all have integer frequencies, and E and DH are outside degree 1, conductor 1 anyway. Within degree 1, conductor 1 and integer frequencies, Hamburger 1921 already leaves no counterfeit. The Euler product is used globally and nonlinearly (multiplicative closure of the whole support), but only to identify the datum, never as a positivity source. The proposer concedes this (alive=false).",
  "B31b is not a new barrier. It is a special case of B3/B20 (zeta's near-null margin is about e^{-12x}) together with B22 (Euler without FE fails early). Any O(delta) comb perturbation at log p_d beats a margin of about 1e-50. 'The residue is invisible to W(x)' holds by definition: R appears nowhere in Pole+Arch-Comb, because the pole term depends only on the pole order. It is not a measured finding.",
  "Part B is less than it looks. '48 configs, 48/48 sector rule, x_B identical across R' rests on 22 non-deduplicated rows. b2_xB.py memoises on the atoms below 1.1 p_d, so configs that differ only in R were NOT recomputed; their equality is a cache hit. That leaves 3 physically distinct cases per P0 (removed, added theta=.51, added theta=.7), 12 in total.",
  "The literature check missed the direct predecessors in exactly this setting. These are Chandrasekharan-Mandelbrojt 1957 (Th. 3: under a gap condition, the frequencies are Z-combinations of finitely many) and Kahane-Mandelbrojt, Ann. Sci. ENS 75 (1958) 57-80. I downloaded and read KM. Its Theorems 1-3 turn a general Riemann-FE Dirichlet series into an almost-periodic self-dual distribution, which is the 'flagged density step'. Its Theorem 7 covers FINITE UNIFORM DENSITY frequencies, not only u.d. ones. So the analytic half of B31 predates LO 2015 by about 57 years, and novelty is essentially just the elementary semigroup lemma. The stated Q22 gap ('non-u.d. is not covered') is also imprecise: bounded-local-count sets are partly covered by KM Thm 7, reducing them to a finite-rank Z-module.",
  "The Part A 'certificate' is float64 with a 1e-12 relative outward margin, not directed-rounding interval arithmetic. It is also a finite-dimensional statement: K=4 moved primes, all others fixed at rational primes, p1 in [1.05,2.5]. K=5 was not certified. The 'visibility law' residual ~ exp(-pi p_a^2/X) is immediate from the Gaussian term at t=1/X. It fails for small primes: (3,5), (5,7) and (7,11) saturate near 1e-2 for X>=25."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Would B31 go through verbatim for a counterfeit? It cannot even be stated for the zoo. E (degree 2, conductor 20, h=2), DH (no Euler product) and LEB/a2-flip/euler-rand (no FE) all violate its hypotheses. Every zoo member has integer frequencies, so the predictor abstains on all 171 battery cells (useful=False, as the proposer reports). B31b as a predictor is a zeta-agreement lookup, with 63 false alarms on control+ members (class 11).\n\nMy own independent code confirms the B31b mechanism is counterfeit-generic. ANY datum whose comb departs from zeta's at log p_d fails just above p_d, because zeta's form is near-null. This involves no Euler-specific structure.\n\nIs the Euler product used nonlinearly and globally in an essential step? Yes in B31 (nu*S in S, nu^k in S, pigeonhole, then denominators), but that step identifies the datum, not positivity. In Part B the residue, the one global Euler quantity, provably never enters Q.\n\nPrereg: PREREG.md was born at 16:53:18, 28 s before the first script (gencomb.py / b0_repro.py at 16:53:46), and has one later modification, the appended SCORES at 17:31. P2 was honestly scored as PARTIAL/MISS. The P2 sub-claim 'rigidity radius decreases from X=10 to X=25' was not actually tested (both sit at the 0.02 ladder floor). PB is a legitimate HIT but a cheap one: the bracket (p_d, 1.3p_d] was wide, and the 'R-independence' component is definitional and cache-driven.",
 "numerics_reproduced": "I wrote an INDEPENDENT window Weil form that does not import the harness: /Users/peterwmurphy/hodge-engine/hengine/w7/beurling_hamburger_frequency_rigidity_skeptic/wform.py.\n- Basis: Legendre P_j(t/A) per parity, not the harness Neumann cosines.\n- Arch term: Gauss digamma-integral u-space representation. Comb overlaps: exact Gauss-Legendre in s on [v-1,1]. Inertia: mp LDL.\n\n1. Zeta control, x=8.5, N=24: PSD and near-null in both sectors (lambda_min 1.64e-26 even / 7.46e-24 odd). These are identical at dps 120/nv 200 and dps 160/nv 260. The Legendre Ritz values are larger than the harness's 7.3e-33, as expected for a weaker subspace.\n\n2. Arch formula cross-checked by the Fourier side, (1/2pi) int |F(r)|^2 (Re psi(1/4+ir/2) - log pi) dr, with F from spherical Bessel functions (t2_archcheck.json).\n- Even sector: agrees to 10 digits (-0.2867923674).\n- Odd sector: 0.48872 on [0,400] plus 0.00477 on [400,1600], plus a slowly converging log(r)/r^2 tail, against 0.49566 in u-space. This is consistent.\n- The minimizing f for P7-removed at x=11.3, N=16 has Q(f) = -0.01414 (u-space) / -0.0163 (Fourier arch, truncated). So it is firmly negative.\n\n3. B31b crossings, independent code (odd sector binds for removed, even for added in every case; the other sector has inertia 0 at the crossing; inertia is 0 just below p_d):\n\n| case | N | crossing | relative excess | harness N=64 |\n|---|---|---|---|---|\n| P0=7 removed-11 | 16 | 11.05237 | 4.76e-3 | |\n| P0=7 removed-11 | 24 | 11.03634 | 3.30e-3 | 11.01440 (1.31e-3) |\n| P0=7 added-10.66029 | 16 | 10.70829 | 4.50e-3 | |\n| P0=7 added-10.66029 | 24 | 10.69418 | 3.18e-3 | 10.67419 |\n| P0=13 removed-17 | 16 | 17.09268 | 5.45e-3 | 17.01190 |\n\nThe excess decays roughly like 1/N (4.76e-3 -> 3.30e-3 -> 1.31e-3 at N=16/24/64). So the continuum x_B is p_d^+. The heuristic scale is x_B - p_d ~ p_d * e^{-12 p_d}, i.e. about 1e-56 relative at p_d=11. The proposer's bracket [p_d, x_mp64] is correct but loose.\n\n4. B31 proof checked by hand.\n- Step 1: the Gaussians-to-Schwartz step closes by the Mellin contour shift (Phragmen-Lindelof gives polynomial growth in the strip from finite order plus the FE), or is covered by KM Thm 1-3.\n- Step 2: LO Thm 1 applies (support = spectrum, both u.d.).\n- Step 3: the semigroup lemma is correct, but its '(nu^d - 1)' phrasing must use two powers nu^d, nu^d' in the same coset. Then nu^d'(nu^D - 1) in (u/v)Z; the denominator b^d' must divide v, so b=1.\n- Step 4: Hamburger's hypotheses are met.\n\n5. Not re-run: the Part A branch and bound, and the degree-2 search. I checked the visibility log against the formula only.",
 "novelty": "Low.\n- The analytic core of B31 is classical: FE <=> self-dual almost-periodic distribution <=> frequency rigidity for Riemann's FE under gap/density conditions. See Bochner-Chandrasekharan 1956 (Ann. of Math. 63, 336-360), Chandrasekharan-Mandelbrojt 1957, and Kahane-Mandelbrojt 1958 (Ann. Sci. ENS 75, 57-80, Thms 1-3, 7, 10; read from the numdam PDF, saved at /Users/peterwmurphy/hodge-engine/hengine/w7/beurling_hamburger_frequency_rigidity_skeptic/km1958.pdf). LO 2015 is the modern general version.\n- The new ingredient is the elementary Euler-closure/pigeonhole/denominator lemma forcing S in Z. It is probably folklore-adjacent: I estimate about 15% that it is genuinely unpublished, against the proposer's 30%.\n- B31b adds nothing beyond B3/B20 + B22.\n- The finite-scale visibility law is immediate from the Gaussian term.\n- Lit-cache action: add KM 1958 and Bochner-Chandrasekharan 1956 to key beurling_hamburger_frequency_rigidity. Note that KM Thm 7 handles finite-uniform-density frequencies, so the Q22 gap statement must be rewritten.",
 "what_is_real": "1. B31 is a correct theorem on paper. The chain is: degree 1, Gamma_R, q=1, poles {0,1}, finite order, positive-mass Euler-closed Beurling semigroup S with u.d. support. Then S = Z_{>0} and zeta_B = zeta. It needs two small repairs: the Mellin contour-shift justification of step 1, and the two-power form of step 3. It is not kernel-checked. The semigroup lemma is short and elementary, a cheap Lean target.\n\n2. B31b is reproduced with independent code and an independent basis, with the arch formula cross-checked by the Fourier side. Moving the first atom at p_d produces a genuine negative direction just above p_d. A removed atom binds the odd sector and an added atom binds the even sector. The Ritz excess tends to 0 with N. Its true content is B3/B20 near-nullness plus B22, and 'the residue is invisible to W(x)' is a definitional fact.\n\n3. The negative lesson stands and is worth recording. On the Weil side, the only global Euler quantity that is invisible to finitely many atoms (the residue) carries no positivity. On the FE side, frequency rigidity comes only from the exact FE at all scales (a finite window sees primes up to about sqrt(X ln(1/delta)/pi)). That is a converse-theorem statement, not a positivity source.\n\n4. The prereg timing is honest.",
 "next_step_if_survives": "It does not survive. The most informative follow-up is to shrink the stated Q22 gap using the literature the proposal missed.\n- Take Kahane-Mandelbrojt 1958 Thm 7: finite uniform upper density implies every frequency is a Z-combination of the finitely many in a fixed interval. Combine it with Euler closure and the Riemann FE.\n- Then try to prove that an Euler-closed, finite-density semigroup S inside a finitely generated Z-module, with self-dual mu, lies in Z. Units such as 1+sqrt2 are the obstruction; their Euler factors 1/(1-eps^{-s}) add poles on Re s=0, so the FE should kill them.\n- A success would reduce the open degree-1 class to Beurling systems with infinite uniform density.\n- In parallel, formalise the semigroup lemma in Lean (a cheap, clean target), and add KM 1958 / Bochner-Chandrasekharan 1956 to the lit cache.\n- Record B31b in the ledger as a corollary of B3/B22, not as a new barrier. Note that its R-independence rows were cache hits."
}
```

### ahk_epstein_real_c_walls (wildcard)
- survives adversarial review: False; prediction matched: False; claimed barrier: B31: AHK/DEFORMATION BARRIER FOR FE-EXACT THETA-LATTICE FAMILIES.

**Covered class.** Continuous one-parameter families of Dirichlet series whose FE and pole order are exactly preserved: here Z_c(s) = (1/2) sum' (m^2 + c n^2)^{-s}, with q = 4c and poles (1,1). The Euler property holds only at isolated c*.

**(i) No type-(ii) invariant.** A frozen multiplicative-support distance (b) hits 0 of 120 non-arithmetic horizons within 1%, with median error 53%. The battery gives useful=False: 39 control+ false alarms and 15 below-horizon false alarms. Any invariant that is a function of (q, distance to c*) is class 7/11, and cannot separate L_G from E_0.0005.

**(ii) The horizon wall is zero emergence (class 2).**
- x_h(c) correlates with the first off-line zero (Spearman -0.60 with Re rho, +0.45 with Im rho) but is not monotone in either.
- beta(c) is vacuous on [1,16]: a real zero exists only for c > 49.7802, i.e. sqrt(c) > 7.05551. This corrects the "7.02" figure.

**(iii) Two kinds of arithmetic point.**
- **(a) A generator collides with the unit (c* = 1).** Z_c acquires zeros with Re s > 1, e.g. 2.425 + 30.48i at c = 1.1. The measured horizons are x_h(1+eps) = 3.85 -> 2.08 (N=256, converged), fitting 2 + 11.4 eps^0.79, while x_h(1) = infinity. This is a genuine discontinuity, the B8 analogue: the a(1)-coefficient jumps instead of the pole order. Every predictor continuous in finitely many labels, coefficients and positions fails there (class 11).
- **(b) Labels coincide only at composite positions (c* = 2, 3, 4, 7).** Resolved horizons grow toward c* from both sides; no discontinuity was observed. But the continuity is NOT a theorem for the full class, because translation is not norm-continuous. Label clusters with O(10) opposite-sign coefficients are decoupled by edge-localized high-frequency directions. So fixed-N horizons are band-limit artefacts near c*: at c = 2.03 they are 25.84 / 19.06 / 19.00 at N = 64 / 128 / 256. Any AHK-style path-propagation principle continuous in c must pay about log(1/eps) against the cluster strength, uniformly in x.

**(iv) Lorentzian/Hessian tests on Euler weights.** The Hessian is identically NSD (lambda_min is concave), with no positive eigenvalue at c = 5 or 7, at x = 15 or 22. Scale-blind and counterfeit-blind (B18).

**Adversarial paths for R22.**
- c -> 1+ breaks the "continuous path" hypothesis.
- The path c: 5 -> 7 passes the positive window [6.25, 7.45], where no x_h <= 40 exists at N=128. So an Euler-endpoint property does not propagate backward along the path.

**Evidence level.** Numeric, one code on top of the harness assembly. Validated to 2e-14 against the harness at integer c, and the Chowla-Selberg zeros are validated against C10. Same-session only; no skeptic or peer check. Nothing is certified.; barrier confirmed: False

**What I did**

I did all six steps, with the prereg first.

**Step 0.** PREREG.md was written before any script. I froze invariant (b) with the functional form x_pred = -28.73 + 32.37 ln(1/d), calibrated only on the ledger values c=5 and c=6. A scored table with honest MISS labels is appended after the runs.

**Step 1: comb validation.**
- comb.py injects arbitrary real log-positions into a harness Window. It matches form.Q to below 2e-14 at c = 5, 6, 1 (zeta_K(-4)) and 2 (zeta_K(-8)) (validate.json).
- Z_c's -Z'/Z coefficients were also cross-checked against Chowla-Selberg numerics (check_c105.json).
- **A pitfall found in my own code:** merging numerically close labels at a 1e-9 tolerance silently double-counts clusters within about 3e-4 of c*. At c = 2.0001 the cluster sum near 36 came out as 28.67 when it should be O(eps).
  - The fix is exact formal labels: polynomials in Z[c] with c-independent formal-log coefficients (cgen_formal).
  - Everything after that point uses v2; the v1 outputs are archived.
- The feature request, including this warning, is in HARNESS_REQUESTS.txt. That file also reports a harness bug: battery() has no `blind` parameter and passes the named ldata to the predictor, although the README says it anonymizes it.

**Step 2: landscape.**
- Grid: c in [1,16] at step 0.05, x in [2,40] at step 0.1, N = 64 and 128 (npz and xh_grid json).
- 122 non-arithmetic counterfeit crossings resolve (|lambda| > 1e-10 on both sides). They are listed in zoo_additions.json, and the file gives 301 rows in total.
- Cross-checks: c=5 at 19.834 and c=6 at 31.790 (N=128) match the ledger; c=14 is unreachable.
- Structure of the negative region:
  - (1,2): x_h falls to about 3 as c -> 1+ and rises toward 2.
  - (2,3): minimum 8.65 at c = 2.3.
  - (3,4): minimum about 22 at c = 3.7.
  - (4,6.25): minimum 19.81 at c = 5.05.
  - [6.25,7.45]: no crossing at or below 40.
  - [7.5,8.5]: 37.4 to 39.8.
  - Beyond 8.55: none at or below 40.

**Step 3: approach to c*.**
- At c* in {2,3,4,7}, resolved horizons grow toward c* from both sides.
- Discovering the band-limit artefact: at c = 2.03 the N=64 horizon of 25.84 drops to 19.06 at N=128 and 19.00 at N=256.
  - The negative eigenvector is edge-localized: 47% of its mass lies in |u| > 0.95A, and it peaks at mode about 73.
  - It exploits a label cluster near 18.3 to 18.6, with coefficients -11.6 / -5.8 / +11.7, that sits just inside the window edge.
- c = 2.01 goes from unresolved at N=64 to 25.04 at N=256. N=512 spot checks at x = 19.25, 20 and 22 stay positive.
- Log law against power law is inconclusive (fits.json).
- At c* = 1 there is a genuine discontinuity: x_h(1+eps) runs 3.85, 3.00, 2.52, 2.30, 2.17, 2.08 down to eps = 0.002, converged in N.
  - Z_c near c=1 has zeros deep in Re s > 1: 2.425 + 30.48i at c=1.1, and 5 zeros in [1.02,3] x [1,120] at c=1.05.
  - The cause is that the generator c collides with the unit label. This is the family analogue of B8, with the a(1) coefficient taking the place of the pole order.
- My P1 argument (joint continuity of the full-class infimum) is wrong: translation is not norm-continuous. Continuity holds only in each band-limited class.

**Step 4: readout.**
- There is no real zero on [1,16]. Z_c(1/2) < 0 until c = 49.7802 (sqrt = 7.05551); the "~7.02" figure is a mis-recollection. Bateman-Grosswald is not in the lit cache, so this is UNVERIFIED as a citation but verified numerically.
- First off-line zeros were found for 18 values of c. x_h is not monotone in Re rho or Im rho: class 2 verdict (readout_analysis.json).

**Step 5: Lorentzian test.**
- No positive eigenvalue anywhere. The test is identically NSD because lambda_min is concave, so it is scale- and counterfeit-blind (B18).

**Step 6: battery.**
- useful=False: 39 false alarms on control+, 15 below-horizon false alarms, 0 counterfeit misses, 11 barrier misses.
- Off battery the predictor fails on E_w (all w share q=20) and on R.
- R21: it cannot separate L_G from E_0.0005 (class 11/7).

**Artifacts**

Directory: /Users/peterwmurphy/hodge-engine/hengine/w7/ahk_epstein_real_c_walls/
- Prereg and requests: PREREG.md (with the appended scoring), HARNESS_REQUESTS.txt.
- Code: comb.py, zeros.py, hifreq.py, mpx.py.
- Results JSON: validate.json, p3_score.json, fits.json, readout_main.json, readout_analysis.json, bateman_grosswald_check.json, lorentz.json, battery.json, zoo_additions.json, spot512.json, nladder_64_128_256.json.
- Approach runs: approach_N64.json, approach_N128_grid.json, approach_N256_grid.json, approach_c1.json.
- Landscape: landscape_N64.npz, landscape_N128.npz.

**Caveats**
- All horizons are fixed-N Ritz crossings, i.e. upper bounds on the full-class horizon.
- No Legendre basis exists in the harness.
- The mp bracket is limited to about 1e-13 by the float64 coefficients and was stopped early.
- The 24-mode packet scan has no JSON artifact.
- Same-session numerics only.

All my processes were killed or finished. No git repo and no harness file was modified; harness/cache entries were written by battery() as designed.

**Skeptic:**

```json
{
 "angle": "ahk_epstein_real_c_walls. This is a barrier hunt and landscape study of the real-c Epstein family Z_c = (1/2) sum' (m^2 + c n^2)^{-s}, c in [1,16]. It proposes no positivity mechanism. The claimed barrier is B31, the \"AHK/deformation barrier for FE-exact theta-lattice families\".\n\nSkeptic verdict: the proposal does not survive, which is the default. It has no mechanism and does not use the Euler product at all. B31 as stated is NOT confirmed. It bundles:\n- one trivial negative result: a single frozen distance-to-c* lookup fails;\n- a vacuous test: the Hessian of lambda_min is always NSD because lambda_min is concave;\n- a correlation study;\n- a heuristic (\"must pay log(1/eps)\");\n- one real numerical phenomenon: the c -> 1+ horizon discontinuity.\n\nI reproduced that last phenomenon with independent code and sharpened it into a lemma. But it is a second instance of the B8 mechanism, not a new barrier.\n\nMy independent runs also found something the proposer missed. Several of its \"resolved\" near-c* approach numerics are band-limit artefacts: Z_{2.003} is O(1) Weil-negative at x = 37.5.",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "No positivity mechanism and no use of the Euler product at all (the proposer's own euler_product_usage says 'None'). Under the wave rules this cannot survive.",
  "B31 is not a precisely stated negative result.\n- (i) 'No type-(ii) invariant' is shown for ONE ad hoc invariant: d(c) = distance to {1,2,3,4,7}, fitted on 2 points. That is not a theorem about invariants.\n- The extension 'any function of (q, distance to c*) is class 7/11' is trivial, because d is itself a function of q = 4c in this family. The L_G vs E_0.0005 argument applies to any q-only predictor and needs no new work.",
  "(iv) The Lorentzian/Hessian test is vacuous by construction. V(t) = lambda_min is a minimum of affine functions, hence concave, so 'no positive Hessian eigenvalue' holds identically for every datum. It is not evidence of a barrier; it only shows the test was ill-posed.",
  "(iii)(b) 'Any AHK-style path-propagation principle must pay about log(1/eps) against cluster strength, uniformly in x' is a heuristic. It is not proved and not quantified.",
  "Independent Legendre runs refute part of the proposer's P1 'HIT (numerics)'. At c = 2.003 the proposer reports positive to x = 37.5 (cosine N = 512, lambda = 8.6e-14). My Legendre basis gives:\n- N = 640: positive (1.1e-12);\n- N = 1024: lambda_min = -1.740 (even) and -1.754 (odd), with 54-62% of the eigenvector mass in |u| > 0.95A.\n- Control: exact c = 2 (zeta_Q(sqrt-2), both integer and formal-label paths) at the same x = 37.5, N = 1024 gives -9.6e-13 / +1.0e-10, i.e. the float floor. So the -1.74 is genuine.\n- c = 2.01: positive through x = 23 at N = 1024; negative at 25.0 at N = 640 (-0.10); positive at 25.2 at N = 320. So x_h(2.01) is in about (23, 25) and still falling with N.\n- Consequence: the 'approach' tables for c* = 2, 3, 4, 7 (c = 3.01/3.003, the c*=7 'positive to 80', and c=4.003 at 38.35) are fixed-N upper bounds that may be wildly high. 'x_h -> infinity as c -> c*' remains unproven. The resolved values I can trust (13.06, 19.00, ~24, <= 37.5 for eps = 0.1, 0.03, 0.01, 0.003 above c* = 2) still increase, but the rate is unknown.",
  "(ii) The Bateman-Grosswald 'correction' is not a correction. The literature threshold is k = sqrt(Delta)/(2a) > 7.0556. Mukhopadhyay-Rajkumar-Srinivas, arXiv:1102.0367, p. 3 cites Bateman-Grosswald [2], and I read that page. For x^2 + c y^2 this is sqrt(c) > 7.0556, which agrees with the proposer's numerics (7.05551). Only the proposer's '~7.02' recollection was wrong. The proposer also did not cite the source.",
  "Minor: check_c105.json shows the Chowla-Selberg -Z'/Z and the comb series DISAGREE at c = 1.05, s = 3+20i (0.064-0.133i vs 0.856-0.092i). This is expected rather than a bug: Z_{1.05} has zeros with Re s near or beyond 3, so the Dirichlet series for -Z'/Z does not converge absolutely at sigma = 3. But the proposer's argument-principle count of '5 zeros in [1.02,3] x [1,120]' can miss zeros with Re s > 3, and the table was not flagged."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Not applicable in the usual sense, because the whole proposal is a study of counterfeits. My control checks:\n- **Code validation.** My independent code reproduces:\n  - E = Z_5: crossing in (19.83, 19.85) at Legendre N = 80, decreasing with N toward the ledger's 19.8225.\n  - Z_6: crossing near 31.80 at N = 80, falling toward the ledger's 31.770.\n  - zeta_Q(i) and zeta_Q(sqrt-2) are positive at x = 5, 10, 20. Their near-null magnitudes (5e-14 at x = 20 for Q(i)) pin the arch constant log q - d log pi to about 1e-13; any convention error would show up as an O(delta) eigenvalue shift.\n- **High-N control.** Exact c = 2 at x = 37.5, N = 1024 sits at the float floor (-9.6e-13), so O(1) negatives at nearby non-arithmetic c are genuine.\n- **Harness bug confirmed (proposer's BUG-1).** battery.battery() has no `blind` parameter, although README line 125 says blind=True anonymizes ldata. Every predictor scored so far could read name/meta (the answer key). The proposer's own score is unaffected, since it reads q only. Other waves' battery scores should be re-audited.\n- **Positive window.** c = 6.8 and c = 7.03 stay positive through x = 40 at N = 512 with O(1e-4) margins (not near-null). The proposer's [6.25, 7.45] positive window is robust there.",
 "numerics_reproduced": "All runs use independent code in /Users/peterwmurphy/hodge-engine/hengine/w7/ahk_epstein_real_c_walls_skeptic/.\n- **Method (leg.py).** No harness import. It uses:\n  - an orthonormal Legendre basis on [-A, A] with the exact scaling G_A(y) = G_1(y/A);\n  - Gauss-exact convolution Grams;\n  - the arch term via Gauss's psi integral in u-space;\n  - the rank-2 pole term;\n  - formal labels in Z[c] with a heap-ordered Dirichlet recursion, validated two ways: it merges to the integer c(n) at c = 2, 3, 5, 6 (error < 4e-15; c_E(6) = 3.5835, c_E(36) = -7.1670), and its -Z'/Z matches a direct lattice sum at c = 1.3, s = 6 to 1e-12.\n\nREPRODUCED:\n1. **c -> 1+ horizons.**\n   - x_h(1.1) = 3.8488 (N = 64 and 96 agree; proposer 3.849).\n   - x_h(1.02) = 2.5214 (N = 48/96/160; proposer 2.52).\n   - x_h(1.005) = 2.1689 (N = 128/224; proposer 2.17).\n   - x_h(1.002) = 2.0798 (N = 192 and 288 agree; proposer 2.08).\n   - Files: c1_eps*.json.\n2. **c = 2.03 band-limit artefact.** Legendre N = 32 and 64 are positive through x = 25.9. N = 128 is negative from 19.05; N = 384 from 19.00 (proposer: 19.06 / 19.00). The negativity is O(1): -0.53 at x = 20 and -2.49 at x = 25.9. The cluster near 18 has coefficients +5.78 / -11.62 / -5.84 / +11.70 at 18.03 / 18.271 / 18.514 / 18.637; they sum to about 0 at c = 2.\n3. **Landscape points** (grid-scan first negative, N = 256):\n   - c = 2.3: 8.65 (proposer 8.654);\n   - c = 3.7: 22.1 (22.03);\n   - c = 1.99: 15.6 (15.51).\n4. **Zero of Z_{1.1}** at 2.4251305 + 30.4760351i, via my own Chowla-Selberg; |Z| = 6e-25. Chowla-Selberg matches the direct lattice sum at s = 3 + 30i to 3e-12.\n5. **Bateman-Grosswald threshold.** Z_c(1/2) changes sign at c = 49.780193, sqrt = 7.0555080, matching the proposer.\n6. **P3 formula.** x_pred(5) = 19.823, x_pred(6) = 31.796, x_pred(14) = -16.9. Misses reproduced at c = 2.3 (34.97 vs 8.65) and c = 3.7 (53.8 vs 22.1).\n\nNEW (skeptic):\n- **Analytic lemma for c -> 1** (lemma_c1.py/json). For x <= 2 the only labels below x are the chain c^k, with c(c^k) = (-1)^{k+1} log c. Then\n  Q^{Z_c}_x - Q^{zeta_Q(i)}_x = (1/2pi) \u222b |F|^2 log c [2 Re(1/(1+z)) - 1] dt >= log c (1-r)/(1+r) ||f||^2,\n  where z = c^{-1/2+it} and r = c^{-1/2}.\n  - Numerically, the minimum eigenvalue of the difference exceeds this bound in all 9 cases (eps = 0.1, 0.02, 0.002; x = 1.5, 1.99, 2).\n  - zeta_Q(i) has lambda_min = 0.473 at x = 2, not near-null and certifiable.\n  - Hence x_h(1+eps) > 2 for every eps > 0. The limit 2 is the position of the label 1+c at c = 1.\n  - Rate: (x_h - 2)/(eps ln(1/eps)) = 8.03, 6.66, 6.38, 6.42, which is consistent with eps log(1/eps). The power-law prefactor 11.4 drifts down to 10.8. So the proposer's eps^0.79 fit is not singled out.\n- **Near-c* results** that contradict the resolved approach tables (see fatal_flaws): c = 2.003 at x = 37.5 gives -1.74 at N = 1024; c = 2.01 has x_h in about (23, 25).\n\nNOT reproduced: the battery scores, the 18-point zero/horizon Spearman correlations, the Lorentz json, and the full 0.05 grid (122 crossings).",
 "novelty": "These are not in the lit cache or the ledger; web verification was minimal.\n- **The c -> 1+ collapse.** The family-level horizon discontinuity x_h(1+) = 2 vs x_h(1) = infinity (under GRH for Q(i)) is plausibly new as a Weil-window statement. The mechanism is structurally the B8 phenomenon (a coefficientwise-convergent family whose horizon jumps), so it is a second witness, not a new barrier class. The \"a(1) jumps 1 -> 2\" framing is imprecise: log-derivatives are scale-invariant. The real mechanism is a generator colliding with the unit, which produces an alternating geometric chain with a 1/(1 - c^{-1/2}) ~ 2/eps resonance at t = pi/eps. It is then amplified by the chain (1+c)c^k, which has O(1) coefficients.\n- **Cluster decoupling.** Near-coincident formal labels with c-independent O(10) opposite-sign coefficients can be decoupled by edge-localized, high-frequency tests. This is a genuinely useful methodological finding for the zoo; B21 already warns about the Galerkin trap, but this cause is new.\n- **Literature status.**\n  - Zeros in Re s > 1: Davenport-Heilbronn (cache, verified) covers integral forms with h > 1. For real non-arithmetic c, the Re s > 1 zeros near c = 1 are unverified as prior art.\n  - Bateman-Grosswald: verified via the arXiv:1102.0367 citation. The threshold is 7.0556, identical to the proposer's numerics, so there is no correction. The original Acta Arith. paper was not fetched and should be backfilled into lit/index.json.",
 "what_is_real": "1. **Real-c Epstein family members are Weil-negative at small x.** Z_c for non-arithmetic real c is a rich source of FE-exact, pole-exact counterfeits that are negative at small x (e.g. c = 2.3 from 8.65, c = 1.5 from about 4.8). Where the labels are not clustered these horizons are converged in N; independent Legendre code agrees with the proposer's cosine-basis values to about 0.1.\n\n2. **The c -> 1+ collapse is real and now partly a theorem.**\n   - x_h(1+eps) -> 2 while x_h(1) = infinity (under GRH for Q(i)).\n   - My comparison lemma gives x_h(1+eps) > 2 for every eps (modulo W(2) for zeta_Q(i), which holds with margin 0.47).\n   - Converged numerics at eps = 0.002 give 2.0798.\n   - The limit is the position of the label 1+c at c = 1. The approach rate is consistent with eps\u00b7log(1/eps).\n   - It is a clean second witness of the B8 discontinuity: predictors continuous in finitely many coefficients fail.\n\n3. **Band-limit trap.**\n   - Near arithmetic points, near-coincident formal labels (spread linear in eps, e.g. 16+c vs (1+c)(4+c) near 18 when c* = 2) carry c-independent O(10) coefficients that nearly cancel at c*. Edge-localized high-frequency tests decouple them and give O(1) negative eigenvalues invisible below a resolution threshold that grows as eps -> 0.\n   - Fixed-N horizons near c* are therefore unreliable upper bounds. At c = 2.003, x = 37.5: cosine N = 512 and Legendre N = 640 are positive, while Legendre N = 1024 gives -1.74.\n   - Consequently the zoo_additions entries near c*, and the proposer's c* = 3, 4, 7 approach series, must be N-laddered much higher before use.\n\n4. **Confirmed harness bug.** battery() lacks the documented blind mode. It should be reported and prior battery scores re-audited.\n\n5. **Prereg was honored.** PREREG.md birth time 16:49:56 precedes every script (the first, comb.py, was created at 16:50:51). Scoring was appended with honest MISS labels: P1-argument, P1 'no discontinuity' and P2 were all scored MISS. However, the decisive test P3 was a pre-registered failure of a 2-point-calibrated lookup, so it carries almost no information. Also, the predictions' immutability after 17:34 cannot be checked (no hash).\n\n**Not real:**\n- B31 as a new barrier;\n- the Lorentzian test (vacuous);\n- the 'no type-(ii) invariant' generalization;\n- 'x_h -> infinity at c* in {2,3,4,7}' as a numerical result, beyond monotone growth of the few resolved values.",
 "next_step_if_survives": "It does not survive; the most informative next steps for the barrier map are:\n\n1. **Measure x_h(c* \u00b1 eps) properly.** Use an edge-graded basis: Legendre up to N = 2048, or explicit edge wave-packets tuned to the cluster splittings (log-split about 8 eps/18 near 18 for c* = 2). Measure at eps = 0.1, 0.03, 0.01, 0.003, 0.001 from both sides of c* = 2 and 3.\n   - This decides between x_h -> infinity at a polylog rate (inverse cluster strength vs log(1/eps)) and a bounded limsup, i.e. a second genuine discontinuity at composite-collision points. A bounded limsup would be a much stronger barrier than B8.\n   - A cheap reduced model gives the threshold directly: Q_{c*} + a 2-4 label cluster perturbation restricted to the edge.\n2. **Certify the c -> 1 lemma.** Interval-certify W(x <= 2) for zeta_Q(i) (margin 0.47), then write the lemma up as a proved B8-type discontinuity (Lean-feasible: it is a one-line Poisson-kernel positivity 2 Re(1/(1+z)) - 1 >= (1-r)/(1+r)).\n3. **Clean up the zoo and harness.** Re-ladder every zoo_additions entry within 0.1 of an arithmetic point before admitting it. Fix battery blind mode (BUG-1) and re-score earlier battery claims.\n\nArtifacts: /Users/peterwmurphy/hodge-engine/hengine/w7/ahk_epstein_real_c_walls_skeptic/ (leg.py, c1.py, c2.py, scan.py, lemma_c1.py, zc.py, ctl_hiN.py, and the *.json outputs)."
}
```

### b8_pole_zero_cancellation (barrier_hunt)
- survives adversarial review: False; prediction matched: True; claimed barrier: B31 RESIDUE COUPLING NEAR POLE-FREE LIMITS IS EXCEPTIONAL-ZERO READOUT.

HYPOTHESIS CLASS. Families Lambda_w with:
- fixed Gamma data, conductor and root number, and an FE;
- pole order m >= 1 for w > 0 and m0 < m at w = 0;
- a_w(n) -> a_0(n) pointwise;
- |a_w(n)| <= C n^A uniformly.
The class includes all real or complex FE-linear mixtures, double poles, and Lambda_pf(1) = 0 limits.

STATEMENT.
- Exactly m - m0 zeros converge to s = 1, with FE partners converging to 0.
- At every fixed x, Q_{w,x} -> Q_{0,x} + (m-m0) H_{1/2}. On the zero side the jump is sum of H_{rho-1/2}, a rank-2-per-sector collision defect of relative size ~ (1-beta) log x.
- For linear mixtures: 1 - rho = w r/Lambda_pf(1) + O(w^2), or rate w^{1/(k+1)} / w^{1/m} in the degenerate cases.
- Every predictor continuous in (finitely many a(n), pole order, arch), including product-topology Euler constraints, is wrong at the pole-free endpoint. The discontinuity is witnessed only by the exceptional zero(s).
- So 'quantified residue coupling' (R5/R21) is class 2. In c-space it is the pole-mass law sum_{n<=X} Delta c = X - X^beta/beta (PNT error / zero-free region at s = 1). For Euler data an effective residue floor is the Landau-Siegel problem.

ADVERSARIES.
- (a)-(c): collide, as predicted.
- (d) The c-linear product path has no discontinuity at all, being affine in (c, fractional pole order). The B8 discontinuity is an a-space-path artefact.
- (e) Unbounded-coefficient escape: OPEN.

WORDING FIXES.
- R21 should read 'continuous in finitely many a(n) plus pole order along a-linear paths'.
- R5's residue coupling must be flagged as readout unless it acts away from s = 1.; barrier confirmed: False

W7 b8_pole_zero_cancellation: final report. conjecture1_proved = False.

Directory: /Users/peterwmurphy/hodge-engine/hengine/w7/b8_pole_zero_cancellation/
- PREREG.md: written first, with the scored table appended.
- REPORT_HARNESS.md.
- common.py.
- s1_slopes_adversaries.py (+ s1.log, s1_out.json).
- s2_reduced_model.py (+ s2.log, s2_out.json).
- s3_product_path.py (+ s3.log, s3_out.json).
- s4_collision_scale.py (+ s4.log, s4_out.json).
- s5_pole_mass.py (+ s5.log, s5_out.json).

1. WHAT B8 REALLY IS
The harness Pole term depends on pole ORDER only; Comb is c-linear over n < x. So the w -> 0 'discontinuity' is literally the integer pole order jumping from 1 to 0 while c(n) (n < x) converges.
- On the zero side, the pole block equals H_{1/2}. It was verified against an independent closed form of H_t to 1e-15.
- A real exceptional pair contributes H_{beta-1/2}.
- L1 (Vitali, under a uniform coefficient bound) plus L2 (the argument principle) prove that exactly m - m0 zeros must converge to 1 whenever the pole order drops in the limit. No reality, self-duality or sign hypothesis is needed.
- So readout equivalence is FORCED in a class much larger than the assignment's 'real FE + r > 0 + Lambda_pf(1) > 0'.

2. SLOPES (T4)
(1-beta)/w -> L(1,chi_D)/L_G(1), confirmed to 2.5e-6 to 5.6e-6 relative at w = 1e-6, with a linear O(w) correction:
- D = -20: 4.156174
- D = -24: 3.403778
- D = -56: 2.269185
- D = -23: 5.334290
Notes:
- For D = -23 the task premise is wrong. L(s,psi) = L(s,psibar) is self-dual (the weight-1 form eta(z)eta(23z)), L(1,psi) = 0.368409 > 0, and the zero stays real.
- My prereg -56 number was an arithmetic slip, labelled MISS.
- w_c values, where the pair collides at 1/2: 0.059340 (-20), 0.072597 (-24), 0.107044 (-56), 0.046290 (-23).

3. ADVERSARIES (the decisive test)
- (a) Lambda_pf(1) = 0: two zeros at 1 +- 2.0387 i sqrt(w). Collision.
- (b) Double pole Lambda_K^2/Lambda_G (Euler + FE): a complex pair at distance 4.156 sqrt(w). Collision; the zero sits at Re = 1 + 1.4e-5, i.e. OUTSIDE the strip.
- (c) Complex weight: one complex zero at 1 - w e^{i theta} r/L_G(1). For theta > pi/2 it lies at Re > 1. Collision.
- (d) Product path zeta_K^w L_G^{1-w}: c-linear with fractional pole order w. Q_w = w Q_K + (1-w) Q_{L_G} to 3.6e-15. There is NO discontinuity and it is positive at every tested point, while the same-w E_w is negative (odd sector; e.g. x = 20: -1.05 vs +1.4e-3).
- Verdict on (d): P5 HIT. It is not an adversary; it shows the discontinuity is an artefact of a-linear paths.
- (e) Escape (fixed residue, unbounded coefficients, no local-uniform convergence): the only hole. It is excluded when there is a uniform polynomial coefficient bound.

4. T2 COLLISION DEFECT
- D = H_{1/2} - H_{beta-1/2} has rank 2 per sector.
- ||D||/||Pole|| ~ c (1-beta) log(x)/2, with c -> 1.7 (odd sector larger at small x).
- The pole-zero cancellation therefore holds for x << exp(c'/(1-beta)).
- The task's corollary that the HORIZON scales like log(1/(1-beta)) is false. x_h -> 5.07 as w -> 0, and the growth follows log(1/(beta - 1/2)) (w6 law).
- Reduced model Q_{L_G,pf} + H_{beta-1/2} against the harness:
  - w = 0.0005: 5.0771 vs 5.0783
  - w = 0.02: 5.3573 vs 5.4170
  - w = 0.05: 6.4146 vs 7.2381 (MISS). The other zeros' O(w) motion matters there.

5. c-SPACE (R20)
sum_{n<=X} (c_{E_w} - c_{L_G}) = X - X^beta/beta, within 1% up to X = 2e5.
- For comparison, zeta_K's full pole mass is about X.
- The pole is 'unpaid' below X ~ e^{1/(1-beta)}. The Weil window sees a pole with no prime mass behind it, which is why E_{0+} is negative from 5.07.
- Any mechanism demanding 'pole paid at scale x' is the PNT error term / a zero-free region near 1: class 2.
- For genuine Euler data it becomes the Landau-Siegel problem (Siegel 1935, lit key siegel_zeros_landau_siegel#0).

6. HYGIENE
- The x_h table was regenerated in the odd sector at N = 64/128/256 (Neumann, float). Even-sector small-w horizons are near-null and unreliable (w6); the E_w even-sector value at x = 8 is +0.115 at N = 64.
- The mp near-null bracket was not needed: the odd crossings have O(1) slope and the noise is about 1e-11.
- T1 Ritz negativity for w = 5e-4 at x = 5.09-5.2 is reported in counterfeit_control.
- No Lean was written; no kernel check is claimed.
- Provenance: all of this is same-session and unverified under #607.

7. LEDGER EDITS PROPOSED
- Add B31 (claimed_barrier).
- Re-word R5: a residue coupling acting at s = 1 is class-2 readout.
- Re-word R21: the discontinuity exists along a-linear paths; c-linear paths are affine and continuous.
- Add (e) as open Q.
- Correct the '|L(1,chi)|^2 for D = -23' premise.

**Skeptic:**

```json
{
 "angle": "W7 skeptic for b8_pole_zero_cancellation (barrier_hunt). The proposal tries to turn the B8/Q24 discontinuity at w -> 0 into a negative theorem, B31: near a pole-free limit, residue coupling is exceptional-zero readout. I checked it in four ways. (1) I read the prereg and scripts and checked file birth times. (2) I rebuilt the slopes, w_c, and the zeros of adversaries (b) and (c) with my own L-functions (Hurwitz-zeta sums over my own character tables, no harness and no mp.dirichlet), plus argument-principle counts. (3) I wrote my own Weil form, with no harness: Legendre basis, Gamma_C arch in t-space via the Gauss psi-integral, my own c(n) recursion. I validated its conventions against the actual zeta zeros with a Gaussian test function (the r-space explicit formula matches to 1e-25), and the Gamma_C psi-transform matches r-space to 1e-21. With it I recomputed the odd-sector horizons, the reduced model and the product-path signs. (4) I recomputed the c-space pole-mass sums on my own. Artifacts are in /Users/peterwmurphy/hodge-engine/hengine/w7/b8_pole_zero_cancellation_skeptic/: sk0_validate.py, sk0b.py, sk1_zeros.py, sk1b_check.py, sk2_weil.py, sk3_p4_rescore.py, sk4_polemass.py, each with its .log and _out.json.",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "The predictor-class clause of B31 is false or vacuous as written. It says every predictor continuous in (finitely many a(n), pole ORDER, arch) is wrong at the pole-free endpoint. But pole order is an integer coordinate. Along E_w the coordinates (a_w, 1) converge to (a_LG, 1), which is L_G + pole. That datum is itself W-negative from 5.07, the same verdict as E_w, so continuity forces nothing wrong. Pole-free L_G sits at a different discrete point, (a_LG, 0). A direct counterexample to the clause is the windowed Weil form Q_x itself: it is continuous in exactly these coordinates (the harness Pole term depends only on the order, and Comb uses c(n) for n < x) and it is correct at E_w, at L_G + pole and at L_G. The discontinuity only exists for predictors that depend continuously on the RESIDUE, a real number that tends to 0. B8's 'Consequence' line had the same defect and B31 inherits it.",
  "Most of the headline is standard complex analysis relabelled as a barrier. L2 is Hurwitz's theorem: when the pole order drops in a locally uniform limit, that many zeros converge to 1. T3 is first-order perturbation (implicit function theorem). The dictionary 'small L(1,chi) <=> real zero near 1', and 'an effective residue floor is the Landau-Siegel problem', is classical (Landau, Siegel 1935 at lit key siegel_zeros_landau_siegel#0, Deuring-Heilbronn). The conclusion that R5/R21 residue coupling 'is class 2' is only shown along families that degenerate to a pole-free limit. For data whose residue is bounded below, which includes all genuine L-functions (Siegel), B31 says nothing. So it cannot rule out residue-type mechanisms in general.",
  "The hypothesis class does not contain two of the adversaries. (b) Lambda_K^2/Lambda_G has poles at every zero of L_G, so it is not entire away from s = 0, 1. (c) The complex-weight mixture violates the stated FE Lambda(s) = eps conj Lambda(1 - conj s); it only satisfies Lambda(s) = Lambda(1-s). The local Hurwitz argument still applies, but the 'adversaries within the class' framing is loose.",
  "Numerical bug in s2: the beta(w) values from mp.findroot (illinois, verify=False) are NOT roots at w = 0.02 and 0.05. F(beta) = +0.00424 and -0.00446. The true values, from bisection with an independent L-evaluation and a sign scan, are beta(0.02) = 0.9080431 (proposer 0.9065851), beta(0.05) = 0.6995132 (proposer 0.7093635) and beta(0.0005) = 0.99791734 (proposer 0.99791712). The same wrong betas feed s4 and s5.",
  "Adversary (e) is probably not merely 'open at 15%'. The only symmetries are the Fricke FE at conductor 20 and z -> z+1. These generate a Hecke group G(lambda) with lambda = sqrt(20) > 2, which has infinite covolume, so the FE space is expected to be infinite-dimensional (Hecke 1936). If so, one expects data with a FIXED residue whose a(n) agree with a_LG(n) up to X_w -> infinity. Then Q_x -> Q_{L_G+pole}, negative from 5.07, with no zero forced near 1. In that case what drives window negativity is 'pole unpaid by prime mass at scale x', not an exceptional zero. B31's identification of the two would hold only under the uniform coefficient bound, which B31 does list as a hypothesis. I did not construct this family."
 ],
 "prereg_honored": true,
 "counterfeit_check": "B31 is a statement about arbitrary families, so it applies word for word to counterfeits and to genuine data. It separates them only through the exceptional zero, which is exactly zero readout, as the proposal itself says.\n\nThe product path (d) is W-positive, but that is a tautology. Q is affine in (c, pole order), so its values along the path are convex combinations of two PSD endpoint forms (Q_K and Q_{L_G} pole-free). That is not evidence about counterfeits.\n\nMy independent Weil code reproduces the sign pattern at M=16:\n- E_w (w=5e-4) is negative in the odd sector at x = 5.2 / 10 / 20: -0.0261 / -0.3695 / -1.0474.\n- The product path is positive at all 18 (x, sector, w) points; the minimum is 2.7e-4 (x=20, even, w=5e-4).\n- zeta_K(-20) is positive: 4.9e-3 (even) at x=20.\n- L_G pole-free is positive: 1.4e-7 (even) at x=20.\n- L_G + pole is -1.058 (odd) at x=20; the harness gives -1.061.\n\nCircularity: none beyond what the proposal already admits. The 'mechanism' is a certificate that residue coupling equals readout, restricted to degenerating families.",
 "numerics_reproduced": "Independent code, no harness.\n\nSLOPES (sk1). I used my own Hurwitz-sum L-functions and the digamma closed form for L(1,chi). For each D: predicted slope, then the rel. dev. of the measured (1-beta)/w from it at w = 1e-6:\n- D = -20: 4.15617384247, dev 4.381e-6.\n- D = -24: 3.40377797132, dev 3.562e-6.\n- D = -56: 2.26918531421, dev 2.53e-6.\nAll agree with s1 to every printed digit.\n\nw_c = 0.059339990244 (-20), 0.0725972122 (-24), 0.1070438436 (-56). All reproduced.\n\nARGUMENT PRINCIPLE for E_w at w = 1e-4 (zeros minus poles):\n- disc |s-1| < 0.01: 0 (one zero, one pole);\n- disc |s-1| < 2e-4: -1 (the pole alone).\nSo exactly one zero converges to 1, as L2 claims.\n\nADVERSARIES (b) and (c). In s1.log the raw findroot outputs are zeros near s = 0 (dist_over_sqrtw = 1000.02 at w = 1e-6). The reported near-1 values come from FE reflection, which the report does not say. I found the (b) zero near 1 DIRECTLY at w = 1e-4: 1.00139378 + 0.04144564i, |rho-1|/sqrt(w) = 4.147, Re > 1. That confirms the claim.\n\nHORIZONS, odd sector, Legendre Ritz values, M = 8 / 12 / 16 / 20 / 24, decreasing towards the harness values (dashes: not run at that M):\n- L_G + pole: 5.0804 / 5.0768 / 5.0743 / - / - (harness 5.0715).\n- E_0.0005: 5.0871 / 5.0836 / 5.0811 / - / - (harness 5.0783).\n- E_0.02: 5.4235 / 5.4216 / 5.4199 / 5.4192 / 5.4187 (harness 5.4170).\n- E_0.05: 7.2591 / 7.2469 / 7.2426 / 7.2421 / 7.2414 (harness 7.2381).\nThe two codes agree.\n\nP4 RESCORE with the TRUE beta (sk3, M=24). Reduced model Q_{L_G,pf} + H_{beta-1/2}:\n- w = 0.02: 5.3538 vs 5.4187, ratio 0.988 (HIT).\n- w = 0.05: 6.5295 vs 7.2414, 9.83% low. That is inside the preregistered 10%, so it is a borderline HIT, not the MISS the proposer reported.\nWith the proposer's wrong beta, my code gives 6.418 at M=16, which reproduces their 6.4146. So the MISS was caused by the root-finding bug, not by the model.\n\nPOLE-MASS LAW (sk4). My own recursion gives identical defect sums (128302.335 at X = 2e5, w = 0.02). Against the TRUE beta, sum Delta c / (X - X^beta/beta) = 0.977 / 1.018 / 0.9965 / 1.0029 / 0.99994 at X = 1e2 / 1e3 / 1e4 / 1e5 / 2e5. That is better than the reported 0.2-1.4%, which was computed with the wrong beta.\n\nThe s4 coefficient 'c -> 1.7' holds only for small 1-beta. At 1-beta ~ 0.093 the ratio goes to 1.02-1.04.",
 "novelty": "Low.\n- The Hurwitz / argument-principle count, the slope r/Lambda_pf(1), and 'residue floor = Landau-Siegel' are all classical.\n- The in-project value is the Weil-form bookkeeping:\n  - the pole block equals H_{1/2};\n  - an exceptional pair contributes H_{beta-1/2};\n  - the collision defect has rank 2 per sector;\n  - the reduced model reproduces x_h to within 1.2% (w = 0.02) and 10% (w = 0.05);\n  - the c-space law sum Delta c = X - X^beta/beta holds.\n- The genuinely useful ledger correction is to B8 itself. The 'discontinuity' is an artefact of treating the pole ORDER as the coordinate. It disappears along c-linear paths (affine in fractional pole order), and it exists only for predictors that are continuous in the residue.\n- Lit-cache entries siegel_zeros_landau_siegel#0-3 and davenport_heilbronn_epstein_offline#2-3 are cited correctly. Deuring-Heilbronn and Bateman-Grosswald are correctly flagged as unverified.",
 "what_is_real": "Reproduced independently:\n- Exactly m - m0 zeros converge to s = 1 when the pole order drops in a locally uniform limit. E_w: argument-principle count 0 / -1 on the two discs.\n- (1-beta)/w -> L(1,chi_D)/L_G(1) for D = -20, -24, -56, to within 2.5-4.4e-6 relative at w = 1e-6.\n- w_c is where the pair (beta, 1-beta) collides at 1/2: 0.05934.\n- The (b) double-pole pair sits just to the right of Re = 1: 1.00139 + 0.0414i at w = 1e-4.\n- Q_{E_w} -> Q_{L_G+pole} at fixed x. On the zero side this is the exceptional pair's H_{beta-1/2} replacing H_{1/2}. The reduced model reproduces the odd horizons within 1.2% at w = 0.02 and 9.8% at w = 0.05, once the correct beta is used.\n- The E_w odd horizons 5.0715 / 5.0783 / 5.417 / 7.238 are confirmed by a second, harness-free code.\n- The c-space pole-mass law holds to <= 2% on 1e2..2e5, and to 6e-5 at 2e5.\n- The product path is affine and positive.\n\nThe correct, defensible scoped statement is: for families with a uniform coefficient bound whose RESIDUE tends to 0 (pole order dropping in the limit), any quantity continuous in (a(n <= X), residue) has its w -> 0+ jump carried entirely by zeros within O(w^{1/m}) of s = 1. So residue-based discrimination near pole-free limits is exceptional-zero readout. This is true but classical in content.\n\nAs written, B31 fails in three ways. Its predictor clause uses pole ORDER, which makes it false (the window Weil form Q_x is a counterexample). Its conclusion about R5/R21 over-reaches to data with residue bounded below. Adversary (e) is likely constructible outside the uniform-bound class.\n\nNo route to W(x): the Euler product is used only as a sign condition, Lambda_pf(1) >= 0.\n\nconjecture1_proved = False.",
 "next_step_if_survives": "It does not survive as a route. The most informative next step is to settle adversary (e) explicitly.\n\nConstruct Dirichlet series with the Fricke FE of conductor 20 and Gamma_C(s), a FIXED residue r, and a(n) = a_LG(n) for n <= X. The Hecke group G(sqrt 20) should give an infinite-dimensional FE space: solve the linear FE constraints at many nodes, as B8/EFW did, but pin the residue instead of letting it vanish. Then:\n- locate its zeros near s = 1 with an argument-principle count;\n- compute its Q_x with the harness and an independent code.\n\nIf Q_x is negative from ~5.07 with no zero within O(1/log X) of s = 1, then 'pole unpaid at scale x' and 'exceptional zero' are different obstructions, and B31 must be restricted to uniformly bounded families.\n\nAlongside that, make these ledger edits:\n- Rewrite B31/B8's predictor clause with 'residue' in place of 'pole order'.\n- Record that the P4 w = 0.05 MISS was caused by the s2 findroot bug (use verify=True or bisection).\n- Recompute s4 and s5 with beta(0.02) = 0.9080431 and beta(0.05) = 0.6995132.\n- Rescore P4 w = 0.05 as a borderline HIT (9.83% vs the 10% threshold)."
}
```

### cspace_relaxed_hull_q21 (micro_experiment)
- survives adversarial review: False; prediction matched: True; claimed barrier: B31: the c-space relaxed hull is a conductor-slack bump budget (class 5 + class 1, and class 4 on genuine data).

Scope: target T, and hull pieces with the same Gamma factor and the same pole order, each assumed GRH, combined through the linear certificate Delta(w) = Q_x(T) - sum w_i Q_x(L_i) >= 0.

Statement:
- Delta(w) = s(w) I - sum_{n<x} d_w(n) C_n exactly.
- The only positive input is the conductor slack s(w) <= log(q_T / q_min), maximized by the tiniest conductors (zeta_K(-3), zeta_K(-4)). That set is the RCI binding set (B23), which is now explained as the slack maximizer.
- The certificate fails at x_c, just above the first integer n where an unfixable c-defect atom exceeds the remaining slack. x_c/x_b(op) lies in [0.99, 1.5] for 21 of 24 cases.
- x_c <= x_h always holds, and x_c << x_h (E: 7.04 vs 19.82; DH: 3.01 vs 30.57; ratios 0.10 to 0.92).
- For genuine data outside the hull (leave-one-out), x_c is just as finite (2.003 to 13.2), so the hull detects non-membership, not negativity. That makes it a converse-type lookup, useless as a predictor (battery useful=False, 28 below-horizon false alarms).
- It is continuous in w, so it reproduces the B8 discontinuity only through the discrete pole-order hull switch and never sees the residue (R21 unmet).
- The dual at E's exit puts 68% of its weight on n=6, the non-prime-power block of B6, in the odd sector only.

Evidence: float SDP plus weak-duality certificates, N = 32/48/64, both sectors, 315 pieces; not interval-certified; same-session only (C39).; barrier confirmed: True

W7 cspace_relaxed_hull_q21: barrier measurement. conjecture1_proved = False.

**1. Setup and theorem.** Delta(w) is the difference of window Weil forms between a target and a convex combination of genuine pieces with the same Gamma factor and pole order.
- The arch and pole blocks cancel exactly, leaving Delta(w) = s(w) I - sum_{n<x} d_w(n) C_n.
- I checked this directly against full form.Q differences: maximum error 1.08e-13, both sectors.
- Under GRH for the pieces, Delta(w) >= 0 implies W(x) for T, so x_c <= x_h.

**2. Numbers.** Two tables in counterfeit_control carry the x_c vs x_h values: one for the zoo members, one for the segment E_w.
- Every counterfeit and barrier has x_c < x_h. E fails at 7.04 against 19.82.
- Controls give x_c = inf only because each is in its own hull.
- With their own piece removed, genuine data fail at 2.003 to 13.2. That is no better than the counterfeits, so the hull detects non-membership, not negativity.

**3. Mechanism of failure.**
- The only positive term is the conductor slack. It is maximized by zeta_K(-3) and zeta_K(-4), the RCI binding set (B23), which R10 asked to explain; here it appears as the slack maximizer.
- x_c sits just above the integer n where an unfixable atom enters: n=6 for E (c_E(6) = 2 log 6, 68% of the dual mass, odd sector), n=3 for LEB/L_G/E_w(0+), n=2-3 for DH.
- The budget law x_c ~ x_b(op) holds within [0.99, 1.5] for 21 of 24 cases. The outliers are a2-flip (2.6), E_w(0.1) (1.51) and leave-one-out zetaK(-20) (1.65).

**4. R21 and the pole caveat.**
- The harness gives E_w (w>0) pole factor 1, and the Weil form sees only the pole order.
- x_c(w) is continuous in w, and x_c(0+) = x_c(L_G+pole) = 3.040.
- L_G is in its own pole-free hull, so its x_c is inf. The B8 discontinuity is therefore reproduced only by the discrete hull switch, with no residue or class-number input.
- The segment Spearman correlation of 0.964 is a shared monotone dependence on w, not tracking: x_c/x_h runs from 0.16 to 0.63.

**5. Battery.** 0 control false alarms, 0 misses, 28 below-horizon counterfeit false alarms, useful=False, sharp=False.

**6. Prereg scoring (honest).**
- Headline matched: x_c << x_h, set by the slack budget.
- Misses: P2a (E_w(0.8) = 9.22 > 8), P2c (rho = 0.964), P3 (E[1,0,6] = 10.37 > 10), P4 (d2 = 5.02 and a2-flip = 13.07, both outside [2, 4]), P6b (leave-one-out zetaK(-20) = 13.2 > 10), and the P1 point estimate.

**7. Harness notes (report only, not edited).**
- README omits the stricter `useful` definition.
- DH x=32 metadata conflict persists.
- There is no Legendre basis, so the Neumann basis was used; no near-null brackets were needed because Delta is O(1) away from the crossing.

**8. Artifacts** (all in /Users/peterwmurphy/hodge-engine/hengine/w7/cspace_relaxed_hull_q21/):
- PREREG.md: predates the scripts; a scored table was appended after the run.
- Code: hullcore.py, hullsdp.py, run_all.py.
- Results: run_all.json/.log, analysis.json, battery_hull.json/.log, dual_cert.json/.log, check_assembly.json.

All processes ended; single process throughout, BLAS threads pinned to 1.

**Skeptic:**

```json
{
 "angle": "Skeptic review of W7 cspace_relaxed_hull_q21. This was run as a barrier measurement, not a mechanism. The certificate is Delta(w) = Q_x(T) - sum w_i Q_x(L_i), with w on the simplex, over Gamma- and pole-matched GRH pieces. I rebuilt it with no harness code: my own characters, Kronecker symbol and Epstein/DH coefficients, and a Legendre basis on the full space. I also added two structural bounds of my own: an upper bound on t* from narrow bumps (arithmetic matrices) and a lower bound from the symbol.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "As a mechanism it is dead, as the proposer says (alive=false). The certificate is c-linear and assumes GRH for each piece. It fails at a finite x_c for counterfeits and for genuine data outside the hull alike. It uses the Euler product only to pick which c-vectors are allowed, never nonlinearly or globally.",
  "The barrier holds only under an unstated condition, sum w_i = 1. The claimed_barrier wording ('Delta(w) = Q_x(T) - sum w_i Q_x(L_i) >= 0') does not say it. With sum w_i = sigma < 1, Delta = (1-sigma) Q_x(T) + sigma Delta_simplex, and at sigma = 0 this is just Q_x(T) >= 0, i.e. W(x) itself, so x_c = x_h. The honest form of B31 is a dichotomy: a certificate with full archimedean cancellation is a lookup, and one that keeps any archimedean part contains W(x) and is circular.",
  "The precise x_c values are finite-N artifacts, and the true x_c is lower. The archimedean block cancels, so Delta is a bounded operator: s(w) I minus a pure-atom convolution. On L^2 of the window, an atom n enters at x = n+ with its full operator norm 1/sqrt(n). I checked this: ||C_7|| at x=7.01 is 0.198/0.289/0.354 at N=32/64/128 and tends to 1/sqrt7 = 0.378. So t*(x) jumps at integers, and the 'quantized just above integer n' offsets (7.044, 3.006, 3.040...) are Galerkin edge-resolution error. The N^-2 extrapolation of 7.02 is also not the limit: my own narrow-bump dual certificate gives x_c(E) <= 7.0001.",
  "P0's 'budget law' is half tautological. x_b(op) is where a triangle-inequality sufficient condition fails, so x_b <= x_c is automatic, and only the upper factor 1.5 is an empirical claim. Also, x_b(op) was computed with N=32 operator norms, which under-count atoms that have just entered (see the previous item). A minor slip: PREREG P1's rationale '2|d|/sqrt6 = 2.93 > max slack' uses the crude 2/sqrt n bound. The true operator norm is 1/sqrt n, giving 1.46 < 1.90. The atom at n=6 therefore cannot fail the certificate on its own, which matches the observed exit at 7 rather than 6."
 ],
 "prereg_honored": true,
 "counterfeit_check": "The certificate cannot tell counterfeits from genuine data, as claimed. Both the proposer's Galerkin runs and my own bounds show this.\n\n- **E:** the certificate fails at x = 7+, while E's Weil horizon x_h is 19.82.\n- **DH:** it fails at 3+ against x_h = 30.57.\n- **Genuine zeta_K(-20) with its own piece removed (LOO):** it stays feasible by my narrow-bump bound through x = 11 (U = +0.22 at 10.9999). This is consistent with the proposer's Galerkin value of 13.2 but gives no finer bound.\n- **zeta_K(-20) with its own piece:** it passes trivially, because Delta = 0 at w = e_20.\n\nSo the argument goes through verbatim for counterfeits: it stops them early, but it stops genuine data outside the hull just as early. Beyond the proposer's heuristic ('the slack is bounded while defect mass grows'), I found a rigorous reason for the finite x_c, which I call the hypercube lemma. Take T and all pieces to be Euler data, so c is supported on prime powers and d_w vanishes at squarefree composites. Place narrow bumps at log(prod of any subset of S). On these, Delta acts as s(w) I - sum_p (d_w(p)/sqrt p) X_p on {0,1}^S, where X_p flips coordinate p. Hence for any finite prime set S with prod S < x:\n\nt*(x) <= max_w [ s(w) - sum_{p in S} |d_w(p)| / sqrt p ].\n\nFor finite-order data outside the hull, d_w(p) is nonzero at a positive density of primes for every w, so this sum diverges. By compactness of the simplex, x_c <= prod S is finite, genuine or not. The hull certificate is a lookup (class 4), in the same family as the c-linear bump lemma (B24, class 5) and linearity (B1, class 1). Circularity: assuming GRH for the pieces only makes the certificate stronger, so it does not weaken the negative result.",
 "numerics_reproduced": "All code is independent of the harness. It is in /Users/peterwmurphy/hodge-engine/hengine/w7/cspace_relaxed_hull_q21_skeptic/: skcore.py, arith3.py, galerkin_leg.py, symbol_lower.py; logs and JSON sit beside them. arith_bound.log holds superseded Clarabel crash/time-limit runs; ignore it.\n\n**(1) Coefficients.** Computed from representation counts, they agree: c_E(6) = 2 log 6 = 3.5835 and c_E(36) = -7.167.\n\n**(2) Legendre Galerkin for E, full space.** Here N=128 full corresponds to the proposer's N=64 per sector.\n\n| N | t*_N(7.02) | t*_N(7.045) |\n|---|---|---|\n| 128 | +0.0737 | -0.0016 |\n\nThis reproduces the proposer's x_c(64) = 7.044. At N = 64/96/128/192 the crossing falls: about 7.09, 7.06, 7.044, then between 7.02 and 7.045. It is converging to 7. The dual atom shares at the Galerkin exits are n=6 about 0.69-0.74 and n=7 about 0.1, which reproduces P8's 68%. Each row has primal value = dual value over all 79 pieces.\n\n**(3) Narrow-bump arithmetic bound, E.** Bumps sit at log m for m in [m0, x m0). U is an upper bound on the true t*, and the dual certificate is checked against every piece.\n\n| x | U by m0 | reading |\n|---|---|---|\n| 6.0001 | 0.10253 (m0 = 12..96) | stable |\n| 6.9999 | 0.0946 / 0.0861 / 0.0851 (m0 = 24/48/96) | positive |\n| 7.0001 | -0.0424 (m0=1, 7 points) / -0.2277 (m0=12) | infeasible; w on zL(3), zL(4) |\n\nSo true x_c(E) <= 7.0001. The Galerkin and bump methods agree that t*(7-) is about +0.08, but both are upper bounds. My symbol lower bound, max_w inf_t sigma_w = -2.64 on (6,7], is too weak to prove t* > 0 below 7, so 'x_c(E) = 7 exactly' is strongly supported but not proved.\n\n**(4) DH.** U(2.9999) = +0.0839 (w = L(4) alone) and U(3.0001) = -0.0610. So x_c(DH) = 3+, reproducing the proposer's 3.006 in the limit.\n\n**(5) LOO zeta_K(-20) and the control.** LOO has U > 0 at 7.0001, 8.0001, 9.0001 and 10.9999, with values 0.57, 0.51, 0.29 and 0.22. That is consistent with Galerkin's 13.2 but does not pin it down. My first Clarabel runs showed spurious negative values; they were solver time-limit failures and were discarded, because a primal lambda_min at a suboptimal w is not a certificate. The control zeta_K(-20) at 12.0001 has U = +0.15 using other pieces. The trivial t* >= 0 via its own piece also holds.\n\n**Not independently reproduced:** the E_w segment, LEB, R, euler-rand, the battery scores, and the Qmax=80 dual certificate. I also did not recompute the P7 assembly check against form.Q; instead I built Delta from first principles and matched the 7.044 crossing.",
 "novelty": "Low for the certificate itself. It is the Odlyzko-Poitou explicit-formula optimisation (lit cache explicit_formula_linear_programming#0) run as a comparison against GRH pieces with matched Gamma factor and conductor. Its failure mode is B24's c-linear bump lemma with a conductor budget, and its optimiser (zeta_K(-3) with zeta_K(-4)) restates B23's RCI binding set.\n\nThe genuinely new, checkable content is what I added here:\n- (a) With the archimedean block cancelled, Delta is a compressed almost-periodic convolution (Toeplitz) operator.\n- (b) Because of (a), t* jumps at integer x, and x_c in the continuum sits at an atom entry point.\n- (c) The hypercube lemma turns the proposer's 'odds' claim (x_c finite for anything outside the hull) into a proof for finite-order Euler targets.\n- (d) The sigma < 1 relaxation collapses to W(x) itself, which gives a clean circular-or-lookup dichotomy.\n\nI found no published c-space hull SDP of Weil forms against GRH pieces; this is unverified and I did no web check. (b) and (c) are elementary and probably folklore-adjacent, via Bohr lift, Kronecker and Helson-type multiplicative Toeplitz matrices; the lit-cache key lee_yang_bohr_lift is related but not the same.",
 "what_is_real": "- **The identity.** Delta(w) = s(w) I - sum_{n<x} d_w(n) C_n holds exactly when the Gamma factor and pole order match and sum w = 1. I rebuilt it from first principles; my crossings match the proposer's harness-based ones.\n- **The 3-line theorem.** GRH for the pieces plus Delta >= 0 gives W(x), so x_c <= x_h. Window nesting makes the feasible set monotone in x, and t*_N >= t*, so the finite-N x_c are over-estimates.\n- **The decisive numbers**, reproduced independently:\n  - E fails by 7+ (x_c(64) = 7.044 at matched resolution; the continuum x_c is at most 7.0001) against x_h = 19.82.\n  - DH fails at 3+.\n  - The optimal support is zeta*L(chi_-3) plus zeta*L(chi_-4), i.e. the smallest conductors, which carry the maximal slack.\n  - n=6 carries about 70% of the Galerkin dual.\n- **The qualitative B31 claim**, now with a proof for Euler targets (the hypercube lemma): the certificate detects hull non-membership, not negativity. It is a lookup (class 4) inside the c-linear classes (5 and 1).\n- **Prereg.** The misses are listed honestly. P3 and P6b are labelled 'partial' but are really misses, and P0's lower bound is automatic. I cannot verify authorship time from mtimes (PREREG was appended after the run); the scripts are from 16:50, and I accept the proposer's statement.\n- **Corrections for the ledger:**\n  - (i) Add sum w_i = 1 to B31's scope, and record the dichotomy: keep any archimedean part and the certificate contains W(x).\n  - (ii) Continuum x_c values sit at integers (E: 7, DH: 3). The '+0.04' offsets and the N^-2 extrapolation are artifacts of the edge-concentrated modes.\n  - (iii) The budget law's lower edge x_c >= x_b is a tautology.\n  - (iv) The atom operator norm is 1/sqrt n, not 2/sqrt n.\n  - (v) The finiteness of x_c outside the hull is a theorem (hypercube lemma) for finite-order Euler data, not an 'odds' estimate.\n- **Evidence grade:** float SDPs plus dual certificates checked against all 79 pieces (q <= 40). Nothing is interval-certified.",
 "next_step_if_survives": "The proposal does not survive as a mechanism. For the barrier, the most informative next steps are:\n\n- (1) **Record B31 with the corrections** in what_is_real: the sum-w=1 scope and the circular-or-lookup dichotomy, integer x_c, the tautological lower edge, and the hypercube lemma as the rigorous core.\n- (2) **Test the one door B24(B) and B31 leave open**: certificates that redistribute the archimedean part. Use pieces with DIFFERENT Gamma factors, or a split Q_T = sum w_i Q_{L_i} + R, where R keeps a fraction of the archimedean kinetic term, the log(1/eps) positivity that kills narrow bumps. The question is whether the residual R can be certified by something other than W(x). By the dichotomy, it must avoid containing the near-null cascade of B3/B25. The concrete experiment: sum w = sigma with R = (1-sigma)(arch + pole + log q) minus the matching part. Measure x_c(sigma) for E and for LOO zeta_K(-20). See whether the curve moves continuously from lookup (sigma=1) toward x_h (sigma=0), and whether it ever separates E from genuine data. Separation at some intermediate sigma would be the first certificate that is neither lookup nor circular.\n- (3) **Optionally, formalise the hypercube lemma in Lean** (finite linear algebra on {0,1}^S plus unique factorisation) as a proved barrier item."
}
```
