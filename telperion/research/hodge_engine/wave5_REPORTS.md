# Hodge engine wave 5

conjecture1_proved = False.

## Portfolio

- **cascade_law_slepian** (survivor_refinement): Wave 4's strongest new barrier (B25/R13) rests on a heuristic cascade law that was never tested (K10 puts ~40% on it being clean). P1 names it the highest information per compute. A proved lower bound on cascade dimension would pre-kill every future bounded-rank Hodge or split proposal, and it is Lean-shaped.
- **ihara_solved_model_calibration** (hybrid): All 25+ angles died against barriers, and nobody has checked which barriers a TRUE mechanism would also exhibit. A solved model with an Euler product, an FE and a known Rayleigh-bound reason for RH is cheap (finite matrices). It is the only way to tell whether R13/R16/B24 point away from mechanisms or describe their required shape, and it resets the search direction for wave 6. Both map entries are untried.
- **maass_selberg_schur_barrier** (wildcard): Automorphic spectral theory is the only domain in the map where a proved Hilbert-space positivity contains zeta together with Hecke structure and the FE, and no wave has touched it. The map flags it as possibly Euler-sensitive with no counterfeit analysis ever done. Either outcome pays: a clean 'sees only Re w > 1' theorem is a Lean-able barrier explaining the classical sigma = 1 limit, and a strip-level catch would be the first non-readout signal.
- **strip_reach_xU_theorem** (barrier_hunt): S15 is the only positive-direction unconditional finding in four waves, and its stall between 6 and 8 is the one place where an open question can become a crisp, kernel-certifiable negative theorem this wave. P3 flags it as the next step. The adversary identification also settles a live interpretive question: whether it is balayage (R15) or conductor-blindness (B19/B23).
- **defect_balance_zoo** (micro_experiment): S19 (O(1)-vs-O(1) failure) was measured for one counterfeit at one x. Whether it is universal decides where wave 6 should look: far from the cascade (lower-bound the Euler form on a cone) or at near-null perturbations. The machinery already exists (cg.py, harness vectors), so this is the cheapest high-leverage question left in the ledger's priorities.

## Results

### cascade_law_slepian (survivor_refinement)
- survives adversarial review: False; prediction matched: False; claimed barrier: B27 (proposed) CASCADE THEOREM / ARCHIMEDEAN RANK LOWER BOUND.

Statement. Unconditionally (zeros only assumed to lie in the closed strip; explicit formula; local RvM count), per parity sector: for all x, T and delta,
lambda_m(Q_x) <= (2 M_L(T,r)/r^2) * I_{T,r}(V)
on the subspace V = {f in the top-(N_L(T)+m) band-T prolates : F = 0 at all zeros with 0 < Re gamma <= T, with multiplicity}. Here I_{T,r} is the strip-weighted out-of-band energy.

Consequences:
- Black box: #{lambda_k(Q_x) <= eps} >= e*(x) - ln(C M x^{1/2+r}/eps) ln(AT*)/(2pi^2) - O(1).
- Numerically sharp version (law c'): count = e*(x) - ln(1/tau) ln(AT*)/(4pi^2) +- 1. It holds on 42 (member, x) rows in the harness.
- So R13 becomes a theorem: any Hodge/ample/pole/split of rank k < e*(x) - O(log(1/eps) log x) has primitive margin <= eps. For zeta this means rank at least about x - 7/8 - O(log x log(1/eps)), with e*(x) = dK + (1/4)sum(1/2 - mu_j) - (pole0+pole1)/2.
- lambda_1 ~ exp(-12.2 e*(x)) universally.
- The cascade is archimedean and counterfeit-blind: each counterfeit's non-negative cascade equals its genuine twin's, and off-line zeros add negative index on top of it.

Loose step. The epsilon is NOT useless: it is within 90x of the certified Rayleigh value and 540x of Ritz at the top of the cascade. The loose step is L1 used as a black box (it gives the prolate width 1/(2pi^2) instead of 1/(4pi^2), costing about 4-5 dimensions per sector at x=20, tau=1e-10). L2 costs a factor of 15 and the strip factor e^{A} costs 7; each costs under 1 dimension.; barrier confirmed: False

WAVE 5 - cascade_law_slepian. conjecture1_proved = False. Barrier strengthening only, not a mechanism.

Files are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/cascade_law_slepian/:
- PREREG.txt (05:07:34, predates every script) and PREREG_ADDENDUM.txt (written before t3 and q8b).
- t1-t4 (counts, scoring, out-of-sample, precursor), pbcore/pb1-3 (Part B), l1/l1b (prolate constant, L1 looseness), q8/q8b (lambda_1 law); logs sit next to each script.

HONEST PREREG SCORE: the primary preregistered law (c) FAILED (6/13; the Landau-Widom width constant was 2x too large, plus a spurious +1). Tau-slope: missed by a factor of 2. Precursor: matched. Q8 form (linear in e*, not K^2): matched. H8 slopes in [10,14]: matched. Part B 'certifies >= law(c)-3 with a 1-3 order gap': better than predicted (it certifies the full count, with a gap of 2-6x at the top). 'Strip factor loosest': WRONG; L1 is loosest. So prediction_matched = false overall.

1. CASCADE LAW. The per-sector near-null count at tau is
N_nn(x, tau) = floor( e*(x) - ln(1/tau) ln(A T*)/(4 pi^2) ), with:
- e*(x) = d(x/q)^{1/d} + (1/4)sum_j(1/2 - mu_j) - (pole0+pole1)/2
- T* = 2 pi (x/q)^{1/d}
- A = (1/2) log x
The x - 7/8 offset for zeta is derived: 7/8 = 1 (pole in the argument principle) - 1/8 (Gamma_R Stirling phase).

Derivation: e* = max_T[AT/pi - N_L(T)] is Landau's excess of Paley-Wiener degrees of freedom over zero constraints. For self-dual data, a zero (even off-line) costs exactly one real constraint per sector. The maximum sits at T*, where the zero density equals the Nyquist density A/pi.

Validation:
- 13 members in-sample and 29 new rows out-of-sample, both sectors, tau in {1e-6, 1e-10, 1e-12}, all within +-1.
- zeta counts at x = 8/12/20/28/36/48/64/100: 4/8/16/23/32/43/59/95.
- Laws (a), (b), (c) and C17 fail.
- The count is purely archimedean: E vs zetaK(-20) agree identically below the horizon.
- zetaK(-4) (e* = sqrt(x) - 1) is far below both of its factors (zeta: x - 7/8; L(chi_-4): x/4 - 1/8).

2. PRECURSOR. None. E departs from zetaK(-20) at the horizon, 19.82 (T* = 0.40 gamma_off). DH departs from L(chi_5) at 30.57 (T* = 0.45 gamma_off). New structural fact: count_nonneg(counterfeit) = count(twin) +-1 at all x in the scan (E to 128, DH to 100). Off-line zeros add negative index on top of an unchanged cascade. Recorded as 'cascade is counterfeit-blind; B2 readout'.

3. PART B.

THEOREM (Lean-ready shape). Hypotheses:
- L has degree d, conductor q, shifts mu_j, pole orders p0 and p1.
- Weil explicit formula Q_x(f) = sum_rho F(gamma_rho) conj F(conj gamma_rho) for real f supported in [-A,A].
- All nontrivial zeros have |Im gamma| <= 1/2 (closed strip; no RH).
- Local count: #{rho : Re gamma in [t, t+2r]} <= M_L(t) := a log(q(t+2)^d) + b. For zeta, derived from the project's rvm_unconditional (O-form) or explicitly from Trudgian 2014 (|S| <= 0.112 log T + 0.278 log log T + 2.51, unverified here).

Then, per sector, for every T > 0 and m >= 1, with V_{T,m} the prolate+constraint subspace (dim V >= m):
lambda_m(Q_x) <= sup_{f in V_{T,m}} (2 M_L(T-2r)/r^2) * [ (1/2pi) int_{|eta| <= 1/2+r} int_{|xi| > T-r} |F(xi+i eta)|^2 ] / ||f||^2.

Proof steps:
- f in V kills the in-band zeros.
- |F(gamma)F(-gamma)| <= |F|^2 average.
- Subharmonic mean value on D(gamma, r).
- Overlap is at most M_L.
- Min-max.

L1 (to prove): a weighted Landau-Widom count for the operator R = int_{|eta| <= 1/2+r} E_eta (1 - B_{T-r}) E_eta d eta, with E_eta = multiplication by e^{-eta u} on L^2[-A,A]. It needs at least AT/pi - ln(1/delta) ln(AT)/(2pi^2) - O(1) eigenvalues <= delta per sector. The unweighted version is Landau-Widom. The numerically sharp version needs a NEW 'constraint-assisted concentration' lemma, with width 1/(4pi^2).
L2: RvM local count.

Numerics for zeta at x=20 (mp dps 50, N=128), summarised; the full table is in test_and_outcome:
- Explicit V certifies at least 16 (even) and 15 (odd) eigenvalues below 1e-10, equal to the Galerkin cascade. U_16(even) = 2.805e-11 against Ritz 4.69e-12.
- The zero sum over 800 zeros reproduces the Rayleigh values to 60-75%. The rest is carried by zeros above height 1183 (the 1/xi^2 tail from the endpoint jump f(+-A)).
- Heuristic 2 pi n(T) E_out agrees with U to within 1.5x.

Where epsilon is loose: the analytic epsilon for even m=16 is 2.5e-9, which is 90x U. The factors are L2 15.1, strip 6.9 and disk 1.27. But L1 used as a black box is loose by 1e4-1e7: the constraints remove the leaky edge prolates. Consequence: the black-box theorem certifies about 11, against the true 16 at x=20, tau=1e-10. Epsilon is therefore USEFUL, not beyond the spectrum scale. The binding looseness is L1, not the e^{A/2} strip factor.

Mathlib gaps:
- Paley-Wiener spaces, prolate spheroidal functions and time-band limiting spectra (Landau-Widom) are all absent.
- The subharmonic mean-value inequality for |F|^2 on disks is probably available via circle averages; it needs checking.
- The Weil explicit formula for window tests is not in Mathlib; it is in-project/Lane B.
- RvM: an O-form sorry statement in-project (RH_rvm_unconditional). No effective version exists.
- Min-max (Courant-Fischer) for compact self-adjoint forms: partial in Mathlib.

B21 note: a Rayleigh quotient on an explicit subspace is, by min-max, a CERTIFIED upper bound on lambda_k, and so is every Galerkin Ritz value (nested subspaces). The counts in this report are therefore rigorous LOWER bounds on near-null counts, modulo arithmetic and P1-P3. B21's caveat applies only to the other direction: positivity and horizon claims.

4. Q8. -ln lambda_1 ~ 12.2 * e*(x) + O(1), with a near-universal slope (11.2-12.4 across zeta, zetaK(-20), zetaK(-4), L(chi_-4), L(chi_5), L(chi_-3)). For zeta it is converged: lambda_1(20) is about 1e-96 (the ledger's 5e-53 was unconverged, N=32). This agrees with Zhu 2608.24827's 2pi^2 N(T*)/ln N(T*). The ledger's contrast between zetaK(-20)'s 'exp(-x/2)' and zeta's 'superexponential' decay is the same linear-in-excess law: e* ~ x for zeta and ~2 sqrt(x/20) for zetaK(-20).

CORRECTIONS for the ledger:
- S17 counts at N <= 48 were unconverged.
- zeta lambda_A ~5e-53 and 'superexponential': see Q8.
- The 'exp(-x/2)' for zetaK(-20) is a sqrt(x) law.
- The ~x - 7/8 offset is now derived.
- Harness: no bugs found. The float path counts reliably at tau = 1e-10 for N <= 1024.

**Skeptic:**

```json
{
 "angle": "cascade_law_slepian (wave 5 skeptic). The proposal is an empirical law plus a claimed theorem (B27) about the near-null cascade of the window Weil form. By the proposer's own statement it is not a positivity mechanism.",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "As a mechanism, it is dead on the gate criteria. The Euler product is used nowhere; the proposer says so. The construction is also counterfeit-blind by design: the whole lower-bound argument needs only the FE, Gamma data, a zero count and zeros in the closed strip, so it goes through word for word for E and DH. survives=false is automatic.",
  "B27 is not a theorem as stated, for three reasons. (i) The count consequence ('#{lambda_k <= eps} >= e* - ln(C M x^{1/2+r}/eps) ln(AT*)/(2pi^2) - O(1)', i.e. 'R13 becomes a theorem') depends on L1, which the proposer marks 'to prove'. L1 is the weighted/strip out-of-band count for R = int E_eta (1-B_{T-r}) E_eta d eta, and it is NOT a corollary of Landau-Widom. Moving a band-concentrated F in PW_A to Im = eta leaks in-band mass across the edge. The Poisson majorant has polynomial tails (about 50% leakage at eta = r = 1/2), so L1 needs a guard band of width about O(1)-O(A), and that has not been shown. (ii) L2 rests on Trudgian's explicit S(T) constants, which were quoted from memory and not verified.",
  "The core inequality is misstated. lambda_m <= (2 M_L(T-2r)/r^2) sup_V I_{T,r} puts the local zero count M_L at height T OUTSIDE an integral over all |xi| > T - r. The overlap of the disks grows like log(height), and the proposer's own numerics show that zeros above 1183 carry 25-40% of the Rayleigh values. The correct statement puts the height-dependent weight M_L(|xi|) inside the integral. The fix is easy, but as written the inequality is false in general (its sup over heights is infinite).",
  "At any FIXED x, Part B adds no certification beyond what the ledger already had. Galerkin Ritz values already give rigorous min-max upper bounds on lambda_m, modulo arithmetic (B21/B25). So 'certifies 16/15 at x=20' is not new. The only new content would be the all-x asymptotic, and that is exactly the unproved L1 part.",
  "Several parts are not new, or not established by the data. Q8 (-ln lambda_1 about 2pi^2 N(T*)/ln N(T*)) and the idea of variational upper bounds are prior art in Zhu arXiv:2608.24827 (in the lit cache, verified). The law '12.2 * e*' is numerically nearly indistinguishable from Zhu's law on [8,100]. The 'derived' 7/8 offset (+1/8 Stirling, -1 pole) cannot be resolved at +-1: dropping the offset still fits 552/580 in-sample entries. The 'counterfeit non-negative cascade = twin's' observation is a heuristic corollary of the zero-sum picture: each off-line pair contributes one hyperbolic block, and e* already counts off-line zeros in N(T). It is not an independent structural theorem. Below the horizons the E-vs-zetaK(-20) comparison is 0 = 0 (uninformative). DH's 'twin' L(chi_5) has mu=0 while DH has mu=1."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Yes, it goes through verbatim for a counterfeit, by design. The lower bound on the cascade needs only the FE and Gamma data, a zero count, and zeros in the closed strip. V kills in-band off-line zeros as well: F(t+i eta) = 0 is one complex condition and covers 2 zeros. So the bound holds equally for E and DH. It cannot be a positivity source, and the proposer says so. I reproduced the structural observation independently.\n- E[1,0,5] vs zetaK(-20) at x=128 (my Legendre code, n=160 and 208, converged): E has count(<1e-10) 9/8 with index 7/7, which leaves 2/1 non-negative. zetaK(-20) has 2/1 with index 0. This matches the proposer.\n- Below E's horizon both counts are 0 at tau=1e-10, so the 'identical below 19.82' claim carries no information.\n- DH vs L(chi_5): the proposer's own t4 log shows +-1 jitter before 30.57.\nVerdict: the cascade is archimedean and counterfeit-blind (confirmed). Counterfeits fail through extra negative directions (B2 readout), not by eating into the cascade.",
 "numerics_reproduced": "All numbers below come from an INDEPENDENT implementation (no harness import): Legendre basis, u-space arch via the psi integral representation, and my own L-data (zeta, L(chi_D), zetaK(D), DH with its own kappa, and the Epstein lattice count). Code: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/cascade_law_slepian_skeptic/wlf.py.\n\n(1) Explicit-formula identity. My prime-side Q equals 2*sum over the first 400 zeros (mpmath zetazero, my own list) of |F(gamma)|^2 to 1e-14 at x=8 and x=20, in both sectors (v1_explicit.py). So 'Q = zero sum exactly' is confirmed.\n\n(2) Zeta counts at tau=1e-10, even/odd.\n| x | mine | converged at n/sector | proposer |\n|---|---|---|---|\n| 8 | 4/4 | n up to 96 | 4/4 |\n| 12 | 8/8 | n up to 96 | 8/8 |\n| 20 | 16/15 | n=128 | 16/15 |\n| 36 | 32/31 | n=224 and 288 | 32/31 |\n| 64 | 58/58 | n=400, still rising | 59/59 |\nAll agree; x=64 is consistent as a lower bound.\n\n(3) Other members, my counts at tau=1e-10, even/odd:\n- L(chi_-4): 6/6 at x=36; 12/12 at x=64.\n- L(chi_5): 5/4 at x=36; 10/9 at x=64.\n- L(chi_-3): 9/8 at x=36.\n- zetaK(-4): 4/4 at x=64; 6/6 at x=100.\n- DH: 2/1 at x=20; 3/3 at x=28.\n- zetaK(-20): 2/1 at x=128.\nAll match the proposer's t1/t3 within +-1 and agree with law c'.\n\n(4) Cross-check of the harness path, my lambda_min against the harness:\n| member | x | mine | harness |\n|---|---|---|---|\n| zetaK(-20) | 64 | 9.87e-11 | 9.901e-11 |\n| DH | 64 | -1.02 | -1.021 |\n| E | 64 | -2.10 | -2.096 |\n| DH | 36 | about -4.8e-9 | -5.09e-9 |\nNo harness bug found.\n\n(5) Part B, independent (pb_indep.py, n=160, my own band-limiting matrix and zero constraints, x=20, T=150, N(T)=52), max Rayleigh U_m on V against my Ritz lambda_m. This reproduces the proposer's pb2 (2.805e-11 / 2.74e-8 / 8.15e-10) within about 1.3x.\n| sector | m | U_m | Ritz lambda_m |\n|---|---|---|---|\n| even | 16 | 2.32e-11 | 3.96e-12 |\n| even | 17 | 2.07e-8 | 8.2e-9 |\n| even | 18 | 2.3e-5 | 1.3e-5 |\n| odd | 16 | 6.5e-10 | 1.65e-10 |\n\n(6) Discrimination (alt_laws.py, on the proposer's t1 data, 580 (member, x, N, sector, tau) entries):\n- law c' (in-sample): 580/580 within +-1.\n- dK - width (offset dropped): 552/580.\n- e* - const*ln(1/tau) (no ln AT*): 572/580.\nSo c' is a genuinely good fit, but the offset and ln(AT*) refinements are only weakly resolved.\n\nNot reproduced: the Q8 mp values (lambda_1(20) about 1e-96), and the claim that the 1/(4pi^2) constant is exact.",
 "novelty": "Modest. The ingredients are all known:\n- Landau density / Paley-Wiener degrees of freedom against the Riemann-von Mangoldt count. This is the wave-4 skeptic's heuristic (B25), and the sampling-density picture is related to Landau 1967 and Kulikov-Nazarov-Sodin (lit key fourier_interpolation_duality#3).\n- Prolate test functions vanishing at zeros, and the Landau-Widom-rate lambda_min law: Zhu arXiv:2608.24827 (verified, in the cache).\n- Small eigenvalues with prolate eigenvectors: Connes-Consani, Enseign. Math. 69 (2023). Whether they already count the small eigenvalues against zeros is UNVERIFIED and needs checking.\n\nWhat is new within the project:\n- The quantitative per-sector count law c', with the RvM offset and the empirical one-sided width 1/(4pi^2), which is half the prolate Landau-Widom value. My data are consistent with lambda_Q scaling like (1-mu)^2: the Ritz values drop about 3.4 decades per index, against about 1.5 for the prolates.\n- The observation that counterfeit non-negative cascade = twin's.\n- The x=20 quantification of epsilon's looseness.\nNone of it is RH progress.",
 "what_is_real": "1. The window form equals the zero sum exactly (confirmed to 1e-14 by independent code).\n2. The near-null cascade is real and is well described EMPIRICALLY by c': N_nn(x,tau) = floor(e*(x) - ln(1/tau) ln(A T*)/(4pi^2)), within +-1. This holds across degree, conductor and mu. Independently reproduced for zeta at x = 8/12/20/36, and for L(chi_-4), L(chi_5), L(chi_-3), zetaK(-4), DH and zetaK(-20).\n3. The cascade is archimedean and counterfeit-blind. In E and DH, off-line zeros add negative index on top of an unchanged non-negative cascade (reproduced: E at x=128 has index 7/7 plus 2/1, against zetaK(-20)'s 2/1).\n4. At fixed x, the counts are rigorous lower bounds by min-max, modulo float arithmetic. This was already true in wave 4.\n5. The prolate+constraint subspace does reach the full cascade at x=20 (reproduced within 1.3x). The provable inequality is lambda_m <= (2/r^2) sup_V \u222b\u222b_{strip, |xi|>T-r} M_L(|xi|)|F|^2 / ||f||^2, with the height weight INSIDE the integral.\n6. The all-x count theorem, which would make R13 unconditional, is a sketch that stands or falls with L1 (strip leakage with a guard band).\n\nRecommended ledger wording: 'S20 (numeric, independently reproduced): cascade law c' +-1; counterfeit-blind; all-x lower-bound theorem pending L1.' Do NOT record it as barrier B27 'theorem'.\n\nPrereg:\n- Timestamps are genuine: PREREG 05:07:34, before t1 at 05:07:56; the OOS predictions file at 05:10:29, before t3 at 05:10:44.\n- The primary law (c) was honestly scored FAILED, and prediction_matched=false.\n- Minor softening: the Part B prediction 'Rayleigh 1-3 orders above Ritz' missed (actual 2-6x), but was reported as 'better than predicted' rather than as a miss. The H8 slope window was set after seeing zeta's slope (disclosed). The zetaK(-20) prereg '2pi^2 e*/ln c*' (about 8.8 per e*, against 11.2 measured) was not scored.",
 "next_step_if_survives": "Does not survive as a mechanism. The most informative next step for the barrier is to prove or refute L1 in guard-band form: for f in the top-(AT/pi - G) prolates with G = O(A), bound sup_{|eta|<=1/2+r} \u222b_{|xi|>T-r} |F(xi+i eta)|^2 by C e^{2A|eta|} (1-mu) + exponentially small. Then restate B27 with M_L(|xi|) inside the integral, and cache Trudgian 2014 and Landau-Widom 1980 in the lit cache. Only after that should R13 be upgraded to a theorem. Also cheap: check whether Connes-Consani (Enseign. Math. 69, 2023) already states the small-eigenvalue count. And test the (1-mu)^2 mechanism behind the 1/(4pi^2) width directly: regress log Ritz lambda_k against log(1-mu_{k+N(T*)}) at x = 20 and 36."
}
```

### ihara_solved_model_calibration (hybrid)
- survives adversarial review: False; prediction matched: True; claimed barrier: SOLVED-WORLD CALIBRATION BARRIER (C-Ihara).
In the Ihara world, where RH holds exactly when the graph is Ramanujan and is decidable, the following ledger barriers still HOLD even though RH is true there:
- B1 (E_G passes every linear identity);
- B2 (the horizon is a zero readout: (M*-1)*L*Im(gamma)_max is about 1.5-5.6);
- B5 (N_m >= 0 always, yet non-Ramanujan graphs fail);
- B24 (exact two-bump +-L*dw_m0);
- B26/R16 (the per-prime split dies at x = q^8 with n = 40 and is exactly infeasible beyond q^{2(n-1)});
- B22 (Euler data without FE: P(PSD) falls to 0.09 by M = 40).
Consequence: these barriers do not discriminate between worlds where RH is true and worlds where it is false. They are properties of the explicit formula, not evidence against a mechanism.

RECLASSIFIED:
- B3/B25 near-null cascade. It is present in a world where RH is true, and it comes first (positive eigenvalues down to 1e-25 at M = 78 for n = 40, before exact nulls at M = 79 = 2(n-1)+1, integer-certified). So it is a NECESSARY feature of positivity near a rank or resolution threshold, not a sign of fragility.
- B20/R9 (Pi^0_1 margin decay). This FAILS in the graph world because of the finite horizon principle: W(q^{2n-1}) implies W(x) for all x. It is reclassified as a necessary feature of infinite rank.
- B19 FAILS for unitary random data (P = 1).

TRANSFER BARRIER: the finite-rank mechanism needs the length spectrum to lie in a lattice (log q)Z. The zeta window form has no exact null vector on the smooth class for any x (Jensen's formula against N(T) ~ (T/2pi) log T, unconditional), so no finite-dimensional unitary-Bhat object built from prime data exists for zeta. The only per-prime transfer, local Hashimoto unitarity, was run blind and is KILLED: useful = False, 165 below-horizon false alarms, 368 barrier misses. It duplicates B18.; barrier confirmed: False

IHARA SOLVED-MODEL CALIBRATION (wave 5). conjecture1_proved = False.
Directory: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/ihara_solved_model_calibration/
- PREREG.txt (05:04:54), written before any script.
- gcore.py: graphs, Hashimoto B, exact N_m, Toeplitz matrices, exact inertia, B-spline Galerkin on both sides.
- t1_killcheck.json, t2_cascade.json, t3b_EG.json, t4_exact.json, t5_q3_n40_ramA_I82.json, t6_q3_n40_ramA.json, t7_b24_b19.json, t8_battery.json/.log.
- graphs.json holds 24 graphs: q in {3,5}, n in {40,80,200}; tags ramA, ramB, nonram_rand, planted. For q = 5 and the planted/non-Ramanujan graphs, simple graphs were too rare, so these are multigraphs with full loops; Ihara-Bass was re-verified against Tr B^m in every case.

0. GO/NO-GO: passed.
- The prime side (atoms m log q, weight N_m q^{-m/2}, arch (1-u^2)^{E-n}, pole from eigenvalue q+1) equals the spectral side, sum over j, +-, k of ghat((+-theta_j + 2 pi k)/L), to worst relative error 6.3e-15 in both sectors. Complex theta (non-Ramanujan) is handled by ghat(z) = F(z) conj F(conj z).
- Exact w_m requires integer subtraction before division; float cancellation of N_m q^{-m/2} - q^{m/2} gave errors of 1e2 at m = 60.
- One self-bug was fixed (degree-15 B-spline truncated powers).
- Sign note: det(I - uB) behaves like 1/zeta, so the spectral points are POLES of Z_G. Non-Ramanujan eigenvalues act as extra hyperbolic 'pole blocks'.

1. KEY STRUCTURAL FACT (fiber theorem). Q(f) = L int_0^L f_r^T T_M(w) f_r dr. So W(x) holds exactly when T_{M(x)} is PSD, horizons are quantized at x = q^{M-1}, and the scaled matrix D T D is an integer matrix. RH for the graph is equivalent to T PSD for all M, i.e. to w being the moments of a positive measure. By flat extension (finite rank), it is enough to check M = 2(n-1)+1.

2. B3/B25 CASCADE -> RECLASSIFIED.
- Exact nullity is M - 2(n-1). The threshold is x > q^{2(n-1)}, i.e. A > (n-1) log q. The assignment's 2A > n log q was off by a factor of 2.
- The Galerkin null count is proportional to the basis size, not '2A/L - n': a commensurate basis gives exactly p(M - 2(n-1)) nulls (9 = 5 + 4 verified at mp100, with a gap of more than 80 orders).
- Before the threshold there is a genuinely positive near-null cascade (Vandermonde conditioning of clustered eigenangles). Counts below 1e-10: 2, 5, 8, 8 at M = 60, 70, 76, 78. Smallest eigenvalue 9.5e-25 at M = 78.
- Float64 misreads the cascade as nulls (the B21 analogue).
- So the ledger's near-null cascade shows up in a world where RH is true, as the pre-threshold regime of finite rank. It is a necessary feature, not an obstruction signal.
- Zeta analogue: exact nulls are impossible for any x (Jensen's formula against the zero count, unconditional). Only the cascade transfers.

3. R4 HOLDS exactly. Q = sum over |rho| = 1 of h_f(rho), with h_f >= 0 on the circle (the periodized |F|^2). Null vectors have h_f(e^{i theta_j}) = 0 at every eigenangle (1e-30, float-angle floor), and min h_f on the circle is >= 0. The lossless split exists, but it is PER EIGENVALUE (2(n-1) PSD pieces), not per prime.

4. B26/R16 HOLDS. Per-prime (cycle-length) split of the exact fiber form with free arch/pole/identity shares (CLARABEL; feasible points exactly certified by rational inertia):
- singletons feasible up to M = 7;
- K_max = 3 at M = 8;
- K_max = 1 for 9 <= M <= 24 (float t* between -7 and -3e4, not Farkas-certified);
- exactly infeasible for K = 2, 3, 8 at M = 79 and 81 (rational null-space inconsistency in every block).
Even when RH is true, positivity does not split over primes.

5. B24 HOLDS exactly: Q_G1 - Q_G2 on the two-bump f = phi + eps*phi(. - m0 L) equals +-L dw_{m0} = +-6.342841 (q=3) and +-1.439525 (q=5), matching the predicted values to all printed digits.

6. B1 HOLDS. E_G passes the FE, the trivial zeros, the degree and the leading coefficient (exact rationals). N^E_m != (N1+N2)/2 (the log-derivative is nonlinear). It is non-integral from m = 3..43 (half-, quarter- and eighth-integers), and negative in only 2 of 12 pairs (m = 2).

7. B5 HOLDS. N_m >= 0 for every genuine graph, yet non-Ramanujan graphs are Weil-negative. E_G has N^E >= 0 through M_max in 10 of 12 pairs and is still Weil-negative.

8. B19 FAILS / B22 HOLDS.
- Random unitary Satake angles at fixed n: P(pos) = 1 at every M.
- Uniform real lambda: P -> P(Ramanujan) = 0.0033 (q=3; theory 0.0037) and 0 (q=5; theory 1e-5). At fixed n the limit is positive, not 0.
- Random Poisson prime-cycle counts without FE: 1.0 -> 0.80 (M=20) -> 0.09 (M=40) for q=3, and 0.67 -> 0.037 for q=5.

9. B2 HOLDS (horizon vs first off-circle root).
- Genuine non-Ramanujan graphs: M* = 7-11 (planted, eta 0.49-0.80) and 14-39 (eta 0.05-0.25). (M*-1)*eta_max is 1.8-5.6. Exact at n = 40; mp60 elsewhere.
- E_G: M* = 9-75. The lowest off-circle roots have Re gamma about 0.5-1.2 and small Im. Horizons track Im(gamma)_max and the conditioning of the rest; M*·L·Im is 1.5-5.5, against 1.29 (E) and 1.06 (DH) on the zeta side.
- 'First off-circle root height' carries little information, since it is fixed mod 2 pi/L. The horizon is a readout of all the zeros.

10. TRANSFER + BATTERY.
- Precise transfer: the graph proof of positivity is 'Bhat unitary on a FINITE space built from prime-cycle data, with lengths in a lattice'. That gives the finite horizon principle and exact finite rank.
- Zeta lacks both: no lattice, and no exact null for any x. So the faithful transfer is either W(x) itself (tautology) or a per-prime unitarity test (B18).
- The latter was run blind on xs = 2..100: 0 control false alarms, 0 counterfeit misses, 475 catches, 165 below-horizon false alarms on counterfeits (181 false alarms in all), 368 barrier misses (LEB, euler-rand, a2-flip never caught). useful = False, sharp = False. KILLED.

PREREG SELF-AUDIT. Matched:
- threshold and exact rank (exact);
- cascade;
- Galerkin count;
- E_G off-circle roots and M* <= 2n-1;
- R4, B24, B1 (non-integral), B5, B19;
- battery verdict (useful/sharp both False) and false-alarm range (165, within 100-200).
Quantitative misses:
- planted M* predicted 2-6, actual 7-11;
- barely non-Ramanujan M* predicted near 2(n-1), actual 14-39 (predicted far too late);
- N^E negative in only 2 of 12 pairs, although 'negative' was listed alongside non-integral;
- battery misses 368 vs the predicted 250-300;
- per-prime split: I predicted K_max = 1 'once M > 2(n-1)'; it happens far earlier, at M = 9.

HARNESS REPORT (do not edit): new battery conflict E[1,0,14] at x = 95. The metadata says -1, but N = 64 float gives +1.1e-7 (finite-N effect just past 94.44). The C11c DH x = 31..35 conflicts persist.

LEDGER SUGGESTIONS:
- Add C-Ihara as a calibration entry.
- Mark B20/R9 and the B3/B25 cascade as 'necessary in infinite rank' rather than evidence of fragility.
- Q11 interlacing_families_ramanujan: the natural zeta handle would be the MSS real-rooted average (the matching polynomial). This gives 'some member positive', never a specific L. It is untested here and flagged as theory only.

**Skeptic:**

```json
{
 "angle": "SKEPTIC review of ihara_solved_model_calibration (wave 5). The proposal uses Ihara zetas of 2k-regular permutation-union graphs as a \"solved world\" (RH there means the graph is Ramanujan) to calibrate the ledger's barriers, plus one transfer criterion run blind on the zeta battery. conjecture1_proved = False.\n\nI reproduced the decisive numbers with my own code, which does not import gcore or the harness. Scripts and JSON are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/ihara_solved_model_calibration_skeptic/: sk_core.py, s1_exact.py, s2_EG_cascade.py, s3_split_farkas.py, s4_split_vs_n.py, s4b.py, and s1/s2/s3/s4/s4b JSON files.\n- N_m is computed directly as Tr B^m of my own Hashimoto arc matrix, in exact integers. That removes the dependence on Ihara-Bass.\n- Exact inertia uses fraction-free Bareiss leading minors plus exact rank.\n- E_G is built from Newton identities in exact Fractions.\n- The split question uses an exact rational Farkas certificate: the CLARABEL dual is rounded, the equalities are repaired exactly, and PD is checked by rational LDL.",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "NOT A MECHANISM (the proposal itself says alive=false). The Euler product is never used nonlinearly and globally as a source of positivity. Graph positivity comes from one global finite operator (Bhat unitary on a 2(n-1)-dimensional space), i.e. from the zeros. The only zeta-side criterion (per-prime Caratheodory-Toeplitz of c(p^k)/log p, plus c(n)=0 off prime powers) is B18 local temperance verbatim. I read t8_battery.py and it is exactly that. The battery shows useful=False: 165 below-horizon false alarms and 368 misses (numbers taken from the proposer's JSON; I did not re-run the battery).",
  "CATEGORY ERROR IN THE HEADLINE CONSEQUENCE. The claim is that 'B1/B2/B5/B24/B26/B22 do not discriminate RH-true from RH-false worlds, hence are not evidence against a mechanism'. The ledger barriers were never evidence that RH is false. They restrict which classes of proof can work. In the random-permutation graph world, a Ramanujan graph is Ramanujan with no reason at all: positivity is typical and certified by one finite computation. So barriers holding there tells us nothing about whether a mechanism exists. The informative calibration is a solved world WITH a known proof (LPS via Deligne / Eichler-Shimura, function-field curves via Weil / Castelnuovo-Severi / Stepanov-Bombieri, MSS existence). It was not run.",
  "B19 'FAILS' IS CIRCULAR. The script (t7_b24_b19.py) draws the unitary Satake angles uniformly and feeds them in as the graph's spectral angles, i.e. its ZEROS. Unitary zeros are RH, so P=1 is a tautology. Ledger B19 randomizes LOCAL per-prime Satake data. The correct graph analogue is the random prime-cycle (Poisson Euler) run, which is the proposer's B22 item and does decay (0.80 at M=20, 0.09 at M=40). The 'uniform real lambda: 0.0033 vs 0.0037' match is 1 hit in 300 samples, so it is statistically empty (and tautological).",
  "B26/R16 'HOLDS' IS MISATTRIBUTED. The graph split has pieces theta_b*Arch + mu_b*Pole + c_b*I + P_b with NO transfer kernels. That is the analogue of the already-killed local PSHR, not of KS-PSHR/B26, which has spline transfer kernels. My exact Farkas certificates show the K=2 split is infeasible at M=9 for n=40 on both my graph and the proposer's ramA. There T_9 is strongly PD: lambda_min = 16.2 (proposer's t6 value) and 14.4 for my graph, nowhere near null. So in the graph world split failure is NOT caused by near-null approximation (the R16 lemma is sufficient, not operative). It comes from the poverty of the piece family. The failure scale also grows with n: M_split = 9 (n=40), 11 (n=80), in {15,16} (n=200); all cases K=2 and exactly certified. The claimed 'exact infeasibility beyond 2(n-1)' is a trivial overdetermined system: 79 equations, 3 unknowns, rank 3 vs 4, reproduced.",
  "B20/R9 'RECLASSIFIED AS A NECESSARY FEATURE OF INFINITE RANK' IS OVERREACH. The graph world shows only that finite rank gives a finite certificate (flat extension). It shows nothing about necessity in infinite rank. The ledger already has infinite-rank data with non-superexponential decay (zeta_K(-20) about exp(-x/2)). Likewise, 'cascade is a necessary feature, not fragility' attacks a strawman. The ledger never read the cascade as fragility. B3/B25/R4/R13 are constraints on SPLITS, and the graph world confirms them (the lossless split is per eigenvalue = zero readout).",
  "TRANSFER BARRIER STATED AS UNCONDITIONAL, BUT PROVED ONLY UNDER RH. 'The zeta window form has no exact null vector for any x (Jensen vs N(T), unconditional)' needs Q(f) = sum |F(gamma)|^2, which requires real gamma. Without RH, Q(f)=0 or f in the kernel gives only that sum_rho F(gamma_rho) e^{i gamma_rho t} vanishes on an interval, which does not force F(gamma)=0. It is fine for the purpose (RH <=> all-x W(x)), but it must be worded 'under RH'.",
  "Minor points:\n- The flat-extension attribution for Toeplitz should be Caratheodory-Fejer / Pisarenko / Iohvidov. Curto-Fialkow is the truncated-moment generalization.\n- The finite horizon principle needs distinct nodes (true generically, and in all graphs checked).\n- The horizon 'law' (M*-1)*eta_max in 1.5-5.6 spans a factor of 3.7, so it is not a law. It is the B2 zero readout."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Graph world: the graph counterfeit E_G = (P_G1+P_G2)/2 passes every linear identity, as B1 says. My pair is the proposer's q3_n40_ramA plus my own seed-99 Ramanujan graph.\n- FE is exact (error 0), E_G(1) = E_G(1/q) = 0, and the leading coefficient is 3^40 exactly.\n- N^E_m is non-integral for 70 of m = 1..90 (first at m=13; denominators up to 2^9), and nonnegative for all m <= 90. This matches B5: sign data cannot catch it.\n- It has 12 off-circle roots (eta_max = 0.1196) and is exactly Weil-negative at M* = 25, with inertia (24,1) from Bareiss minors, well below 2(n-1)+1 = 79.\nIt is caught ONLY by the exact Toeplitz inertia, i.e. by W(x) itself, a zero readout. Nothing in the proposal separates it at the input level.\n\nZeta side: the local-unitarity criterion is scale-blind by construction (B18).\n- It flags E at x=7 because c(6) != 0 at a non-prime-power (hence the below-horizon false alarms from x=7).\n- It never flags LEB, euler-rand or a2-flip, which are locally pure.\nSo it goes through verbatim for counterfeits below their horizons and misses the barrier members. The proposer's verdict useful=False, sharp=False stands. I checked the script logic; the 165/368 counts come from the proposer's JSON and I did not re-run the battery.",
 "numerics_reproduced": "Everything below is independent code: my own Hashimoto arc matrix with exact integer Tr B^m; no gcore, no harness.\n\n1. Ihara-Bass check. Chebyshev traces plus (E-n)(1+(-1)^m) match direct Tr B^m with mismatch exactly 0 for m = 1..90 on three graphs:\n   - the proposer's q3_n40_ramA;\n   - my q=3 n=40 simple Ramanujan graph (seed 99, rho = 3.398 < 3.464);\n   - my q=5 n=40 Ramanujan multigraph.\n   The proposer checked only m <= 14. The spectral identity w_m = sum 2cos(m theta_j) holds to 1.5e-13.\n\n2. Cascade threshold, exact.\n   - q=3 (both graphs): D T_M D has all leading minors positive for M = 70 and 78. At M = 79, 80, 85 the first zero leading minor is at 79, the rank is 78 and the nullity is 1, 2, 7.\n   - q=5: nullity 1 at M=79 and 3 at M=81.\n   This is exactly the proposer's (78,0,1), (78,0,2), (78,0,7). The threshold x > q^{2(n-1)} is confirmed.\n\n3. Near-null cascade (mp dps 80, my own graph).\n   | M | smallest eigenvalue | count below 1e-10 |\n   |---|---|---|\n   | 60 | 8.4e-14 | 2 |\n   | 70 | 1.7e-19 | 4 |\n   | 76 | 4.3e-24 | 7 |\n   | 78 | 8.1e-27 | 8 |\n   At M=80 there are 2 exact nulls (1e-79, the dps floor) and the next eigenvalue is 3e-22. This qualitatively reproduces the proposer's 9.5e-25 at M=78, with a graph-dependent constant.\n\n4. Genuine non-Ramanujan graphs (my own), exact M* from Bareiss sign change, inertia (M*-1, 1):\n   | graph | M* | eta values | (M*-1)*eta_max |\n   |---|---|---|---|\n   | planted | 9 | 0.489 | 3.91 |\n   | random multigraph | 14 | 0.282, 0.039 | 3.66 |\n   Both lie inside the proposer's ranges.\n\n5. E_G: see counterfeit_check. M* = 25 exact; (M*-1)*eta_max = 2.87.\n\n6. B24. The identity dQ/||f||^2 = eps * L * dw_{m0} follows in two lines from the fiber formula (w_0 is shared). The proposer's 6.342841 = L*30/3^{3/2} is consistent with dN_3 = 30.\n\n7. Per-prime split, exact Farkas certificates (UPGRADE over the proposer's float SDP).\n   - n=40: K=2 is infeasible at M = 9 and 12 for both graphs, and at M = 20 for ramA (my graph's M=20 rounding failed PD). Float says feasible at M = 8 (K = 2 and 3).\n   - Scale vs n: M_split(K=2) = 9 (n=40), 11 (n=80), in {15,16} (n=200). This is far below 2(n-1)+1, and at M=9 T is PD with lambda_min about 14-16.\n   - At M=79, K=2 with three different cut points: rank [A | b] = 4 > rank A = 3, so the system is exactly inconsistent.\n\nNot reproduced: the Galerkin 9-null count, the battery re-run, and the E[1,0,14] x=95 harness conflict. For that conflict, the finite-N explanation is plausible (B21) but unchecked by me.",
 "novelty": "Mathematically none, as the proposer concedes.\n- Ihara zeta, Bass's determinant formula, Hashimoto, and 'Ihara RH <=> Ramanujan' (Stark-Terras) are classical. So is the Weil explicit formula for graphs.\n- The fiber/Toeplitz reformulation is classical Caratheodory-Toeplitz.\n- These are cited from memory and flagged as not in the lit cache (acceptable). The cache citations used (MSS I/II, Friedman, Huang-McKenzie-Yau, Weil 1948, Bombieri Bourbaki 430) check out against lit/index.json.\n\nNew to the project:\n- the factor-2 correction of the cascade threshold (A > (n-1) log q);\n- integer decidability of graph W(x);\n- a ledger-calibration use of the graph world;\n- (skeptic addition) exactly certified per-cycle-length split failure in an RH-true world at a strongly PD scale that grows with n, which shows that split failure there is not driven by the near-null cascade.",
 "what_is_real": "Real, and exactly reproduced:\n(i) The fiber theorem. Graph W(x) holds iff T_{ceil(log x / log q)}(w) is PSD, and D T D is an integer matrix, so graph W(x) is decidable in integers.\n(ii) For generic Ramanujan graphs T_M has rank exactly 2(n-1). There are exact nulls from M = 2(n-1)+1 (threshold x > q^{2(n-1)}), preceded by a genuinely positive near-null (Vandermonde) cascade. It reaches about 1e-25 to 1e-27 at M = 2(n-1) for n=40.\n(iii) Finite rank plus lattice lengths give a one-shot certificate: W at M = 2n-1 implies all x.\n(iv) E_G-type graph counterfeits pass the FE, trivial zeros and degree, have non-integral but mostly nonnegative N^E, and are Weil-negative at finite quantized horizons. The horizons are zero readouts.\n(v) B24's two-bump identity holds exactly.\n(vi) Per-cycle-length PSD splits with free arch/pole/identity shares fail even in an RH-true world. They fail early (M=9 at n=40), where the form is O(10) PD, at a scale that grows with n.\n(vii) Nothing transfers. Zeta has no length lattice and, under RH, no exact null vector at any x (Jensen vs N(T)). The only non-tautological per-prime transfer is B18 and is killed on the battery.\n\nSuggested ledger entry (narrowed C-Ihara):\n'In the finite-rank, lattice-length Ihara world, B1, B2, B5, B22, B24 and the no-transfer (local-PSHR-type) split barrier all hold for Ramanujan graphs. The per-prime split fails there at an O(1)-PD scale, so split failure is not only a near-null effect. Finite rank makes R9 vacuous. None of this bears on mechanism existence, because the random-graph world has no proof mechanism.'\nThe B19 item and the 'barriers do not discriminate worlds' consequence should NOT enter the ledger.",
 "next_step_if_survives": "It does not survive. The most informative follow-up is to calibrate against a solved world that has a PROOF, not a random one.\n- Take LPS graphs X^{p,q}, which are Ramanujan by Deligne via Eichler-Shimura / Jacquet-Langlands, and their function-field analogue (curves over F_p).\n- Map each step of the known proof (finite-dimensional H^1 with Frobenius, integrality of traces, Rankin-square/tensor-power amplification over a monodromy family, Castelnuovo-Severi) onto the ledger barriers.\n- Record which barrier each step evades, and whether every evasion uses finite rank or a length lattice, both of which zeta lacks.\nIf every known Ramanujan/RH proof in solved worlds is either finite-rank-cohomological or existence-only (MSS), that is a precise, citable transfer barrier; the current wording is not.\n\nCheap Lean win: the fiber theorem plus the integer statement 'rank D T_79 D = 78 and all leading minors of D T_78 D are positive' for a fixed n=40 graph is a FiniteDecide showcase.\n\nAlso report the E[1,0,14] x=95 battery conflict to the harness owner (do not edit the harness)."
}
```

### maass_selberg_schur_barrier (wildcard)
- survives adversarial review: False; prediction matched: True; claimed barrier: B2 + R15 instance, and a NEW sharpened subclass B-MS, 'automorphic Gram positivity is one strip too far'.

Statement. Let phi(s)phi(1-s) = 1, phi real, with growth index 1. For T > 1, the Maass-Selberg/Lax-Phillips truncation Gram K_T^phi is PSD on all finite sets exactly when every pole of phi in Re s > 1/2 is real, simple, with positive residue. The Schur (T^{2s-1}-contractive) part is automatic by Phragmen-Lindelof.

For phi_L = Lambda_L(2s-1)/Lambda_L(2s), this is exactly 'Lambda_L has no zeros with Re > 1':
- it holds unconditionally for every Euler product;
- strip zeros, on or off the line, become Blaschke ZEROS of phi_L, or rank-one-invisible poles at rho/2 with Re < 1/2;
- |phi_L| > 1 never occurs without a pole (no independent Schur failure);
- the T > 1 threshold is universal (at T = 0.5 even zeta fails).

Counterfeit consequence: DH is not detectable. Its first Re > 1 zero needs >= 20 primes up to 157 simultaneously phase-aligned, a heuristic height of order 1e15 or more, and it is absent for t <= 400 (min |D| on sigma = 1 is 0.23). When detection does happen (synthetic Re rho = 1.1 zero), it is a zero readout (B2) localized at rho/2, with T* ~ (|r|/eps)^{1/(Re rho - 1)}, unrelated to x. Positivity lives on Re s > 1/2 for Lambda(2s), i.e. Re > 1 for L: an R15 instance at the maximal possible distance from the line.

Relation to other barriers. The E[1,0,5] stretch adds a K1/R6 converse lookup: E is a matrix entry of the class-group scattering matrix, not a channel.

Requirement for the ledger: any spectral/scattering certificate whose denominator L-function is evaluated at 2s, or at s with the spectral line at Re = 1, can at best reach edge-of-strip nonvanishing (the Sarnak / Gelbart-Lapid level).; barrier confirmed: False

MAASS-SELBERG / SCHUR BARRIER: wave 5 report

The short version: the idea is dead, but for a clean, provable reason. The Maass-Selberg Gram positivity only knows whether Lambda_L has zeros with Re > 1. That holds for every Euler product for free, and it cannot see anything inside the critical strip.

Files are in scratchpad/hengine/w5/maass_selberg_schur_barrier/:
- PREREG.txt, timestamped before any numerics
- gate1.py / .log
- mscore.py
- fe_check.py
- zerosearch.py (+ Dscan.npy)
- gram.py, with logs gram_zeta.log, gram_rest.log, gram_rest2.log
- prec_probe.py
- ldl_cert.py / .log
- spectral_id.py / .log
- extras.py
All processes were killed or had finished, and no repo or harness file was modified.

1. FORMULA GATE (passed). The sesquilinear Maass-Selberg relation, with w* = conj w, is
K_T(s,w) = [T^{s+w*-1} - phi(s)phi(w)* T^{1-s-w*}]/(s+w*-1) + [phi(w)* T^{s-w*} - phi(s) T^{w*-s}]/(s-w*),
with E = y^s + phi y^{1-s} + ..., phi = xi(2s-1)/xi(2s), and the constant term removed for y > T.
- It matches direct integration of Lambda^T E_s times conj(Lambda^T E_w) over the truncated fundamental domain F_T for SL2(Z) at T = 2.
- Relative errors are 1e-31 at 0.8+2i, 0.7+5i, the off-diagonal pairs (0.8+2i, 1.1-3.5i) and (0.3+4i, 0.9+i), and 2e-15 at s = 1.3 (the finite offset used for a real diagonal).
- The Fourier normalization was checked by invariance under z -> -1/z to 1e-31.
- The Iwaniec proposition number is unverified. It is not in the cache, and the web search budget was exhausted.

2. THEOREM. The main facts:
- Rescaling: K_T^phi(s,w) = T^{s-1/2} T^{w*-1/2} K_1^{psi}(s,w) with psi = phi(s) T^{1-2s}.
- FE covariance: K(s,w) = phi(s) K(1-s,w), so Re s < 1/2 adds nothing beyond rank-one rescalings.
- Schur part is automatic: phi * Blaschke(poles) * T^{1-2s} is Schur on Re s > 1/2 for T >= 1 by Phragmen-Lindelof, since |phi| = 1 on the line and the function is bounded.
- Sufficiency: the Parseval/contour identity K = (1/4pi) Int G_s conj G_w + Sum r_p c_p(s) conj c_p(w) holds for T > 1. It was checked to 5e-8 .. 5e-6 at T = 2 for zeta, including r = 3/pi, and for chi_-4. It FAILS at T = 0.5, where K(s,s) = -2.08 for zeta and -0.94 for chi_-4.
- Necessity: diagonal blow-up near a pole. A non-real pole always gives K(s,s) -> -infinity. For a real pole the |s-p|^{-2} coefficient is r - r^2 T^{1-2p}/(2p-1), which is positive exactly when r > 0, because Schur-ness forces r <= 2p-1. Poles of order >= 2 always violate PSD.

Corollary for phi_L:
- Violations come only from zeros of Lambda_L with Re rho > 1, which put poles at rho/2.
- Strip zeros become Schur-allowed zeros of phi_L at (1+rho)/2, or invisible poles at rho/2 with Re < 1/2.
- For Euler products, PSD is unconditional.
- For DH, no independent |phi| > 1 failure exists; on the grid, max |phi * Blaschke| = 0.977. So the only class is B2 (zero readout of Re > 1 zeros) plus R15.

3. COUNTERFEIT GATE.
- FE checks: zeta, chi_-4 and DH satisfy phi(s)phi(1-s) = 1 to 1e-30. DH(kappa=0) fails (0.83-0.09i, ...), so it is reported separately as an FE-violation detection only.
- DH zeros with Re > 1: none for t <= 400; min |D| on sigma = 1 is 0.2306. The Kronecker count says the first one needs >= 20 primes ≡ 2,3 mod 5 (up to 157) perfectly aligned at sigma = 1, 29 at sigma = 1.02 and 4457 at sigma = 1.1, so its height is heuristically of order 1e15 or more.
- Gram results (the full lambda_min(T) table is in test_and_outcome):
  - zeta, chi_-4 and DH are PSD on 77-point grids for T from 1.01 to 200. mp LDL gives 0 negative pivots; zeta at T = 1.01 needed dps 250.
  - The DH strip pole 0.4043+42.85i appears only as an EXACT null direction with its FE partner 0.5957-42.85i. It is not a negative direction.
  - The synthetic Re rho = 1.1 zero gives lambda_min between -51 and -6 at every T, localized at Im 20 (the pole ordinate) and its FE image, with T* ~ (|r|/eps)^{10}.
- T*(DH) does not exist in range. Where detection does happen, it tracks the depth and ordinate of the Re > 1 zero, never x.
- No positive surprise, so battery was not run. The predictor is equivalent to the 'always +' baseline, which has 60 misses.

4. STRETCH (argument only). The Q(sqrt -5) scattering matrix diagonalizes over class-group characters into Euler-product channels (Efrat-Sarnak 1985, unverified). E[1,0,5] is a matrix entry averaged over channels, not a channel. So its failure is a converse-theorem lookup (K1/R6), and its Re > 1 zeros (DH 1936) need 7 or more aligned primes, so they are also out of range.

BARRIER ENTRY: B-MS, 'one strip too far'. This is an R15 instance plus B2. The new, sharpened content is the exact equivalence 'MS Gram PSD <=> no zeros with Re > 1'. It matches the known literature ceiling of Eisenstein positivity: Sarnak and Gelbart-Lapid edge nonvanishing and lower bounds (both unverified citations).

Flagged citations: Iwaniec §6.4 proposition number; Efrat-Sarnak 1985; Sarnak 2004; Gelbart-Lapid 2006; the DH-function statement that it has sigma > 1 zeros; Balanzario & Sanchez-Ortiz 2007.

conjecture1_proved = False.

**Skeptic:**

```json
{
 "angle": "WAVE 5 skeptic review of maass_selberg_schur_barrier. The proposal treats the Maass-Selberg Gram K_T^phi of truncated Eisenstein series, with phi_L = Lambda_L(2s-1)/Lambda_L(2s), as an \"automorphic Gram positivity\" certificate. It claims that PSD holds exactly when every pole of phi in Re s > 1/2 is real, simple and has positive residue, and so it sees only zeros of Lambda_L with Re > 1. My own code is in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/maass_selberg_schur_barrier_skeptic/ (core.py, t1..t8 plus logs). I did not use the harness or the proposer's code, except to cross-check the DH coefficients.",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "As a mechanism it is dead, and the proposer says so (alive=false). The Euler product is used only linearly, only where it converges absolutely (Lambda_L(2s) != 0 for Re 2s > 1), and only to fix the sign of one residue. The mechanism goes through verbatim for DH: it gives a PSD Gram for DH at every T I tested (my run: T = 2 and 200), with 0 negative eigenvalues at dps 40. It fails R1, R2, R3 and R15 (positivity on Re s > 1/2 for Lambda(2s) means Re > 1 for L). For SL2(Z) the positivity is also circular in a trivial way: K_T is literally an L^2 Gram matrix, so PSD for zeta is automatic and tests nothing.",
  "The CLAIMED GENERAL THEOREM IS FALSE AS STATED. The sufficiency claim ('real, simple, positive-residue poles => PSD for all T > 1') and the consistency claim ('Schur-ness forces r <= 2p-1') both fail once phi has 2 or more real poles. Counterexample (t2_multipole.py): phi = phi_zeta * (s-(1-p))/(s-p), p = 1.5. It satisfies the FE, |phi| = 1 on the line, bounded growth, and S_T = phi_zeta*b_1*T^{1-2s} is Schur (sampled sup 0.991). Its poles at 1 and 1.5 are real and simple with residues 3/pi and 5.4737 > 0. Yet |s-p|^2 K(s,s) converges to r - r^2 T^{1-2p}/(2p-1): -9.2119 at T = 1.01, -4.930 at T = 1.2, -1.184 at T = 1.5. My numbers match the asymptotic to 7 digits, so K(s,s) -> -infinity and the kernel is not PSD for T < 1.654. For p = 1.2 it is still negative at T = 3 (critical T = 3.434); for p = 2 the critical T is 1.204. What Schur-ness actually forces is r <= (2p-1)T^{2p-1}/|B_{P minus p}(p)|, which is weaker than needed. So the claimed contour-shift identity K = int|G|^2 + sum r_p c_p c_p* cannot hold for such phi. The correct condition is at least r_p <= (2p-1)T^{2p-1} for every p, probably a full Pick-type matrix condition, and it depends on T. That also refutes the claim that the T > 1 threshold is universal. The phi_L corollary survives only because Euler products have at most one real pole (s = 1, with r <= 1 by Schur), and DH's poles in Re s > 1/2 are non-real, where the necessity argument is correct.",
  "The sufficiency direction is not a proof. It is a contour-shift identity checked at 3 point pairs at T = 2 (5e-8 .. 5e-6 relative), and as shown above it is false in general. The corollary's 'plus sign conditions on real ones' is likewise insufficient when there are several real zeros with Re > 1.",
  "Unlabelled prereg miss. Prediction (b) said: 'For fixed grids K_T is PSD for T large regardless of phi... T* is a SMALL-T threshold'. The report then gave T* ~ (|r|/eps)^10, which is about (0.0881/0.05)^10, roughly 3e2. My T-scan of synth_off on the proposer's exact 77-point grid (t8_synth_T.log) finds 1 negative eigenvalue at every T tested up to 1e14: lambda_min = -17.5 (1e3), -103.9 (1e5), -34.6 (1e8), -5.81 (1e10), -1.28 (1e14). The negative diagonal at the 0.55+20.05i probe only turns positive between T = 1 and 1e8 (t4_diag.log). So T* is not small and does not follow the stated law, yet prediction_matched=true.",
  "Minor numerical correction. Min |D(1+it)| for 0 <= t <= 400 is <= 0.1839 at step 0.02, not 0.2306; the proposer's step of 0.25 missed the minimum. The conclusion is unchanged."
 ],
 "prereg_honored": true,
 "counterfeit_check": "- **DH is not detected** (reproduced independently). My DH coefficients match the harness: a(2) = kappa = 0.2840790438404123. FE and |phi| = 1 on the line hold to 1e-30. The strip zero 0.808517182+85.699348485i gives a phi pole at 0.404258591+42.849674243i, which lies in Re s < 1/2 and is a rank-one rescaling of its FE partner.\n- **No DH zeros with Re > 1 up to height 400.** An argument-principle count on the rectangle 1 <= sigma <= 3, 0 <= t <= 400 (left side step 0.02, t6_dhzeros.log) gives total winding/2pi = -9e-11, i.e. 0 zeros. Conjugate symmetry covers t < 0.\n- **Kronecker count** (t7_kron.log): reaching |arg| = pi - 2 arctan kappa = 2.58802 needs at least 20 primes \u2261 2,3 mod 5 (up to 157) at sigma = 1, 29 (up to 257) at sigma = 1.02, and 4457 (up to 91957) at sigma = 1.1, all perfectly aligned. I also checked that each prime contributes at most 2 arctan(p^{-sigma}).\n  - My own alignment heuristic puts the first zero with Re > 1 even higher than the proposer's 1e15-1e20: around 10^34 for alignment within \u00b10.3 rad.\n  - Either way, DH is caught only in principle, and only by a zero readout at Re > 1 (B2).\n- **Existence of DH zeros with Re > 1 is unverified.** That DH has infinitely many such zeros is, I believe, Saias-Weingartner, Acta Arith. 140 (2009): Dirichlet series with periodic coefficients that are not P(s)L(s,chi). This is UNVERIFIED: it is not in the lit cache and the web-search budget was exhausted.\n- **DH(kappa=0)** is only an FE-violation detection, as the proposer says. I did not rerun it.\n- **Synthetic Re > 1 control:** synth_off reproduces the proposer's numbers exactly: lambda_min = -9.8348 (T = 2) and -9.00857 (T = 200), 1 negative eigenvalue, 3 negative diagonals.\n- **Controls:** zeta and DH give lambda_min of about -1e-38..1e-41 at dps 40. This is dps noise; the proposer saw about 1e-33 at dps 34. There is also an exact null pair from K(s,.) = phi(s)K(1-s,.).\n- **Non-real-pole necessity asymptotic:** confirmed to 4 digits, e.g. |s-p|^2 K(s,s) = -0.072408 vs predicted -0.072413 at T = 2, and the same at T = 200 and 1e6.\n- **T < 1 failure without a pole:** confirmed for chi_-4. At T = 0.9, K(s,s) at sigma = 6 and 12 is -0.056 and -0.072; it is positive at T >= 0.99 for sigma <= 12.",
 "numerics_reproduced": "Independent code (core.py). The Maass-Selberg kernel and xi / L(chi_-4) / DH through Hurwitz zeta were written from scratch.\n\n**Gate (t5_gate.log).** SL2(Z) Eisenstein series from my own Fourier expansion. Invariance under z -> -1/z holds to 1.9e-21. I integrated brute-force over the truncated fundamental domain with 2D Gauss-Legendre, 24\u00b2 and 36\u00b2 nodes. I did NOT use the proposer's Parseval step on y in [1, T]; Parseval appears only for the y > T tail, which is about 1e-10 relative. At T = 2 the relative error against MS is:\n\n| s | w | relative error |\n|---|---|---|\n| 0.8+2i | 0.8+2i | 1.1e-15 |\n| 0.8+2i | 1.1-3.5i | 2.6e-15 |\n| 0.3+4i | 0.9+i | 7e-15 |\n\nThese are float64-node limited. The values agree with the proposer's to all 14 printed digits (1.1830380342791; 0.62160445765314 - 0.40527844301543i; 0.26645887927104 + 0.07466085510005i). Gate (a) PASS.\n\n**Grams (t3_gram.log).**\n- synth_off: -9.8348 at T = 2 and -9.00857 at T = 200 (exact match).\n- zeta and DH: no negative eigenvalues above noise at T = 2 and 200.\n\n**Other checks.**\n- Necessity asymptotics: t4_diag.log.\n- DH has no zeros with Re > 1 for t <= 400 (argument principle): t6_dhzeros.log.\n- Kronecker counts 20 / 29 / 4457: t7_kron.log.\n\n**Numbers the proposer did not report.**\n- Multi-pole counterexample to the theorem: t2_multipole.log output is printed in the transcript (eps^2 K = -9.2119 at T = 1.01 for p = 1.5).\n- synth_off stays indefinite up to T = 1e14 (t8_synth_T.log).\n\n**Not re-run.** The spectral-identity integral and the mp LDL at dps 250. For SL2(Z), zeta's PSD is automatic because K_T is an L^2 Gram matrix.",
 "novelty": "Low.\n\n- **Known content.** 'Eisenstein / Maass-Selberg positivity reaches only the edge Re s = 1' is the standard content of:\n  - the Pavlov-Faddeev and Lax-Phillips resonance picture (cached, verified): the zeros of zeta(2s) are resonances in Re s < 1/2, invisible to contractivity;\n  - Sarnak's Maass-Selberg proof of zeta(1+it) != 0 and the Gelbart-Lapid edge bounds (both unverified: not in the cache, and the web-search budget is exhausted).\n- **What is new.**\n  - An explicit characterization for an abstract phi: diagonal blow-up gives necessity for non-real poles and poles of order >= 2.\n  - The sharp observation that strip zeros become Blaschke ZEROS of phi_L in the physical half-plane, so they can never cause a Schur failure.\n  - These are clean and correct.\n- **What is incorrect.** The advertised iff theorem (see fatal flaws).\n- **Stretch argument.** The E[1,0,5] / Efrat-Sarnak argument is unverified and unreproduced. It is also partly misframed: Epstein zeta values are values of Eisenstein series at CM points (E(z_Q, s)), not scattering entries, so 'E has no scalar channel' is true but trivial.",
 "what_is_real": "**What holds, all reproduced.**\n- The Maass-Selberg formula matches brute-force integration over the truncated domain to 1e-14.\n- The rank-one FE identity K(s,w) = phi(s)K(1-s,w) and the T-rescaling identity both hold.\n- For phi_L:\n  - a strip zero rho with 1/2 <= Re rho <= 1 creates only zeros of phi_L at (1+rho)/2 and 1 - rho/2 in the physical half-plane, and poles at rho/2 on the non-physical side;\n  - a non-real pole of phi in Re s > 1/2 forces K(s,s) ~ -|r|^2 T^{1-2Re p}/((2Re p - 1)|s-p|^2), so PSD fails near it (confirmed to 4 digits);\n  - T < 1 fails at large sigma even with no pole.\n- DH has no zeros with Re > 1 for |t| <= 400 (argument principle), and the Kronecker counts make its first such zero astronomically high. So the MS Gram cannot see DH in any computable range; in principle it catches DH only through a zero readout at Re > 1 (B2).\n\n**Correct ledger wording (narrowed, per K7).** B-MS: for phi_L = Lambda_L(2s-1)/Lambda_L(2s) with phi_L having at most one real simple pole in Re s > 1/2 (all Euler products, where it is s = 1 with r <= 1 by Schur-ness):\n- Maass-Selberg Gram positivity for T > 1 fails exactly when phi_L has a non-real pole in Re s > 1/2, i.e. Lambda_L has a zero with Re > 1.\n- It is blind to every zero in the closed critical strip, on or off the line.\n- For Euler products it is unconditional, because the product converges absolutely there.\n\n**Drop from the entry:**\n- the general 'real, simple, positive residue <=> PSD' theorem, which is false with 2 or more real poles (counterexample: phi_zeta*(s+1/2)/(s-3/2), not PSD for 1 < T < 1.654);\n- 'Schur-ness forces r <= 2p-1';\n- 'T* is small / tracks (|r|/eps)^10' (synth_off is still indefinite at T = 1e14).\n\nIt is an R15 instance: Eisenstein positivity is the edge-of-strip nonvanishing level. conjecture1_proved = False.",
 "next_step_if_survives": "It does not survive, so no follow-up on this angle.\n\n- **Ledger entry.** Record B-MS with the narrowed wording above as a sub-case of R15 plus B2, and add the multi-pole counterexample to corrections.\n- **Most useful follow-up (cheap).** Determine the true positivity condition for several real poles, presumably a Pick-matrix condition on the residues r_p and the scale T^{2p-1}.\n  - Do this only if some future proposal uses an abstract scattering matrix with residual-spectrum poles, such as Rankin-Selberg or Eisenstein series on higher-rank groups (the Langlands-Shahidi setting).\n  - It will not reach the strip either.\n- **Direction to prefer.** Any automorphic Gram route to W(x) has to put the Weil-window L-function in the numerator's critical strip on the spectral line, not in the denominator at 2s. The only known objects that do this, Rankin-Selberg unfolding and triple products, give central-value or moment positivity. That matches the ledger's P6 lead central_value_nonnegativity_families, which should be screened against R13-R16 before anyone spends compute on it.\n- **Citations to verify when the search budget allows:** Saias-Weingartner 2009 (DH has zeros with Re > 1), Sarnak 2004, Gelbart-Lapid 2006, and the Maass-Selberg proposition number in Iwaniec, Ch. 6."
}
```

### strip_reach_xU_theorem (barrier_hunt)
- survives adversarial review: False; prediction matched: False; claimed barrier: STRIP-REACH BARRIER (two tiers). Everything is finite-section N=16. Strip-side certificates are explicit test functions, and line-side values are interval-checked, both at dps 40. The Galerkin tail is not certified.

(i) FAMILY ROUTE (larger-window Odlyzko-Poitou, S15). The route proves W(x) for every pole-kept degree-2 zeta*L(chi_d), ramified included, at x=6.5 (both sectors) and x=6.75 (even), Arb-certified per base. It FAILS at every window x'<=151 at:
- x=6.875 and 7.0, even sector (eps*=(-1,1,-1), N_min=13);
- x=7.25, 7.5 and 8, odd sector (eps*=(-1,1,1,-1), N_min=11; at x=8 failing vertices are certified to 151 and found by B&B up to 307).
So x_U(even) is in [6.75, 6.875) and x_U(odd) is in [6.5, 7.25); odd 6.75 and 7.0 are OPEN, with B&B gaps unclosed after about 2500 nodes. The adversarial extensions are heavily ramified, with N_min >1e8 and true slack >=16. Since CRT realizes every finite pattern and the strip functional does not depend on d, the failure is pure conductor blindness: answer (b). There is no match to LEB or euler-rand d2 (answer (a) is rejected for the family).

(ii) BALAYAGE REACH LAW (new). Even with each genuine L's own pattern, strip-positive (edge-positive) test functions certify W(x) only while m_L(x) >= delta_L(x'). Here delta_L(x') >= delta_L(inf) = 2*pi*inf_v sum_gamma sech(pi(gamma-v)), which is fixed by the low zeros. Because m_L(x) -> 0, every genuine L has a finite strip reach at ANY window:
- zeta: x_bal in (5.1, 5.2) (floor 1.304e-18; at x'<=151 about 4.7);
- zeta_Q(i): fails at x=8 for x'<=151 (certified), extrapolated to about 9.7 as x'->inf;
- the tiniest conductors bind, consistent with B23 and R15.
Wider-than-line positivity is blind not only to counterfeits but also to genuine low zeros' sech clouds.; barrier confirmed: False

WAVE 5 / strip_reach_xU_theorem. Directory: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/strip_reach_xU_theorem/. PREREG.txt (05:03) predates every script. Code: eng.py (fast Legendre engine = indep.py to 6e-14), bb.py (ternary B&B, box-SDP nodes, p^2 triangle hull), cert.py (mp/mp.iv rebuild with independent quadrature, interval LDL), cert_pos.py (rigorous positive-side certificates from SDP duals). Logs are t0..t6*.log.

1. REPRODUCTION (T0). Wave-4 numbers reproduce exactly (-4.3103e-2 at x=6/x'=12; +0.0221 vertex and +0.166 box at x=8/x'=70). C19 cannot affect S15: the strip class h*h~/cosh(t/2) is exact, and for even real F it is exactly the cone with Re Fhat >= 0 on the closed strip.

2. STRUCTURAL FACTS.
(a) The box SDP equals min over ONE mixed strip test function of max over the box (Sion minimax, since W is affine in both). That is why it saturates at about +0.16 while vertex maxima are much lower. B&B restores per-extension test functions.
(b) Uniformity check: CRT/Dirichlet realize every finite ternary pattern (sieve realizers found, e.g. 31739 for the x'=23 adversary), and mu is d-independent. The family route must therefore beat the worst extension.

3. FAMILY RESULT (T1, T4, T5).
- At x=8 the odd sector fails with eps*=(-1,1,1,-1). Vertex max minus lam: +0.136 (23), +0.098 (47), +0.0955 (79, exhausted after 530 nodes), +0.0891 (151, node limit 600). At larger windows: +0.061 / +0.009 / +0.088 / +0.071 at 173 / 200 / 251 / 307.
- Interval-certified at 23/47/97/151: mu_N > lam_N + 0.068 / 0.049 / 0.047 / 0.045. An independent Neumann basis gives +0.096 / 0.095 / 0.074.
- Ramified extensions are the adversary's main tool (+0.022 with ±1 only, +0.096 with ramified).
- Brackets: x_U(even) in [6.75, 6.875) (6.8125 OPEN); x_U(odd) in [6.5, 7.25) (6.75 and 7.0 OPEN because B&B gaps stay unclosed on the d=-4, d=-8 and (-1,1,1) bases). The positive sides at 6.5 (both sectors) and 6.75 (even) are certified base by base (27 bases each).

4. CONDUCTOR BLINDNESS (T2). The base eps*'s smallest member is d=-11, with slack only 0.057. The adversarial full patterns have N_min >1e8 (the ramified product alone is >=1.5e12 at x'=151), so the true slack is >=16. The prior's answer (b) holds for the family route.

5. BALAYAGE REACH LAW (new; answers the (a) question for GENUINE data). Running the route member by member (conductor shift: only |d| <= e^{ell_max(x)} matter), the obstruction becomes the sech clouds of genuine low zeros: delta_L >= 2*pi*inf_v sum sech(pi(gamma-v)).
- Floors: zeta 1.304e-18; d=-3 2.70e-10; d=-4 1.53e-7; d=5 2.13e-8; d=-7 1.97e-5; d=-8 3.3e-4.
- Member-wise failures with x'<=151: d=-4 at x in (7.5, 7.75], certified at 8 (3.375e-6 > 2.24e-6) and proved at 7.5; d=-3 and d=-11 at 8.5; d=5 by 10.
- Zeta: Weil margin at N=40 is 3.47e-18 at x=5.1 and 1.08e-18 at x=5.2. So no strip certificate at any window can prove W(5.2) for zeta (modulo the Ritz caveat).
- The deficit delta(x') decays slowly (zeta 5.3e-16 at x'=151), so the finite-window reaches sit well below the x'=inf ones.

6. T3. No numerical coincidence with LEB 5.0506 or euler-rand d2 5.776. Zeta's reach (5.1, 5.2) is the nearest value and misses LEB by more than 0.05.

7. BATTERY (T6). 126 agree, 0 catches, 0 false alarms, 26 misses (all on no-FE members, which break the strip inequality), 19 abstentions. Not useful and not sharp. The R11 members LEB, d2 and DH(kappa=1) get false '+' certificates right after their horizons.

8. PREREG SELF-AUDIT.
- Matched: P0, P1 (qualitative), P3, P4, P6, P2's full-pattern N_min and answer (b), and even-sector x_U within P5's range.
- MISSES:
  - P1: the x'=151 margin is +0.089 (N=16) / +0.074 (Neumann), outside [0.005, 0.05]. Ramified options changed the margin by 0.07, more than the predicted <0.05.
  - P2: N_min(base)=11, not >=50, and its slack is 0.057, not >1.
  - P5 odd: bracket unresolved; the even >= odd ordering is unscorable.
  - The path-adaptive question was replaced by the member-wise analysis.

9. LEDGER UPDATES.
- S15 -> certified two-tier barrier (claimed_barrier).
- R15 refined: wider-than-line positivity is blind to genuine low-zero clouds, not only counterfeits.
- C12 correction: Yoshida 1992 IS in the cache. Poitou 1976/77 bibliographic data verified, content unread.
- Open items: close the odd OPEN points (6.75, 7.0) with larger budgets; Arb-certify the Galerkin tail on the line side (the single remaining non-rigorous step on the positive side; the strip side uses explicit test functions); interval-certify the zeta x_bal margins. No harness bugs found. conjecture1_proved=False.

**Skeptic:**

```json
{
 "angle": "strip_reach_xU_theorem (wave 5 barrier hunt): skeptic review. I rebuilt the engine and the branch-and-bound from scratch in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/strip_reach_xU_theorem_skeptic/ (myeng.py, rbb.py, v0-v6 with logs).",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "The proposal says itself that it is dead as a mechanism. It is linear in c (B1), uses no Hecke-quadratic input (R2), and the member-wise route looks up the genuine characters (R6/K1). The Euler product is never used nonlinearly or globally. So survives=false.",
  "Tier (i) fights a strawman. The family route ignores the conductor information that ramification gives for free: a ramified p divides |d|, so log|d| >= sum of log p over the ramified set. No sieve, no lookup and no zeros are needed. I added only that rule (v3b/v3c, my own B&B, N=16). With it, x=7.25 odd eps*=(-1,1,1,-1) is PROVED at x'=59, where the proposer has it FAILING at every window. x=7.0 odd (-1,1,1) is PROVED at x'=37, where the proposer has it OPEN. At x=8 odd, 7 of the 11 bases that were not proved become PROVED. So most of the claimed brackets, x_U(odd) < 7.25 in particular, measure the strawman, not the strip method. The proposer's own T2 shows the adversary patterns carry 3-7 ramified primes, which gives |d| >= 3e4 to 1.5e12.",
  "The claimed 'x=6.875 even FAILS' and '6.8125 OPEN' have no artifact: no log or json in the directory mentions either x. I reproduced 6.8125 as OPEN. I did NOT reproduce 6.875 FAILS. My blind B&B at x=6.875, base (-1,1,-1), with a 2500-node budget found no vertex above lam at x'=79, 97 or 113: the incumbents were -7.7e-4, -2.3e-2 and -3.3e-2, and the open upper bounds about +5e-3 to +7e-3. So x_U(even) in [6.75, 6.875) is unsupported as stated.",
  "Every failure claim is finite-section. A failure needs a LOWER bound on the strip minimum mu, and a Ritz value is only an upper bound. The rigour is also one-sided in N, as shown here: the best ramification-aware vertex at x=8, x'=151 goes from +0.0189 (N=16) to -0.0003 (N=32) to -0.0009 (N=48). Another vertex restores the failure at N=32 (+0.0143), but the small N=16 margins at the brackets (1e-4 to 1e-2 at 6.875-7.25) are not robust. 'Every window x' <= 151' means only the checkpoint grid.",
  "Tier (ii), the balayage reach law, is correct, but it is essentially a corollary of R15 (the balayage identity) plus B20 (m_L(x) -> 0). The strip route's slack is at least a fixed floor 2*pi*inf_v sum_gamma sech(pi(gamma - v)) > 0, while the Weil margin goes to 0. For a single genuine L with q known, the route is also redundant: it still needs a certified lower bound on lam(eps_d, x), and that bound already decides W(x) directly. Its only role is inside the family route at tiny-conductor bases, where it duplicates B23/R10."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Soundness is as claimed. The strip inequality needs the functional equation and zeros in the closed strip. I checked that the edge condition at sigma = 1/2 is necessary and, via the positive-definite product cosh(sigma t)/cosh(t/2), sufficient, so h*h~/cosh(t/2) is exactly the maximal unconditional cone. On counterfeits with a functional equation (E ladder, DH), the route abstains and catches nothing. The battery log (t6.log) shows no false alarms on the controls. It gives false '+' on the no-FE members right past their horizons: LEB from 6, euler-rand d2 from 6, and d1 and DH(kappa=1) from 3. That violates R11. The route goes through verbatim for anything that has an FE and zeros in the strip, and it cannot see line-confinement (R15). It is not circular for the family, but the member-wise tier looks up genuine zeros for the floor. That use is diagnostic, not a mechanism.",
 "numerics_reproduced": "I wrote my own engine (myeng.py). The archimedean term uses a closed form (psi(a/2) plus an explicit tail series instead of log1p), with Gauss-Legendre autocorrelation and an optional mpmath path. It reproduces all 8 t0 line/strip eigenvalues to 10 digits and is stable in nt.\n\nMy own B&B (rbb.py, box SDP built on my matrices, CLARABEL) reproduces the proposer's exact adversary maxima at x=8 odd eps*: +0.13641 at x'=23 and +0.09838 at x'=47, both exhausted.\n\nN-convergence of the certified blind adversary vertices, N=16/24/32/40/48:\n- x'=47: +0.0984 / 0.0959 / 0.0954 / 0.0953 / 0.0951.\n- x'=97: 0.0945 to 0.0950.\n- x'=151: +0.0891 / 0.0796 / 0.0722 / 0.0720 / 0.0716. So the headline 0.089 at x'=151 overstates by about 0.017; the Neumann 0.074 was closer.\nlam(eps*,8) drifts slowly (-2.341259 at N=16 to -2.341791 at N=48). Conclusion: the blind x=8 odd failure is robust.\n\nRamification-aware route: x=8 odd eps* still FAILS on the whole grid 11..151 at N=16 (smallest found margin +0.0056 at x'=113). At N=32 it still fails at x'=97 (+0.0206) and 151 (+0.0143), with purely unramified vertices. The vertex at x'=47 is stable at +0.0335 / 0.0332 / 0.0333 (N=16/32/48).\n\nZeta balayage, mp dps 45, my Legendre engine:\n- Floor 2*pi*S(0) = 1.3036323e-18, and it is the minimum over v in [0,7].\n- Weil margin at N=24/32: x=5.0: 9.70e-18 / 9.50e-18; x=5.1: 3.05e-18 / 2.94e-18; x=5.2: 9.77e-19 / 9.27e-19 (< floor); x=5.3: 2.97e-19 at N=32.\nThese Ritz values sit below the proposer's harness values, which use a Neumann-cosine basis and converge algebraically (3.47e-18 and 1.08e-18). The bracket (5.1, 5.2) is reproduced. The failure end at 5.2 is in the rigorous direction, modulo arithmetic. The success end at 5.1 is not rigorous.\n\nStrip deficits delta(20) = 1.19234e-12 and delta(151) = 5.55754e-16 (N=16) match the proposer to 6 digits.\n\nPrereg: PREREG.txt mtime 05:03:28 predates eng.py (05:04:29) and t0.py, and the misses are honestly listed. One item was left unscored: P5's 'ramified patterns lower x_U by at most 0.25'. The ramified options are in fact what move the odd bracket.",
 "novelty": "Low. The family x_U brackets are new numbers, but they belong to a deliberately conductor-blind route. The unconditional-vs-GRH gap from the cosh(t/2) weight is classical: see the Odlyzko 1990 survey (lit cache explicit_formula_linear_programming#0) and Omar 2000 (Acta Arith. 95) in the same cache entry. Stating it as a per-L reach floor, 2*pi*sum sech(pi*gamma), is a clean repackaging of R15 and has not been searched (unverified). Yoshida 1992 is in the cache (weil_explicit_positivity), which confirms the C12 correction. Poitou's content remains unread.",
 "what_is_real": "1. The engine, the exact vertex maxima and the rigorous positive-side certificates at x=6.5 (both sectors) and 6.75 (even) are real. I checked that all 27 bases are True in each cert_pos json. They are finite-section on the line side only, which is disclosed.\n\n2. The unconditional Odlyzko-Poitou strip route does NOT reach x=8 in the odd sector at base eps*=(-1,1,1,-1), at any checkpoint x' <= 151. This holds even when ramified primes are credited to the conductor, and the margin survives N=32. That is the robust, narrowed family barrier. Suggested ledger wording: 'Ramification-aware larger-window strip route: x=8 odd fails at every checkpoint to 151 (N=16; N=32 at 97/151); x=7.0 and 7.25 odd are proved; 7.5 odd and 6.875/7.0 even are open. The blind-route brackets 6.875 even and 7.25 odd are conductor-blindness artefacts.'\n\n3. The balayage floor is correct: for each genuine L, the conductor-scalar strip route has slack at least 2*pi*inf_v sum sech(pi(gamma - v)). For zeta this floor is 1.3036e-18, and the route fails at x=5.2 at every window, because the Legendre Ritz upper bound 9.27e-19 is below the floor. This is a correct negative statement, but it is a corollary of R15 and B20.\n\n4. S15 should be updated to: the strip route stalls between 7.25 and 8 once ramification is credited. The claim 'stalls in [6.5, 7.25)' holds only for the blind route.",
 "next_step_if_survives": "It does not survive. Most informative next step, cheap: settle the ramification-aware x_U with N=32 nodes and interval lower bounds on mu at the failing vertices. That turns 'x=8 odd fails' from finite-section into a genuine certificate: Schur-tail lower bound for the strip minimum at the explicit ext, plus a lower bound for lam. Also resolve the open 7.5 odd and 6.875/7.0 even bases. Then retire S15/Q13, because the question has become small-number bookkeeping with no mechanism content. Energy should go to ledger P1 (cascade law) and P2 (Lean kill-switch lemmas). Harness note, not a bug: form.Q's default Neumann basis gives near-null Ritz values about 20-30% above the Legendre ones at N=24-40 (zeta, x=5-5.2). Near-null horizon brackets should be computed with the polynomial basis."
}
```

### defect_balance_zoo (micro_experiment)
- survives adversarial review: False; prediction matched: False; claimed barrier: NO SINGLE COUNTERFEIT ANATOMY (a negative calibration result, numeric: float N=128/256 plus mp dps 60 at N=120/160).
- Four E-ladder counterfeits and both barrier members fail by O(1)-vs-O(1) cancellation: |Q_Def(v_cf)| is 0.45-4.2 and matches Q_ref(v_cf) to about 1e-4.
- DH fails by perturbing the reference's near-null cascade:
  - Q_Def(v_cf) = -0.0281;
  - v_cf has 98.4% of its weight on Re L(chi_5)'s two lowest eigenvectors (5e-8, 4e-3), with cos(v_cf, v_ref) = 0.978;
  - Q_Def(v_ref) = +1.2e-3.
- Consequences:
  - A mechanism must cover both regimes. Lower-bounding the genuine form away from its near-null set is not enough, since DH lives inside it.
  - Near-null-perturbation mechanisms are not irrelevant.
  - The R criterion is nearly tautological near the horizon (R = 1 + lam/|Q_Def|).
  - The local/global split of the Euler defect does NOT predict the anatomy: the local-defect LEB and a2-flip are balanced, while the global-defect DH is perturbative.
- Defect-size horizon laws (n0, sup|dc|/sqrt n, M2) fail with LOO >= 49%.; barrier confirmed: True

WORK DIR: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/defect_balance_zoo/

Files:
- PREREG.txt: mtime 05:01:10, before every script.
- balance.py and run_float.log: all float rows, N=128/256.
- dh_mp.py, dh_N120_even.log and dh_extra.log: DH mp dps 60, N=120 both sectors, N=160 even.
- loo.py, loo.log and loo.json: the secondary fit.
- The JSON outputs.

The harness was used read-only and cg.py was reused; no harness bugs were found. No processes are left running; every job ran in the foreground and has exited.

S19 REPRODUCED: E[1,0,5], x=19.87, N=128, ref zeta_H/2 gives Q_ref(v_E) = +0.9632 and Q_Def = -0.9632.

1. PER-MEMBER VERDICTS. The full table is in test_and_outcome.

The verdict rule is: BALANCED iff R is in [0.8, 1.25] and |Q_Def(v_cf)| >= 0.1, under both refs and at both x.
- E[1,0,5]: BALANCED. |Q_Def| 0.96 (zH/2) or 1.87 (zK).
- E[1,1,6]: BALANCED. 1.68 or 4.19; odd sector fails first.
- E[1,0,6]: BALANCED. 0.72 or 1.44.
- E[1,0,14]: BALANCED. 1.42 or 4.22. zeta_K(-56)'s margin is 1.9e-6, yet v_cf puts only 2.3% of its weight there.
- zetaK(-20)[a2=-1]: BALANCED. Odd sector; |Q_Def| 0.45 or 1.61; R at x_h+1 is 0.870 or 0.966.
- LEB: BALANCED, marginally. Odd sector; |Q_Def| 2.84 or 1.51; R at x_h+1 is 0.889 or 0.8084.
- DH: PERTURBATIVE. |Q_Def| = 0.0281 at x = 30.621 and 31.571, with N=120 and N=160 agreeing to 3e-5 relative.
  - DH's odd sector would be balanced (0.238), but the even sector fails first.
  - Galerkin caveat: at N <= 160, x_h+0.05 is still pre-crossing (lam = +1.6e-30), as B21 predicts. |Q_Def(v_cf)| is the same at x_h+1, where lam is negative, so the verdict does not depend on it.
  - The DH step took about 8 minutes, well inside the 30-minute time box. It is not INCOMPLETE.

2. N-CONVERGENCE (N=128 to 256).
- The maximum relative change is 5.7e-4 in R and 4.9e-4 in Q_Def (a2-flip vs zK). Every E-ladder row is <= 1.1e-4.
- All members count as converged (< 1%).
- lam_cf itself is not converged at x_h+0.05. E[1,0,14] even changes sign between N=128 and 256; this is the known Ritz upward bias.

3. R14 REFERENCE INVARIANCE.
- No verdict flips between references. For DH this is vacuous: Re L(chi) and Re L(chibar) coincide, so there is only one ref.
- R14's no-comparison content still shows. Q_ref1(v_cf) - Q_ref2(v_cf) is O(1): 0.90, 2.51, 0.72, 2.79, 1.16, 1.33.
- Anatomical descriptors are ref-dependent. The cos(v_cf, v_ref) values are:
  - LEB: 0.60 (zK) vs 0.996 (zH/2) at x_h+0.05, and 0.13 vs 0.98 at x_h+1.
  - a2-flip: 0.97 vs 0.80.
  - The sign of Q_Def(v_ref) also changes: LEB +0.11 vs -1.45; a2-flip -0.17 vs +0.03.
- So "does the defect attack the genuine minimizer" is not a reference-invariant question. Only |Q_Def(v_cf)| (about Q_ref(v_cf)) being O(1) is invariant for these members.

4. OUTCOME RULE. Not all balanced.
- The PERTURBATIVE member is DH alone. It is NOT one of the local-defect barrier members, so the local-perturbative vs global-balance taxonomy proposed in the assignment is falsified as stated.
- The observed split is by the counterfeit's own near-nullness:
  - DH's margin decays like e^{-2.4x} (C2), and it inherits L(chi_5)'s near-null pair, which has eigenvalues 5e-8 and 4e-3 at x=30.6.
  - The Epstein zetas and the barrier members have margins of O(1e-3) or more, and they fail by O(1) cancellation.
- I did NOT add the requirement "near-null-perturbation mechanisms are irrelevant to counterfeits"; DH is a counterexample.
- Proposed replacement ledger requirement: "A mechanism must lower-bound the genuine Euler form BOTH on directions where it is O(1) (the E ladder, LEB, a2-flip; |Q_Def(v_cf)| 0.45-4.2) AND to within ~3% of the cascade scale inside the reference's near-null cascade (DH: Q_Def(v_cf) = -0.028, weight 0.984 on the ref's two lowest modes)."

A further correction to S19's framing: even among balanced members, v_cf is not "far from the near-null direction."
- E[1,0,5] puts 34.5-35% of its weight on zeta_K(-20)'s lowest mode (m = 4.9e-3), and E[1,0,6] puts 45% on its lowest mode.
- Only E[1,1,6] and E[1,0,14] are nearly orthogonal to it.

5. SECONDARY LOO (expected to fail; it did).
- Features, taken against ref1: n0 = 4 for the E ladder and DH(k=0), and 2 for the others; S = sup|dc|/sqrt n; M2 = sum dc^2/n.
- 7 members:
  - 4-parameter fit: LOO median 66%; LEB's error is 2.3e5 (extrapolation blow-up; the fit is exactly underdetermined in spirit).
  - 1-feature fits: log n0 mean 111% / median 65%; S 176% / 78%; log M2 125% / 33%.
- 11 members (adding the DH kappa variants and euler-rand):
  - 4-parameter fit: mean 51%, median 49%.
  - 1-feature fits: 90% / 292% / 125%.
- E[1,0,5] and E[1,0,14] have nearly identical S (1.46 vs 1.40) but horizons 19.8 vs 94.4. The defect size carries no horizon information.

6. K9 SELF-AUDIT OF PREREG MISSES. The DH miss is decisive, so prediction_matched = false.
- (a) DH predicted BALANCED (60%) with |Q_Def| 0.1-2. Observed PERTURBATIVE, 0.028. MISS, and the most important one.
- (b) Q_Def(v_ref) > 0 for every member. Missed for the a2-flip vs zK (-0.168, and -0.149 at x_h+1), the a2-flip vs zH/2 at x_h+1 (-0.014), and LEB vs zH/2 (-1.45 and -1.64). MISS.
- (c) v_cf weight < 5% on ref modes below 0.05 for the E ladder. MISS for E[1,0,5] (0.35) and E[1,0,6] (0.45); matched for E[1,1,6] and E[1,0,14].
- (d) |Q_Def| ranges. Outside the predicted range: E[1,0,5] vs zK (1.87 > 1.5), E[1,1,6] vs zK (4.19 > 3), a2-flip vs zH/2 (1.61 > 1). Minor quantitative misses.
- (e) Not predicted: at N <= 160, x_h+0.05 is still pre-crossing for E[1,0,14] at N=128 and for DH.
- Matched:
  - LEB's R at x_h+1 fell in 0.75-0.9 (0.889 and 0.808).
  - The a2-flip and LEB were BALANCED against the default prediction. My deviation was right: the a2-flip failure is in the odd sector, where zeta_K(-20) is O(0.3).
  - The E ladder was BALANCED, with R near 1 as the a-priori identity forces.
  - N-convergence was < 1%.
  - No R14 flips.
  - The secondary law failed, and every 1-feature LOO exceeded 20%.
- K9 note: R's near-1 values are tautological (R = 1 + lam/|Q_Def|), so the BALANCED verdicts carry information only through |Q_Def| >= 0.1, which equals Q_ref(v_cf) - lam. The default-prediction clause "R far from 1" can only be triggered by deep negativity, as LEB at x_h+1 nearly did (R = 0.808). That is not perturbation.

conjecture1_proved = False.

**Skeptic:**

```json
{
 "angle": "defect_balance_zoo (wave 5 skeptic). This is a calibration measurement of where each counterfeit fails relative to a genuine reference, Q_cf = Q_ref + Q_Def. It is not a mechanism.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "Not a mechanism, by the proposer's own statement. The Euler product enters only through the choice of genuine reference. The split is linear in c, so as a mechanism it dies by B1, B24/R14 and R6. The default survives=false applies.",
  "Wrong attribution in the barrier text: 'DH inherits L(chi_5)'s 2-dimensional near-null cascade' is backwards. DH has its own cascade, 5 modes per sector and far deeper. Even sector at x=30.62 (my mp N=48): 3.9e-28, 2.9e-21, 6.8e-16, 1.6e-10, 4.0e-6, then 0.013. Odd sector at 31.57: 3.9e-25 ... 5.6e-5, then 0.089. The reference has only 5e-8 and 4e-3, then 0.686 (odd: 1.7e-5, then 0.186). The reason is that Re L(chi) for a complex chi counts the zero set Z(chi) union Z(chibar), so it behaves spectrally like half of a degree-2, conductor-25 object. That makes the only available DH reference analytically mismatched with DH, even though its Gamma factor and q agree formally.",
  "The two-regime taxonomy is a threshold choice on a continuum, not a dichotomy. Weight of v_cf on the reference's low modes: 0 (E[1,1,6], a2-flip, LEB), 0.01-0.02 (E[1,0,14]), 0.35 (E[1,0,5]), 0.45 (E[1,0,6]), 0.84 (DH odd sector, |Q_Def| = 0.236), 0.98 (DH even). The DH odd sector is intermediate.",
  "'|Q_Def| matches Q_ref(v_cf) to 1e-4' and R ~ 1 are tautological near the horizon: R = 1 + lam/|Q_Def|, which the proposer flagged in the prereg.",
  "The proposed replacement requirement (lower-bound the genuine form both on O(1) directions and inside the reference's near-null cascade) is already implied by R4, exactness on the whole cascade. Its only new content is negative: do NOT add P4's 'far from the near-null cascade' requirement.",
  "Secondary LOO horizon law: I did not reproduce it. With 7-11 points and a 4-parameter fit it is underpowered, so its failure is nearly guaranteed and carries little information."
 ],
 "prereg_honored": true,
 "counterfeit_check": "This is a measurement on the counterfeits themselves, so 'going through verbatim for a counterfeit' does not apply. The circularity check passes trivially: nothing here claims to prove positivity. R14 applies: the anatomy descriptors (cos, sign of Q_Def(v_ref)) depend on the reference, as the proposer also found. Only |Q_Def(v_cf)|, which is about Q_ref(v_cf), is reference-invariant in magnitude class.\n\nThe key robustness question is whether DH's small |Q_Def(v_cf)| = 0.028 is just an artefact of the absolute 0.1 threshold, with DH's defect small overall. It is not:\n- DH's defect is O(1) as an operator. Its spectrum is [-2.22, +2.59] at N=60 and [-2.62, +3.20] at N=90, and max|dc(n)|/sqrt n = 0.79 (at n=6).\n- The normalized ratio rho = |Q_Def(v_cf)|/|lambda_min(Q_Def)| is about 0.011-0.013 for DH (even sector). For every other member it is 0.17-0.84: E[1,0,5] 0.29-0.32, E[1,0,6] 0.17-0.22, E[1,1,6] 0.80-0.83, a2-flip 0.19-0.45, LEB 0.66-0.84.\n- DH's odd sector is about 0.10.\n- So the DH outlier survives normalization.\n\nSkeptic side test (prereg file SKEPTIC_PREREG.txt, written before the runs). I predicted that anatomy tracks the counterfeit's Gamma/q cascade estimate d(x_h/q)^{1/d}:\n- DH(kappa=1), no FE, at x=2.98, even sector: |Q_Def(v_cf)| = 0.355, BALANCED. My prediction matched.\n- DH(kappa=0), no FE, at x=20.126, odd sector: lam = -6.7e-4 and |Q_Def(v_cf)| = 1.12, BALANCED. My prediction missed: its own spectrum has no cascade (0.013, 0.06, ... even; -6.7e-4, 0.088 odd).\n\nThe refined reading, which the data support, is this. The perturbative anatomy occurs only when the counterfeit is itself near-null the way a genuine L-function is, and that needs the FE plus a small analytic conductor. DH is the only such zoo member.",
 "numerics_reproduced": "I wrote independent code in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w5/defect_balance_zoo_skeptic/: wl.py (float) and mpwl.py (mpmath). It does not import the harness, and it differs from the harness path in four ways:\n- orthonormal Legendre basis instead of the cos/sin Neumann basis;\n- archimedean term from Gauss's psi integral in u-space instead of the Loewner closed forms;\n- all coefficients rebuilt from scratch: Epstein lattice counts, Kronecker characters, Satake roots, DH a(n) recursion, and zeta_H(-20)/2 = (zeta_K(-20) + L(chi_-4)L(chi_5))/2 with pole weight 1/2.\n\nValidation:\n- zeta_K(-20) at x=20: 4.549e-3 at N=60, against the harness value 4.532e-3 extrapolated.\n- Coefficients c_E(36) = -7.167, c_E(9)/log 3 = 6, and c_E(6), c_E(14), c_E(21) = 3.584, 5.278, 12.178 all match.\n\nFloat rows (N=60 and 90, fl.log). All match the proposer to 3-4 digits:\n- E[1,0,5] vs zH/2: Q_ref 0.9632, Q_Def -0.9632, Q_Def(v_ref) +1.319, cos 0.587, w 0.345.\n- E[1,0,5] vs zK: 1.868, w 0.354.\n- E[1,0,6]: 0.7227 / 1.440, w 0.452.\n- E[1,1,6] vs zK(-23): 4.189, Q_Def(v_ref) 3.82, cos 0.09.\n- a2-flip vs zK: -0.4539, R 0.870 at x_h+1, Q_Def(v_ref) -0.168, cos 0.965.\n- a2-flip vs zH/2: -1.611, Q_Def(v_ref) +0.032 then -0.0137.\n- LEB vs zK: -2.839, R 0.889 at x_h+1.\n- LEB vs zH/2: -1.506, R 0.8084 (N=60) / 0.8083 (N=90), Q_Def(v_ref) -1.453 / -1.637, cos 0.996 / 0.981.\n\nDH, even sector, x=30.621, mp dps 60. Q_Def(v_cf) by Legendre N:\n- N=16: -0.02054\n- N=32: -0.02711\n- N=48: -0.02801\n- N=64: -0.028166\n\nThe proposer had -0.028140 (cosine basis, N=120) and -0.028139 (N=160), so the agreement is about 1e-3 relative. Other quantities at N=64:\n- cos(v_cf, v_ref) = 0.97796 (proposer 0.97798);\n- weight on the two lowest reference modes 0.98423 (proposer 0.98424), split 0.956 on the 5.05e-8 mode and 0.028 on the 4.08e-3 mode;\n- Q_Def(v_ref) = 0.0011997 (proposer 0.0011998);\n- reference low eigenvalues 5.054e-8 and 4.078e-3 (proposer 5.063e-8 and 4.077e-3).\n\nAlso reproduced:\n- x=31.571 even, N=48: Q_Def = -0.027866 (proposer -0.02811 at N=120).\n- DH odd sector at 31.571: |Q_Def| = 0.2362, w 0.836 (proposer 0.237, 0.835).\n\nGalerkin trap confirmed: at x=31.571 my N=48 lam_DH is still +6.7e-29, while the harness N=120 gives -8.5e-30. Q_Def is insensitive to this, as claimed.\n\nNot reproduced: the LOO secondary fit, and the E[1,0,14] and E[1,1,6] rows against zeta_H/h (h=3, 4 class-group characters not built).\n\nPrereg audit:\n- PREREG.txt mtime 05:01:10 precedes balance.py (05:01:39) and every output file.\n- The DH miss is decisive and was honestly scored, with prediction_matched=false.\n- Two minor quantitative misses were not listed (the C21/K9 pattern):\n  - the a2-flip R at x_h+1 against zK is 0.870, outside the preregistered 0.95-1.0;\n  - |Q_ref1 - Q_ref2|(v_cf) reaches 2.51 and 2.79, against a preregistered O(0.1-1).\n- These do not change any verdict, so I count the prereg as honored.\n\nNo processes are left running.",
 "novelty": "Low to modest. It is the first zoo-wide, two-reference, N-converged calibration of counterfeit-failure anatomy. It extends S19 and settles P4/Q6 negatively. No literature claim is made. The two cited lit-cache keys exist (davenport_heilbronn_epstein_offline#0, weil_explicit_positivity#0), and nothing in the literature bears on this measurement.\n\nThe skeptic adds two things:\n- A structural observation: a complex-character reference Re L(chi) is spectrally half of a degree-2, conductor-q^2 object. Its zero set is doubled, so its cascade is 1-2 modes, against 5 for DH at the same Gamma and q. This is a data point for Q5/P1: DH at (d=1, q=5) gives x/q of about 6, with 5-6 modes; the reference as (2, 25) gives about 2.2, with 2 modes.\n- The DH(kappa) control: breaking the FE (kappa=0 or 1) removes the cascade, and the anatomy becomes balanced.",
 "what_is_real": "1. There is no uniform failure anatomy (reproduced independently). Six counterfeit/barrier members fail by O(1)-vs-O(1) cancellation against a genuine reference: E[1,0,5], E[1,0,6], E[1,1,6], the a2-flip, LEB and DH(kappa=0,1). For these, |Q_Def(v_cf)| = 0.35-4.2 and rho = |Q_Def(v_cf)|/|lambda_min(Q_Def)| = 0.17-0.84. The FE-satisfying DH instead fails at Q_Def(v_cf) = -0.0282 with rho of about 0.012, and 95.6% of v_cf lies on the reference's 5e-8 mode.\n\n2. P4's proposed requirement ('a mechanism must lower-bound the genuine Euler form on a cone FAR from its near-null cascade') is refuted by DH and must not enter the ledger.\n\n3. The perturbative anatomy appears exactly when the counterfeit is itself deeply near-null. Measured: a 5-mode cascade down to 1e-28 for DH, which requires its FE. DH(kappa=0,1) without the FE have no cascade and are balanced.\n   - It does NOT come from 'inheriting' the reference's cascade. The only reference is analytically mismatched, since Re L(chi) has a doubled zero set.\n   - The local/global defect type does not predict it.\n\n4. The anatomy descriptors are reference-dependent, consistent with R14: LEB cos 0.13 vs 0.98, and the sign of Q_Def(v_ref) flips. R ~ 1 is a tautology.\n\n5. The classification is a continuum. The weight of v_cf on reference low modes runs 0, 0.02, 0.35, 0.45, 0.84, 0.98, so 'two regimes' is a threshold choice.\n\nLedger wording I endorse, as the barrier narrowed from 'NO SINGLE COUNTERFEIT ANATOMY': 'Counterfeits do not uniformly fail far from the genuine near-null set; the FE-satisfying, small-conductor DH fails inside it (rho about 0.01), so P4 is withdrawn. Anatomy tracks the counterfeit's own near-nullness, not defect locality.'\n\nconjecture1_proved = False.",
 "next_step_if_survives": "The angle does not survive as a mechanism. The most informative follow-up is to fold this into P1/Q5, the cascade law, and treat anatomy as a consequence of it:\n- Measure near-null counts for DH, Re L(chi_q) for complex chi (q = 5, 7, 13), and genuine self-dual degree-1 references of small conductor, at N >= 64 in mp.\n- Test two things: whether Re L(chi) behaves as degree 2 at conductor q^2, and whether the counterfeit's own cascade dimension at its horizon predicts perturbative anatomy.\n- Candidates: DH-type FE-satisfying combinations of complex characters mod 7 and 13, where the reference is again Re L(chi), and the kappa family near the FE value.\n\nThe deeper point for mechanism builders: what makes DH dangerous is that its FE supplies genuine-looking near-nullness, which is R4/R13 territory.\n\nSeparately, file two harness-independent notes:\n- A complex-character reference is not a like-for-like genuine comparator for a self-dual counterfeit.\n- The rho normalization (|Q_Def(v)|/|lambda_min(Q_Def)|) should replace the absolute 0.1 threshold in any future anatomy classifier."
}
```
