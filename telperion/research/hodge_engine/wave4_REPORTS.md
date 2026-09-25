# Hodge engine wave 4

conjecture1_proved = False.

## Portfolio

- **rci_gap_q20** (survivor_refinement): RCI is the only survivor that is counterfeit-sensitive by construction and finitely testable. It has been proposed since wave 3 and never run. The exact shift identity ell = log q0 - lambda_min makes the cube sweep cheap with FormSetup, and K8's 2-4% can only be updated by this measurement.
- **odlyzko_unconditional_rci** (hybrid): RCI turned W(x) into a conductor lower bound, and conductor lower bounds are exactly what Odlyzko/Poitou explicit-formula LPs prove unconditionally. The two have never been set side by side. The cvxpy/CLARABEL stack is now available for the LP/SDP, and the result either produces a new unconditional multi-character window theorem or a sharp duality-gap barrier.
- **class_group_amgm_defect** (wildcard): The ledger requires a Hecke-quadratic input (R2) and asks for a horizon-vs-Hecke-defect law (Q6). S4's log cosh identity is the h=2 shadow of a general class-group AM-GM decomposition that nobody has computed. The full Epstein ladder (h=2,3,2,4) is already in the zoo, so the law can be tested blind on four counterfeits at once.
- **hodge_signature_barrier** (barrier_hunt): P3 and Q5 have sat open since wave 3 with only float anatomy. The ingredients (harness parts, wave-3 CC class, Lane B interval tooling) are all in place, and barriers are what the project kernel-certifies. Pinning 'Hodge shape is counterfeit-blind' stops future waves from proposing signature-type Hodge theorems.
- **ks_pshr_sdp** (micro_experiment): KS-PSHR is the only wave-2 survivor never run, because no SDP solver was installed. cvxpy with CLARABEL/SCS is now available, and at x = 3.02 and 5 the problem has only 2-3 place blocks, so it is answerable in one session. Either outcome settles an untested ledger entry (K3).

## Results

### rci_gap_q20 (survivor_refinement)
- survives adversarial review: False; prediction matched: True; claimed barrier: B23: RCI SLACK IS NOT CONDUCTOR-CONTROLLED, AND ITS BINDING SET IS THE NEAR-NULL TINY-CONDUCTOR LIST.

1. **Bulk.** For real patterns, x = 10 to 40, |d| <= 1e8: log N_min(eps) is fixed by counting, ≈ pi(x) log 2 + log prod p/(p-1) (10.2 at x=40). It is flat across ell deciles, and corr(ell, log N_min) falls from 0.40 to 0.036 as x goes from 10 to 40. So slack ≈ log N_min - ell has an O(1), pattern-dependent spread (sd 1.0-1.6 within 0.5-wide conductor bins, versus means of 1.8-7.6), and the conductor does not see which patterns are dangerous.

2. **The minimum.** The minimum of the RCI slack over all realized patterns is always at the smallest conductors: d=-3 or -4, then 5, 8, -7, -8, ... in |d| order. There the slack equals the near-null window margin of zeta_K(d): 3.4e-10 at x=10 falling to <= 2.2e-28 at x=40 (mp, N=40, Ritz upper bounds). Complex characters are less tight (q=5 quartic: 1.5e-9 at x=40). So RCI's content collapses onto B3/B20, i.e. GRH for a finite list of tiny-conductor L-functions with superexponentially small margins. The arithmetic of realizing patterns carries no finite-scale positivity.

3. **Extreme tail.** The extreme-ell tail (all+1, ell = 1.477 sqrt(x) + 0.54) is the GRH-conditional least-nonresidue problem (Ankeny/Bach/LLS/CMQR). The unconditional elementary bound covers it only for x <= ~2.2.

4. **Detector.** An RCI predictor built on log N_min alone is a detector. It has 0 false alarms on controls but 45 false alarms below counterfeit horizons (useful=False), because all its catches are input exclusion plus a converse-type match, which violates R6.

Also reported:
- C11 still stands: harness/README.md lists DH as 'about 30.6, NOT converged' while zoo.py has 30.571.
- The battery's DH truth at x=31 and 33 conflicts with its own N_mp=24 measurement (the known N >= 120 issue).; barrier confirmed: True

WAVE 4, rci_gap_q20: a micro-experiment and barrier hunt, NOT a mechanism claim. conjecture1_proved=False.

## Setup
- **Shift identity (S0).** It holds exactly: B(q) = B(q0) + log(q/q0) I in Gram normalization. Errors are <= 2.4e-15 in float and 0 in mp, at q=5 and 163, x=12 and 20, both sectors.
- **ell.** ell(eps,x) = -lambda_min over both sectors at q=1, N=64 Neumann, float, via batched FormSetup. The pole class uses Gamma_R(s)Gamma_R(s+a) with a=1 for d<0 and a=0 for d>0, with poles (1,1). The pole-free cross-check is L_eps with Gamma_R(s+a).
- **Validation.** The engine matches harness zeta_K(d) and L(chi_d) to about 1e-15.
- **N_min.** Computed by a numpy sieve over fundamental discriminants with 1 < |d| <= 1e8, both signs, as ternary patterns on p <= 37 (validated, 0 mismatches). Every realized pattern was evaluated (up to 668,931 at x=40), plus all +-1 patterns, and all of those are realized.

## Table 1: gap(x), min over all realized patterns, pole class

Values are from mp dps 40 at N=40 (Ritz upper bounds; float is at noise).

| x | gap(x) | argmin | other tight values |
|---|---|---|---|
| 10 | 3.36e-10 | d=-3 | -4: 8.0e-8; 5: 1.9e-7; 8: 3.9e-5 |
| 12 | 8.1e-12 | d=-3 | |
| 14 | 3.5e-13 | d=-3 | |
| 16 | 1.1e-14 | d=-3 | |
| 18 | 3.4e-16 | d=-3 | |
| 20 | 1.29e-17 | d=-3 | -4: 3.6e-14; 5: 2.0e-13; -20: 4.54e-3 |
| 22 | 8.7e-19 | d=-3 | |
| 24 | 8.0e-20 | d=-3 | |
| 28 | 1.4e-22 | d=-3 | |
| 32 | 6.4e-25 | d=-3 | |
| 36 | 6.2e-27 | d=-3 | |
| 40 | 2.2e-28 | d=-3 | -4: 1.5e-23; 5: 4.6e-22; -20: 1.39e-7 (N=256) |

- There is no negative value anywhere (T1 passes).
- The pole-free cross-check agrees (min -4.7e-15, which is noise).
- The top-20 patterns are the smallest-|d| genuine characters in near-|d| order, and they converge in N (64/128/256).
- **Caveat.** R8 asks for a Schur tail at |lambda| < 1e-6, and it was NOT run. There is only an N=24 to N=40 mp trend (decreasing about 10-20%), so the x >= 20 near-null numbers are upper bounds, subject to B21.
- **Unramified-only minimum.** The minimum is at the least admissible |d| just above x: 13 or 17 at x ≈ 10-16, then -23, 29, 37, 41 at x=40. Values are 1e-4 to 1e-2.
- **Complex characters.** Of 1e4 (all prime conductors < 200, random primes < 1e5, and products), none is negative. The minimum slack upper bound is at q=5 (quartic) and q=7: 5.9e-4 at x=12, 1.1e-5 at 20, 2.6e-7 at 28, 1.5e-9 at 40.

## T2: zetaK(-20) control
N_min = 20. Gap is 4.566142e-3 at x=20 and 1.680049e-3 at x=22 (N=64). At N=128/256 it is 4.5434e-3 / 4.5361e-3, matching the zoo and Lane B. q0 in {4, 5, 23} reproduces it to 1e-15. PASS.

## T3: slack law (B23)
- corr(ell, log N_min) over unramified patterns: 0.40, 0.27, 0.22, 0.24, 0.19, 0.15, 0.15, 0.10, 0.11, 0.05, 0.05, 0.036 for x = 10 through 40.
- Slope of slack on log N_min goes from 0.65 to 0.96. The residual sd, 0.79 to 1.30, equals the sd of ell.
- Bin statistics at x=40: [6-6.5: 1.80 ± 1.00], [9: 4.83 ± 1.24], [10: 5.80 ± 1.28], [11: 6.82 ± 1.31], [12: 7.56 ± 1.62].
- Mean log N_min matches the counting prediction pi(x) log 2 + log prod_{p<x} p/(p-1): 7.22 vs 7.3 at x=20, 9.44 vs 9.5 at x=32, 10.18 vs 10.2 at x=40.
- log N_min is flat across ell deciles, except that the top decile rises by about 0.5 for d>0.
- Minimum slack in the top 1% of ell: 2.65/2.77 at x=20, 1.68/1.74 at x=32, 1.73/1.39 at x=40.
- The slack is NOT conductor-controlled in the bulk. It is conductor-ordered only in the near-null tiny-|d| regime. B23 is recorded.

## T4: all+1 pattern and the unconditional window
- max_eps ell is always all+1 with d>0: 5.10 (x=10), 7.20 (20), 8.89 (32), 9.80 (40).
- Fits: 1.4771*sqrt(x) + 0.5394 (rms 0.046, best), 3.44*log(x) - 3.03 (0.083), 0.707*x/log(x) + 2.35 (0.126).
- Actual log N_min(all+1): 9.80 (d=18001) at x=18, 13.90 (d=1083289) at x=40, so the all+1 slack is about 3-4.
- The rigorous elementary bound log N_min >= log(2(ceil(x)-1)), from |partial character sum| <= q/2, beats max ell only for x <= ~2.2 (1.39 vs 1.28 at x=2.05; fails at 2.30).
- Pólya–Vinogradov in the form sqrt(q) log q (constant unverified) is weaker.
- The unconditional window is therefore x < 2.2, inside the KWin/Yoshida x=2 territory. It is NOT a Lean target.
- Remark: the all+1 slice of RCI is exactly a Fourier-optimized, GRH-conditional least-nonresidue bound, n_chi <~ 0.46 log^2 q in the window class. That is literature territory (Ankeny/Bach, LLS arXiv:1309.3595, CMQR arXiv:2404.08380, abstracts verified); the constant comparison is unverified.

## S4: battery
Blind detector, no lambda_min. s_fit(x) = max(gap(x), 0) = 0. Rule: cube data are '+' iff some fundamental d with |d| <= q realizes the pattern (a converse-type match); non-cube data are '-' for x > 6.

On 19 members × 14 x values:

| score | value |
|---|---|
| agree | 213/266 |
| catches | 86 |
| false alarms (total) | 49 |
| false alarms on control+ | 0 |
| false alarms below counterfeit/barrier horizon | 45 |
| misses | 4 |
| misses on counterfeits | 0 |
| useful | False |
| sharp | False |

Per member:
- **Controls:** all '+' at every x, including x=100.
- **LEB:** missed at 5.5; caught from 8.
- **euler-rand(d1):** missed at 3 and 5.5; caught from 8.
- **euler-rand(d2):** classified 'complex cube'. Correct '+' at 3 and 5.5, caught from 8.
- **zetaK(-20)[a2=-1]:** false alarms at 8 to 21; caught from 23.
- **DH(kappa=0):** false alarms at 8 to 20; caught from 21.
- **DH(kappa=1):** missed at 5.5.
- **DH:** false alarms at 8 to 29; caught from 31.
- **E[1,0,5]:** false alarms at 5.5 to 16; caught from 20.
- **E[1,1,6]:** caught from 29.
- **E[1,0,6]:** caught from 33.
- **E[1,0,14]:** '+' correct at 5.5 and 8, where it is pattern-realized by a small d. False alarms at 12 to 40; caught at 100.

Explicitly: every catch comes from input exclusion (non-cube, c(6) != 0 Hecke violation, or non-unitary local roots) plus a converse-type match to a genuine real character, so R6 is violated. The predictor cannot locate any horizon, which is the class-P shortcut. It is a detector, not a reason.

## Bugs and notes
- C11 persists: harness/README.md still lists DH as 'about 30.6, NOT converged'.
- The battery flags DH at x=31 and 33 as conflicts: positive at N_mp=24, which is the known N >= 120 issue.
- Harness bugs found: none.
- No git repo or harness file was modified. No process is left running.

## Files
All in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/rci_gap_q20/:
- Preregistration: PREREGISTRATION.txt
- Engine: rcicore.py
- Scripts: s0_shift.py, s1_ell.py, s2_sieve.py, s3_analyze.py, s3_slack.py, s3_tail.py, s4_t4.py, s5_refine.py, s6_complex.py, s7_battery.py
- Logs: the matching *.log files
- Data: nmin_100000000.npz, ell_x*.npz

## Verdict
RCI is correct as a restatement: no violations at x <= 40, |d| <= 1e8, and 1e4 complex characters. As a finite-scale structure it collapses:
1. In the bulk, the conductor is counting-dominated and blind to the pattern.
2. The binding set is the near-null tiny-conductor list (B3/B20).
3. The extreme tail is the conditional least-nonresidue problem, with an unconditional window of x < 2.2.

The angle is dead as a positivity mechanism, and the new barrier B23 goes to the ledger.

**Skeptic:**

```json
{
 "angle": "rci_gap_q20 skeptic review. The proposal is a micro-experiment and barrier hunt on the Reciprocity-Conductor Inequality RCI(x): ell(eps,x) <= log N_min(eps) over quadratic-character patterns. It claims no mechanism and proposes a new barrier, B23. I built an independent Weil-form implementation (my own formulas, orthonormal Legendre Galerkin, float64 and mpmath) and my own fundamental-discriminant sieve to 1e8, and used them to cross-check the decisive numbers.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "As a positivity reason RCI is circular. By the shift identity, which is exact (the conductor enters Q_x as log q * ||f||^2), the slack of a realized pattern equals lambda_min Q_x of the genuine Dedekind zeta zeta_{Q(sqrt d_min)}. T1 therefore just re-measures W(x) for about 670k quadratic fields; RCI(all x) is equivalent to RH plus GRH for real quadratic L. The Euler product is used only as an input gate (the cube test) and a lookup (N_min), never inside an inequality. The authors say so themselves (R6 violated, alive=false).",
  "Against counterfeits it works verbatim only through input exclusion. E, DH and the Epstein ladder are rejected as 'non-cube' (c(6) != 0), and every S4 catch comes from that exclusion or from a converse-type match. The detector cannot locate any horizon: 45 false alarms below the horizons, useful=False, sharp=False.",
  "B23 part 2 overstates. The claim that RCI's content 'collapses onto' a finite tiny-conductor list is wrong as a statement about content. At each x the argmin, i.e. the binding margin, is d=-3 or -4. But RCI over all x still contains GRH for every quadratic field. If d != d' realize the same pattern on p < x, then chi_d chi_d' is a nontrivial character that is trivial on all primes < x, which forces x < |d d'|. So for x >= d^2, d is the unique realizer. The correct statement is: 'RCI is at least as hard as W(x) for zeta_{Q(sqrt -3)}, since it contains that instance, and its tightest margin at every x is that near-null margin.'",
  "B23 part 3 and T4 are misframed. The 'unconditional window x < 2.2' comes from replacing N_min with the elementary bound |partial sum| <= q/2. At fixed x, N_min(all+1) is exactly computable: it is the pseudosquare L_p, OEIS A002189 (17, 73, 241, 1009, 2641, 8089, 18001, 53881, 87481, 117049, 515761, 1083289), which my sieve reproduces term for term and which is tabulated far beyond p=37 (Lehmer-Lehmer-Shanks 1970, Wooding-Williams 2006, Sorenson 2010). The all+1 slice has slack about 3-4 (log L_p - ell), making it the easiest part of RCI to certify at fixed x, not the hardest. Only the uniform-in-x statement needs GRH strength (ell ~ 1.48 sqrt(x) against polynomial-in-x unconditional least-nonresidue bounds). The conclusion 'not a Lean target for RH' stands, but the stated reason does not. The proposal also missed the pseudosquare identification and literature: the counting law log N_min ~ pi(x) log 2 + sum log(p/(p-1)) is the pseudosquare-type heuristic.",
  "Preregistration was scored generously. Two quantitative misses are reported transparently but not labeled as misses under prediction_matched=true. (i) The preregistered unramified-only minimum was O(0.1-1); the observed value is 1e-4 to 1e-2, and 0.000 at x=36 and 40 (d=41). (ii) The preregistered unconditional window was x < ~6-10; the observed window is x < 2.2.",
  "The near-null values at x >= 20 are Ritz upper bounds with no Schur tail or lower-bound certificate (R8 not run; B21). My N=32 mp value for d=-3 at x=20 is 2.5e-16, against theirs of 1.29e-17 at N=40. That is consistent in order of magnitude and ordering, but neither number is certified."
 ],
 "prereg_honored": true,
 "counterfeit_check": "Every counterfeit (E ladder, DH and variants, LEB, euler-rand) is flagged only by input exclusion (non-cube or Hecke violation, e.g. c_E(6) != 0) or by failing to match a genuine character. Never by an inequality that would hold for zeta and fail for the counterfeit at a scale. Below each horizon the detector raises false alarms: E[1,0,5] on 5.5 to 16, DH on 8 to 29, zetaK(-20)[a2=-1] on 8 to 21. It therefore cannot separate 'counterfeit that is still positive' from 'counterfeit that is negative', which is the B1/B2 failure pattern. Inside the cube the mechanism is exactly GRH readout: the slack of a realized pattern IS the window margin of a genuine zeta_K. Verdict: counterfeit-blind as a reason, and a correct but trivial detector.",
 "numerics_reproduced": "Independent code is in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/rci_gap_q20_skeptic/: weil_indep.py (mpmath), weil_np.py (float64) and sieve_indep.py, with checks t1.py through t6.py. The form used is Q = log q ||f||^2 + 2F+F- + 2 sum_mu Arch_mu - 2 sum Lambda(n)/sqrt(n) g(log n), with Arch derived from the Gauss psi integral. No harness code was used.\n\n(1) Form validation, zeta_K(-20):\n- x=20 even sector: 4.716e-3 (N=40), 4.568e-3 (N=80), 4.549e-3 (N=120), 4.544e-3 (N=160). Theirs: 4.566e-3 (N=64), 4.5361e-3 (N=256).\n- x=12: even 0.16449, odd 2.0509 at N=160. Theirs: 0.16470 and 2.0518.\n\n(2) N_min sieve: my independent sieve to 1e8 agrees exactly with theirs on every realized pattern, for P=8 and P=12 and both signs (6558/6558 and 334422/334509; 0 mismatches in realization or value). All+1 with d>0 is exactly the pseudosquare sequence A002189.\n\n(3) T1 at x=20, all 13116 realized patterns, my N=80 against their N=64:\n- max |ell_mine - ell_theirs| = 3.5e-3, median 1.2e-4.\n- No gap below -1e-9.\n- The tight list is -3, -4, 5, 8, -7, -8, 12, 13, -11, 17, -15, 21, 24, -20 (gap(-20) = 4.568e-3), identical to theirs.\n- max ell = 7.196 at the all+1 pattern, d=53881 = L_19. Theirs: 7.198.\n\n(4) Near-null tiny conductors in mp:\n- x=10 (N=32, dps 40): d=-3 3.21e-10, d=-4 8.06e-8, d=5 1.84e-7. Theirs: 3.36e-10 (N=40) and 3.13e-10 (N=256); 7.6e-8; 1.83e-7.\n- x=20 (N=32, dps 50): d=-3 2.5e-16, d=-4 5.6e-14, d=5 2.8e-13. Theirs: 1.29e-17 (N=40, mp) and float values of 3.1e-14 and 1.8e-13. Ordering and scale are confirmed; the values are uncertified Ritz upper bounds.\n\n(5) T3/B23 bulk:\n- x=20 unramified: slope of slack on log N_min 0.866 (theirs 0.87). Residual sd 1.08. Bins [6, 6.5): 2.55 +- 1.00; [7, 7.5): 3.61 +- 1.07; [8, 8.5): 4.69 +- 1.08.\n- x=40, 1500-pattern samples per sign: corr(ell, log N_min) = +0.064 (d>0) and -0.046 (d<0). Mean log N_min 10.28 / 10.23, against the counting prediction 10.22 (theirs 10.18 / 10.2). log N_min is flat across ell deciles, except that the top decile rises by about 0.5 for d>0 (by about 1.2 at x=20).\n- All confirmed.\n\nNot reproduced: the S4 battery, the 1e4 complex characters and the x=40 mp values. None of these is decisive.",
 "novelty": "Low.\n- The RCI restatement is equivalent to GRH for quadratic Dedekind zetas via the exact log q shift.\n- The extreme tail is the classical pseudosquare problem (Lehmer 1954; Lehmer-Lehmer-Shanks 1970; Wooding-Williams 2006; Sorenson 2010; per OEIS A002189, fetched this session). The proposal missed this.\n- The GRH-conditional least-nonresidue direction belongs to Ankeny/Bach, Lamzouri-Li-Soundararajan (arXiv:1309.3595) and Carneiro-Milinovich-Quesada-Herrera-Ramos (arXiv:2404.08380); abstracts only, per the proposal.\n- A GRH-conditional pseudosquare lower bound (Schinzel 1997, I believe) is UNVERIFIED: my web budget was exhausted.\n- The window-class constant comparison (log L_p >~ 1.477 sqrt(p) + 0.54, equivalently n_chi <~ 0.46 log^2 q) against LLS/CMQR is UNVERIFIED.\n- The new content is empirical: an exact numeric map of the slack landscape. The argmin is always the smallest |d| (-3 or -4) with superexponentially small margin, and the bulk slack is counting-dominated with O(1) spread.",
 "what_is_real": "All of the following was reproduced by independent code:\n- The exact log q shift identity.\n- The N_min table (exact match to 1e8).\n- No RCI violation in Ritz values at x=20, over all realized patterns.\n- The tightest instances are the smallest-conductor fields, in |d| order: -3, -4, 5, 8, -7, ... Their slack is the near-null window margin of zeta_{Q(sqrt d)}: about 3e-10 at x=10 and at most about 1e-16 at x=20 (uncertified upper bounds).\n- In the bulk, log N_min is counting-dominated (pi(x) log 2 + sum log(p/(p-1)) = 10.22 at x=40) and nearly uncorrelated with ell: corr about 0.06 at x=40, slack sd about 1 within conductor bins.\n- max ell is the all+1 pattern, about 1.48 sqrt(x) + 0.54, and its N_min is exactly the pseudosquare L_p.\n\nA corrected B23 should read as follows. The minimal RCI slack at every x is attained at the smallest-conductor quadratic fields and equals their near-null W(x) margin, so RCI is at least as hard as the B3/B20 near-null problem for zeta_{Q(sqrt -3)}. Bulk slack is controlled by pattern-dependent ell and not by the conductor. The large-ell tail is the pseudosquare regime, with O(1) slack of about 3-4 at fixed x, and needs GRH strength only uniformly in x.\n\nThe proposal's 'collapses to a finite list' wording and its 'unconditional window x < 2.2' framing should be dropped or corrected as above. No positivity mechanism exists here; conjecture1_proved=False.",
 "next_step_if_survives": "The angle does not survive: retire RCI as a mechanism and ledger the corrected B23 (wording above). The most informative cheap follow-up tests whether the near-null binding margins are pure zero readout (B2), which would close the angle as circular.\n- Take the tiny-conductor list (d = -3, -4, 5, 8, -7, -8, 12, 13) on x in [10, 40].\n- Regress log margin(d, x) on log x times the first-zero height gamma_1(d), and on the low-zero counting function N_d(T) near T ~ pi/log x.\n- If one law fits across d (margin ~ exp(-c * gamma_1(d) * log x)-type), the ordering of RCI's binding set is dictated by zero heights, not by conductor arithmetic.\n- Pair this with a Schur-tail lower bound (Haynsworth inertia) for d=-3 at x=20, so the headline near-null figure is certified rather than a Ritz upper bound.\n\nSeparately, a literature check (low priority): compare the window-class GRH-conditional pseudosquare bound log L_p >= 1.477 sqrt(p) + 0.54 against Schinzel's GRH bound for pseudosquares and against LLS/CMQR constants. This is only for correct attribution; it is not RH progress."
}
```

### odlyzko_unconditional_rci (hybrid)
- survives adversarial review: False; prediction matched: False; claimed barrier: B23 STRIP-POSITIVITY LOSS.

Setup. The strip cone C_S = {F = g/cosh(t/2) : ghat >= 0, window support} is exactly the set of window tests with Re Phi_F >= 0 on the closed critical strip (Lemma S). It sits strictly inside the Weil cone. Define:
- B(eps,x) = log q0 - mu_min, the best unconditional Odlyzko-Poitou conductor bound;
- ell(eps,x) = log q0 - lambda_min, the Weil/RCI threshold;
- Delta = ell - B = mu_min - lambda_min.

Statement.
- (i) Delta >= 0 identically, and it is independent of log q, so gap_U = min_cube(B - ell) <= 0 always. Unconditional explicit-formula bounds can prove RCI only where Delta = 0.
- (ii) Numerically Delta > 0 at every tested x and pattern:
  - zeta: 1.04e-4 at x = 2.5, 6.1e-10 at x = 8, 1.08e-12 at x = 20;
  - L(chi_-4): up to 1.6e-2;
  - zetaK(-20): 6e-3 rising to 0.143;
  - ±1 cube at pole kept: gap_U = -0.027 at x = 2.5, -0.33 to -0.39 at x = 8.
- (iii) For zeta, Delta(x) >= 2pi sum_gamma sech(pi gamma) - lambda(x) ≈ 1.30e-18, uniformly in x (the zero-free gap smeared by the strip Poisson kernel). Meanwhile lambda(x) -> 0 superexponentially (1.5e-38 at x = 20), so Delta/lambda >= 1e20 for x >= 8. Near-null members are therefore out of reach at every scale (B3/B20 compounding).
- (iv) Dual witness. At log q = B, the explicit-formula functional equals, exactly on window tests, a discrete positive measure of virtual zeros on Re s = 0 and 1 at the double zeros of the strip minimizer's ghat* (NNLS residual 5e-8). The loss is intrinsic.
- (v) Balayage identity. For every compactly supported F, a line zero 1/2 + i gamma pairs identically with its unit-mass sech(pi(u - gamma)) cloud on the edges. Explicit-formula tests cannot see zero discreteness, so any 'positive on a region wider than the line' class is blind to counterfeits whose zeros stay in the closed strip.
- (vi) Battery. Zero false alarms, but it catches no counterfeit (E x4, DH, DH(kappa=0)) up to x = 100. It catches only no-FE data, and late.; barrier confirmed: False

WAVE 4: odlyzko_unconditional_rci. Verdict: DEAD. This is a quantified negative theorem, recorded as barrier B23 (strip-positivity loss).

1. The idea. Odlyzko-Poitou discriminant bounds are unconditional because they use only test functions F with Re Phi_F(s) >= 0 on the whole closed critical strip. For a real-character prime pattern eps, that gives log N(eps) >= B(eps,x) with no hypothesis. If B(eps,x) >= ell(eps,x) held for every eps, where ell is the Weil threshold, the Reciprocity-Conductor Inequality, and with it W(x) for zeta·L(chi), would follow for x up to some x_U.

2. Exact class identification (Lemma S). With Phi(s) = int F(t) e^{(s-1/2)t} dt and F even, Re Phi(1+iu) = (F cosh(t/2))^(u). The interior of the strip follows because cosh(sigma t)/cosh(t/2) is positive definite. So the strip cone is exactly {g/cosh(t/2) : ghat >= 0}; Odlyzko's extra g >= 0 is not needed for a fixed pattern. Both B and ell are generalized eigenvalue problems on the same span:
- ell = log q0 - lambda_min(M; G), with M_ij = L(sym h_i*h_j);
- B = log q0 - mu_min(K; G), with K_ij = L(sym h_i*h_j / cosh).
No SDP is needed.

Since g/cosh with ghat >= 0 is positive definite (Krein/Boas-Kac), C_S ⊂ C_L, so Delta = ell - B = mu - lambda >= 0 identically. This holds across both parity sectors combined; sector-wise Delta can be negative. log q cancels exactly (verified: lambda(e q) = lambda(q) + 1). So gap_U <= 0 is automatic, and the question is only whether Delta vanishes. It does not.

3. Numerics (scripts in scratchpad/hengine/w4/odlyzko_unconditional_rci/).
- Validation: strip.py is an independent real-space build that matches harness form.Q to 1.3e-13.
- Precision: float64, Neumann basis, both sectors, N = 16/32/48 (96 for zeta at x >= 10).
- Zeta: Delta = 4.4e-4 (x = 2), 1.04e-4 (2.5), 1.5e-5 (3), 5.3e-7 (4), 5.0e-8 (5), 8.3e-9 (6), 6.1e-10 (8), 1.2e-10 (10), 2.7e-11 (12), 4.2e-12 (16), 1.08e-12 (20). For x >= 4 these are mu_min itself, since lambda_min is below 1e-12 there.
- Analytic floor: Delta_inf = 2pi sum_gamma sech(pi gamma) = 1.3036e-18. It is positive unconditionally because of the zero-free gap below 14.13 and Littlewood's bounded gaps.
- L(chi_-4): Delta = 7e-3 .. 1.6e-2 .. 1.2e-3. L(chi_5): 1e-2 .. 5e-4. zetaK(-20): 6e-3 rising to 0.143 at x = 8.
- ±1 cube (degree 2, pole kept, 16 patterns at x = 8): every pattern has Delta > 0. gap_U = -0.0267 (x = 2.5, kill), -0.035, -0.088, -0.132, -0.217, -0.327 for mus [0,1], and -0.034 .. -0.388 for mus [0,0]. Delta_max is roughly 0.05(x - 2).

4. Why the loss is intrinsic.
- (a) The Weil minimizer's edge transform is negative: -6.1e-5 at u = 13.90 for x = 2.5, just below gamma_1. So it is not in the strip cone.
- (b) Krein dual at log q = B: a discrete nonnegative measure of virtual zeros on Re s = 1 (mirrored on Re s = 0) reproduces the whole window explicit formula (NNLS residual 5e-8). Its atoms are at the double zeros of ghat* (14.02, 20.30, 24.56, 31.36, ...). This is the counterfeit-admissible configuration, maximally off-line, that makes B optimal.
- (c) Structural side result, the balayage identity: F^(gamma) = int (F cosh)^(u) sech(pi(gamma - u)) du for every compactly supported F. Each line zero pairs identically with a unit-mass Poisson cloud on the strip edges. Compact-support explicit-formula tests cannot see discreteness, and discreteness is exactly where Weil's criterion gets RH. Any class certified by positivity on a region wider than the line inherits this blindness.

5. Counterfeit control and the R-checks.
- Blind battery: 0 false alarms on control+ (guaranteed by the theorem), but all counterfeit rows missed (E[1,0,5], E[1,0,6], E[1,1,6], E[1,0,14], DH, DH(kappa=0)) up to x = 100. It catches only no-FE barrier data, where the zero-sum identity is invalid, and late: LEB only from x = 6, and zetaK(-20)[a2=-1] never.
- The strip test is exactly blind to any datum whose zeros all lie in 0 <= Re s <= 1. It can catch E or D only through zeros with Re > 1, far beyond their Weil horizons.
- Checks: fails R1, R2 (linear in c), R4 (lossy by Delta), R9 and R11. The pre-screen (B1/B11 linear; B3/B20 near-null) is confirmed and quantified.

6. Prediction audit. Items (1), (2), (4), (5) and the sanity check matched. Item (3) was WRONG for zeta: I predicted Delta_zeta(2.5) of order 0.1-1 and growing. It is 1.0e-4 and decays like x^-6 to a positive floor, because the strip class is itself near-null for zeta. It grows only for non-near-null members and the cube (0.003-0.39). The decisive kill still holds, since Delta_zeta/lambda_zeta goes from about 10 (x = 2.5) to above 1e20 (x >= 8). prediction_matched = false because of item (3).

7. Unverified, flagged:
- Poitou references (not in the lit cache);
- Krein extension / Boas-Kac;
- Littlewood gap bound;
- Davenport-Heilbronn zeros in sigma > 1 for E.
Nothing is interval-certified. The float Delta values are well above noise (about 2e-13) for x <= 20, and the floor is analytic. conjecture1_proved = False.

Files (all in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/odlyzko_unconditional_rci/):
- PREREG.txt: the preregistered prediction;
- strip.py: the line/strip functional builder;
- validate.py: cross-check against the harness;
- t1.py, t1b.py: T1 tables and convergence in N;
- t23.py: conductor shift (T2) and cube (T3);
- t_floor.py: large-x zeta values and the analytic floor;
- t_dual.py: Krein edge-measure dual witness;
- t_cone.py: line minimizer vs strip cone;
- t_battery.py: blind battery run.
Each script's output is in a matching .log file. No background processes were left running.

**Skeptic:**

```json
{
 "angle": "odlyzko_unconditional_rci (skeptic). The idea: use Odlyzko\u2013Poitou unconditional strip-positive explicit-formula bounds B(eps,x) to prove the Reciprocity-Conductor Inequality ell(eps,x) <= log N_min(eps), and through it W(x). The proposer killed it by showing Delta = ell - B >= 0 in the same window (the strip cone sits inside the Weil cone) and recorded the result as B23.",
 "survives": false,
 "barrier_confirmed": false,
 "fatal_flaws": [
  "The mechanism is linear in c(n). The strip functional, and every B built from it, is a linear functional of the coefficients, so it falls under B1. The Euler product is used only for cube membership and for keeping zeros in the closed strip; it is never used nonlinearly or globally. The route is exactly blind to any counterfeit whose zeros lie in 0 <= Re s <= 1: the battery reads '+' for E x4, DH and DH(kappa=0) out to x = 100.",
  "In the same window the kill is a tautology, not a discovery. C_S = {g/cosh(t/2) : ghat >= 0} is contained in C_L (FT of sech(t/2) is 2pi sech(pi u) > 0), so mu_min >= lambda_min, B <= ell and gap_U <= 0 before any numerics. The preregistered 'decisive' test could not have come out otherwise.",
  "OVERREACH in the claimed barrier. B23(i) says 'unconditional explicit-formula bounds can prove RCI only where Delta = 0'. That is FALSE once the strip test uses a larger window x' > x and B is minimized over all cube extensions of eps on the primes in [x, x'). ell(eps', x') >= ell(eps, x) because the Weil threshold is monotone in the window, so the cone inclusion no longer orders the two sides. My independent code, enumerating every +-1 cube vertex exhaustively (mus [0,1] and [0,0], pole kept), gives max_ext mu(eps', x') <= lambda(eps, x) for EVERY base pattern at x = 2.5, 3, 4 (x' = 4.5), x = 5 (x' = 7.5; worst margin -0.042) and x = 6 (x' = 12; worst -0.043). A box-SDP over all c(p) in [0, 2 log p], which also covers ramified primes, closes x = 6 at x' = 18 (worst -0.0012). So the proposer's 'kill at x = 2.5' kills only the same-window strawman. Unconditional strip bounds DO prove family-wide W(x) for small x.",
  "The larger-window route also dies, at a small scale and for a different reason: adversarial extensions. At x = 8, worst base pattern eps = (2:-1, 3:+1, 5:+1, 7:-1), the vertex search finds an extension (inert 11..29, split 31..43) with mu - lambda = +0.146 (x' = 20, exhaustive), +0.039 (x' = 45, local vertex search) and +0.022 (x' = 70, local search). The box-SDP (ramified-inclusive) saturates at +0.172 / +0.166 / +0.166 for x' = 45 / 70 / 110. So no x' <= 110 proves RCI(8) with the ramified-inclusive box relaxation, and the vertex-only case stays open (+0.022 and shrinking at x' = 70). Even in the best case this reaches only finitely many x, consistent with B20 and with the known saturation of unconditional Odlyzko bounds. It cannot give W(x) for all x.",
  "A minor internal inconsistency in the proposer's files. t_dual.log reports that the zeta line minimizer at x = 2.5 is inside the strip cone ('outside strip cone: False', min +1.68e-4) because of crude np.gradient quadrature. t_cone.log, with Gauss quadrature, gives -6.08e-5 at u = 13.90, and the report quotes the t_cone value. Independently I get -1.31e-4 at u = 13.915 (Legendre basis, N = 12 and 18), so the minimizer is outside and the t_cone sign is right. Separately, the quoted 'x^-6' decay of Delta_zeta is really closer to x^-6.8 between x = 10 and x = 20."
 ],
 "prereg_honored": true,
 "counterfeit_check": "The route goes through verbatim for a counterfeit, i.e. it is counterfeit-blind. B(eps,x) is linear in c(n), and the strip test pairs each zero with a positive Poisson cloud on the edges. So any datum whose zeros all lie in the closed strip satisfies log q >= B automatically, Euler product or not. That covers E (in M_1(Gamma_0(20), chi_-20)) and D below the height of their first Re > 1 zeros. The proposer's blind battery confirms this: 0 false alarms, all counterfeit rows missed to x = 100, and catches only on no-FE barrier data, where the zero-sum identity itself is invalid. The larger-window variant I found inherits the same blindness: it certifies W(x) for the genuine degree-2 family only at small x, and uses nothing a counterfeit with strip-confined zeros lacks. There is no circularity in the strict sense, since no zeros are read out, but there is no Euler input either.",
 "numerics_reproduced": "Independent code: no harness import; Legendre-polynomial basis instead of the proposer's Neumann cosines; exact Gauss autocorrelations; own derivation of the Weil explicit formula from the psi integral representation. Files are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/odlyzko_unconditional_rci_skeptic/ (indep.py, run1..run6 .py/.log, sdp.py, sdp6.log, sdp8.log, vsearch.py/.log). No processes are left running.\n\n(1) Zeta, pole kept, N = 24. Delta = 4.4411e-4 (x = 2), 1.0355e-4 (2.5), 1.4953e-5 (3), 5.2519e-7 (4), 8.3264e-9 (6), 6.200e-10 (8). Proposer: 4.444e-4, 1.0365e-4, 1.5015e-5, 5.2688e-7, 8.30e-9, 6.14e-10. Agreement is 3-4 digits.\nL(chi_-4): Delta = 7.2142e-3, 1.1696e-2, 1.5776e-2, 1.0252e-2, 4.2232e-3, 1.2471e-3. Matches the proposer to 4 digits.\nL(chi_5): Delta = 1.0144e-2 .. 5.478e-4. Matches.\n\n(2) Cube gap_U, N = 18.\n- mus [0,1]: -2.6645e-2 (x = 2.5), -8.811e-2 (x = 4), -3.2587e-1 (x = 8). Proposer: -2.665e-2, -8.815e-2, -3.268e-1.\n- mus [0,0]: -3.387e-2, -1.101e-1, -3.877e-1. Matches.\n\n(3) Analytic floor 2pi * sum_{+-gamma} sech(pi gamma) = 1.30363e-18. Reproduced.\n\n(4) Balayage identity Fhat(gamma) = int ghat(u) sech(pi(gamma - u)) du, checked on a random NON-strip-class F = f*f~: agrees to 10 digits at gamma = 0, 14.1347, 21.022. It is the strip Poisson kernel, i.e. standard.\n\n(5) The line minimizer is outside the strip cone: -1.31e-4 at u = 13.915 (x = 2.5) and -2.98e-5 at u = 13.81 (x = 4).\n\n(6) NEW, larger-window test (float64, not certified).\n- Vertex-exhaustive, x' > x with extensions: RCI holds for all patterns at x = 2.5, 3, 4 (x' = 4.5), x = 5 (x' >= 7.5) and x = 6 (x' >= 12).\n- Box-SDP, CLARABEL (flagged 'may be inaccurate' on some runs): x = 6 closes at x' = 18 (worst -0.0012, a thin margin); x = 8 fails and saturates at about +0.166 up to x' = 110.\n- Vertex adversary at x = 8: +0.146 (x' = 20, exhaustive), +0.039 (x' = 45) and +0.022 (x' = 70); the last two are from local search.\nNot reproduced: the NNLS Krein edge-measure dual, and the battery run. The dual is plausible, being LP duality.",
 "novelty": "Low.\n- The inclusion (GRH/Weil bounds dominate unconditional Odlyzko\u2013Poitou bounds, i.e. unconditional bounds are weaker) is folklore. Odlyzko's survey (lit cache explicit_formula_linear_programming#0, verified) tabulates the gap between unconditional and GRH bounds.\n- The F = g/cosh(t/2), ghat >= 0 strip class is Poitou's standard device. Poitou 1976/77 is NOT in the lit cache and remains unverified.\n- Lemma S and the balayage identity are the Poisson representation of Re Phi in the strip.\n- What is modestly new is the quantified same-window gap: zeta's Delta decays toward a positive analytic floor, and the cube gap_U values are measured.\n- My larger-window observation, that unconditional bounds with a bigger window prove family-wide W(x) at small x, is in the spirit of Yoshida's unconditional small-support Weil positivity (Yoshida 1992, from memory, NOT in the lit cache, unverified). It should be checked against that literature before any claim of novelty.",
 "what_is_real": "- Same window: Delta = ell - B = mu_min - lambda_min >= 0 is a correct, one-line theorem (C_S inside C_L). log q cancels exactly. The numeric values (zeta 1.04e-4 at x = 2.5 decaying toward the 1.30e-18 floor; L(chi) up to 1.6e-2; cube gap_U -0.027 to -0.39) reproduce with an independent Legendre-basis code to 3-4 digits.\n- Lemma S (Re Phi >= 0 on the closed strip iff (F cosh(t/2))^ >= 0) is correct, and so is the balayage/Poisson identity.\n- The proposer's prediction audit is honest. PREREG.txt (02:10:19) predates every script (02:11:06 onward), and wrong item (3) was scored against themselves.\n- The barrier as CLAIMED is overstated. With a larger strip window x' > x and minimization over all cube extensions, unconditional Odlyzko\u2013Poitou bounds DO prove the RCI, and hence W(x) for every genuine member of the degree-2 +-1 family, at x = 2.5 through 6 (float, vertex-exhaustive; box-SDP at x = 6).\n- The route stalls between x = 6 and 8. The adversary is a counterfeit-like extension pattern (inert at small primes, then split). The box relaxation saturates (+0.166 at x = 8) and the vertex margin shrinks slowly (+0.022 at x' = 70).\n- The correct B23 therefore has two parts:\n  - (a) Same-window strip bounds never beat the Weil threshold (a tautology, quantified).\n  - (b) Larger-window strip bounds beat it only up to a finite family horizon x_U, where 6 <= x_U(deg-2 cube, mus [0,1], pole kept) <= 8 is not settled, set by adversarial extension patterns that the linear strip functional cannot exclude. This is a restatement of B1/B20 for unconditional bounds.\n- No positivity mechanism for all x, and no nonlinear or global Euler input.",
 "next_step_if_survives": "The mechanism does not survive. The most informative follow-up is to restate B23 correctly and pin down the larger-window family horizon x_U.\n1. Run a branch-and-bound over extension vertices, using the box-SDP as the node bound, with the ramified option {0, log p, 2 log p} and the conductor accounted for. Decide whether the x = 8 vertex margin (+0.022 at x' = 70, from local search) crosses zero as x' grows, or saturates at a positive value.\n2. Report x_U for mus [0,1] and [0,0], with interval-certified lambda and mu at the endpoints.\n3. Check whether the saturating adversary pattern is a genuine chi_d with a large |d|, as B19 would predict, or a non-realizable counterfeit.\n4. Compare the result with Yoshida's unconditional small-support Weil positivity and add Yoshida to the lit cache.\nEither outcome settles the question 'how far do unconditional bounds reach' as a finite number rather than the claimed zero."
}
```

### class_group_amgm_defect (wildcard)
- survives adversarial review: False; prediction matched: True; claimed barrier: B23 ZERO-MEAN DEFECT SYMBOL (class-group AM-GM). Take any decomposition of a counterfeit as (1/h)·(Euler product) + Def in which the archimedean parts, the conductor and the pole agree up to a scalar pole weight. On the pole-free class, Q_Def(f) = (1/2pi) ∫|F|^2 sigma with sigma(t) = -2 sum c_Def(n) n^{-1/2} cos(t log n). This symbol has mean zero, so Q_Def is indefinite as soon as c_Def ≠ 0 on [2,x), with a nearly symmetric spectrum (measured ±(log 2)/2 at x just above 4, ±3.4 at x = 20 for x^2+5y^2, ±7 at x = 113 for x^2+14y^2).
- AM-GM / log-sum-exp convexity controls only the Laplace side (real s > 1), never the unitary Fourier side. So no convexity or Cauchy-Schwarz sign theorem can separate E from zeta_H.
- Anatomy: zeta_H/h is not near-null (m_H >= 1.2e-3; >= 0.53 on the pole-free class). E's failure is an O(1)-versus-O(1) balance along Def's negative directions, not a perturbation of zeta_H's minimizer: Q_E(v_H) stays at +1.3..+4.5. Both blind horizon laws are off by 68-97%.

B24 HECKE-EIGEN INSUFFICIENCY. Exact Hecke multiplicativity of a(n) (the defining input that separates E) gives Def ≡ 0 for every Euler product. It therefore certifies '+' on LEB, euler-rand(d1, d2) and zetaK(-20)[a2=-1], which fail at 5.05, 2.16, 5.78 and 22.47 (36 misses in the blind battery). Hecke-quadratic input is necessary (R2) but not sufficient without the FE (R3). The positivity of the Euler survivor zeta_H is inherited, not explained (R6 unmet).; barrier confirmed: True

The class-group AM-GM defect idea is dead, and the result is a negative one. It explains how the counterfeits fail, not why zeta_H is positive (R6 unmet). conjecture1_proved = False. No mechanism is claimed.

**Setup.** For D = -20, -23, -24 and -56, I built zeta_H = zeta_K times the L(psi) of the non-trivial class characters. The characters come from differences of theta series: (r0 - r1)/2 for h = 2; eta(z)eta(23z) for D = -23; for D = -56, the genus character plus the order-4 pair on Z/4. The coefficients c come from the Satake roots using the Hecke recursion. Multiplicativity holds exactly for n <= 200, and the c values agree with the Dirichlet-series log to within 1e-31. The split Q_E = Q_{zeta_H}/h + Q_Def is exact:
- the archimedean part cancels to 5e-15;
- the pole weight of Def is 1 - 1/h (checked to 9e-16);
- an independent build of Def agrees to 6e-15.

c_Def lives on non-prime-power and impure n. For x^2+5y^2 these are n = 4, 6, 9, 14, 16, 21, and c_Def(36) = -7.167.

**Decisive test: negative.** For every x > 4, Q_Def is indefinite on both the full class and the pole-free CC class, with an almost symmetric spectrum:
- just past x = 4, ±0.347 = ±(log 2)/2;
- at x = 20, [-3.46, +3.44] for D = -20 and [-4.54, +4.47] for D = -23;
- at x = 113, [-7.00, +6.86] for D = -56.

The structural reason: on the pole-free class, Q_Def = ∫|F|^2 sigma / 2pi, where sigma is a cosine sum with mean zero. AM-GM gives a sign only on the real s-axis (the Laplace side), not on the unitary axis. So no convexity sign theorem can exist; I record this as barrier B23. The variance diagnostic was not run, because the condition for running it (Q_Def <= 0) failed.

**Anatomy.**
- m_H = lambda_min(Q_{zeta_H}/h) is not near-null. Its minimum over the grids is 1.17e-3, it stays >= 0.53 on the pole-free class, and it decays slowly (about e^{-0.24x} for D = -20). Averaging forms whose near-null directions differ makes zeta_H/h comfortably positive.
- E's negative direction is not near zeta_H's minimizer v_H: Q_E(v_H) = m_H + Q_Def(v_H) stays at +1.3 to +4.5 in the even sector.
- E fails where Def's O(1) negative directions outweigh zeta_H/h's O(1) positivity in the same directions.

**Blind horizon laws** (N = 128, with N = 64 agreeing to 1e-3):

| D | law 1 | law 2 | true x_E |
|---|---|---|---|
| -20 | 2.79 | 6.34 | 19.82 |
| -23 | 2.30 | 4.60 | 27.63 |
| -24 | 3.09 | 10.04 | 31.77 |
| -56 | 2.81 | 15.37 | 94.44 |

Law 1 is 'first x with |Q_Def(v_H)| > m_H'. Law 2 is 'first x with lambda_min of Q_Def on span{v_H, pole} < -m_H'. Both are off by 68-97%, and law 1 is triggered by the bare pole block. Q_Def is O(1) and indefinite from the start, so the horizon is set by zeta_H's own margin, which is circular.

**Battery** (blind; xs = 3..36, plus x = 100 for the Epsteins). The predictor says '+' when a(n) is Hecke-multiplicative, '-' past its own law-2 crossing when it identifies a theta series, and abstains otherwise.
- Scores: n = 228, agree 133, catches 11, false alarms 23 (counterfeits below their horizon), misses 36, abstain 36; useful = False, sharp = False.
- No false alarms on control+ members and no misses on counterfeits. All four Epsteins are caught at x = 100.
- LEB, euler-rand d1 and d2, and zetaK(-20)[a2=-1] are single Euler products, so Def = 0. The method calls them '+' and misses every one past 5.05 / 2.16 / 5.78 / 22.47. This confirms barrier B24: Hecke-eigen input alone is insufficient (R3).
- The DH family has no class-group decomposition, so the method does not apply to it.

**Preregistration.** It matched, with two corrections. m_H decays more slowly than exp(-x/2) and is not near-null. The DH rows are abstentions by design, not the false alarms I preregistered.

**Numerics.** Float64 Galerkin with the Neumann basis, N = 64 and 128, both parity sectors. The negative Ritz values of Q_Def witness the indefiniteness, and the symbol identity makes it exact in the limit. There is no positivity claim, so no certificate is needed. mp was not needed: every m_H is above 1e-3, and the noise floor is 6.5e-13.

**Harness note (C11 still open).** harness/README.md still lists DH at about 30.6, not converged, while zoo.py has 30.571. The battery also flags DH at x = 32 as positive at N_mp = 24.

**Files** (all in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/class_group_amgm_defect/):
- cg.py – builds zeta_H, E, the pole-free constraints and the restriction
- PREREG.txt – preregistered prediction
- step1.py / step1.log – sanity checks
- step2.py / step2_all.log / step2_20_23_24_56_64_128.json – the decisive test
- step3.py / step3.log / step3.json – horizon laws
- symbol.py / symbol.log – zero-mean symbol check
- step4.py / step4_law2.log / step4_law2.json – battery

A path bug made steps 2 and 3 write their JSON to the scratchpad root; I moved those files here. All processes have finished and the monitors are stopped. The harness was not modified.

**Skeptic:**

```json
{
 "angle": "class_group_amgm_defect (wave 4 wildcard): E_Q = (1/h) sum_psi L(s,psi), so Q_E = Q_{zeta_H}/h + Q_Def, where Def is the AM-GM defect log(mean L) - mean(log L). The hoped-for sign theorem Q_Def <= 0 on the pole-free class fails. The proposal submits this as a negative result: claimed barriers B23 (zero-mean defect symbol) and B24 (Hecke-eigen insufficiency).",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "No positivity mechanism, and the proposal says so itself (alive=false). Positivity of the survivor zeta_H = prod_psi L(psi), the Dedekind zeta of the Hilbert class field, is assumed. Q_{zeta_H} >= 0 for all x is exactly RH for zeta_H, so it is fully circular (R6 unmet).",
  "The Euler product is not used nonlinearly and globally in any essential step. At the form level the split Q_E = Q_H/h + Q_Def is LINEAR in c: c_Def is just defined as c_E - mean(c_psi). The only nonlinearity is the map a -> c, which is the usual log-derivative. So the B1 linearity barrier applies directly.",
  "It would also go through verbatim for a counterfeit. Davenport-Heilbronn is itself a weighted average of two Euler products with complex weights, DH = [(1-i xi)L(chi) + (1+i xi)L(chibar)]/2, so the same log-of-mean minus mean-of-log defect exists for it. The battery's 'abstain on DH' is a design choice, not a structural limit. With complex weights AM-GM gives no sign even on the real axis.",
  "The rigour of the barrier argument is misattributed. The 'wave packets near argmax/argmin sigma' heuristic is not a proof: on the window, |F|^2 has frequency width ~1/A, which is comparable to the variation scale 1/log x of sigma. The correct elementary proof is the two-bump test described under what_is_real.",
  "B24 is not a new barrier. That Def = 0 for every Euler product, so the predictor calls LEB, euler-rand and the a2-flip '+', follows by construction of the predictor. Its content is B22 plus R3.",
  "The battery predictor is effectively a lookup. It says '-' for a non-multiplicative theta series of discriminant -q past the method's own law-2 crossing, so its 11 catches and 23 false alarms carry no information about a mechanism."
 ],
 "prereg_honored": true,
 "counterfeit_check": "The decomposition is not specific to theta series. Any counterfeit that is a weighted sum of Euler products (DH with complex weights, family averages) has the same defect split. For E, zeta_H/h is positive while E fails from x_E = 19.82. The split separates E from zeta_K only because the Euler-product summand's positivity is assumed. Anatomy check, independently reproduced for D=-20 at x=20, N=128, even sector, at E's own minimizer v_E: Q_H/2(v_E) = +0.962 and Q_Def(v_E) = -0.963, and lambda_E = -1.8e-4 is their small difference. At x=23.8 the pair is +4.044 / -4.099. So the counterfeit fails through an O(1)-versus-O(1) cancellation. It is not a small perturbation of zeta_H's near-null direction: at zeta_H's own minimizer v_H, Q_Def(v_H) = +1.28..+1.76 in the even sector for x = 8..23.8.",
 "numerics_reproduced": "Scripts, logs and outputs are all in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/class_group_amgm_defect_skeptic/:\n- cgskep.py, independent code with NO harness: my own lattice counts, my own class-character tables (full Z/4 table for D=-56, cubic characters for D=-23), c from a by the Dirichlet log-derivative, and my own Gauss-Legendre comb matrix and pole-free constraints.\n- mH_check.py, law_check.py, m24.py: semi-independent. zeta_H is built from the harness Dirichlet and Dedekind LData (chi_-4 x chi_5 for D=-20, chi_-3 x chi_8 for D=-24), not from theta series or cg.py, and Def comes from my own comb.\n- Outputs: indep.log, mH_check.log, law_check.log, m24.log.\n\nResults:\n(1) c_Def reproduced exactly for all four D (D=-20: 4:0.693, 6:3.584, 9:4.394, 14:5.278, 16:0.693, 21:12.178, 36:-7.167; c_E(36) = -7.16704). The Hecke defect is 0 for n<=200 (1.6e-40 for the D=-23 cubic characters).\n(2) Pole-free Q_Def spectra (even sector, N=128) match to 3-4 digits:\n- D=-20: x=5 [-0.3466, 0.3466]; x=10 [-2.5046, 2.5046]; x=20 [-3.4590, 3.4368]; x=23.787 [-4.8629, 4.8552].\n- D=-23: x=20 [-4.5353, 4.4736].\n- D=-24: x=20 [-3.0856, 3.0633].\n- D=-56: x=113.328 [-7.0042, 6.8606].\n- Caveat: at x=113 the N=64 range is [-5.93, 6.09], so the \u00b17 figure is a Ritz lower bound on the spectral radius, not a converged value.\n(3) The identity Q_E = Q_H/2 + Q_Def holds to 3.7e-14 .. 2.3e-13 through the independent Dirichlet route.\n(4) m_H(D=-20) = 2.3452e-2 at x=20 and 9.578e-3 at x=23.8. m_H(D=-24, x=38.124, even) = 1.1680e-3. All match. The pole-free m_H for D=-20 is >= 1.22.\n(5) Horizon laws for D=-20: law 1 = 2.78669 and law 2 = 6.34300 at N=128 (proposal: 2.787 / 6.343).\n\nHarness footgun, not a bug: FormResult.parts is returned already G^{-1/2}-normalized. My first cross-check double-normalized the pole and produced a spurious O(1) mismatch. The README should say that parts are in B-normalization.",
 "novelty": "Low.\n- E_Q = (1/h) sum_psi L(psi) is classical (Hecke; class-group orthogonality on r_C(n)).\n- The indefiniteness lemma is elementary: a pure translation kernel with no identity component.\n- B24 duplicates B22 and R3.\n- The one genuinely informative item is quantitative anatomy, which is new to the ledger:\n  - zeta_H/h is not near-null. m_H is 5-100x larger than zeta_K's own margin, e.g. 1.17e-3 against 1.07e-5 for D=-24 at x=38.1.\n  - E fails at its own minimizer through an O(1)-vs-O(1) cancellation, e.g. +0.962 against -0.963 at x=20.\n  - So counterfeit failure is not a perturbation of a genuine L-function's near-null direction.\n- Literature: nothing in lit/index.json states the no-comparison lemma. The proposal made no web check, and neither did I.",
 "what_is_real": "1. What is real is B23, and it is better stated in its general form, a NO-COMPARISON LEMMA, with a rigorous proof that replaces the proposal's wave-packet heuristic.\n   - Statement: let L1 and L2 have identical Gamma factors and conductor, and pole weights that differ only by a scalar multiple of the pole block. Then Q_{L1} - Q_{L2} restricted to the pole-free window class is -sum_{n<x} dc(n) n^{-1/2} 2 g(log n). Its sup and -inf are each >= max_{n<x} |dc(n)|/sqrt(n).\n   - Proof: take f = phi + eps phi(. - log n0).\n   - phi is a thin bump of width < min_{m != n0} |log m - log n0|, with the three moment conditions \u222bphi = \u222bphi e^{\u00b1u/2} = 0 (preserved under translation).\n   - Then Q/||f||^2 = -eps dc(n0)/sqrt(n0) exactly, with eps = \u00b11.\n   - This reproduces the measured \u00b10.3466 = (log 2)/2 at x=5 for D=-20/-24/-56 and \u00b10.6931 for D=-23, where c_Def(4) = log 4.\n   - Consequence: no comparison or domination principle Q_L >= Q_ref can hold between distinct L-data on the pole-free class. Any AM-GM, convexity or Cauchy-Schwarz ordering is ruled out, because AM-GM gives a sign only on the real axis s>1 (the Laplace side).\n2. Also real, reproduced by me: the exact split (1e-13), the c_Def values, the fact that zeta_H/h is comfortably positive, and the O(1)-vs-O(1) anatomy of E's failure.\n3. Circular: every statement about zeta_H's positivity (GRH for the Hilbert class field).\n4. Prereg scoring. PREREG.txt (mtime 02:09:02) predates all code (cg.py at 02:10:26), and most items were scored honestly, including disclosed misses on the m_H decay rate and the DH abstentions. One miss went unlisted: prereg item 4 predicted Q_Def(v_H) NEGATIVE, but it is POSITIVE (+1.3..+4.5; my +1.28..+1.76 in the even sector for D=-20). The report states the positive value openly in its anatomy but omits it from the 'two corrections'. Law 1 also fired at 2.3-3.1, not the predicted 5-10, and it is triggered by the bare pole block, so law 1 is degenerate.",
 "next_step_if_survives": "The proposal does not survive. The most informative next steps:\n(a) Record the no-comparison lemma (the B23 generalisation above) with its two-bump proof in the ledger. It is short enough to formalize in Lean as a reusable kill-switch for any future 'Q_L >= Q_reference' or convexity-ordering proposal.\n(b) Drop B24 as a duplicate of B22 plus R3.\n(c) Use the anatomy as a calibration target. Measure, across the counterfeit zoo, the ratio Q_{EulerPart}(v_cf) / |Q_Def(v_cf)| at each counterfeit's own minimizer v_cf near its horizon. If it is always ~1 with O(1) magnitudes, any positivity mechanism must control the Euler-product form along directions that are far from its near-null vector, i.e. a GLOBAL lower bound for Q_{zeta_H} on a specific cone. That redirects the search away from near-null-perturbation mechanisms, which this data refutes.\n(d) Document in the harness README that FormResult.parts is already B-normalized."
}
```

### hodge_signature_barrier (barrier_hunt)
- survives adversarial review: False; prediction matched: False; claimed barrier: B23 HODGE-SHAPE BLINDNESS.

(1) The Hodge shape (hyperbolic pole block, primitive A, Schur scalar S) exists per sector. The pole form is 2(a^2 - b^2), rank 1 per sector. Haynsworth gives W_sector(x) <=> [A > 0 and S(x) >= 0]. But the shape is automatic and blind:
- by interlacing, just past any first crossing A is PD and S < 0 for ANY hyperplane (random-l control: 60-100% of random hyperplanes reproduce the pattern);
- the pole plays no role: pole-free L(chi_-20) has the same l-aligned near-null (cos = 0.933);
- the pattern is not universal: DH(kappa=0) dies in A 0.12 past its crossing; E, LEB, DH(kappa=1) and euler-rand die in A further out. E's primitive horizons are 23.38/23.50 (even, C1/C2) and 26.16 (odd), at N=256.

(2) The global index is not 1: E at x=22 has index 2 (even crossing 19.825, odd 21.267).

(3) Kill for zeta: the near-null subspace is a cascade of dimension at least 13-16 per sector at x=20, growing with x. So lambda_A(zeta) <= lambda_{k+1}(Q) is about 5e-53 at x=20 for every codim-k split with k <= 12. The primitive block is as delicate as W(x) itself. R4 applies to BOTH pieces, and no finite-rank ample class exists.

(4) Reduction: a Hodge-index mechanism = [pole-free positivity for all x, itself RH-equivalent] + [S(x) >= 0, which given A > 0 is literally W(x)]. The S-inequality must be Hecke-quadratic (R2), and E's S is an O(1) signed cancellation across the Hecke groups (primes +3.05, c9 -1.20, X -1.92, interaction -1.0 against a net of -0.0055 at x=19.8). So the S-inequality has no perturbative small parameter.

Sharpens R5 and R7, and adds a new requirement: any positivity split must have ample rank >= dim of the zeta near-null cascade(x), which is unbounded.; barrier confirmed: True

B23 HODGE-SHAPE BLINDNESS: the Hodge-index split does not give a mechanism for W(x), and for zeta it breaks outright. In the decisive test on E at x=22, A is positive definite and λ_min(Q) is negative, but the total index is 2 rather than 1. That third ledger criterion fails. My preregistered prediction did not match on three points (details below).

Scripts, logs and witness are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/hodge_signature_barrier/:
- hsb.py builds A, S and the inertias on top of the harness;
- t1 is the decisive test, t2 the horizons, t3 zeta, t4 the Hecke attribution, t5 the zoo table, t6 the random-hyperplane control, t7 the witness and convergence, t8 and t9 the zeta cascade;
- witness_E_x22.json holds the rational Ritz witnesses;
- HodgeShapeBlindness.lean is a Lean skeleton. It was not compiled (no built Mathlib was available), and its sorry lemmas are open obligations.

**Setup.** I use the Neumann basis, Gram-normalized, and l(f) = fhat(i/2).
- Even sector: the pole block is +2·a² (with pf=1). Odd sector: it is −2·b².
- Across both sectors the pole form is 2(a² − b²): hyperbolic, rank 1 per sector.
- C1 means P = ker l, the set {u = v = 0}. C2 adds fhat(0) = 0, which only changes the even sector (it becomes codim 2, with a 2x2 Schur matrix).
- A = Q restricted to P. Because the pole block vanishes on P, A is the same as the pole-free form restricted to P.
- S = min{Q(f) : l(f) = 1}. It equals S_pf + 2 in the even sector and S_pf − 2 in the odd sector.
- Haynsworth: neg(Q) = neg(A) + neg(S).

**Decisive test: E[1,0,5] at x=22.** Float runs at N = 32..1024; mp at dps 40 matches float to 10 digits.

(a) λ_min(A) is positive and converges in N:

| sector, convention | λ_min(A) at N=1024 | Richardson limit |
|---|---|---|
| even, C1 | 0.4322 | 0.4318 |
| even, C2 | 0.4460 | 0.4456 |
| odd (C1 = C2) | 0.23490 | 0.23490 |

These values are about 19 orders of magnitude above the B21 Galerkin-trap regime. No Lane B lower-bound certificate yet.

(b) Inertia:
- Q has one negative per sector, so index 2 in total. The even sector crosses at 19.8254 and the odd at 21.2671 (N=256).
- Q − Pole has exactly one negative, in the even sector (−6.72).

(c) λ_min(Q) at N=512 is −5.467e-4 (even) and −1.683e-2 (odd).
- Rational Ritz witnesses (N=24, 6-digit coefficients) give −5.3135e-4 and −8.4799e-3, identical at dps 40 and 80. They are not interval-certified.

Point (ii) of the assignment is automatic per sector: a rank-1 pole block on top of a PD A allows index at most 1 in that sector. It is not automatic globally, and E at x=22 has index 2.

The wave-3 pole-free horizon is reproduced: A becomes non-PD for E at 23.38 (C1) and 23.50 (C2) in the even sector, and at 26.16 in the odd sector. Wave 3 needs no K7 correction.

**Finding 1: the pattern is a tautology.** Interlacing and Haynsworth imply that, just past any first crossing, A is PD and S < 0 for any functional l with l(v_min) ≠ 0.
- Random-hyperplane control: for 200 random functionals per case, the count with A PD always equals the count with S < 0. That count is 124 to 200 across nine counterfeit and barrier cases.
- The pole plays no role in making l special. The pole-free L(χ₋₂₀) has cos(v_min, l) = 0.933, the same as ζ_K(-20).
- The pattern is also not universal:
  - DH(κ=0) dies in A only 0.12 past its crossing (λ_A = −7.1e-4, S = +1.09).
  - E at 24, LEB at 10, and DH(κ=1) and euler-rand at 10 and 28 also fail in A.

**Finding 2: zeta kills the Hodge shape.** Zeta's near-null set is a cascade, not one direction.
- At x=20, N=32: 13 eigenvalues per sector are below 1e-6. The lowest (even sector) are 3.5e-59, 8.4e-53, 4.9e-47, 1.2e-41, ...
- The count grows with x: per sector 1, 3, 5, 9, 13, 16, 20, 22 at x = 3, 5, 8, 12, 16, 20, 28, 36 (N=48). These are lower bounds on the true count.
- By interlacing, any codim-k primitive split with k up to 12 has a primitive margin of at most about 1e-6. Measured directly, λ_A(zeta, x=20) is 5.4e-53 (C1, N=32, dps 80).
- So wave 3's "O(1) primitive margins" hold for ζ_K(-20) (λ_A = 1.36 at x=22) but not for zeta. This fits Connes–Consani's "very small eigenvalues" (arXiv 2106.01715).

**Finding 3: the payload, a table of S across the zoo and hybrids.** Values are sector-wise S_unit = S·‖l‖², under C1.

| member | x=15 | x=19.8 | x=21 | x=22 | x=28 |
|---|---|---|---|---|---|
| ζ_K(-20) | e .053 / o 2.24 | e .0056 / o 1.00 | e .0031 / o .70 | e .0019 / o .52 | e 7.6e-5 / o .059 |
| E | e .19 / o 3.50 | e 9.7e-5 / o 2.07 | e −.00125 / o .24 | e −.00135 / o −.279 | A<0 both |
| E_pp | e 2.26 / o 2.15 | e 2.44 / o 1.53 | e 2.49 / o 1.32 | e 2.53 / o 1.15 | o −.066 |
| ζ_K + X | e −1.15 | e −1.41 | e −1.46 | e −1.53 | |
| ζ_K + c9 | e −.68 | e −.81 / o −.18 | e −.83 / o −1.02 | e −.85 / o −1.50 | |

Attribution of the ζ_K → E gap, by Shapley values over four groups, even sector:
- The groups are P = the primes 2, 3, 7, 23 (where E has a(p) = 0), c9, PP = the other prime powers 4, 8, 16, 27, 32, and X = 6, 14, 21.
- At x=19.8: P +3.05, c9 −1.20, PP +0.07, X −1.92. The net gap is only −0.0055, and the interaction term is about −1.0, the same order as the main effects.
- At x=22: P +3.19, c9 −1.25, PP +0.08, X −2.03.
- Of the negative push, X gives about 62% and c(9) about 38%. But the sign is decided by an O(1) cancellation against the prime group.
- In the odd sector, the hybrid ζ_K+P+c9+X makes A singular at x≈21–22 (λ_A = −0.0156 at 22). S has poles in coefficient space there, so a linear attribution is ill-defined.

Barrier members:
- LEB, L_G+pole, the a2-flip, euler-rand d1/d2 and DH(κ=1) all first fail through S < 0 with A PD. This is the automatic pattern from Finding 1.
- Further out, several of them (LEB, euler-rand, DH(κ=1), E) also fail in A.
- DH itself stays positive at N=32 mp through x=32; resolving it needs N ≥ 120.

**Reduction statement.** A Hodge-index mechanism has to prove two things:
- A(x) > 0 for all x. This is pole-free Weil positivity, which is again RH-equivalent, and for zeta it is just as near-null.
- S(x) ≥ 0. Given A > 0, this is literally W(x).

So the mechanism has to be exactly an inequality on S(x) that is Hecke-quadratic (R2). E shows that such an inequality has to control O(1) signed Hecke-group contributions to within 1e-3 to 1e-5, with no small parameter. It also has to face an "ample" rank that is unbounded, because the zeta cascade dimension grows with x.

**New B-entry.** B23 HODGE-SHAPE BLINDNESS, with the content given in claimed_barrier.

**Preregistered prediction versus outcome** (prediction_matched = false):
- Missed:
  - I predicted total index 1 in the odd sector; it is 2, and E fails first in the even sector.
  - I predicted an O(1) primitive margin for zeta; it is about 1e-53.
  - I predicted the universal "dies in S" pattern at all listed x; it fails further out, and for DH(κ=0) almost immediately.
- Matched:
  - A is PD under both conventions.
  - λ_min(Q) is in the predicted range.
  - Q − Pole has index 1 in the even sector.
  - X is the larger share of the negative push.

**Not done:**
- Lane B lower bound on A.
- Arb interval certification of the witnesses.
- Q7 (earliest unitary-cube vertex).
- Battery scoring. It is not applicable here: the only predictor this split gives reads off the inertia of Q, which is circular.

**Harness notes.** No harness bugs found. The mp path of form.Q returns no parts, so hsb.py builds the pole vectors from Window.scalars. The C11 README horizon mismatch is still present.

conjecture1_proved = False.

**Skeptic:**

```json
{
 "angle": "Wave-4 adversarial skeptic of hodge_signature_barrier (B23 Hodge-shape blindness). I rebuilt the Weil window form from scratch without the harness, in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/hodge_signature_barrier_skeptic/indep.py. It works in u-space: closed-form autocorrelations g_mn(u) of the Neumann basis, the archimedean term from the integral formula psi(z) = -gamma + int (e^-t - e^-zt)/(1-e^-t) dt, and Gauss-Legendre quadrature. The coefficients c(n) are recomputed from lattice counts (Epstein), the Kronecker symbol and the von Mangoldt function. Scripts: t1.py, t2_cascade.py, t3_wit.py, t4_misc.py. I then re-checked the decisive E numbers, the witnesses, the zeta near-null cascade, the claimed failure of DH(kappa=0) in the primitive block, and the hybrid Schur scalars. On top of that I attacked three things: the logic (tautology, interlacing), the prereg scoring, and the explanation offered for the cascade.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "It is not a mechanism, and the proposal says so itself (alive=false). The Euler product plays no role in the split. The Schur-complement/Haynsworth reduction is lossless linear algebra, so '[A>0] and [S>=0]' is just W(x) written in another way. It goes through verbatim for every counterfeit. The random-hyperplane 'control' is Haynsworth restated: with index 1 in a sector, exactly one of {A not PD, S<0} holds, so equal counts are forced. They are not evidence.",
  "Prereg scoring error. Prediction (c) was lambda_min(Q) in [-1e-2, -1e-3]. The measured values are -5.47e-4 (even) and -1.683e-2 (odd), and I reproduced both. Neither sector is in the range, yet the report lists (c) under 'Matched' ('(a) and (c) hold'). The hybrid sub-prediction 'interaction about 10-20%' also failed: the interaction is -1.01 against a net gap of -0.0055 and a negative push of about -3.1, so it is roughly 30% or more of the push. That miss is not reported. Nothing timestamps the prereg before the runs; it exists only in the proposal JSON. The headline prediction_matched=false is honest.",
  "Mechanism for the cascade is misattributed. The report says the zeta near-null count 'roughly tracks the number of prime-power atoms below x', and it gives this 30% odds as a clean law. Its own data and mine refute it. zeta_K(-4) has the same prime-power support with doubled weights, yet at x=20 it has only 1-2 eigenvalues per sector below 1e-6 (3/2 below 1e-3), against 16-17 for zeta. The zeta count also exceeds the prime-power count: 17 vs 12 at x=20 (N=64), 20-21 vs 15 at x=28, 22-24 vs 17 at x=36 (N=48). A Paley-Wiener degrees-of-freedom versus Riemann-von Mangoldt zero-count heuristic fits every row I measured. It predicts a per-sector near-null dimension of about d*(x/q)^{1/d}: zeta about x-7/8; zeta_K(-4) about sqrt(x); L(chi_-4) about x/4; zeta_K(-20) about 2*sqrt(x/20), roughly 2 at x=22. The cascade is therefore an analytic-conductor effect ('missing zeros below T* = 2*pi*(x/q)^{1/d}'), not an arithmetic one, and it is counterfeit-blind.",
  "L3 is stated too strongly in claimed_barrier and mechanism: 'past the first crossing, S<0 and A PD for ANY l with l(v_min) != 0'. It holds only in a neighbourhood of the crossing that depends on l, which is exactly why DH(kappa=0) already fails in A 0.12 past its crossing. The Lean skeleton's version of L3 (A PD and Q v v < 0 imply a negative point on the slice) is the correct, trivial statement.",
  "Minor. The C2 Schur-matrix eigenvalues and 'S_unit 300' in t1.log depend on how the fhat(0) constraint is scaled. My unit-vector normalization gives 405.8 where the report gives 185.2. Only the signs and inertia are invariant, so do not quote those magnitudes. witness_E_x22.json does not say that its coefficients are in the unnormalized basis (gram[0] = 2A); they are, and in that basis they reproduce."
 ],
 "prereg_honored": false,
 "counterfeit_check": "The Hodge shape does not separate anything, and it goes through verbatim for counterfeits.\n- Haynsworth forces the 'dies in S with A PD' pattern for any l not orthogonal to v_min near a crossing.\n- I confirmed the pattern is not universal. DH(kappa=0) at x=20.2, odd sector, N=128: lamQ = -3.96e-3, lamA = -7.124e-4, S = +1.0889, cos(v_min, l) = 0.159. This matches the claimed -7.1e-4 / +1.09 / 0.16.\n- E at x=24, even sector, N=128: lamA = -0.0688 (claimed -0.069), and S_unit is positive (+2.5e-3 at N=128; the report quotes +6.4e-4, N not stated).\n- The zeta cascade that kills the bounded-rank split is set by the Gamma factor and conductor (zero density against Paley-Wiener dimension). A counterfeit with the same analytic data therefore carries the same cascade. The barrier is a correct negative result about the shape, but it contains no arithmetic that could separate zeta from E or D.",
 "numerics_reproduced": "Everything below comes from my independent u-space code, with no harness import. Agreement with the harness is 1e-10 to 1e-12 absolute.\n\n- **E[1,0,5], x=22, N=32:**\n  - even: lamQ = -5.361981679e-4 (harness -5.361981663e-4), lamA(C1) = 0.5107042766 (identical), S = -3.4934e-4;\n  - odd: lamQ = -0.01358531219, lamA = 0.2367904142, S = -0.32559.\n- **E[1,0,5], x=22, N=64:**\n  - even: lamQ = -5.444547538e-4, lamA = 0.4497191841, lamA(C2) = 0.4667847218, pole-free form index 1 (-6.72096);\n  - odd: lamQ = -0.01613263576, lamA = 0.2351189823, S = -0.38943, pole-free form PD (+0.04999).\n- **Inertia.** Index 1 per sector, 2 in total. CONFIRMED.\n- **zeta_K(-20), x=22, N=64:** lamA = 1.3616 (even) / 1.4893 (odd); S = 5.1e-4 / 0.748.\n- **Rational witnesses** (unnormalized basis, N=24):\n  - even: Q = -0.00235260197, Rayleigh -5.313508e-4 (claimed -5.3135080e-4);\n  - odd: Rayleigh -8.47991227e-3 (claimed -8.479912274e-3).\n- **Crossings at N=64:** even 19.8562, odd 21.3230. The claimed N=256 values are 19.8254 and 21.2671; the N-drift is the same size as the harness's known 19.856 to 19.825.\n- **Hybrids, x=22, N=128:**\n  - zK+X even S_unit = -1.533;\n  - zK+c9 = -0.854 (even) / -1.501 (odd);\n  - E_pp = 2.533 / 1.146.\n  - All match.\n- **c_E:** c_E(36) = -7.1670, first negative n = 36, c_E(6, 9, 14, 21) = 3.584, 6.592, 5.278, 12.178. Matches.\n- **Zeta cascade** (float, count below 1e-6 per sector; my quadrature noise is about 1e-12):\n  - x = 5 / 8 / 12 / 20 gives 3 / 5 / 9 / 13 at N=32 (matches t9), and 17 / 16 at N=64 for x=20, still growing with N;\n  - L(chi_-4) at x=20: 3/3;\n  - zeta_K(-4) at x=20: 2/1.\n- **Not reproduced:** the mp values 5.4e-53 / 3.5e-59 (I used float only). The interlacing consequence lamA <= lambda_{k+1}(Q) < 1e-6 for k <= 12 follows from the float count.",
 "novelty": "Low to moderate.\n- **Standard:** Haynsworth inertia additivity and Cauchy interlacing. The observation that a lossless Schur split contains exactly W(x) is immediate.\n- **Already in the literature:** the very small eigenvalues of zeta's window form (Connes-Consani, Enseign. Math. 69 (2023), arXiv:2106.01715, verified in the cache; Connes-Moscovici prolate, arXiv:2112.05500).\n- **Genuinely useful within the program:**\n  - (a) It corrects the wave-3 anatomy claim of 'O(1) primitive margins'. That claim is true for zeta_K(-20), whose cascade dimension is about 2, but false for zeta, whose cascade dimension is about x.\n  - (b) It adds a quantitative requirement that any positivity split must meet: the ample/pole rank has to be at least the near-null dimension, which is unbounded in x.\n  - (c) It shows E at x=22 has index 2, one per sector.\n- **Skeptic addition:** the near-null dimension follows an analytic-conductor law, about d*(x/q)^{1/d} per sector, not the proposed prime-power law. This makes B23(3) sharper and shows it is purely archimedean and counterfeit-blind.",
 "what_is_real": "1. **Exact elementary facts.** The per-sector pole form is hyperbolic, 2(a^2 - b^2), rank 1 per sector. Haynsworth: neg(Q) = neg(A) + neg(S). Interlacing: lambda_1(Q) <= lambda_1(A) <= lambda_{k+1}(Q). With these, the Hodge-index split carries no information beyond W(x), and 'counterfeits die in the scalar' near a crossing is automatic for generic l.\n\n2. **E[1,0,5] at x=22.** I reproduced every decisive number independently. A is PD with margin 0.43 (even) and 0.235 (odd). Q has index 2, one per sector. The pole-free form has index 1, in the even sector. Rational witnesses show Q(f) < 0 in both sectors.\n\n3. **Zeta near-null cascade.** Reproduced: at least 13 eigenvalues per sector below 1e-6 at x=20 (N=32), and 16-17 at N=64. So any codim-k split with k <= 12 has a primitive margin below 1e-6 for zeta, and a bounded-rank 'ample class' cannot exist.\n\n4. **Right explanation for the cascade (skeptic's).** It is the gap between Paley-Wiener degrees of freedom and zero count, which scales with the analytic conductor as about d*(x/q)^{1/d} per sector. It is not the prime-power count. zeta_K(-4) has 1-2 near-null eigenvalues against zeta's 16-17 at x=20, even though zeta_K(-4) has more prime-power atoms.\n\n5. **Hybrid S table and the O(1) Hecke-group cancellation.** Reproduced at the rows I checked. S is a signed near-cancellation of O(1) terms. It is descriptive and has no mechanistic content.\n\n**Summary.** B23 is a correct negative result about the Hodge/Schur shape, but it is mostly a tautology and it is not a mechanism. The prereg was mis-scored on (c).",
 "next_step_if_survives": "Does not survive as a mechanism. Keep B23 in the ledger with three edits:\n- restate L3 as the local (l-dependent) statement;\n- replace the 'tracks prime-power atoms' explanation with the analytic-conductor count;\n- fix the prereg scoring of (c).\n\nThe most informative next probe is to test the conductor law precisely: near-null count(x; d, q) \u2248 d*(x/q)^{1/d}, with O(1) corrections from the 7/8 term and the threshold. Run it at larger N (at least 128, mp for zeta) across zeta, L(chi_q) for several q, zeta_K(D) and DH/E. If it holds, any positivity split needs 'ample rank' of about x/q for degree 1. Then prove the upper-bound half rigorously: construct about T*/pi Paley-Wiener test functions that vanish at the first N(T*) zeros and have tails below epsilon. That half is a Landau-Slepian argument plus Riemann-von Mangoldt and needs no RH. It would turn B23(3) into a theorem, ready for Lean or Arb."
}
```

### ks_pshr_sdp (micro_experiment)
- survives adversarial review: False; prediction matched: False; claimed barrier: B23 KS-PSHR DICHOTOMY. Kernel-split place-separable positivity (free archimedean shares theta_p, free pole weights mu_p, identity transfer c_p, and smooth transfer kernels s_p with K hats) is either lossy or tautological.

(a) Bounded complexity is lossy and false-alarms on zeta first. It is feasible for zeta at 3.02 (efficiency about 0.9-1.0, blocks mp/interval-verified PD up to N=64). But the Farkas certificate for zeta at x=5 (K=16, N=16, both sectors) is exact over Q on mp-rationalised data: Y_2, Y_3 are PD, stationarity holds exactly, and the scaled dual bound is -0.046. The necessity test gives horizons x_KS(K) <= 4.14, 5.31, 7.0 and 8.0 for K = 8, 16, 24, 32 (N=48). All K <= 32 are dead at x=10. The fixed-K battery (K=8) is not useful: 16 false alarms on controls, and E is accepted at x=10 while zeta is rejected at 4.5. Loss is set by the margin: zeta_K(-20) survives to x=21 at K=16/32.

(b) Unbounded complexity is tautological. As K grows, the optimal transfer becomes transport of prime atoms (fixed-mass spikes at log p), theta_p and mu_p tend to 1/#places, and M_p tends to Q/#places. The pole kernel lies in the smooth span, so the pole weights are unidentifiable. At finite N with K >= 2N the trivial split is exact (residual 4.5e-15).

There is no intermediate regime with place-local structure. Feasibility is decided by the global near-null vector (every block must annihilate it), not by local data. This is consistent with B13 (finite primes act as a metric) and B20 (bounded-complexity certificate families cannot reach all x).; barrier confirmed: True

KS-PSHR (ks_pshr_sdp, wave 4) — full write-up. conjecture1_proved = False.

**Setup.**
- Scripts: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/ks_pshr_sdp/
  - build.py: mp blocks. Arch, Pole and the per-prime W_p use harness Window scalars and form._assemble_mp with component-zeroed scalars. Hat-spline transfer matrices are K[s] = int s(y) atom(y) dy with 6-point Gauss per knot interval.
  - sdp.py: cvxpy with CLARABEL/SCS.
  - cert.py: exact-complement mp re-verification plus mp.iv interval LDL.
  - nec.py: rigorous-structure necessity test.
  - horizon.py: bisection on x for the necessity test.
  - relsdp.py / relsdp2.py: a Q-congruence-scaled mp barrier SDP, with Frobenius-orthonormalised transfer directions and a warm start.
  - dualcert.py: exact rational Farkas certificate using sympy and fractions.
  - ks_battery.py, step5.py.
- Logs: run2_3.02.log and the matching .json, horizon.log, nec_Kscan.log, rel2_zeta5b.log, ks_battery.log, ks_battery_N24_K8.jsonl.
- Identity sum_p M_p = Q: 9.2e-41 at dps 40.
- Arch is not spline-representable (log|k| symbol), so it is imposed at the Galerkin level through theta_p. The pole kernel is smooth and therefore lies in the spline span, so mu_p is unidentifiable: unconstrained runs gave mu = 118, 175, 599, 3882. Runs are reported with simplex mu, theta >= 0 and with free mu.

**Step 1 (x=3.02, zeta, {2,3}, both sectors): feasible — the preregistered prediction was wrong.**
- Ratio t*/(lambda_min/2), SCS, by (N,K): 16/8: 0.98; 16/16: 1.00; 24/8: 0.95; 32/16: 0.99; 48/8: 0.96; 48/32: 1.00; 64/8: 0.96; 64/32: 0.99.
- lambda_min(Q) (even sector): 5.76e-8, 4.91e-8, 4.68e-8, 4.57e-8, 4.54e-8 at N = 16, 24, 32, 48, 64.
- CLARABEL was 'optimal_inaccurate' throughout. It gave spurious negative t at (16,32), (24,16) and (32,32), but its points still verified PD at (16,32) and (32,32).
- Re-verification from the SDP parameters (exact dyadics, exact complement): the blocks are PD by mp eigenvalues and interval LDL for 14 of 15 (N,K) pairs.
- Relative mp barrier at N=12, K=8: scaled tau* = 0.367 (maximum 0.5), and the rational dual bound is 0.368.
- Degeneracy caveat: at K >= 2N the trivial split is exact (residual 4.5e-15 at N=16, K=32). Non-degenerate feasibility holds at N=64, K=8 (residual 0.93).
- delta-inflation: t*(delta) = t*(0) + delta/2 exactly, because of the c_p transfer. Numerically, t*(delta) - delta/2 = 2.378e-8, 2.345e-8, 2.346e-8, 2.334e-8. The extrapolation is therefore trivial and uninformative.

**Step 2 was not reached at 3.02, since the problem was feasible there. The certified dual was obtained at x=5 instead.**
- zeta, x=5, places {2,3}, N=16, K=16, both sectors jointly, with theta, mu, c and 17 hats all free.
- Barrier tau* = -0.0479, gap 0.0020.
- Exact certificate: Y_2, Y_3 are PD by exact rational LDL, with min pivots (0,2) 3.74e-5, (0,3) 3.66e-5, (1,2) 3.38e-5, (1,3) 5.53e-5.
- The shared multiplier is exact: sum_s tr((Y_2 - Y_3) V_i) = 0 over Q for Arch, Pole, I and every hat.
- F = sum_s [tr Y_3 - tr((Y_2 - Y_3) W~_2)] = -0.04598 tr Y < 0.
- Caveat: the rationalised data are the mp dps-90 Galerkin entries and the mp Cholesky scaling. These are not Arb intervals. The margin is 0.046 against a data error of about 1e-80.
- By compression this kills the continuum K=16 family at x=5.
- The pole enters with a free sign, so the simplex restriction would only strengthen the result.

**Complexity horizons (necessity test).** The test rests on this inequality: if M_p >= 0 and M_p <= Q, then for every v, (M_p v)^T Q^{-1} (M_p v) <= v^T M_p v <= v^T Q v. Minimising over the transfer parameters is an exact mp least-squares problem, and rho > 1 certifies infeasibility.

At N=48, joint sectors:

| K | bracket for x_KS(K) | rho at upper end |
|---|---|---|
| 8 | [4.11, 4.144] | 1.21 |
| 16 | [5.281, 5.3125] | 1.12 |
| 24 | [6.969, 7.0] | 1.41 |
| 32 | [7.969, 8.0] | 1.26 |

- rho is jagged in x (for K=8: 1.2 at 4.144, 609 at 4.178, 8.2 at 4.246).
- rho grows with N at fixed K. For example K=16 at x=6: 280 at N=24, 399 at N=32, 610 at N=48.
- At x=10 all K <= 32 are dead with rho >= 1e11.
- The necessity test is weaker than the SDP: relsdp already kills K=16 at x=5, where rho is 0.19.

**Mechanism of the loss.**
- The near-null vector v of zeta must be annihilated by every block, M_p v ~ 0. A transfer of resolution K cannot do this once lambda(x) (about 2e-17 at x=5, 1e-31 at 8, 1e-43 at 10) falls below the transfer approximation error.
- As K grows, the optimal s_p becomes spikes of fixed mass at log p, i.e. atom transport, with theta and mu tending to 1/2. The limit is the trivial split Q/#places.

**Step 5 (formally not triggered; run for calibration).** zeta_K(-20), N=32, places [2,3,5,7]:
- x=10: K = 8/16/32 feasible, efficiency 0.63 / 0.91 / ~1.
- x=15: K=8 infeasible (t = -0.099); K = 16/32 feasible (0.70 / 0.99).
- x=21: K=8 infeasible (t = -0.144); K = 16/32 feasible (0.66 / 0.72).
- So loss depends on the size of the margin, and near-null controls die first.

**Battery (blind, K=8, N=24).**
- Predictor: -1 if Q is not PD or rho > 1; +1 if the float SDP gives t* > 1e-10; otherwise abstain.
- Scores: agree 32, catches 12, false alarms 22 (16 on controls), misses 0, abstain 2. useful = False, sharp = False.
- Row pattern:
  - zeta: false alarm from 4.5.
  - L(chi_5): false alarm from 10.
  - zetaK(-20): false alarm from 15.
  - E: + through 10, false alarm at 15, caught at 21 and above.
  - DH: false alarms at 15-25.
  - LEB: caught from 6.
  - zetaK(-20)[a2=-1]: false alarms at 15 and 21, caught at 25 and above.
- The battery reports a known conflict at DH x=32 (N_mp = 24).

**R3 probe.**
- LEB: feasible at 3 and 4.5, infeasible from 6, and at 5.2 infeasible because Q_LEB < 0.
- zeta: infeasible at 5.2 for every K <= 16 (necessity test, and relsdp at x=5).
- So there is no separation. KS-PSHR never sees the FE, and its catches are inherited from Q < 0 (B2).
- The feasibility-deciding feature is global (the near-null vector), not the per-place W_p against the Arch share.
- The local-block criterion without transfer is scalar PSHR, which is B3-dead.
- B13 is consistent: the transfer acts as metric freedom. Death as x grows is predicted and observed.

**Death classes and ledger mapping.**
- Bounded K: lossy split (B3/R4), false alarm on zeta, and a complexity barrier like B20.
- Unbounded K: restatement of W(x) (R7 tautology).
- Linear in c: B1/R2 fail.
- No FE: R3 fail.

**Harness notes (report only; the harness was not edited).**
- form.Q(parts=True) exists only on the float path. The mp parts were built here via _assemble_mp with zeroed scalars. This is a feature request, not a bug.
- C11 stands.

**Summary of the prediction.** The prediction was wrong at 3.02 (feasible, not infeasible). It was right on "lossy by 5-8" (zeta dies at x_KS(K) between 4.1 and 8 for K <= 32) and on inherited catches. It was wrong on zeta_K(-20) being lost before 24: that happens only at K=8. KS-PSHR is dead as a mechanism.

**Skeptic:**

```json
{
 "angle": "ks_pshr_sdp (wave 4 skeptic). This is kernel-split, place-separable Weil positivity. Each block M_p = theta_p Arch + mu_p Pole + c_p I + K[s_p] - W_p must be PSD, and the blocks must sum to Q. I rebuilt the window form independently and re-solved the SDP myself.",
 "survives": false,
 "barrier_confirmed": true,
 "fatal_flaws": [
  "It is linear in c(n) and never uses multiplicativity or the functional equation. Grouping coefficients by prime is additive bookkeeping, so B1 applies unchanged.",
  "KS-PSHR implies W(x), because the blocks sum to Q. Every catch is inherited from Q < 0 (LEB from 6, E from 21), so B2 applies. The construction goes through verbatim for any counterfeit.",
  "It is lossy, and it misfires on the true zeta first. zeta is certified infeasible at x=5 for K=16 and K=24, while lambda_min(Q) = 2e-17 > 0. The blind battery (K=8) has 16 false alarms on controls and accepts E at x=10. This is B3 plus B20 again, in a richer family.",
  "The 'horizons' x_KS(K) from the necessity test are only points of certified infeasibility, not horizons. rho is not monotone in x (K=8: 1.2 at 4.144, 609 at 4.178, 8.2 at 4.246). The lower bracket ends (rho < 1) do not certify feasibility. My SDP shows K=24 is already infeasible at x=5 (N=24), well below the claimed '<= 7.0'. The necessity brackets are loose upper bounds.",
  "Overclaim in part (b) of B23. 'Tautological at unbounded K' is only shown at finite N, where K >= 2N spans the Galerkin image. There is a genuinely non-trivial feasible regime: x=5 with K=32 is feasible at N=24 (efficiency 0.59) and at N=32 (0.545), both with K < 2N. So 'no intermediate regime' is false as literally stated. The true statement is that the required K grows with x.",
  "The 'optimal s_p = atom-transport spikes at log p' reading is not an identifiable observable. The SDP optimum is non-unique, and mu is degenerate with the spline span. My K=32/N=32 solution has mu = -7105.6 with hats about 14000-19000, which are almost exactly -mu*2cosh(u/2). The residual is noisy and O(1-10): a -9.4 dip near log 3 and a ragged +-5 structure near log 2, with no clean fixed-mass spike.",
  "Minor: the proposer quotes a 'data error ~1e-80', but their hat matrices use 6-point Gauss quadrature, so the error is really the quadrature error. Their Farkas certificate is exact for a discrete-atom family at the Gauss nodes, not literally for hat splines. My 40-point-per-interval Gauss-Legendre rebuild removes this caveat and reproduces the result, so the conclusion stands."
 ],
 "prereg_honored": true,
 "counterfeit_check": "It goes through verbatim for any counterfeit. The only coefficient input is the additive per-prime grouping of c(n), with non-prime-power n assigned to their smallest prime factor for E. No functional equation, no multiplicativity, no Euler nonlinearity. KS-PSHR(K) implies Q >= 0, so a counterfeit can only be caught where Q_counterfeit < 0 (inherited) or where the method is lossy, and the lossy cases hit near-null controls first. That the order is inverted (zeta rejected at 4.5, E accepted at 10) is consistent with feasibility being set by the size of the margin lambda(x), not by arithmetic: zeta's margin decays superexponentially, E's does not. Grouping all places other than 2 into one block (my runs at x=5.3125 and x=8) is a relaxation, so certified infeasibility there is even stronger. Nothing in the method could see reciprocity or the functional equation.",
 "numerics_reproduced": "Independent code, not the harness assembly: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hengine/w4/ks_pshr_sdp_skeptic/.\n- kskw.py builds Q in position space. Arch uses the psi integral representation: Arch = -log(pi) g(0) + int_0^inf [g(0)e^{-2u}/u - g(u)e^{u/2}/sinh u] du. Pole uses exponential moments; comb uses closed-form autocorrelations. Hat transfers use 40-point Gauss-Legendre per knot interval.\n- ks.py whitens by the mp Cholesky factor of Q and Frobenius-orthonormalises the transfer directions jointly over both sectors in mp. It then solves a float SDP on O(1) data and verifies in mp: the primal by eigenvalues, the dual by exact-projection stationarity, a PSD shift, and F/trY.\n\n(0) Independent check of the harness path. My Q matches harness form.Q(mp) to 5.9e-40 / 6.4e-40 (x=3.02, N=8, dps 40, both sectors). lambda_min = 8.14876060707e-8 / 1.75701508087e-5 in both codes. At x=5, N=16: lambda_even = 2.0288e-17, matching the proposer.\n\n(1) x=3.02, N=12, K=8: scaled t* = 0.36718 (SCS and CLARABEL agree; efficiency 0.734), mp-verified PD. The proposer reports 0.36697 (barrier gap 1.5e-3). REPRODUCED.\n\n(2) x=5, N=16, K=16: t* = -0.04774. Independent mp dual certificate: Y PSD (after a 7e-10 shift), stationarity residual 9e-64 in the original directions, F/trY = -0.04774. The proposer reports -0.0479 (barrier) and -0.046 (rational certificate). REPRODUCED.\n\n(3) New data:\n\n| x | N | K | t* | status |\n|---|---|---|---|---|\n| 5 | 24 | 16 | -0.2016 | dual certificate |\n| 5 | 24 | 24 | -0.0389 | dual certificate |\n| 5 | 24 | 32 | +0.296 | primal mp-verified, efficiency 0.59 |\n| 5 | 24 | 40 | +0.317 | primal mp-verified |\n| 5 | 32 | 32 | +0.2726 | primal mp-verified, efficiency 0.545 |\n| 5.3125 | 24 | 16 | -0.796 | dual certificate, 2-block grouping |\n| 8 | 24 | 32 | -1.328 | dual certificate, 2-block grouping |\n\n- Infeasibility strengthens with N, as compression requires.\n- Feasibility at x=5 needs K roughly 32, and it is lost by x=8. This confirms the qualitative claim that the required complexity grows with x.\n- It sharpens the numbers: K=24 is already dead at x=5.\n- Not reproduced: the N=48 necessity-test rho values and the battery rows.",
 "novelty": "Low. The wave 2 synthesis posed this directly (hodge2 table item 1: 'Connes' semilocal question as a finite SDP'), and the proposer runs exactly that. The negative outcome refines B3: near-null annihilation forces a lossy split. What is new is only the certified instance, now with smooth transfer kernels allowed, plus the observation that the required transfer complexity grows with x, a B20 corollary. The lit cache has nothing on per-place kernel-split SDPs. I did not search the web, so novelty is unverified. It is most likely folklore-level. Closest verified relatives: Connes 1999 (Selecta 5, 29-106; the semilocal trace formula), Connes-Consani 2021 (Selecta 27, Paper 77; the archimedean place only), and Connes-Consani 'Spectral triples and zeta-cycles' 2023. The last explains the tiny eigenvalues that are the mechanism of the loss.",
 "what_is_real": "What is real, in narrowed form (B23'):\n- Kernel-split place-separable positivity is infeasible for zeta at x=5, while Q is positive definite there (lambda_min about 2e-17). The setting is places {2,3}, uniform hat transfer kernels on [0, log x] with K=16 or K=24 knot intervals, and free theta, mu, c.\n- The K=16 case has two independent Farkas certificates: the proposer's exact rational one, and my mp dual on independently built matrices with 40-point quadrature. By compression, the finite-N certificate transfers to the continuum K=16 family, up to quadrature error of order 1e-60.\n- Feasibility does exist in a non-trivial regime: x=5 with K=32 is feasible at N=24 and N=32, with K < 2N and efficiency about 0.55-0.6. It is lost by x=8 at K=32, so the resolution the transfer needs grows with x. Mechanism: every block must annihilate zeta's near-null vector to within sqrt(lambda(x)), with lambda(x) about 2e-17 at x=5 and 3e-31 at x=8, while the approximation error of a d-dimensional transfer family is fixed. This is the B3 argument applied to a richer family, and it is a B20-type complexity barrier.\n- The method is linear, blind to the functional equation, and every catch is inherited from Q < 0, so it is dead as a mechanism (B1/B2). It is not useful on the battery.\n- Not confirmed: part (b) of the claim as stated ('tautological at unbounded K', 'no intermediate regime') and the 'atom transport spikes' picture. These are finite-N artefacts or non-identifiable, because the SDP optimum is not unique and mu is degenerate with the spline span.\n- The ledger should carry B23' (lossy at every bounded K, certified at x=5 for K=16 and K=24, required K grows with x), not the dichotomy.\n- The preregistration was scored honestly: the proposer reported prediction_matched=false after finding feasibility at 3.02. There is no timestamped preregistration file, so I could not check when the prediction was written.\n- No harness bug found. The harness Q matches my independent position-space build to 6e-40.",
 "next_step_if_survives": "It does not survive; do not spend more compute on split SDPs. Two cheap items would make it permanent.\n(1) Turn the near-null argument into a lemma. If M_p >= 0 and M_p <= Q, then dist_{Q^{-1}}(W_p v, span{V_i v})^2 <= v^T Q v. So a d-dimensional linear split family can be feasible at x only if its approximation error for the shifted near-null vector is at most sqrt(lambda(x)). With lambda decaying superexponentially, this gives d(x) -> infinity for any family with a fixed error-versus-dimension profile. This single statement covers B3 and B20 and every future 'split Q into PSD local pieces' proposal.\n(2) Arb-certify the 16x16 (x=5, K=16) Farkas certificate for the ledger, reusing my kskw.py scalars with mp.iv.\nThe only split-SDP question still genuinely open: put strict locality on s_p (support in [0, delta] with delta < log 2, i.e. no atom transport, an archimedean-share-only split). It is expected to be dead by B13 and the result above; run it only as a one-shot confirmation."
}
```
