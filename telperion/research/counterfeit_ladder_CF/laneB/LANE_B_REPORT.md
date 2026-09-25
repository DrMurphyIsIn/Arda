# Lane B: go/no-go gate for zeta_K window positivity (repaired report)

conjecture1_proved = False. Numerics only, interval-certified where stated. The own-session skeptic REFUTED two small numbers; this is the repaired report. The peer-session verdict is in PEER_SKEPTIC_VERDICT.md.

## Numbers

GATE: GO on the numeric Step-1 gate, with the qualifications below.

Where it passes:
- The certified full-class lambda_min(zetaK) is >= 3.44e-3 at x=20, where E is certified negative (continuous test, -1.18e-4). That is more than 3000 times the 1e-6 threshold.
- It is also >= 1.30e-3 at x=22 (E <= -1.6e-2). x=22 is a substitute window, not one of the listed ones.
- The gate list {20, 24, 28} is met by a full-class certificate ONLY at x=20. At x=24 and x=28 there is no full-class certificate; the finite-span certified values there are Ritz upper bounds and count only as float evidence.
- Every full-class number is conditional on the paper-level steps P1 to P4.

What does not pass (the Step-2 deliverable):
- By this lane's own cost estimate, a full-class Lean theorem at x=20 or 22 is NOT feasible at KWin/Crux3 budgets. It would take about 10^3 to 10^4 times those budgets.
- Making it feasible needs restructuring: a partial-fraction coupling Gram, an analytic far-tail bound, and verified-float Cholesky.
- The 16-mode separation described under "remaining" is a WEAKER statement: a finite-span separation, not a positivity theorem. It is not the Step-2 deliverable.

Normalization is Q(f)/int|f|^2 on the window, as in KWin.

Float lam_min, minimum over sectors (Neumann basis, 256 modes per sector):

| x | zetaK | E |
|---|---|---|
| 18 | +1.31e-2 | +9.1e-3 |
| 19 | +7.72e-3 | +2.07e-3 |
| 19.5 | +5.90e-3 | +5.45e-4 |
| 20 | +4.536e-3 | -1.88e-4 |
| 21 | +2.77e-3 | -5.2e-4 |
| 22 | +1.666e-3 | -1.68e-2 |
| 23 | +1.08e-3 | -2.13e-2 |
| 24 | +6.556e-4 | -7.86e-2 |
| 26 | +2.03e-4 | -1.94e-1 |
| 28 | +5.99e-5 | -2.20e-1 |
| 30 | +2.12e-5 | -4.18e-1 |
| 32 | +7.05e-6 | -4.73e-1 |

Convergence of zetaK, corrected. The claim "changes by under 2e-6" was FALSE. Going from 128 to 256 modes in the even sector (the binding sector), the value changes by:

| x | change | relative |
|---|---|---|
| 18 | 1.51e-5 | 0.12% |
| 19 | 1.24e-5 | 0.16% |
| 19.5 | 9.9e-6 | 0.17% |
| 20 | 7.33e-6 | 0.16% |
| 22 | 3.20e-6 | 0.19% |
| 24 | 1.86e-6 | 0.28% |
| 28 | 3.0e-7 | 0.50% |

So the relative change is about 0.1% to 0.5%, and the Ritz values keep decreasing slowly (about N^-1.7). Every full-class lower bound sits below every Ritz value, which is consistent. The skeptic's larger spans agree: 4.5336e-3 at N=512 for x=20.

E threshold: the bracket is [19.8562, 19.8562] at 64 modes, [19.8318, 19.8318] at 128 modes and [19.8254, 19.8254] at 256 modes, so x_E is about 19.82. E is certified negative at x=19.9 (the skeptic confirms +6.8e-6 at 19.82 and -5.8e-6 at 19.83).

zeta itself, float only and NOT certified: about 1.5e-38 on a 16-mode span at x=20 (the skeptic confirms 1.49832e-38 at dps 90), 3.4e-40 at x=24 and 1.4e-41 at x=28.

Conductor-scaled wall for zetaK: the value decays like exp(-0.5 x) and crosses 1e-6 near x of about 35.7. This is a float extrapolation.

Full-class parameters at x=20 and 22:
- head N2=128 per sector;
- exact coupling columns up to 16384;
- far-tail bound up to 2^19;
- S(t) >= 0.45 certified on [76, 408] in 33221 cells;
- A_L = 10.8935;
- leakage <= 1.1e-3;
- tail floor d >= 0.4307 (0.4327 in the odd sector).

Why the odd-sector certificate at x=20 is loose. It certifies 8.76e-3, while the Schur estimate at lam=0 is 0.136 and the head Ritz value is 0.587.
- The certified value is the fixed point of lam = lam_min(H - K^T K/(d - lam)), with d = 0.4327.
- Fitting a single binding direction v with a = v^T H v and b = v^T K^T K v to the two numbers gives a - b/d = 0.136 and a - lam* - b/(d - lam*) = 0 at lam* = 8.76e-3. That solves to a of about 6.3 and b of about 2.7.
- So the binding direction is a high-frequency head mode (Rayleigh value about 6) whose coupling mass to the tail, about 2.7, is large against the small tail floor d = 0.43. Near-cancellation of a - b/d makes lam* very sensitive to d.
- This two-parameter fit is a heuristic inference and was not re-run. The bound is conservative (safe side). Raising d with a larger N2 or a sharper leakage bound would tighten it.

Prior claims:
- E at x=24 is -0.0786, not -0.035.
- E at x=28 is -0.2198. The earlier -0.020 was a basis-truncation artifact.
- zetaK at x=32 is 7.05e-6, where 1e-5 had been claimed.
- E's threshold "19-20" is confirmed as about 19.82.
- The 9-mode values at x=28 (-0.165 / +4.96) were not re-tested.

## Evidence

Repair round: what was changed and how it was checked.

(a) The convergence claim was false and is corrected. r2_conv.py recomputes lam_min for zetaK in the even sector at N=128 and N=256 for x in {18, 19, 19.5, 20, 22, 24, 28}; the output is in r2_conv.log. The changes are 1.5e-5, 1.24e-5, 9.9e-6, 7.33e-6, 3.2e-6, 1.86e-6 and 3.0e-7. These match the skeptic's figures.

(b) The Lean target was false and is corrected. At x=24, odd sector, 16 modes:
- float lam_min(zetaK) = 0.1865386 (r1_repair.py);
- interval certificate via cert.py gives [0.1865386480075, 0.1865386480085] for zetaK and [-0.0190779094704, -0.0190779094694] for E;
- at x=23 the certificate gives [0.24406307503, 0.24406307503] for zetaK and E = -0.01369192533.
- The new target is zetaK >= 0.1865 ||v||^2 against E <= -0.019 ||v||^2.

(c) The gate framing is corrected. The finite-span values at x=24 and x=28 are removed from the gate justification and labelled as Ritz upper bounds. Among the gate list {20, 24, 28}, the full-class certificate exists only at x=20; x=22 is named as a substitute.

(d) Rigor labels are corrected. Each full-class theorem now carries the conditions P1 to P4.
- A written derivation of the Loewner structure is added in LOEWNER_DERIVATION.txt. It uses the Neumann-mode transforms Phi_m(t) = 2(-1)^m t sin(tA)/(t^2 - k^2) for the even sector and 2i(-1)^m t cos(tA)/(t^2 - k^2) for the odd sector, followed by exact partial fractions. That gives L_in = (-1)^(i+n) (G(k_n) - G(k_i))/(k_n^2 - k_i^2), with G(k) = (k^2/2pi) int 4 s(t)^2 Omega(t)/(t^2 - k^2) dt.
- The pole kernel 2cosh((u-v)/2) is kept separate as +-2 P_i P_n.
- The row-0 corollary is numerically verified to <= 4.7e-13 (r4_loewner_row0.log): 96 modes, x in {20, 24}, ZK and E, both sectors.
- The Y closed form (P4) is still only numerically identified. The derivation file says explicitly that it is NOT derived.

(e) The GO is qualified. It is GO on the numeric Step-1 gate only. The full-class Lean theorem that Step 2 calls for is not feasible without restructuring, and the 16-mode separation is weaker and is not the Step-2 deliverable.

(f) Optional item: the looseness of the odd-sector certificate is explained by a two-parameter binding-direction fit (see numbers). This is a heuristic.

Unchanged and independently confirmed by the skeptic, whose code is separate (time-domain quadrature, own chi_-20, lattice-count a(n)):
- the whole lambda_min table;
- the E threshold of 19.82;
- the Loewner columns (about 1e-14 up to n=20000);
- the rigor audit of fullclass.py and icore.py (no soundness hole found);
- zeta at 1.49832e-38.

The earlier evidence stands:
- bcore and icore agree to 1e-14 and match time-domain quadrature to about 1e-15;
- the geometry angle's 7.38017e-4 is reproduced;
- E's weights come from the exact -E'/E recursion with a(1)=1;
- the interval LDL^T and Rayleigh-quotient certificates were run at dps 34, with entry widths about 4e-29.

No processes are left running. There were no repo writes.

## Remaining

- A full-class Lean proof at x=20 or 22 has an estimated cost of about 10^3 to 10^4 times the Crux3/KWin budgets.
-   Scale of that proof: two 128x128 LDL^T at about 10-12 digits, a symbol check with about 4e5 enclosures, and a coupling Gram of about 2.7e8 multiply-adds done brute force.
-   It is infeasible with decide +kernel unless restructured. The pieces needed are a partial-fraction coupling Gram (about 2e6 operations), an analytic mean-square far bound, and verified-float Cholesky.
- Realistic Crux3-scale Lean target, which is WEAKER than the gate's Step 2: a finite-span separation in the odd sector, 16 Neumann modes.
-   At x=24: zetaK >= 0.1865 ||v||^2 and E <= -0.019 ||v||^2. The certified values are 0.18653865 and -0.01907791.
-   At x=23: zetaK >= 0.244 and E <= -0.0136.
-   Entries are needed only to about 1e-3.
- Full class at x=24 and x=28 is NOT certified. The symbol dips there (S < 0.5 up to t = 898, because of the prime 23), which forces a head of about 600 to 1800 modes per sector. That needs verified-float Cholesky.
- Paper-level obligations:
-   (P1) the Crux3 closed forms;
-   (P2) the frequency representation on H^{1/4} window tests;
-   (P3) convergence of the Neumann expansion in the form norm;
-   (P4) G(k) = -k Y(k) + const. This can be avoided by rerunning fullclass.py with the row-0 Loewner form from LOEWNER_DERIVATION.txt Step 3, which needs only the head closed forms;
-   mollification from Lipschitz to smooth tests for the E witnesses.
- Tightening the odd-sector certificate (currently 8.76e-3, with a Ritz value of 0.587) by raising the tail floor d. The binding-direction diagnosis is heuristic and was not re-run.
- The 9-mode claim at x=28 (-0.165 / +4.96) was not recomputed. zeta's own margins are not certified.
- conjecture1_proved = False.

## Own-session skeptic (pre-repair)

I could not break any of lane B's core results. The refuted flag is set only because the rule says any false claim counts, and two stated numbers are false; both are small. Everything below is float or high-precision numerics from my own code; nothing is kernel-checked.

What I rebuilt independently, in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B_skeptic/:
- sk.py computes the Weil form in the time domain rather than from the lane's closed forms. The archimedean term uses the identity Re psi(a+ir/2) - psi(a) = int_0^inf 2e^{-2at}(1-cos rt)/(1-e^{-2t}) dt with Gauss-Legendre panels. The pole term uses the moments int f e^{-+u/2}. The prime and E weights are my own: chi_-20 from a Jacobi symbol, and E's a(n) from a direct lattice count r_Q(n)/2 of x^2+5y^2, with no characters used.
- The archimedean data checks out: conductor 20, Gamma_R(s)Gamma_R(s+1) with a = 1/4 and 3/4, pole terms h(+-i/2), and A_L = 10.8936 and S_min = -15.50 recomputed by hand.

Results:
(1) Every value in the lambda_min table (x = 18 to 32, N = 128 and 256, both sectors, zetaK and E) matches the lane to all printed digits.
- Examples: E at x=20, even sector, N=64 is -1.57162263e-4 (theirs -1.571622625e-4); E at x=24, even, N=64 is -7.3551947e-2.
- The E threshold is confirmed. At N=256, lambda_E is +6.8e-6 at x=19.82, -5.8e-6 at 19.83 and -8.77359e-5 at 19.9.
(2) The Loewner off-diagonal formula, which the lane used for coupling columns up to n = 16384 and checked only against the 128x128 head, agrees with my time-domain code to about 1e-14 at (i,n) = (0,300), (5,1000), (3,5000), (100,4000), (127,20000) in both sectors.
(3) Larger Galerkin spans (even sector, x=20): 4.534323e-3 at N=384 and 4.533567e-3 at N=512. At x=22 the N=512 value is 1.665186e-3. Both sit above the full-class lower bounds of 3.443e-3 and 1.300e-3, so nothing contradicts them.
(4) The zeta comparison value is confirmed by a separate mpmath computation at dps 90 with my own quadrature: lambda_min = 1.49832e-38 at N=16, x=20, even sector.

Audit of the rigor in fullclass.py and icore.py: I found no soundness hole.
- The digamma and trigamma remainder bounds |B_2K|/(2K (Re w)^2K) and |B_2K|/(Re w)^(2K+1) follow correctly from the remainder-sign lemma for phi.
- The recurrence shift to Re w >= 24 is asserted in the code.
- mpmath.iv has a rigorous atan2 (mpi_atan2), and cos is rigorous at large arguments.
- The beta-family tails are enclosed.
- Omega is monotone, and the cell check S >= Omega(t0) - C(t0) - h*D_C is valid.
- I re-derived the leakage integral t^2/(k^2-t^2)^2 for both parities; it is correct.
- The odd-sector negative pole, -2(sum r_n P_n)^2, is correctly subtracted from the tail floor. Dropping the even-sector pole is fine because it is >= 0.
- The u/P/v/e split of the far columns and the (1+eps) inequalities are correct.
- Interval LDL^T of H - lam - (GK+Far)/(d-lam) is a valid Schur-complement sufficient condition.
- The odd-sector certified value (8.76e-3, against a Schur estimate of 0.136) is loose, but on the safe side. The likely cause is a high-mode direction with large coupling.

What is false or overstated:
(a) False: "going from 128 to 256 modes changes the [zetaK] value by under 2e-6". The actual changes are 7.3e-6 at x=20, 1.2e-5 at x=19, 1.5e-5 at x=18, 9.9e-6 at x=19.5 and 3.2e-6 at x=22.
(b) False: the proposed Lean target "zetaK >= 0.187||v||^2" in the odd sector at x=24 with 16 modes. The true minimum is 0.186539, confirmed with both my code and the lane's own bcore.py. As stated, that Lean goal cannot be proved. The x=23 figures (0.2441 against -0.01369) are fine.
(c) Overstated framing: "the finite-span certified values at x = 20, 24 and 28 also exceed 1e-6" is offered as support for the gate. Those values are Rayleigh-Ritz upper bounds, so they cannot certify a lower-bound gate at x=24 or 28. The gate named x in {20, 24, 28}; a full-class certificate exists only at x=20, plus 22, which was not in the gate list.
(d) Rigor labelling: the full-class "CERTIFIED-NUMERIC" theorems depend on the Crux3 closed forms and on the Loewner identity for columns 128 <= n < 16384. Neither is proven in-lane; both are only numerically cross-checked, including by me. The theorem statement itself should carry the (P) flag.
(e) The GO call is correct against the numeric gate: margin 3.44e-3, far above 1e-6, at x=20, where E is certified negative (continuous test, -1.18e-4). But the report's own cost estimate says a full-class Lean proof of Step 2, as the gate defines it, is 10^3 to 10^4 times the Crux3/KWin budget. The finite-span fallback it proposes is a weaker statement: a separation on 16 modes, not a positivity theorem. The report should say this explicitly.

conjecture1_proved = False.
