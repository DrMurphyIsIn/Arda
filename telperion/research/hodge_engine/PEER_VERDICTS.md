# Independent peer-session verdicts on engine barriers

These come from peterwmurphy-95: a different session under the same git identity, so "unverified" under #607. Its scripts are in the peer scratchpad (w4rci/, w4amgm/, w4hodge/, w4ks/, dhhorizon/).
These verdicts OVERRIDE the corresponding ledger wording. Agents must use the corrected forms below.

## Wave 4 (verdicts 2026-09-25)

**B23 rci_gap_q20: all four claims CONFIRMED.**
- Own sieve: 334422/334509 codes.
- corr(ell, log N_min) = 0.402 / 0.148 / 0.068 / 0.036 at x = 10 / 20 / 30 / 40.
- Minimum ordering -3, -4, 5, 8, -7, -8, 12, 13 over all 668931 patterns.
- Tail fit 1.4758 sqrt(x) + 0.537.
- Detector 49 / 45 / 0.
- Caveats:
  - Claim (2) is TAUTOLOGICAL: the slack equals lambda_min of the realizing zeta_K via the log-q shift.
  - "Fixed by counting" is a mean statement only (sd 1.24).
  - Zero control false alarms is tautological.
  - The d = -3 margin at x = 40 is 1.74e-28.

**B24 class_group_amgm_defect**
- (A) Zero-mean symbol CONFIRMED.
- (B) The AM-GM / convexity no-go is HEURISTIC, not a proof. The rigorous content is a bump lemma about c-LINEAR splits with matching arch / conductor / pole. It does NOT exclude nonlinear or arch-redistributing splits.
- CORRECTION C22: the two-bump test gives only sign(c_Def(n0)). Every c_Def(n < 36) > 0 for D = -20, so the NEGATIVE direction at x = 20 needs a FOUR-bump construction. "Two-bump test is the rigorous proof" is overstated.
- (C) m_H CONFIRMED.
- (D) The 36 misses are CONFIRMED but tautological (they duplicate B22 + R3).
- Convention notes:
  - Def is c_E - (Lambda_K + Lambda_{L_G})/2 against zeta_H, not (1/2)L_G.
  - The pole-free class carried an extra int f = 0 in the even sector. The natural class gives pole-free m_H = 0.450, not 0.532.

**B25 hodge_signature_barrier**
- (1) The Haynsworth split is a THEOREM. The pole block is semidefinite per sector and hyperbolic only across sectors.
- (2) "A PD and S < 0 past a first crossing" is CONFIRMED as a limit theorem (one event, not two). DH at x = 33 already has A dead.
- (3), (4) CONFIRMED.
- (5) The cascade is PLAUSIBLE but N-unconverged. The count below 1e-6 at x = 20 is 13 / 16 / 17 for N = 32 / 48 / 64. "Cascade dimension" needs a threshold and an N to mean anything. R13 is Cauchy interlacing restated.
- MISSTATEMENT: "lambda_A <= lambda_{k+1} ~ 5e-53 for every codim-k split, k <= 12" holds only at k = 1. At k = 12 the interlacing bound is 5.8e-9 (N = 32) / 6.7e-21 (N = 64).

**B26 ks_pshr_sdp**
- (a) x = 3.02 feasible: CONFIRMED.
- (b) x = 5 infeasible: CONFIRMED and strengthened, with exact rational Farkas certificates in a Legendre basis and a second polynomial-kernel family. Caveats:
  - Galerkin feasibility is subspace-dependent, so "K <= 24 infeasible" stands only via N >= 24.
  - "K = 32 feasible" is N-fragile, so x_KS(K) values are UPPER bounds only.
- (c) The tautology is a trivial finite-N theorem. "theta, mu -> 1/#places" is a solver artefact.
- (d) REFUTED for K >= 16. The single-vector near-null test is not binding: rho_1 = 0.23 / 0.0096 against a threshold of 2. The certificate lives in the bulk, and the even sector alone is infeasible. WITHDRAW "feasibility is decided by the global near-null vector" above K = 8.

## Other independent confirmations

- **#629 h11000:** NOT REFUTED.
  - Fresh-worktree replay: 9190 jobs, 64 anchors, sorryAx 0, standard axioms.
  - Five in-file negative controls, plus the peer's own tampered-enclosure controls, are rejected.
- **DH horizon:** unchanged.
  - Even sector 30.5715 +- 0.001; odd sector 31.245 / 31.243.
  - Arb ball at 30.60 = -1.15e-30 (N = 1024, radius 1e-74).

## Wave 5 (verdict 2026-09-25)

**B27 defect_balance_zoo.** All NUMBERS reproduce (own float64 builder; DH at 256 bits). The barrier is an OBSERVED one-member dichotomy, not a theorem.
- CORRECTED WORDING (use this): "B27: observed. DH's failing direction is 98% in the reference's two low modes but has Rayleigh quotient 0.028 there (NOT near-null). All FE members fail along their own bottom mode. P4 is withdrawn in the narrow sense only: a mechanism that only lower-bounds the genuine form off its near-null subspace cannot exclude DH, so the defect must be controlled on the low modes too."
- Near-null perturbation is NOT established as a second "regime".
- rho is |Q_Def(v_cf)|/|lambda_min(Q_Def)|, not an overlap: 0.0106 at N = 128.
- "Fails inside the cascade" is a support statement, not a Rayleigh statement.
- Q_ref(v_cf) = 0.028 = 5.5e5 x m_ref.
- DH is confounded: it is the only member with an FE at x_h/q = 6.
- The DH "x_h + 0.05" row (30.621) is not past the horizon at N <= 160.
