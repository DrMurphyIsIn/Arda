# Hodge index for Spec Z, wave 1: angle `squareroot`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Angle "squareroot": positivity as a norm

conjecture1_proved = False. This angle did not find a Hodge-index mechanism. It did produce an exact, verified anatomy of why E fails, plus two refutations of natural square-root candidates.

## 1. What Bochner gives, and why it is circular
W is positive definite on the window if and only if W(f * f~) = ||Tf||^2 for some Hilbert-space map T.
- Under RH the canonical T is f -> (f^(gamma)) over the zeros gamma. That is the zero side, and it is circular.
- The angle asks for a T built from the prime side.

## 2. Candidate A: a local (Euler-factor) square root. REFUTED beyond x ~ 2
**The idea.** For zeta, the prime-p part of the Weil distribution is Delta_p = log p * (mu_p - delta_0), where mu_p = sum over k in Z of p^{-|k|/2} delta_{k log p}.
- mu_p is positive definite: its Fourier transform is the Poisson kernel P_r(t log p) with r = p^{-1/2}.
- So <mu_p, f*f~> = ||S_p f||^2, a genuine Euler-local square root.
- The sharpest bound it yields is Comb_p(f) <= 2 log p * r/(1-r) * ||f||^2.

**Test (local.py).**

| x | lambda_min(Q_zeta) | lambda_min(Pole+Arch) | Poisson-local sum |
|---|---|---|---|
| 2 | 1.335e-3 (= KWin margin, reproduced) | | |
| 2.5 | +1.0e-5 | -0.225 | 3.35 (trivial atom bound 0.98) |
| 3 | +5.9e-8 | -0.43 | |
| 4 | +9.6e-13 | -0.72 | |

**What this shows.**
- Pole+Arch alone is not PD past x ~ 2.
- The subtracted prime terms raise the minimum; they are not a negative perturbation.
- Any split of the form "positive part = pole+arch, remainder = primes (bounded locally)" is dead. Positivity comes from global cancellation.

## 3. Candidate B: the Euler-factor square root, and the cross term of a counterfeit (EXACT)
**Theorem (elementary, verified to 1e-30).** Let L1 and L2 share their gamma factor, conductor and root number, and let F = c1 L1 + c2 L2. Then:
- F = C * sqrt(L1 L2) * cosh(u + c), where u = (1/2) log(L1/L2).
- -F'/F = (1/2)(-L1'/L1 - L2'/L2) - d/ds log cosh(u + c).
- Hence Q_F = Q_{sqrt(L1L2)} + R. Under GRH, Q_{sqrt(L1L2)} = (1/2)(Q_L1 + Q_L2) is PD, with square root T given by the zeros of L1 and L2 at weight 1/2. R is the log-cosh cross term, supported on products of at least two primes.
- An Euler product is exactly the case R = 0 (Lemma O).

**For E = (1/2) sum' (x^2+5y^2)^{-s} = (zeta_K + L(chi_-4) L(chi_5))/2:**
- u is supported on the non-principal-class primes 2, 3, 7, 23, 43, ...
- So c_E(2) = c_E(3) = c_E(7) = 0.
- The atoms c_E(6) = 3.584, c_E(9) = 4.39 + 2.20, c_E(14) = 5.28, c_E(21) = 12.18 and c_E(36) = -7.17 come entirely from u^2 = (class-group character sum)^2.

**For D:** D = sqrt(1+kappa^2) * sqrt(L Lbar) * cos(v - arctan kappa).
- The linear term kappa*v is prime-supported.
- The first non-Euler term is -(1+kappa^2) v^2 / 2. This recovers c_D(6) = (1+kappa^2) log 6 exactly.

## 4. Numerics (bcore Galerkin, Neumann basis, N = 48 per sector; scan48.log, run2.log)
**Q_avg is PD at every x tested,** as GRH predicts: 0.50 (x=6.5), 0.038 (18), 0.024 (20), 0.0092 (24), 0.0044 (28).
- Q_zK: 4.6e-3 at x=20.
- Q_LG: 1.4e-7 at x=20. Positive but nearly null.

**The remainder R is indefinite at every x (lambda_min about -1.5 to -4.8), even at x = 6.5.** So "the remainder's sign tracks E's failure" is FALSE.

**Failure is a race along one direction.** On E's failure vector at x = 19.82:

| Contribution | Value |
|---|---|
| Pole | +3.05 |
| Arch | +0.40 |
| Euler comb | -0.96 |
| Atom 6 | -1.27 |
| Atom 9 | -1.00 |
| Atom 14 | -0.19 |
| Atom 4 | -0.02 |
| Atom 16 | -0.008 |

**Cross-term tolerance t\*(x).** This is the largest t for which Pole + Arch - Comb[Euler + t * cross] stays PD. It is the quantity that tracks the failure:

| x | 12 | 16 | 18 | 19 | 19.5 | 19.82 | 20 | 22 | 24 | 28 |
|---|---|---|---|---|---|---|---|---|---|---|
| t\* | 1.105 | 1.021 | 1.004 | 1.0009 | 1.0003 | 1.0000 | 0.9999 | 0.989 | 0.983 | 0.944 |

So t\* = 1 exactly at x_E ~ 19.82.

**The u^2/2 truncation fails at x ~ 18.9-19.0.** For x < 16 it coincides with E, so this only measures the effect of the u^4 atom at 16. It is not an independent prediction.

**D (dh.py).**
- The identity is verified.
- lambda_min(Q_D) is at float64 roundoff (about 1e-15) from x = 20 on, so x_D ~ 31 is not resolved here.
- The truncations D_lin and D_quad are strongly negative already at x = 10 (-0.064 and -0.0011).
- D's cross term is non-perturbative, and the truncation does not predict x_D.
- The Euler part (1/2)(Q_L + Q_Lbar) stays positive: 1.8e-3 (x=10) falling to 3.5e-11 (x=50).

## 5. Verdict
- The square-root angle, made precise, factors every counterfeit as (a GRH-PD Euler square) + (a nonlinear log-cosh cross term). This pins E's failure to the squared non-principal-class primes 2*3 and 3*3.
- For zeta, u = 0 and R = 0, so the only square root is the zero side.
- "Positivity because the cross term vanishes" is equivalent to class P = {zeta}. It says nothing about why W(x) holds. The Hodge-index source is still missing.
- A split into "positive pole+arch minus primes" is refuted at x ~ 2.5.

## 6. Literature
All citations are from memory. The web-search budget was exhausted, so none were re-checked; treat them as UNVERIFIED.
- Bombieri-Hejhal (~1995): zeros of linear combinations of Euler products are governed by log(L1/L2), our u.
- Weil 1952; Bombieri 2000.
- Yoshida 1992.
- Burnol and Haran: local conductor operators, not positive.
- Connes-Consani (~2021): an archimedean-place Weil positivity via prolate / Sonin functions.
- Conrey-Li (~2000): de Branges' positivity condition fails for zeta.
- Lagarias (~2006): de Branges spaces for L-functions.

## 7. Odds and deliverables
**RH: < 0.1% via this angle.**

**Deliverable** (plausible, about 70%):
- The weight identity as a finite, decidable Lean lemma.
- An Arb-certified t\*(x) curve, with t\*(22) < 1 kernel-checked via FWindow.
- This slots into Lane A (the counterfeit ladder) as an explanation of *which* atoms kill E.

The files are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/squareroot/. No processes are left running and the repo was not modified.

## Adversarial verdict

```json
{
 "angle": "squareroot (skeptic review): positivity as a norm; Bochner square roots from the Euler product; E and D factored as sqrt(L1 L2) times cosh or cos of the log-ratio",
 "survives": false,
 "fatal_flaws": [
  "No positivity mechanism for zeta. For zeta u = 0, R = 0 and the only square root left is the zero side f -> (f^(gamma)). That is circular: it assumes RH. The proposal admits this itself (alive=false).",
  "The flagship 'prediction' is a tautology. Q_t = Pole + Arch - Comb[avg + t*cross] is affine in t, and Q_1 is identically Q_E. The set of t where Q_t is PD is therefore an interval containing 0. So t*(x) >= 1 holds exactly when Q_E is PSD, and t*(x_E) = 1 follows from the definition. I checked this numerically: with an unrelated base point (zeta_K itself, which is not a square root of E) the path gives the same crossing, t* = 1.0267 / 1.0006 / 1.0000 / 0.9949 at x = 16 / 19.5 / 20 / 22. The Euler square root gives 1.0224 / 1.0005 / 1.0000 / 0.9914.",
  "The positive part is circular even for the counterfeit. That Q_avg is PD needs GRH for L(chi_-20), L(chi_-4) and L(chi_5). The numerics only check it window by window, and nothing proves it for all x. Separately, the t-path sets its base at Pole(full) + Arch - Comb(avg). That is (Q_zK + Q_LG)/2 + Pole/2, not the GRH square root itself. Run1/scan48 do use Pole/2 correctly.",
  "The log-cosh identity is only elementary algebra: (a+b)/2 = sqrt(ab) cosh(1/2 log(a/b)), applied to Dirichlet series. Nothing is proved from it. That 'the cross term vanishes' is the same thing as 'F is an Euler product' (Lemma O / class P = {zeta}) is a characterization, not a source of positivity.",
  "The remainder R is indefinite at every x, including x = 6.5 where E is comfortably PD. So R's sign does not separate zeta_K from E at the level of forms. Only the tautological race along E's own failure vector does.",
  "D is not controlled. x_D ~ 31 is unresolved in float64 in both the original bcore run and my independent code: lambda_min(Q_D) is about 1e-14 noise from x = 20 through 50. The D_lin and D_quad truncations fail already at x = 10, so the cross term is non-perturbative there.",
  "The literature could not be re-verified: the web-search budget was exhausted (200/200). The log(L1/L2) mechanism for zeros of linear combinations is essentially Bombieri-Hejhal (Duke 80, 1995), cited from memory in both the proposal and the project docs."
 ],
 "linearity_or_classP_violation": "The Euler product enters nonlinearly only as a way to describe the counterfeit. The cross term -d/ds log cosh(u) is quadratic and higher in u and is supported on products of two or more non-principal-class primes (2, 3, 7, 23, ...). So the proposal technically clears the linearity barrier. But the only statement it can make about zeta is 'R_zeta = 0', which is the class-P = {zeta} characterization (Theorem A / fooling lemma). Membership in class P is not a positivity argument. For zeta the square root must be the zero side, so any positivity conclusion drawn from it assumes RH. It adds nothing that separates zeta at all scales beyond what class P already says.",
 "counterfeit_check": "I reproduced this independently in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/squareroot_skeptic/. The code is wf.py plus t0-t3.py, with no bcore. Setup:\n- Basis: (1-v^2)^3 P_m(v), vanishing at the edges. Rayleigh quotients on a subspace give upper bounds on lambda_min.\n- Archimedean term: direct t-quadrature of Re digamma, checked for convergence in the cutoff T. An earlier version aliased in u; I fixed it.\n- Prime side: exact autocorrelation quadrature.\n- Coefficients: computed from lattice representation counts of x^2+5y^2 and 2x^2+2xy+3y^2, independent of the character formulas.\n\nResults:\n- c_E(2) = c_E(3) = c_E(7) = 0.\n- c_E(6) = 3.5835, c_E(9) = 6.5917 (of which 4.3944 is cross), c_E(14) = 5.2781, c_E(21) = 12.178, c_E(36) = -7.167.\n- The cross term is also nonzero at 4 and 16 (0.6931 each). This all agrees with the proposal.\n\nE threshold at N = 40:\n- lambda_min(Q_E) = +8.2e-4, +4.0e-4, +1.5e-4 and -5.0e-5 at x = 19.5, 19.7, 19.85 and 20.0.\n- The threshold falls as N grows (at N = 24 it is still +3.8e-5 at x = 20.2; at x = 22 it is -6.9e-3).\n- This is consistent with x_E ~ 19.82. zeta_K stays positive: +4.8e-3 at x = 20 (an upper bound; the certified lower bound is 3.44e-3).\n\nSo E's failure near 19.82 is REAL, but the mechanism does not predict it: t* = 1 at x_E is definitional (see fatal flaw 2). D's failure near 31 is not resolved by either code (float64 noise at the 1e-14 level). The proposal makes no working prediction for D.",
 "numerics_reproduced": "Every quoted figure checked was reproduced with independent code. Values at x = 2 are minimum Rayleigh quotients (lambda_min) of the Weil form Q_zeta:\n- KWin at x = 2: lambda_min goes 2.46e-3, 1.72e-3, 1.53e-3 for N = 6, 10, 14, with no primes entering, heading to the 1.335e-3 margin.\n- The local split refutation holds. lambda_min(Pole+Arch) = -0.219 at x = 2.5 and -0.424 at x = 3.0, while Q_zeta = +1.19e-5 and +4.1e-8.\n- The E threshold falls between 19.85 and 20.0 at N = 40 and is still decreasing with N, consistent with 19.82.\n- The weight identity holds exactly on the representation-count coefficients.\n\nThe claim that t* tracks the failure is reproduced numerically but shown to be a tautology: any PD base point gives t* = 1 at x_E. D is unresolved at x = 20-50 (|lambda| about 1e-14).\n\nScripts: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/squareroot_skeptic/{wf.py,t0.py,t1.py,t2.py,t3.py}. No processes are left running, and the repo was not modified.",
 "novelty": "Low. The factorization of a sum of two Euler products through u = (1/2) log(L1/L2) is the Bombieri-Hejhal (Duke 80, 1995) viewpoint, cited from memory: web search was exhausted and I could not re-check it. Reading it as a Weil-form decomposition, with E's failure localized to the atoms 6 = 2*3 and 9 = 3*3 on the failure eigenvector, appears new, but it is a description of the counterfeit. The t* curve has no content beyond the window threshold. The Poisson-kernel local square root (mu_p positive definite) is standard; that Pole+Arch alone is not PD past about x = 2 is folklore consistent with Yoshida 1992 needing the primes' cancellation.",
 "what_is_real": "1. An exact finite identity, checkable in Lean: c_E = (c_zK + c_LG)/2 + [coefficients of -d/ds log cosh u], with u supported on 2^k and the non-principal-class primes, and the analogous cos identity for D. This is decidable coefficient arithmetic.\n2. An anatomy result: on E's failure eigenvector at x ~ 19.82 the negative mass comes mainly from the cross atoms 6 (-1.27) and 9 (-1.00), against -0.96 from the Euler average. The failure is caused by the class-group-character-squared atoms. This is a genuine, reusable description for the counterfeit ladder.\n3. A confirmed negative result: splitting 'positive = Pole+Arch, remainder = primes (bounded locally)' is dead beyond x ~ 2.5. Positivity at larger scales needs global cancellation among the prime atoms. Any future Hodge-index candidate has to explain this, not bound it away.\n4. An independent confirmation of the E threshold (about 19.8-20.0) and of zeta_K positivity at x = 20 with a different basis and code path.",
 "next_step_if_survives": "It does not survive as a mechanism. The single most informative next step is to test whether the negative result (3) is structural. Take the minimizing eigenvector v_x of Q_zeta at x = 2.5-5, and ask whether the prime-atom contribution -Comb(v_x) is positive on it (primes helping) and stays positive as x grows. Any Hodge-index-type proof must show where that sign comes from, and it must fail for E at the 6/9 atoms. As a bookkeeping deliverable only: add the finite weight identity as a Lean lemma and an Arb-certified lambda_min(Q_E) < 0 at x = 22 through the existing FWindow. Drop the t* framing, since it is equivalent to that single certificate."
}
```
