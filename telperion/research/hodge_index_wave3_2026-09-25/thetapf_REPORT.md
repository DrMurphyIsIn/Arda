# Hodge index WAVE3: angle `thetapf`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Angle thetapf: total positivity of the theta kernel as a blindness calibration

**Verdict:** the mechanism is dead, as the class-P barrier predicted. What survives is a clean calibration theorem, supported by concrete witnesses.

`conjecture1_proved = False`.

Scripts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/thetapf/`:
- `kernel.py`, `scan.py`, `lc.py`: positivity and log-concavity.
- `toep.py`, `dirich.py`: lattice PF_k minors.
- `pf1scan.py`: 1218 real characters.
- `rnd.py`: random off-lattice minors.
- `xcheck.py`: cross-check against Michalowski's certificate.
- `edrei.py`, `jensen0.py`, `jhi.py`: moment total positivity.
- `wit.py`: explicit witnesses.

Kernels are taken from the wave-2 `hodge2/jensen/moments.py`, which uses the Gamma_C normalization for zeta_K and E.

## 1. Mechanism, stated precisely

For F in {zeta, zeta_K, E, D}, write Xi_F(t) = 2 ∫_0^∞ Phi_F(u) cos(tu) du, with Phi_F(u) = e^{u/2} g_F(e^u). Phi_F is the theta kernel. For zeta it is 2× Riemann's Phi in the u ↦ u/2 scaling. Phi_F is even exactly when the functional equation holds.

Phi is **PF_k** if det[Phi(x_i − y_j)] ≥ 0 for every choice of increasing x_1 < … < x_k and y_1 < … < y_k.

The candidate mechanism is: "Phi_F is PF_k for all k (or variation-diminishing), therefore Xi_F has only real zeros."

**Obstruction 1 (Schoenberg 1951).** If Phi is PF_∞, then ∫ Phi e^{-su} du = 1/Psi(s) with Psi in the Laguerre–Pólya class. That transform has no zeros. Xi_F has zeros, so **no Phi_F is PF_∞**. Only finite orders can hold, and a finite order cannot imply RH.

**The correct TP form is the dual one (Aissen–Schoenberg–Whitney / Edrei; Katkova 2005).** Write Xi_F(t) = G(−t²) with G(z) = Σ c_m z^m, where c_m = gamma_m/m!, G has genus 0, and c_m > 0. Then RH for F holds exactly when (c_m) is a PF_∞ sequence, i.e. when the Toeplitz matrix [c_{i−j}] is totally nonnegative.

This is an equivalence with RH, not a reason for it. It is the same kind of statement as Theorem A of wave 1.

## 2. Where the Euler product enters

It doesn't. Phi_F is a linear functional of the coefficients a_F(n) through the theta series. Its evenness is exactly the functional equation. So this angle is subject to both the linearity barrier and the class-P barrier, as the brief predicted.

The finite PF order does depend on the coefficients, but only through character-sum oscillation near u = 0. It is a conductor and Gamma-factor effect (see §4). D has non-multiplicative coefficients and gets the same order as genuine characters of similar conductor.

## 3. Validation of the numerics

- **Evenness.** Relative error ≤ 2e-75 for all four kernels.
- **Normalization.** Xi_{zeta_K}(0) from the kernel moment is 0.916990968993278739…. An independent mpmath evaluation of −Lambda_K(1/2)/4, with Lambda_K = (√5/π)^s Γ(s) ζ(s) L(s, χ_{−20}), gives the same value to all digits shown.
- **External certificate.** In de Bruijn–Newman scaling, K(u) = Phi_Riemann(2|u|), my 5×5 Toeplitz minor at (u0, h) = (0.01, 0.05) is **−1.847236e-9**. That lies inside the interval-certified enclosure [−1.8472496, −1.8472225]e-9 of Michalowski, arXiv:2602.20313. The same run gives D2, D3, D4 > 0, which also matches his paper.

## 4. The test: PF orders (lattice minors at h ∈ {.05, .1, .2, .35, .5}, u ≤ 2; high-order minors computed at 80–100 digits, positivity/log-concavity checks at 60 digits)

| Function | Euler product? | RH/GRH? | Largest PF order | First failure (witness) |
|---|---|---|---|---|
| zeta | yes | yes | **4** (0 negatives in 1500 random off-lattice minors at k = 3 and at k = 4) | k = 5: normalized −1.39e-7 at h = .1, u = 0; 6/800 random 5×5 minors negative |
| chi_5, chi_8, chi_{−3} | yes | yes (expected) | 3 | k = 4 |
| chi_12, chi_{−4}, chi_{−7} | yes | yes | 2 | k = 3 |
| **D** (q = 5, odd) | **no** | **no** (0.8085 + 85.70i) | **2**; log-concave, max (log Phi_D)'' = −2.55 on [0, 2.4] | k = 3: det[Phi_D((i−j)·0.2)] = −4.29e-4 |
| chi_13, chi_{−8}, chi_{−11}, chi_{−20} | yes | yes | 1 | k = 2: log-convex somewhere |
| **zeta_K**, K = Q(√−5) | yes | yes (Weil-positive to x ≥ 26) | **1** | k = 2: Phi(.36)² − Phi(.32)Phi(.40) = −1.29e-5; (log Phi)'' up to +0.072 on (0.27, 0.45) |
| chi_{−19}, chi_{−40}, chi_{−43}, chi_{−52}, chi_53, … (407 of 1218 fundamental discriminants with abs(D) ≤ 2000) | yes | yes | **0** | Phi(0) < 0; for chi_{−19}, Phi(0)/max ≈ −0.38 |
| **E** = ½ Σ′ (m² + 5n²)^{−s} | **no** | **no** | **0** | Phi_E(0) = −0.07502; Phi_E < 0 on abs(u) < 0.30021 |

**Calibration theorem** (numerically established; every witness is a finite determinant, so each is Arb/Lean certifiable):

> For every k ≥ 1, the property "the theta kernel Phi_F is PF_k" is neither necessary for GRH nor sufficient for RH.
>
> - k = 1: fails for genuine L(s, χ_{−19}), and holds for D.
> - k = 2: fails for genuine zeta_K, and holds for D, which violates RH.
> - k ≥ 3: fails for genuine chi_{−4} and chi_{−7}, and it is already k-independent that no finite order implies RH (Schoenberg).
>
> The PF order is governed by the conductor and the Gamma factor. D sits exactly in the band of genuine odd characters with conductor 4–7.

Answer to "the exact k where things first differ": the order separates functions only by conductor. There is no k at which the Euler-product functions and the counterfeits split.

Two things look like separations but are not:
- E drops out at k = 1, but so do 407 of the 1218 genuine real characters tested.
- zeta and D differ at k = 3, but so do zeta and chi_{−4}.

The only non-FE input that moves the order is the sign pattern of a(n) near n ~ sqrt(q). That is not the Euler product. It predicts nothing about x_E ~ 19.82 or x_D ~ 31.

## 5. The dual (Edrei) form: the tail is provably blind

Moments gamma_m, m ≤ 400, were taken from wave-2's `gam.pkl`.

- **Contiguous Toeplitz minors.** det[c_{m+i−j}] for k = 2..15 and m ≤ 200 are all positive for zeta, zeta_K, E **and** D.
- **Why the tail cannot separate.** Large moments see only the u → ∞ end of Phi, i.e. a(1) and the leading theta term. gamma_m(E)/gamma_m(zeta_K) − 1 is:

| m | gamma_m(E)/gamma_m(zeta_K) − 1 |
|---|---|
| 10 | −4.0e-4 |
| 50 | −2.9e-11 |
| 100 | −1.6e-18 |
| 200 | −2.1e-31 |
| 400 | −2.1e-54 |

- **Consequence for the published tail results.** Katkova's fixed-order asymptotic positivity and Michalowski's tail theorem (arXiv:2607.16795: D_{r,k} > 0 for k ≥ 1e18·r³, Arb-certified saddle point) apply to E and D just as well. They are FE-plus-growth results, and they are what the fooling lemma predicts.
- **Head regime.** At shift 0, the Jensen polynomials of E and D are hyperbolic for every degree d ≤ 80.
- **Degree 120 is precision-limited.** The run showed spurious non-real roots for the GRH control zeta_K as well as for E, so no claim is made at d = 120. The degree-200 run did not converge.
- **Consequence.** The first Toeplitz or Jensen level where E must fail (Edrei, plus the certified off-line zero at t = 15.668 − 0.433i) lies beyond degree 80 / order 15. That is the same "high order only" sensitivity wave 1 found for Theorem A. Locating it needs an Arb Jensen/Sturm run with more digits in gamma_m.

## 6. Lesson for wave 3

Total positivity of the theta kernel is the cleanest possible example of an FE-only positivity. It fails in both directions at every order, and its genuinely RH-related dual is either equivalent to RH or, in its tail, provably counterfeit-blind.

Any "Hodge index" positivity has to be nonlinear in a(n). This result sharpens that requirement: a positivity of a kernel built linearly from the theta series (its PF order, variation diminishing, log-concavity, Turán, or tail Toeplitz minors) is excluded by the data above, not just by the barrier argument. The CNV log-concavity of Riemann's Phi is special to conductor 1. It already fails for zeta_K.

## 7. Literature

**Verified this run (abstract pages fetched):**
- W. Michalowski, arXiv:2602.20313 (Feb 2026, v2 July 2026): the kernel is not PF_5; PF_4 not established. Reproduced here independently.
- W. Michalowski, arXiv:2607.16795 (July 2026): RH ⇔ PF_∞ of the xi coefficients; tail k ≥ 1e18 r³ proved.
- O. M. Katkova, arXiv:math/0505174, "Multiple positivity and the Riemann zeta-function".

**From memory, unverified** (the session's web-search budget was exhausted):
- Schoenberg, J. Analyse Math. 1 (1951).
- Aissen–Schoenberg–Whitney, J. Analyse Math. 2 (1952).
- Edrei, Canad. J. Math. 5 (1953).
- Csordas–Norfolk–Varga, Trans. AMS 296 (1986).
- Griffin–Ono–Rolen–Zagier, PNAS 116 (2019).
- Katkova's journal reference: CMFT 7 (2007).

**Not seen in the literature (possibly new):**
- PF_1 failure for genuine L(χ_{−19}) and 1/3 of real characters with abs(D) ≤ 2000.
- PF_2 failure for zeta_K.
- D being log-concave while violating RH.
- The E/zeta_K moment coincidence as a direct demonstration that tail Toeplitz methods are blind.

## 8. Odds and deliverables

- **Kernel-TP route to RH:** about 0 (structural).
- **Edrei route:** equals RH; tail methods are blind.

**Deliverables:**
1. Add to the barrier ledger:
   - "TP-of-theta-kernel barrier" with witnesses Phi_E(0) < 0, the zeta_K PF_2 witness (u = .36, h = .04), and the D PF_3 witness;
   - positive side: D is PF_2.
   All are small determinants, so they are cheap Arb and Lean `decide`/interval targets.
2. Record the E/zeta_K moment coincidence as a formal statement: any argument that uses only gamma_m for m ≥ M cannot separate E from zeta_K. This is a quantitative fooling lemma for Jensen/Turán/Toeplitz-tail methods.

## Adversarial verdict

```json
{
 "angle": "thetapf (skeptic): whether total positivity (PF_k) of the theta/Polya kernel Phi_F, or the dual Edrei moment-TP, could explain Weil positivity",
 "survives": false,
 "fatal_flaws": [
  "No kernel is PF_infinity: by Schoenberg (1951), PF_infinity of Phi_F would make Xi_F zero-free. Any finite PF_k is too weak to imply RH. The proposer correctly concedes this, so this is structural death, not a gap.",
  "Phi_F is linear in the coefficients a_F(n) and is even exactly when the functional equation holds. There is no Euler-product input anywhere, so the angle falls under the linearity barrier and the class-P barrier. D (PF_2) lands in the same PF band as the genuine chi_{-4} and chi_{-7}.",
  "The dual Edrei/ASW form (the coefficient sequence c_m = gamma_m/m! being PF_infinity) is equivalent to RH, not a reason for it. That is circular in exactly the Theorem-A sense.",
  "Its provable tail regime (Katkova; Michalowski 2607.16795) sees only the u -> infinity end of Phi, so by the fooling lemma it is blind to counterfeits. The gamma_m(E)/gamma_m(zeta_K) coincidence confirms this.",
  "No prediction of x_E ~ 19.82 or x_D ~ 31. The PF order is governed by conductor and Gamma factor, which is the wrong invariant.",
  "Novelty claim over-stated. The PF_1 failure of the theta kernel for genuine real characters (e.g. chi_{-19}) is very likely already in the Siegel-zero / real-zeros literature. That literature uses positivity of sum n chi(n) e^{-pi n^2 x/k} to exclude real zeros, and records where the positivity fails. Suspected sources, from memory and unverified: Low, Acta Arith. 14 (1968); Chowla-Selberg; Rosser; Watkins, Math. Comp. (2004). My web search budget was exhausted, so I could not confirm."
 ],
 "linearity_or_classP_violation": "Full violation, and the proposer admits it. Phi_F = e^{u/2} g_F(e^u) is a linear functional of a_F(n), and the functional equation is used only as the evenness of Phi_F. The same argument goes through verbatim for E and D, whatever conclusion it reaches: D is PF_2, like the genuine chi_{-4} and chi_{-7}. E is PF_0, like 407 of the 1218 tested genuine real characters, including chi_{-19} and chi_{-43}. No PF level separates Euler-product functions from counterfeits. The Edrei form separates them only because it IS RH, and its tail is counterfeit-blind.",
 "counterfeit_check": "There is no mechanism here that fails at x_E ~ 19.82 or x_D ~ 31, and no PF level predicts either threshold.\n\nIndependently verified:\n- Phi_E(0) < 0, while D's kernel is positive and log-concave (PF_2) despite D's off-line zero. So PF_k \"passes\" a counterfeit that violates RH and \"fails\" the genuine zeta_K (at PF_2) and chi_{-19} (at PF_1).\n- Neither direction works as a criterion. The requested counterfeit predictions (E fails near 19.82, D near 31) are not made by this angle at all.",
 "numerics_reproduced": "I rebuilt everything independently in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/thetapf_skeptic/, with my own kernel constructions:\n- E and zeta_K: lattice sums over the two reduced forms of discriminant -20, x^2+5y^2 and 2x^2+2xy+3y^2, with G = (theta^2+theta)psi.\n- D: the Davenport-Heilbronn weight-3/2 odd theta series with xi = (sqrt(10-2sqrt5)-2)/(sqrt5-1).\n- zeta: the de Bruijn-Newman Phi.\n\nScripts are sk.py and c19.py. Results at 60 digits:\n- Every claim I tested was reproduced.\n- Evenness holds to 1e-61 for E, zeta_K and D, which validates the functional equation and my construction.\n- Xi_K(0) from the kernel is 0.9169909689932787, identical to -Lambda_K(1/2)/4 from mpmath (zeta(1/2) times L(1/2, chi_{-20})).\n- Phi_E(0) = -0.07502415224, and the root of Phi_E is at u = 0.3002050229. Both match.\n- zeta_K PF_2 witness: Phi(.36)^2 - Phi(.32)Phi(.40) = -1.2943e-5. Matches.\n- de Bruijn-Newman 5x5 minor at (0.01, 0.05): -1.847236073e-9. This is inside Michalowski's certified enclosure [-1.8472496, -1.8472225]e-9; the D_2, D_3, D_4 minors are positive.\n- zeta, normalized lattice minors: k=3 min 1.3e-6, k=4 min 1.3e-10, k=5 min -1.39e-7 at h=0.05, u0=0 in my scaling. That is the proposer's h=0.1 in its u/2 scaling, so this matches.\n- D, my y=e^{2u} scaling: 2x2 minors all positive, Phi_D > 0 on [0, 2.4], and 3x3 minors negative (normalized -0.0116 at h=0.3; unnormalized -6.9e-5 at h=0.1). The sign reproduces. The proposer's -4.29e-4 depends on its scale and normalization, and I did not match that absolute value.\n- chi_{-19}: y^{3/4} theta(y) = -0.4806 at y=1 and +0.091 at y = 0.5 and 2, so PF_1 fails for a genuine L-function. chi_{-43} is negative at all three points; chi_{-3} and chi_{-4} are positive.\n- Not re-run: the 1218-character census, the random off-lattice minors, and the Edrei/Jensen moment computations (I did not re-derive gam.pkl).",
 "novelty": "Low. These are known:\n- Schoenberg's PF_infinity-implies-zero-free theorem.\n- The ASW/Edrei equivalence (Katkova 2005/07; Michalowski 2607.16795).\n- The failure of PF_5 for the de Bruijn-Newman kernel (Michalowski 2602.20313, reproduced exactly here).\n- Csordas-Norfolk-Varga log-concavity for conductor 1.\n\nTheta-kernel positivity failing for some real characters is, I believe, known in the real-zero / Siegel-zero literature (Low 1968 and successors; unverified, search budget exhausted).\n\nPossibly new, as organized data only:\n- zeta_K is not PF_2 (not log-concave), while D is PF_2 even though it violates RH.\n- The E-versus-zeta_K moment coincidence as a quantitative fooling lemma for tail Toeplitz/Jensen methods.",
 "what_is_real": "This is a clean, independently reproduced negative-control (\"barrier ledger\") result, not a mechanism. It is real for five reasons:\n1. The exact witnesses: Phi_E(0) = -0.07502 < 0 (root at 0.30021); the zeta_K log-concavity failure (-1.294e-5 at .32/.36/.40); D is PF_2 but not PF_3; chi_{-19} has a negative theta kernel at y = 1.\n2. The zeta PF_5 failure, matching Michalowski's certificate to 7 digits.\n3. Taken together: kernel PF_k is neither necessary for GRH nor sufficient for RH at every k tested (1, 2, 3, and 5 for zeta).\n4. Every witness is a small determinant of fast-converging theta sums. That makes them cheap Arb and Lean interval targets for the barrier ledger.\n5. The observation that moments gamma_m for m >= M cannot separate E from zeta_K formalizes blindness in the Jensen/Turan tail. It is worth stating as a fooling-lemma corollary. The 1e-54 figure at m=400 is plausible from the saddle analysis (the ratio decays roughly like exp(-c m / log m)) but was not re-verified here.\n\nThe proposer's own verdict (alive=false) is correct.",
 "next_step_if_survives": "It does not survive as a mechanism. The single most informative next step for the ledger is an Arb certificate of Phi_E(0) < 0 together with the zeta_K PF_2 witness and the D PF_3 minor. That gives a Lean-checkable \"TP-of-theta-kernel barrier\" with one genuine L-function failing and one counterfeit passing.\n\nTwo further steps:\n- Before claiming novelty, verify Low (Acta Arith. 14, 1968) and Watkins (Math. Comp. 2004) on where the theta-kernel positivity of real characters fails.\n- Wave 3 should not spend more effort on any positivity of kernels built linearly from theta series."
}
```
