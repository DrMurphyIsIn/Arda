# The Missing Frobenius: Synthesis (2026-09-24)

conjecture1_proved = False. Nothing below proves RH, reduces it, or narrows the problem.

## 1. What a "Frobenius for Spec Z" has to be

Each framework calls the pieces by different names:

| Axiom | Connes | Deninger | Hilbert-Polya | F_1 geometry |
|---|---|---|---|---|
| X1. Space | Adele class space A_Q/Q^x | Foliated 3-dimensional space with a preserved archimedean leaf | Hilbert space | Spec Z-bar x_{F_1} Spec Z-bar |
| X2. H^1 | Cokernel of E (the absorption spectrum) | Reduced leafwise H^1 | The spectral subspace | Primitive classes |
| X3. Flow | Scaling action of C_Q -> R_+ | R-flow; closed orbits = primes | e^{itH} | Frobenius graphs Gamma_lambda |
| X4. Lefschetz | Semilocal trace formula (proved) | ALKL 2024 trace formula (proved, smooth compact case) | Gutzwiller/Selberg reading | Gamma_f . Delta |
| X5. Locality (Euler product) | Weights on prime powers | Orbit lengths log p^k | Orbit axioms | Fixed points p^k |
| X6. Purity | Unit local roots | Holonomy with abs value 1 | Bound c(n) <= log n | Weight 1/2 |
| X7. Hodge index | W(f*f^#) >= 0 | Leafwise Kahler, alpha = 1 | Self-adjointness | D_f^2 <= 0 on primitive classes |

Notes on the axioms:
- **X4.** In all four frameworks the trace formula is the Weil explicit formula. It is proved semilocally (Connes 1999) and in the smooth compact case (ALKL 2024).
- **X5.** This is Lemma O: c(n) is supported on prime powers if and only if a(n) is multiplicative. It is textbook material. Combined with the project's classP_eq_zeta, it leaves no arithmetic freedom: X4 + X5 + zeta's archimedean data single out zeta.

**Where the frameworks agree:** X4 and X5 are identical in all four.

**Where they disagree:** on where positivity would come from.
- **Connes:** positivity of a quadratic form on the adelic space.
- **Deninger:** conformal scaling of the flow. In the compact category this is impossible: the volume lemma forces alpha = 0, and the period group is finitely generated. Both facts are known.
- **Hilbert-Polya:** self-adjointness.
- **F_1 geometry:** an intersection form on a surface that nobody has built. Borger's square collapses to Spec Z, and the Fargues-Fontaine curve has genus 0 and works one prime at a time.

## 2. The one obstruction

All four frameworks stop at the same statement, W(x):

> Q_x(f) = W(f * f~) >= 0 for every smooth f supported in [-(1/2) log x, (1/2) log x], full class, pole terms kept, for all x.

- RH holds if and only if W(x) holds for every x (Weil 1952).
- Connes' global trace formula is W; CCM 2025, Cor. 3.8, states the RH criterion in this form.
- Deninger's X7 is W restated on H^1.
- Hilbert-Polya self-adjointness together with X4 implies W, and W implies RH.

Each framework's "Frobenius" is a device that proves X4. None of them has a source for X7. **The missing piece is a positivity, not an operator.**

There is a second shared obstruction. Every framework has infinite genus, and its prime side is a set of atoms on the non-discrete set {log n}. So there is no Castelnuovo-Severi inequality and no tensor-power amplification.

**How the project's results fit:**
- **KWin (x = 2).** This is Yoshida's 1992 theorem, which Connes-Consani cite. Yoshida proved it on the pole-free subspace; the project's version keeps the pole terms and is kernel-checked. Margin 1.33e-3.
- **KWin2 (x = e^0.8).**
- **L = 1/2 (x = e).**

All three are counterfeit-blind:
- **D** (Davenport-Heilbronn function) stays positive up to x of about 31-35.
- **E** stays positive up to at most x of about 19-20. E is the Epstein zeta function (1/2) sum' (x^2+5y^2)^{-s}, normalized so a(1) = 1. Its first off-line zero is at 0.93297 + 15.66825i. It keeps the pole, the Gamma_C functional equation, a_n >= 0, and c_E(n) >= 0 for n < 36. The threshold of about 20 is only an upper bound, since the least eigenvalue is not yet converged in the number of modes.

The project's barriers (fooling lemma, class P = {zeta}, the semilocal barrier W_{p,c}, Crux3) are consistent with this. Every ingredient that uses no Euler product is DH-blind. The skeptics confirmed this for:
- the Connes-van Suijlekom realness theorem;
- the accuracy of CCM zeta-cycles (reproduced by D below its horizon);
- GUE local statistics;
- the Bender-Brody-Muller Hamiltonian (for D it gives the non-real eigenvalue -171.3987 + 0.6170i).

The precise gap is a positivity mechanism that uses prime-power support at windows past a counterfeit's horizon. The x of about 31 figure is specific to D. For zeta itself no matched counterfeit exists (the class-P barrier), so the right proxy is zeta_K for K = Q(sqrt(-5)) against E.

## 3. Surviving proposals, ranked by (value if true) x (feasibility)

1. **zeta_K vs E window separation (the geometry angle; the only proposal the skeptic passed).**
   - Crux3-style Lean certificate at x = 28 with 9 modes: Q_E(v)/||v||^2 = -0.165 and Q_zetaK(v)/||v||^2 = +4.96. The zero side agrees with the arithmetic side.
   - Control: the zeta_K side uses the weights Lambda(n)(1 + chi_-20(n)), which are supported on prime powers. E has no such weights, and D fails as well.
   - Kernel-checkable with the existing FWindow infrastructure (conductor 20, Gamma_C archimedean factor). High feasibility.
2. **Lemma O in Mathlib's ArithmeticFunction form, plus witnesses** c_D(6) = (1 + kappa^2) log 6 and c_E(6) = 3.584, wired to classP_eq_zeta.
   - This is plumbing: it pins each counterfeit's failure to a specific orbit (length log 6).
   - Estimated 200-500 lines. It carries its own D control.
3. **Kernel index witness ind Q_{D,x} >= (1,1) at x = 40 or 57.** This is the odd-sector companion to Crux3, and the Pontryagin-index form of D's off-line quadruple. Cheap to build. It is a barrier result.
4. **Corrected Lemma H** (rank-one Schur complement with a pseudo-inverse and a range condition; the pole acts as the fibre class).
   - Useful dictionary infrastructure, but it only relabels the Weil criterion.
   - Undefined for D, which has no pole; E is the correct control.
5. **Arb-certified DH control of the CCM zeta-cycles.** Publishable calibration, not Lean work.
   - Keep: CvS realness holds for D, D's zero approximations collapse at its horizon, and a false zero at 85.70 shadows its off-line quadruple.
   - Drop: the float64 claims near roundoff (x = 17, x = 31-34, the second eigenvectors).
   - The BBM/D trap goes into the docs as a standard test for any Hamiltonian claim.

**Dropped:**
- GCE: a counting triviality, redundant with C1, and passed by rational counterfeits.
- OHT prediction 1: miscalibrated; L5 itself will falsify it at 10^4 spacings.
- The claim that D is "more rigid" than L5: probably a truncation artifact.
- Period and volume lemmas: already known.
- The "x >~ 31 universal" prescription: D-specific.

### Recommended build lanes (at most two)

**Lane A: the counterfeit ladder.** Proposals 1 + 2, with proposal 3 optional.
- Make E the project's standard second counterfeit.
- Certify E's threshold as an interval in Arb, extrapolated in the number of modes M, over x in {17, ..., 20}.
- Kernel-check the x = 28 separation and the Lemma O witnesses.
- Success gives a certified map of where every non-Euler control dies (E at about 19, D at about 31), and a mechanical filter: any claimed positivity mechanism must fail for E at x = 28.
- Failure would mean an Arb value outside [-0.17, -0.16], or a threshold that drifts materially below 19. Either would expose a modelling error in FWindow.

**Lane B: the first counterfeit-sensitive positivity theorem.**
- Step 1, a one-week gate: compute the certified full-window lambda_min(zeta_K, x) at x in {20, 24, 28}. The geometry angle's float value at x = 32 is +1e-5; conductor 20 rescales the window, which is why this is plausible where zeta's own margins, about 1e-150 at x = 57, are hopeless.
- Step 2: if the margin is at least 1e-6, build a KWin-style full-class Lean positivity theorem for zeta_K at a window where E is kernel-certified negative.
- Success teaches that kernel positivity can cross a counterfeit horizon. Such a certificate must consume prime-power support, which is the first finite instance of the missing input actually being used.
- Failure teaches where the conductor-scaled numerical wall sits.
- Either way it is a single window of a single function. It is not a mechanism and not a step to all x.

## 4. Bottom line

The four frameworks are one dictionary. Each proves the trace formula and makes RH equivalent to W(x) for all x, and none has an idea for proving W. Odds that any of the four angles reaches RH in a foreseeable horizon: below 1%, about 0.5%.

What the project can realistically deliver:
- a rigorously certified counterfeit ladder;
- counterfeit-blindness theorems for all current windows;
- possibly one kernel-checked positivity window that no counterfeit with the same functional equation passes.

That is honest barrier and calibration science. It shows exactly where arithmetic has to enter, but not how.

Corrections to carry forward:
- KWin is Yoshida 1992 (pole-free) in a pole-kept, kernel-checked variant.
- In Connes 1999, critical zeros form an absorption spectrum and non-critical zeros appear as resonances.
- E's normalization is half of the stated sum, so that a(1) = 1.
- E's threshold of about 20 is an unconverged upper bound.
- Off-line zeros of Epstein zeta functions are classical (Potter-Titchmarsh 1935, Davenport-Heilbronn 1936, Stark 1967).
