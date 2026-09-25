# Hodge index for Spec Z, wave 1: angle `amplify`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# ANGLE amplify: tensor / convolution / tower amplification of Weil positivity

conjecture1_proved = False. Nothing here proves RH or reduces it.

## 0. Summary
- **What I looked for.** A Deligne-style amplification lemma: a positivity-preserving map from tests in window x to tests in window x^k (or from one L-function to another), with W_zeta(x) following from positivity for a power, product or tower.
- **Best candidate.** The convolution-power cone. It yields **Theorem A**: for ANY fixed base x > 1, RH holds iff W(f^{*k} * (f^{*k})~) >= 0 for all f in window x and all k. KWin (x = 2) is the case k = 1.
- **Why it does not amplify.** Theorem A is an equivalence. The per-power input Deligne needs, a one-sided bound with loss o(k), is RH-strength over Q.
- **Numerics.**
  - The E and D counterfeits fail the amplified criterion at every base. This is verified on the arithmetic side, and every failing window lies past the known horizons.
  - zeta and zeta_K stay positive on the same test functions.
  - The measured deficit per power for zeta does not go to 0.
  - Tower additivity is confirmed: zeta_K's positivity is inherited from L(chi), not from zeta.

## 1. Setup
- T = (1/2)log x, and f is in C_c(-T, T).
- F(s) = ∫ f(u) e^{(s-1/2)u} du.
- f_k = f^{*k}, and g_k = f_k * f_k~, which is supported in [-k log x, k log x], i.e. window x^k.
- ĝ_k(s) = F(s)^k · conj F(1 - s̄)^k.
- s_k(f) := W(g_k) = Σ_ρ λ_ρ^k, where λ_ρ = F(ρ) · conj F(1 - ρ̄).
  - A zero on the line gives λ = |F(γ)|² ≥ 0.
  - An off-line pair ρ, 1 - ρ̄ gives the conjugate pair λ, λ̄.
- Arithmetic side (the explicit formula, validated numerically):

  s_k = [pole] ĝ(1) + ĝ(0) + (1/2π) ∫ |F(1/2 + it)|^{2k} A_L(t) dt − Σ_n c(n) n^{-1/2} (g_k(log n) + g_k(−log n))

- The weight A_L(t) is:
  - zeta: −log π + Re ψ(1/4 + it/2)
  - zeta_K and E: log 20 − 2 log 2π + 2 Re ψ(1/2 + it)
  - D: log(5/π) + Re ψ(3/4 + it/2), with no pole.

## 2. Theorem A (single-base power criterion)
**Statement.** Let L have a functional equation and a Hadamard product, with zeros symmetric under ρ → 1 − ρ̄. Fix x > 1. Then all zeros of L lie on Re s = 1/2 iff s_k(f) ≥ 0 for all Lipschitz f supported in window x and all k ≥ 1.

**Quantitative form.** If s_k(f) ≥ −A·M^k for all k, then every λ_ρ(f) with |λ_ρ(f)| > M is a positive real number, provided the top-modulus set is a single conjugate pair. A generic choice of parameters guarantees that.

**Proof.**
- (⇒) is trivial.
- (⇐), when an off-line zero ρ = 1/2 + δ + iγ exists:
  1. Take f(u) = e^{i g0 u} [B(u − T0) + B(u + T0)], where B is the m-fold box convolution of width ε and T0 + ε = T. Then F = 2 cosh(T0 z) B̂(z) with z = s − 1/2 − i g0, and B̂ = (sinh(zε/m) / (zε/m))^m.
  2. With τ = γ − g0, λ_ρ = 4 cosh²(T0(δ + iτ)) · B̂(δ + iτ)². Its modulus is about 4(sinh²(T0 δ) + cos²(T0 τ)).
  3. On the line, sup |F|² ≤ 4.
  4. So |λ_ρ| > sup_line |F|² ≥ every on-line λ once sinh(T0 δ) > |sin(T0 τ)|, for ε small. This works at every T > 0.
  5. F decays like t^{−m} on the line. The zero sum therefore converges, and only finitely many off-line λ compete.
  6. Generic (g0, τ) gives a unique top pair with phase φ ≢ 0. Then s_k = 2 Re(c λ^k) + o(|λ|^k) < 0 for infinitely many k. ∎

**Status.** This is the Li / Bombieri-Lagarias dominance argument transplanted to compact-window cones. KWin (Yoshida 1992, x = 2) is its k = 1 instance. RH is equivalent to the statement for all k at x = 2.

## 3. Why no Deligne amplification: the obstruction
Deligne's mechanism needs two things at once:
- **(i)** the power operation raises the spectral parameters to the k-th power;
- **(ii)** the trivial bound on the k-th object loses only O(1), because the tensor power's Euler product runs over the same points, with its abscissa fixed at weight + 1.

Over Q these separate:
- **Convolution powers** (Theorem A, including scale-doubling f → f*f) satisfy (i). But the prime side spreads to n ≤ x^k. The trivial bound Σ c(n) n^{−1/2} |g_k| is essentially ĝ_k at the pole, i.e. the pole acting as the extreme "off-line zero". The quantitative form of Theorem A with the trivial bound therefore only recovers Re ρ ≤ 1. Any o(k) loss is square-root cancellation at scale x^k, which is RH (Ingham/Landau equivalence).
- **Rankin-Selberg, sym^n and towers** satisfy (ii) and use the Euler product nonlinearly, e.g. c_{π×π~}(p^k) = log p · |Σ α_i^k|² ≥ 0. But:
  - they are additive on Weil forms: W_{L1 L2} = W_{L1} + W_{L2};
  - they act on Satake parameters, not zeros, so they give Ramanujan (Langlands 1970);
  - the trivial motive is idempotent: 1^{⊗n} = 1.
- **Over F_q** the two coincide. Zeros of ζ_C are Frobenius eigenvalues on H¹, which are local parameters of a family over a base (Lefschetz pencil).

**The missing object:** a family over a base whose local parameters at "points" are the zeros of ζ (Spec Z as a fibre, or Spec Z ×_{F_1} Spec Z with an Euler product over its closed points). Kurokawa's absolute tensor products have zeros ρ + ρ′ but no positive-coefficient Euler product, so (ii) is unavailable for them too.

## 4. Numerics
All code is in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/amplify/ (amp.py, val.py, scan.py, verify.py, dscan.py, deficit.py, tower.py).

**4.1 Validation (val.py).** The arithmetic side matches the zero side for zeta (300 zeros) and for zeta_K and E (the project's zero lists to height 100):
- x ∈ {e^1.5, e^2, 8}, k = 1..3;
- relative error 2e-11 to 8e-4.

**4.2 Amplified sums on the arithmetic side (verify.py).** Test parameters are (frac, m, g0); values are s_1, ..., s_k.

| base x | test (frac, m, g0) | zeta | zeta_K | E |
|---|---|---|---|---|
| 19 | (0.3, 2, 14.968) | 2.82, 4.04, 6.07 | 15.7, 30.1, 69.3 | 13.7, 17.3, **−0.818** (window 6859) |
| 12 | (0.3, 2, 14.968) | all > 0 | all > 0 | 16.2, 26.3, 31.0, **−41.9** (k = 4, window 20736) |
| 8 | (0.45, 2, 14.668) | all > 0 | all > 0 | **−48.2** at k = 5 (window 32768) |
| 5 | (0.3, 2, 16.568) | all > 0 to k = 8 | all > 0 to k = 8 | **−812** at k = 8 (window 390625) |

- The zero side reproduces each value to about 1e-3.
- scan.py (zero side) predicts E's first failure at k = 12 for base 3 and k = 26 for base 2 (window 6.7e7). These are not computable on the arithmetic side.
- D, arithmetic side (dscan.py, g0 near 85.699):

| base x | first failing k | window x^k |
|---|---|---|
| 31 | 3 | 2.98e4 |
| 20 | 4 | 1.6e5 |
| 12 | 5 | 2.5e5 |
| 8 | 6 | 2.6e5 |

- All failing windows lie above x_E ≈ 19.82 and x_D ≈ 31, as required.

**4.3 Deficit per power for zeta (deficit.py).** The quantity is (1/k) log(Σ |comb| / s_k).
- Base 2: 0.048 (k = 8), 0.066 (k = 12), 0.070 (k = 16), 0.071 (k = 19). It saturates at a positive constant.
- Base 5: 0.72 to 0.77, against (1/2) log 5 = 0.80.
- s_k^{1/k} / sup|F|² settles at 0.959 (zeta, base 2) and 0.541 (zeta, base 5).
- For E it exceeds 1 at base 2 (1.005 at k = 19) and is −0.578 at base 5, k = 8.
- Conclusion: the loss does not go to 0, so there is no amplification.

**4.4 Tower (tower.py, bcore Galerkin, 16 even modes).**

| x | λmin zeta | λmin L(χ_−20) | λmin zeta_K | λmin E | spectrum of Q_E − Q_zetaK |
|---|---|---|---|---|---|
| 5 | ~1e-16 | 1.060 | 1.082 | 1.846 | [−1.72, 1.63] |
| 10 | ~1e-16 | 0.364 | 0.379 | 0.535 | [−4.19, 2.88] |
| 20 | ~1e-16 | 3.9e-3 | 5.0e-3 | 7e-4 (unconverged) | [−5.67, 4.42] |

- Q_zetaK = Q_zeta + Q_Lχ exactly, since the forms are additive.
- zeta_K's positivity says nothing about zeta. E's defect relative to zeta_K is an indefinite pure-comb perturbation.

## 5. Counterfeit control
Theorem A fails for E and D at every base, as it must, because it is an equivalence. The step that separates them is exactly the per-power input s_k ≥ −A M^k:
- For E the dominant term is the off-line zero 0.93297 + 15.66825i.
- For D it is 0.808517 + 85.699348i.

No step of the lemma uses the Euler product, so as a proof mechanism it is dead by the linearity/fooling barrier. The Euler-product-using operations (Rankin-Selberg, towers) do not power the zeros.

## 6. Literature
All citations are from memory; web search was unavailable because the session search budget was exhausted. Treat them as unverified.
- Li, J. Number Theory 65 (1997): λ_n ≥ 0 for all n iff RH.
- Bombieri-Lagarias, J. Number Theory 77 (1999) 274-287: the power-sum/multiset version; the same dominance argument as Theorem A.
- Deligne, Weil I, Publ. Math. IHES 43 (1974): tensor-power amplification.
- Langlands, "Problems in the theory of automorphic forms" (1970): sym^n analytic properties give Ramanujan.
- Ingham (1932), ch. V (Landau): one-sided error terms are equivalent to zero-free half-planes.
- Bombieri, Séminaire Bourbaki 430 (1973), on Stepanov.
- Kurokawa, Adv. Stud. Pure Math. 21 (1992): multiple zeta / absolute tensor products.
- Yoshida, Adv. Stud. Pure Math. 21 (1992): small-support positivity.
- de la Vallée Poussin (1896).

Novelty of Theorem A is at most a repackaging of Li / Bombieri-Lagarias to compact-window cones.

## 7. Odds and deliverables
- **RH via this angle:** below 0.3%.
- **Deliverables:**
  - (a) A Lean statement "KWin = k = 1 case of a single-base power criterion" (Phragmén-Lindelöf dominance plus a Kronecker phase lemma).
  - (b) Kernel-checkable E amplified-failure witnesses at (x = 19, k = 3) and (x = 8, k = 5), and a D witness at (x = 8, k = 6).
  - (c) The obstruction statement of §3, with measured deficits of 0.071 per power (base 2) and about 0.76 (base 5).
- **Chance (a) and (b) are kernel-checked within weeks:** about 60%.
- **Pointer for future work:** a real amplification needs an operation that powers the ZEROS while keeping the prime support FIXED. Over Q that is equivalent to realising the zeros as local parameters of a family, which is the "Spec Z as fibre" problem.

## Adversarial verdict

```json
{
 "angle": "amplify (skeptic): tensor-power, convolution-power and tower amplification of Weil forms over Q",
 "survives": false,
 "fatal_flaws": [
  "Theorem A says RH holds if and only if the power-sum condition holds, so it only restates RH. It cannot prove it. The per-power bound that Deligne-style amplification would need (loss o(k)) is square-root cancellation of Lambda at scale x^k, which is RH itself. The proposer concedes this.",
  "Calling this a 'single-base' criterion is misleading. The tests g_k = f^{*k} * (f^{*k})~ fill every window x^k, so Theorem A is Weil's all-scales criterion restricted to a thin cone. It is not a statement about W(x) at the fixed x. KWin being its k=1 case says nothing about k >= 2.",
  "The linearity barrier applies unchanged. No step uses the Euler product. The theorem holds equally as an equivalence for E and D, and the proposal admits it. The steps that do use multiplicativity (Rankin-Selberg, sym^n, towers) act additively on Weil forms and raise Satake parameters to powers, not zeros.",
  "The counterfeit control does not discriminate. For E and D, any correct explicit-formula evaluation goes negative only in windows beyond x_E (about 19.82) or x_D (about 31). This follows automatically because W(x) is monotone in x. The 'consistency check passed' confirms correct bookkeeping, not the mechanism. No failure location near 19.82 or 31 is predicted.",
  "The measured 'amplification deficit' is the RH gap by definition. I measured (1/k)log(trivial bound / s_k) at 0.77-0.78 at base 5, against (1/2)log 5 = 0.80. That is the difference between the trivial bound sum Lambda(n)/sqrt n (about x^{k/2}) and square-root cancellation. It restates the obstruction; it does not newly discover it.",
  "Literature: Theorem A is a Li / Bombieri-Lagarias dominance argument moved onto compact-window convolution cones. The citations are from memory, and the web-search budget was exhausted in this session too, so they remain unverified."
 ],
 "linearity_or_classP_violation": "Yes, and the proposer states it. Theorem A is a statement about a symmetric multiset of zeros, and its proof (Phragmen-Lindelof dominance plus the phase/Kronecker lemma) goes through word for word for E and D, as an equivalence. The Euler product never enters nonlinearly. The operations that are nonlinear in L (Rankin-Selberg coefficients log p |sum alpha_i^k|^2 >= 0, sym^n, Dedekind towers) feed into Weil forms additively. Q_{zeta_K} = Q_zeta + Q_{L(chi)} holds exactly because the Weil functional is linear in log L. They therefore cannot turn zeta's k=1 positivity into positivity at k >= 2. The fooling lemma applies: nothing in the argument separates zeta from E or D except the input it assumes (s_k >= -A M^k with M = sup|F|^2), which is RH-equivalent.",
 "counterfeit_check": "I reproduced the counterfeit numbers with my own code (skeptic/sk.py). It builds g_k by Fourier inversion of |F(1/2+it)|^{2k} on the critical line, not by the proposer's u-grid FFT convolution. E's coefficients come from a brute-force count of x^2+5y^2 = n, not from genus characters. c(n) comes from the Dirichlet-log recursion.\n\nResults:\n- E (base 19, k=1..3): +13.68, +17.32, **-0.809** (claimed -0.818).\n- E (base 12, k=4): **-41.91** (claimed -41.9).\n- E (base 8, frac 0.45, g0 14.668, k=5): **-47.84** (claimed -48.2).\n- D (base 31, k=3): **-3.52** at frac 0.3, tau -0.75, and -0.54 at frac 0.45, tau +1.0.\n- D (base 8, k=6): **-44.7** at frac 0.45, tau +1.25.\n- zeta on the same tests stays positive: (19) 2.82, 4.04, 6.06; (8) 4.26 ... 606; the D-test control gives 9.13, 22.3, 59.8.\n\nSo the counterfeits do fail the amplified criterion as claimed. But every failing window (6859 up to 2.6e5) is far past the horizons, and that is automatic. The mechanism does not predict x_E ~ 19.82 or x_D ~ 31. Its detection sits one or more orders of magnitude further out, because the cone is thin.",
 "numerics_reproduced": "Yes, independently, for zeta, E and D. Scripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/amplify_skeptic/ (sk.py, run1.py to run4.py). Everything ran single-process and nothing is left running.\n\n- **Validation (run1.py).** For zeta, the arithmetic side matches the zero side (300 mpmath zeros plus their conjugates) to 1e-5 relative at x = e^1.5, 8 and 19 for k = 1, 2.\n- **Counterfeits (run2.py, run3.py).** Reproduced as listed in counterfeit_check. The E values agree to about 1% with the proposer's (discretization). For D I had to redo the tau/frac scan, because a naive g0 = 85.0 test stays positive up to k=6; the failures appear at the scanned parameters.\n- **Deficit (run4.py).** For zeta at base 5, (1/k)log(trivial/s_k) is 0.42, 0.73, 0.77, 0.78, 0.78, 0.77 for k = 1..6. This matches the proposer's 0.72-0.77 and is close to (1/2)log 5 = 0.80.\n- **Not reproduced:** the base-2 deficit series, the zero-side-only predictions k=12 (base 3) and k=26 (base 2), and the tower/Galerkin table. The tower additivity is an exact identity in any case.",
 "novelty": "Low. Theorem A is Weil's criterion restricted to the cone of tests generated from one window by convolution powers. The proof is the Li / Bombieri-Lagarias dominance argument applied to a compact-window family. The obstruction analysis (convolution raises zeros to powers but spreads the prime support; Rankin-Selberg keeps the support but raises Satake parameters, not zeros; over F_q the two coincide through Lefschetz families) matches the standard account of why Deligne's method does not transfer. The citations (Li 1997; Bombieri-Lagarias 1999; Deligne 1974; Langlands 1970; Kurokawa 1992; Yoshida 1992) are plausible but were not verified this session because web search was unavailable. What is somewhat new is packaging and data: an explicit, reproducible table of amplified-failure witnesses for E and D, and the observation that the cone detects off-line zeros from any small base window.",
 "what_is_real": "- **Theorem A is true.** I checked the proof sketch: lambda_rho = 4 cosh^2(T0(delta + i tau)) Bhat(delta + i tau)^2; the on-line sup is at most 4; the off-line zero dominates once sinh(T0 delta) > |sin(T0 tau)|. Two proof steps need tightening before a Lean formalization:\n  - Choose g0 so that the top off-line lambda is not a positive real. At tau = 0 it is positive, so genericity is essential, not cosmetic.\n  - Handle ties in top modulus with a mean-square almost-periodicity argument rather than a 'unique top pair' genericity claim. With positive multiplicities and no zero phase, sum Re(c_j e^{ik theta_j}) has mean 0 and positive mean square, so it is negative infinitely often.\n- **The counterfeit witnesses are real and reproducible:**\n  - E: (x=19, k=3), (x=12, k=4), (x=8, k=5).\n  - D: (x=31, k=3), (x=8, k=6).\n  \n  They are legitimate small certificates that E and D fail Weil positivity at windows 6859 to 2.6e5. That is weaker than, and implied by, the already-certified E failure at x >= 19.9.\n- **The obstruction statement is an accurate diagnosis.** Over Q, the operation that raises zeros to powers and the operation that keeps the support fixed come apart. The measured deficit per power, about (1/2)log x, is exactly the gap between the trivial bound and square-root cancellation. This is a useful negative result for the missions ledger. It is not a path to positivity.",
 "next_step_if_survives": "It does not survive as a mechanism. The single most informative next step is to look for a nonlinear operation that raises zeros to powers while keeping prime support bounded by x^{O(1)} (not x^k). Concretely:\n- Test whether any bilinear operation on Dirichlet series with a positive Euler-product output keeps the base-2 deficit per power below the 0.07 measured for convolution powers. Candidates are Kurokawa absolute tensor products, or Rankin-Selberg of zeta against the theta-lift families behind E. If none does, the whole amplify family can be closed with a stated obstruction.\n- Separately, formalize Theorem A in Lean, with the two proof fixes above, as the statement 'KWin is the k=1 case of a cone criterion'. Kernel-certify one E witness, (x=8, k=5), which needs n <= 32768. That is low-cost and cleanly true, but it adds nothing toward RH. conjecture1_proved = False."
}
```
