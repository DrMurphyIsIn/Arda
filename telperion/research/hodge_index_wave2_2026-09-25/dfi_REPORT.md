# Hodge index WAVE2: angle `dfi`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Angle dfi: the amplifier. Verdict: DEAD as a positivity mechanism. It yields one barrier theorem and one detector.

conjecture1_proved = False. Nothing here proves or reduces RH.

## 1. Setup and precise mechanism

Let L be zeta_K (K = Q(sqrt -5)) or its counterfeit E = (1/2)Σ'(x^2+5y^2)^{-s}. Let d run over fundamental discriminants with gcd(d,20) = 1 and 1 ≤ |d| ≤ D, and set L_d = L ⊗ χ_d.

- For zeta_K: L_d = L(χ_d) L(χ_d χ_{-20}).
- For E: E_d = (1/2)[L(χ_d)L(χ_dχ_{-20}) + L(χ_dχ_{-4})L(χ_dχ_5)].
- Both have conductor 20d^2, a Γ_C(s) archimedean factor and root number +1. For d ≠ 1 they have no pole.
- Twisting by a completely multiplicative χ_d commutes with Dirichlet convolution, so -L_d'/L_d has coefficients c_L(n)χ_d(n) for ANY base.

Write Q_{d,x}(f) = Pole + (log 20d^2)||f||^2 + Arch_Γ_C(f) − Σ_n c_L(n)χ_d(n) n^{-1/2} [g(log n) + g(−log n)], with g = f * f~ and supp f ⊂ [−A, A], x = e^{2A}.

**Family theorem (easy, true for any base).**
- Averaging: Q̄ = (1/N)Σ_d Q_d = (mean log conductor)||f||^2 + Arch − Σ_{n=□}(...) + O(x log x / D)||f||^2.
- So Q̄ ≥ 0 once log D ≳ log x + C.
- With the amplifier A(χ_d) = Σ_{p≤L} χ_d(p), the same holds for Σ|A|^2 Q_d when x L^2 ≲ D^{1−ε}. This is the ILS / Özlük-Snyder style support range, not needed in full here.

**DFI transfer (what is needed).**
- The target is Q_{d0} ≥ 0.
- The identity |A(χ_{d0})|^2 Q_{d0} = Σ|A|^2 Q_d − Σ_{d≠d0}|A|^2 Q_d only helps if the dropped terms are nonnegative. That is GRH for the rest of the family. So the transfer is circular.
- In DFI, amplification bounds a quantity that is nonnegative term by term (|L|^2). The Weil form is not known to be nonnegative term by term, and that is precisely the goal.
- Quantitatively, isolation needs w_{d0}/(1 − w_{d0}) ≳ (margin of the others)/|deficit of d0|. In the provable range, w_{d0} ≈ π(L)/(π(L) + N) ≪ 1.

## 2. Euler-product usage

Averaging only uses orthogonality over d, which is linear in c_L and blind to counterfeits. For GL(1) twists, the amplifier's Hecke-type relation χ(p)χ(q) = χ(pq) is automatic. It is NOT a property of the base, so the premise that E and D leave the weights undefined is false.

The single nonlinear point is the pair of amplified cross terms p ≠ q. In the infinite-family limit they give −Σ_{p≠q} Σ_{n: npq=□} c_L(n) n^{-1/2} K_n.
- This vanishes identically when c_L is supported on prime powers (Lemma O), since npq is never a square for n = r^k and p ≠ q.
- For E it is nonzero: c_E(6) = 3.584, c_E(14) = 5.278, c_E(21) = 12.178, c_E(36) = −7.167.
- Computed as a form, it is indefinite: eigenvalues in [−7.38, +6.76] at x = 28 (even sector, L = 13) and [−9.30, +9.10] at x = 100.

So the amplifier detects a missing Euler product, but it contributes no sign.

## 3. Counterfeit control and tests

Code: scratchpad/hodge2/dfi/fam.py. It builds the per-member form from arch(q=1) + (log q)·Gram − Σ w(n) K_n. It reproduces bcore to about 1e-15 for E and zeta_K at x = 20 and 28 in both sectors. Mode counts are 9-14 (Neumann cos/sin basis). Negativity is a genuine certificate, since more modes only lower λ_min. Positive values are upper bounds.

**T1-T2: amplified/averaged E-family vs E itself** (67 members, |d| ≤ 200, 9 modes).

| x | sector | E itself | E-family average | amplified L=37 (w1=0.22) | crossover w1* | isolation ratio |
|---|---|---|---|---|---|---|
| 28 | odd | −1.72e−2 | +9.41 | +7.80 | 0.99837 | 613 |
| 35 | even | −5.74e−2 | +4.17 | +3.21 | 0.99477 | 190 |

Also found:
- E⊗χ_{−19} (conductor 7220) is Weil-negative at x = 28: −4.19e−2 (even sector).
- By x = 150, 6 of the 21 E-members with |d| ≤ 60 are negative.
- Every zeta_K-family member is positive at every x tested.

Transfer is refuted on a counterfeit: the positive family forms coexist with negative members.

**T3: averaging makes the counterfeit horizon WORSE.**
- Single E: x_E ≈ 19.8.
- 5-member family {1, −3, −7, −11, 13}: the E-average first goes negative at x ∈ [662.9, 663.4] (even sector, 12 modes).
- 21-member family: the E-average is still positive at x = 3000 (+0.31 even, +1.71 odd).
- The zeta_K averages stay positive throughout: 5-member +0.02 / +0.65 and 21-member +0.91 / +4.68 at x = 3000.

So the average IS eventually counterfeit-sensitive (an average of PSD forms is PSD under GRH). But the sensitivity sits orders of magnitude beyond any provable range, and it recedes as the family grows.

**T4: zeta quadratic family** (123 fundamental d with |d| ≤ 200, Γ_R(s) or Γ_R(s+1)).
- The small-conductor members (d = 1, −3, −4, 5, 8) have λ_min at float roundoff, about 1e−15. This is the near-null saturation.
- The family average is +1.46 / +3.23 at x = 20, +0.96 / +2.97 at x = 57 and +0.77 / +2.71 at x = 100 (even / odd).
- This margin is conductor dominance, decaying roughly like log D − log x. It contains no arithmetic information about d = 1.

**D:** not run. D ⊗ χ_d does not keep D's functional equation (the root number of χχ_d changes), so the twist family needs its own κ_d per member. That is a further structural failure, since the family itself is not defined.

## 4. Literature

Cited from memory; the web-search budget ran out this session.
- DFI, Invent. Math. 112 (1993).
- ILS, Publ. IHES 91 (2000).
- Özlük-Snyder (support 2 for the quadratic family under GRH).
- Rubinstein, Duke 109 (2001).
- Hughes-Rudnick, Q. J. Math. 54 (2003).
- Kowalski-Michel, Pacific J. Math. 207 (2002): density near 1 via amplification.
- Iwaniec-Kowalski, Ch. 26.

It is folklore that amplification gives power savings (subconvexity) and density bounds near σ = 1, never Lindelöf or zero-free regions near 1/2. Our circularity is the Weil-form incarnation of that. I know of no paper that amplifies the Weil functional itself (unverified).

## 5. Deliverables and odds

- **Odds.** About 0% for RH via DFI transfer; about 0.1% for some nonlinear variant.
- **Deliverable 1, the Amplification barrier.** Any averaged or amplified positivity of twist-family Weil forms that is provable by conductor dominance plus orthogonality holds verbatim for E-twist families, which contain certified Weil-negative members (E at x = 28, E⊗χ_{−19} at x = 28). So it cannot imply individual positivity. The certificates are finite and kernel-checkable with the FWindow infrastructure (conductor 20d^2, Γ_C).
- **Deliverable 2, the cross-term detector.** The amplified form's p ≠ q part equals 0 if and only if c_L is supported on prime powers. This is Lemma O in amplifier form: a detector, not a positivity.
- **Recommendation.** Do not pursue DFI transfer. Fold the E-family certificates into Lane A (the counterfeit ladder) as the "averaging/amplification" rung.

## Adversarial verdict

```json
{
 "angle": "dfi (skeptic): Duke-Friedlander-Iwaniec amplification, moving Weil positivity from a family average of quadratic twists to a single member",
 "survives": false,
 "fatal_flaws": [
  "Circular transfer: Q_{d0} = (sum w_d Q_d - sum_{d != d0} w_d Q_d) / w_{d0} gives Q_{d0} >= 0 only if the dropped members satisfy Q_d >= 0, which is GRH for the rest of the family. The proposer says this too. In DFI, amplification bounds a quantity that is nonnegative term by term (|L|^2 or a spectral sum); here that nonnegativity is exactly what we are trying to prove.",
  "Linearity barrier holds in full. Averaging over the family uses only orthogonality of chi_d, and c_{L x chi_d}(n) = c_L(n) chi_d(n) for any base, so the averaged and amplified forms are linear in c_L. The easy family positivity (conductor dominance, log D >> log x) holds verbatim for E. I confirmed this with my own code: the E-family average is positive while members of the family are certified negative.",
  "The only place the Euler product enters nonlinearly is the amplified p != q cross terms, and they have no sign. They are indefinite for E and identically zero for zeta and zeta_K, so they detect a missing Euler product but cannot supply positivity.",
  "Overstated claim: the proposer says the cross terms vanish 'if and only if' c_L is supported on prime powers. Only the 'if' direction is true. The cross terms vanish iff c_L(p q m^2) = 0 for all p != q, which misses n with 4 or more primes to an odd power. For E, c_E(966 = 2*3*7*23), c_E(1806), c_E(1974) and c_E(2814) are nonzero, while c_E(30), c_E(42), c_E(105) and c_E(1155) are 0. In any case, whether an Euler product exists can be read straight off a(6) vs a(2)a(3), so the 'detector' adds nothing beyond Lemma O.",
  "The isolation ratios (613 and 190) are not invariants: they depend on the Galerkin basis and mode count. With my basis and 13 modes I get 295 (x=28 odd), 58 (x=28 even) and 26 (x=35 even). The qualitative point, that the target needs about 96-99.7% of the weight while the provable range allows pi(L)/N << 1, survives.",
  "Averaging moves the counterfeit horizon the wrong way: a single E fails at x ~ 20, the 5-member family average at x ~ 663, the 21-member one beyond 3000. So any mechanism built on family averages is strictly blinder to counterfeits than the individual form."
 ],
 "linearity_or_classP_violation": "Yes, and the proposer concedes it. The averaged and amplified Weil forms of a quadratic-twist family are linear in the log-derivative coefficients c_L, because twisting by a completely multiplicative chi_d commutes with the Dirichlet convolution that produces c_L. The amplifier weights |A(chi_d)|^2 depend only on the family parameter d and are defined for any base, including E. So the provable family positivity (conductor dominance plus Polya-Vinogradov on the off-diagonal terms) holds verbatim for the E-twist family. I reproduced this: the 67-member E-family average has lambda_min +9.39 (x=28, odd sector) and +4.17 (x=35, even), while E itself is negative (-3.7e-2 and -4.6e-1) and so is E x chi_{-19} (-4.4e-2 at x=28 even). The fooling lemma applies directly.\n\nThe only nonlinear, Euler-sensitive term is the p != q amplified cross terms, which carry no sign. D was not run: twisting D by chi_d breaks its functional equation because the two component root numbers change differently. That argument is plausible but I did not check it numerically.",
 "counterfeit_check": "Independent code, sharing nothing with bcore or fam.py: scratchpad/hodge2/dfi_skeptic/wf.py. It uses a u-space Weil form, with the archimedean Gamma_C term taken from the integral representation of psi, pole terms h(+-i/2), and log-derivative coefficients from a(n) log n = sum_{d|n} c(d) a(n/d). The basis is Legendre P_j(u/A); in the even (odd) sector, J = 7, 10, 13 or 17 modes are the first J even (odd) degrees.\n\n- **E crosses near 19.82.** The x_E prediction reproduces. With J=13 (even sector), E is +3.3e-3 at x=19, +6.0e-4 at x=19.9, and first goes negative (-1.0e-5) at x=20.5. It is -1.75e-1 at x=28 and -4.6e-1 at x=35. With the same basis and modes, zeta_K stays positive: +5.2e-3 at x=19.9, +7.3e-5 at x=28, +1.9e-6 at x=35. The onset near 20 matches the certified x_E ~ 19.82. Fewer modes (J=7 or 10) stay positive through x=35, so the negative direction needs high polynomial degree and functions that do not vanish at the edge of the window.\n- **c_E values match the proposer's:** c_E(6)=3.5835, c_E(14)=5.2781, c_E(21)=12.1781, c_E(36)=-7.1670.\n- **Family average and member negativity reproduce** (67 fundamental d = 1 mod 4 with gcd(d,20)=1 and |d| <= 200):\n  - x=28 odd: E-family average +9.39 (proposer +9.41), zeta_K-family +9.22.\n  - x=28 even: E-average +4.49 (proposer +4.5), with negative members {1, -19}.\n  - x=35 even: E-average +4.17 (proposer +4.17).\n  - Every zeta_K-twist member is positive.\n- **The 5-member horizon at ~663 reproduces.** For {1, -3, -7, -11, 13} in the even sector, the E-average is +0.0975 at x=500 and -0.0109 (J=13) / -0.0151 (J=17) at x=663, then -0.154 at 800. The zeta_K average stays positive (+0.106 at 663, +0.071 at 1000).\n- **Side finding.** The member E x chi_{-3} is Weil-positive and near-null (lambda ~ 1e-11) up to x=1000. So not every counterfeit twist fails early. The effect is the same near-null Galerkin saturation that zeta_K and its d=-3 twist show at these sizes, not a sign of an Euler product (c(14) is nonzero after the twist).\n\nD was not tested; the x_D ~ 31 prediction was not checked.",
 "numerics_reproduced": "Yes: the main numbers agree to about 1% with independent code (averaged forms +9.39 / +4.49 / +4.17; E x chi_{-19} = -4.4e-2 against the proposer's -4.19e-2), even though the bases differ. The E threshold near 20 and the 5-member family horizon near 663 also reproduce. The negative lambda_min values are Rayleigh-Ritz certificates in the sense that more modes can only lower them, but my matrices are double-precision quadrature, not interval-certified.\n\nIsolation crossover weights do NOT reproduce numerically. They depend on the basis:\n- x=28 odd: w1* = 0.99662 (ratio 295), against the proposer's 0.99837 (613).\n- x=28 even: 0.98302 (ratio 58).\n- x=35 even: 0.96286 (ratio 26), against the proposer's 190.\n\nThe qualitative conclusion survives: isolating the target needs about 96-99.7% of the weight on one member. Scripts are t0.py through t4.py in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/dfi_skeptic/.",
 "novelty": "Low. I could not verify the literature this session because the web-search budget was exhausted (200/200), so every citation below is unverified.\n\nThe citations the proposer gave from memory are standard and look plausible:\n- Duke-Friedlander-Iwaniec, Invent. Math. 112 (1993)\n- Iwaniec-Luo-Sarnak, Publ. IHES 91 (2000)\n- Rubinstein, Duke 109 (2001)\n- Hughes-Rudnick (2003)\n- Kowalski-Michel, Pacific J. Math. 207 (2002)\n- Iwaniec-Kowalski, Chapter 26\n\nIt is well known that amplification gives subconvexity and zero-density estimates near sigma = 1, never zero-free regions near 1/2. The circularity found here is that folklore restated for the Weil functional. The 'Amplification barrier' amounts to 'a positive average does not imply positive members', instantiated with E-family certificates. The cross-term detector restates the project's Lemma O, and its 'iff' is overstated.",
 "what_is_real": "The negative verdict is correct, and three pieces are worth keeping.\n\n1. **Finite certificates for the counterfeit ladder (Lane A).** A twisted counterfeit E x chi_{-19} (conductor 7220, Gamma_C, no pole) is Weil-negative at x=28 in the even sector, and the E-family average (67 members) is positive there. This is a concrete, kernel-checkable instance of 'positive average does not imply positive members'. It is already certifiable with FWindow machinery by changing the conductor.\n2. **The averaging horizon grows with family size.** The single-E horizon of about 20 moves to about 663 for 5 members and beyond 3000 for 21 members; I reproduced the 663. This is a quantitative form of the linearity barrier for family methods: averaging weakens counterfeit detection.\n3. **The cross-term observation, as a corrected statement.** The amplified p != q cross-term form vanishes iff c_L(p q m^2) = 0 for all primes p != q and all m. That is implied by an Euler product but does not imply one (c_E is nonzero at 966 = 2*3*7*23). It detects, but has no sign.\n\nNothing here brings W(x) closer. conjecture1_proved = False.",
 "next_step_if_survives": "Not applicable as a mechanism, since it does not survive. The single most informative follow-up is to certify one E-twist counterfeit rung at the kernel level: E x chi_{-19} is negative at x=28 in the even sector, and the matching averaged E-family form is positive. Use the existing FWindow / bcore certificate pipeline with conductor 20*361 and no pole, adding it as the 'averaging/amplification' rung of the counterfeit ladder. Also correct the 'iff' in the Lemma-O detector statement before anything is recorded."
}
```
