# Hodge index WAVE3: angle `converse`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Wave 3, converse angle: the converse theorem as the global Euler-product × FE coupling

**Verdict: dead against E, and structurally so.** It yields one new barrier and one correction to an existing barrier. `conjecture1_proved = False`.

All scripts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/converse/`. No repo files were modified.

## 1. Mechanism (precise)

For an L-function L with Γ-factor Γ_L, conductor q_L and −L'/L coefficients c_L(n), and a primitive character χ mod r, the twist L⊗χ has c_{L⊗χ}(n) = χ(n)c_L(n).

Its window Weil form is Hermitian on complex f supported in [−A, A], with x = e^{2A}:

Q_{L⊗χ}(f) = [pole if χ = 1 and L has a pole] + Arch_{Γ, q}(h) − Σ_{n ≤ x} n^{−1/2} [c(n) h(log n) + c̄(n) h(−log n)], where h = f * f̃.

Pairing χ(n) with h(+log n) or with h(−log n) is only a convention: swapping them gives χ̄, whose zeros are the conjugates.

**Two family forms:**
- **(a) Block form.** W_tot = Σ_χ Q_{L⊗χ}(f_χ), with an independent f_χ for each χ. On the idele class group ℝ₊ × Ẑ^* this is Weil's 1952 explicit-formula positivity for all Größencharaktere, which is also Connes' adelic formulation.
- **(b) Averaged form.** Q̄_r(f) = φ(r)^{−1} Σ_{χ mod r} Q_{L⊗χ}(f), with the same f for every χ. By orthogonality its prime side is φ(r) Σ_{n ≡ 1 (r)} c(n) (· · ·). This is the 1-level-density family average.

**Hoped-for theorem.** Family positivity follows from something weaker than individual GRH, and it implies W_ζ(x).

**What is true:**
- **(a) is trivial.** It is block-diagonal, so it is exactly equivalent to the conjunction of the individual GRH-window statements. It "implies" W_L(x) only because L is the trivial-twist member.
- **(b) is genuinely weaker** and has the manifest-positivity flavour: for r > x every prime term vanishes. But it cannot see counterfeits (§3).

## 2. Where the Euler product enters: nowhere nonlinearly

- **Twisting is linear.** χ is completely multiplicative, so twisting commutes with Dirichlet convolution and with d/ds log, for every Dirichlet series.
- **Twisted FEs are linear conditions.** They hold on the whole Hecke-stable space spanned by eigenforms that share root numbers.
- **E is automorphic.** E = ½(ζ_K + L_G), with L_G = L(χ₋₄)L(χ₅), is the theta series of x² + 5y². It is a weight-1 modular form in M₁(Γ₀(20), χ₋₂₀) and a sum of two Eisenstein eigenforms.
- **The root numbers match for every twist.** Let w(ψ) denote the root number of L(ψ). For (r, 20) = 1: w(χ)w(χχ₋₂₀) = w(χχ₋₄)w(χχ₅) = w(χ)² χ₋₂₀(r) χ(20). So every coprime twist of E has an FE.
- **Consequence.** Weil's GL(2) converse theorem outputs *automorphy*, and E is automorphic. The Euler product corresponds to the **Hecke-eigen / multiplicity-one** property: T_p E ∝ E, a quadratic rank condition. No converse theorem uses it.
- **Status under the barrier.** The proposal is dead by the linearity barrier for E. The missing nonlinearity is multiplicity one (Selberg orthonormality: Rankin–Selberg pole order 1), not "more functional equations".

## 3. Counterfeit controls, with the numerics actually run

**Validation.**
- The complex-basis form matches `bcore` to about 1e−15: ζ_K at x = 20 gives 5.2567e−3, and E at x = 22 gives −1.6603e−4.
- The D zero checks out: |D(0.808517 + 85.699348i)| = 6.5e−7, against |L(χ₅)| = 0.70 at the same point.

**T1: which twists satisfy an FE** (`fe.py`). Test: is Λ(s)/Λ_dual(1−s) constant across three points s?

| Object | Moduli that pass (spread) | Moduli that fail (spread) |
|---|---|---|
| E⊗χ, all primitive χ | 3, 7, 9, 11, 13: all pass (≤ 1.4e−14; mod 3: 1.8e−20) | none |
| D⊗χ | r ≡ ±1 mod 5, i.e. 4, 9, 11 (≤ 9e−15) | r ≡ ±2 mod 5, i.e. 3, 7, 8, 13 (spread 1.3 to 8.8) |

This matches the derivation: the FE for D⊗χ exists iff χ₅(r)² = 1.

- **E is invisible to the converse theorem. D is caught by the GL(1) converse theorem, and linearly.**
- **Correction to the project's LINEARITY BARRIER.** "D satisfies every linear summation formula" is false as worded. D's twisted FE/Voronoi formulas at moduli r ≡ ±2 mod 5 fail. The robust statement should be made with E: E satisfies every linear FE-type identity satisfied by elements of M₁(Γ₀(20), χ₋₂₀), including all coprime twists.

**T2: block family** (`scan.py`, N = 16 complex Fourier modes; λ_min values).

| x | 14 | 19 | 20 | 22 | 26 | 35 |
|---|---|---|---|---|---|---|
| ζ_K | 7.5e−2 | 8.3e−3 | 5.0e−3 | 1.9e−3 | 2.6e−4 | 2.3e−6 |
| E | 1.1e−1 | 3.5e−3 | 5.0e−4 | **−7.1e−3** | **−0.17** | **−0.55** |
| ζ_K⊗χ₋₃ | 0.71 | 0.39 | 0.34 | 0.25 | 0.14 | 3.3e−2 |
| E⊗χ₋₃ | 0.22 | 0.11 | 0.10 | 7.8e−2 | 4.7e−2 | 1.0e−2 |
| E⊗χ mod 7, all 5 | ≥ 1.6 | ≥ 1.05 | ≥ 0.97 | ≥ 0.83 | ≥ 0.60 | ≥ 0.24 |

- **Mode convergence** (`conv.py`). At x = 35, E⊗χ₋₃ gives 1.026e−2, 1.006e−2 and 1.002e−2 at N = 16, 32 and 48.
- **Far scan** (`far.py`, N = 32). E⊗χ₋₃ is positive at x = 70, 100, 140 and 199: 8.1e−5, 7.7e−6, 2.5e−7 and 6.0e−9. The corresponding ζ_K⊗χ₋₃ values are 1.3e−4, 1.5e−5, 3.1e−7 and 9.2e−9.
- **Conclusion.** The family fails first, and only, through its untwisted member, at x_E ≈ 19.82. Twisting raises the analytic conductor to 20r², which raises the margin; the counterfeit twist behaves like the genuine one.
- **Prediction** "E's family goes negative earlier": **refuted**.

**T3: averaged family** (`avg.py`, N = 16, x ∈ {14, …, 45}).
- For every r ∈ {3, 7, 11, 13, 23, 37}, the averaged E form is positive through x = 45. For r = 3 it is +0.34 at x = 45, while E alone is −1.07 there.
- For r = 37 the E and ζ_K rows are identical to every printed digit. For r = 23 they are identical up to x = 22. In both cases no n ≡ 1 (mod r) lies in 2..x.
- The averaged form is **provably blind**: for r > x it depends only on arch data, and E and ζ_K share their arch data.

**D control.**
- D itself is near-null: λ_min is 7.5e−4 at x = 6, 1.1e−7 at x = 10, and float64 noise from x ≈ 14. So "does D's family fail before D?" cannot be decided in float64; it needs mpmath matrices with N ≳ 50 to reach the off-line zero at height 85.7.
- The FE-valid twist D⊗χ₋₄ (conductor 20) is positive and converged: 3.3e−8 at x = 35 and 4e−12 at x = 50.
- The formal no-FE twists D⊗χ (cubic χ mod 7) go negative at x ≈ 28–31. These forms equal no zero sum, so this is not a valid detection.

## 4. What survives (barrier ledger entries)

1. **Converse-theorem barrier (new, precise).** Let 𝓕 be any criterion built from (i) functional equations of twists L⊗χ, or (ii) averages over χ of twisted window forms. Then 𝓕 cannot separate ζ_K from E, because E ∈ M₁(Γ₀(20), χ₋₂₀) satisfies every twisted FE with (r, 20) = 1, and its averaged forms equal ζ_K's for r > x. Evidence: T1–T3, which are decidable-style checks.
2. **Hierarchy of counterfeits.**
   - D (degree 1) is excluded by the linear GL(1) converse theorem. It is a *weak* counterfeit.
   - E (degree 2) survives every linear and automorphic test. It is excluded only by the Hecke-eigen property, a quadratic condition.
   - Hence the separating input is multiplicity one / primitivity, i.e. the Selberg-orthonormality / pole-order-1 of Rankin–Selberg. It is not "more FEs".
3. **Conductor monotonicity (empirical).** Twisted margins exceed untwisted ones: E⊗χ₋₃ stays positive to x ≥ 199. Family positivity is therefore dominated by the minimal-conductor member.

## 5. Pivot (untested)

Couple the **Hecke-eigen quadratic constraint** to the FE. One candidate is a Rankin–Selberg window form for L × L̃ with the pole order fixed at 1. Another is to merge it into the wave-1 EFW experiment (Euler shape + truncated FE, Lane 2) by adding the constraint "coefficients satisfy the Hecke relations a(m)a(n) = Σ_{d | (m,n)} χ(d) a(mn/d²)". E violates this at small n.

Caution: Conrey–Farmer (1995), from memory, show that an Euler product can *replace* twists in converse theorems at small level. That is consistent with the direction here, but it concerns automorphy, not positivity.

## 6. Literature

Web search was exhausted, so everything below is from memory and unverified this session.

- **Twisted explicit formula.** Weil 1952, *Sur les formules explicites*: the criterion for all Größencharaktere, which is the block family, so it is classical. Connes 1999, Selecta: the adelic, all-characters trace formula.
- **Converse theorems.**
  - Weil 1967, Math. Ann. 168: GL(2) converse theorem.
  - JPSS 1979/83; Cogdell–Piatetski-Shapiro (IHES 1994, 1999): GL(n).
  - Conrey–Farmer, IMRN 1995: Euler product in place of twists.
  - Farmer–Wilson (Ramanujan J. ~2007): partial Euler product.
  - Booker, Mathematika 2019: without root numbers.
  - Booker–Krishnamurthy (~2013–2016).
- **Degree 1.** Kaczorowski–Perelli: degree-1 Selberg class.
- **Family averages.** Özlük–Snyder; Iwaniec–Luo–Sarnak (IHES 2000); Hughes–Rudnick; Katz–Sarnak.
- **E's zeros.** Potter–Titchmarsh 1935; Davenport–Heilbronn 1936.
- **Novelty.** None for the mechanism. The explicit barrier statement, the D-linearity correction, and the numerics are new to the project.

## 7. Odds

| Question | Estimate |
|---|---|
| This angle leads to RH | < 0.1% |
| Barrier entry 1 can be made kernel-checkable | ≈ 70% (T1 via root-number algebra; T3 is exact coefficient arithmetic) |
| The Hecke-eigen pivot is worth one experiment | 1–3% that it is interesting |


## Adversarial verdict

```json
{
 "angle": "converse: the twisted-FE family (block and averaged Weil forms over Dirichlet twists) as the global Euler-product x FE coupling. The proposer already declared it dead; this is the skeptic's audit.",
 "survives": false,
 "fatal_flaws": [
  "E is automorphic: E = 1/2(zeta_K + L(chi_-4)L(chi_5)) is the theta series of x^2+5y^2, a weight-1 form in M_1(Gamma_0(20), chi_-20). My own Gauss-sum code shows the root-number identity w(chi)w(chi chi_-20) = w(chi chi_-4)w(chi chi_5) holds, with matching Gamma sets, for all 62 primitive chi mod 3, 7, 9, 11, 13, 17, 19 (max error 2.1e-14). So every coprime twist of E has a functional equation (FE) with the correct dual. Any criterion built from twisted FEs therefore cannot separate zeta_K from E.",
  "The block form sum_chi Q_{L x chi}(f_chi) is block-diagonal. Its positivity is exactly the conjunction of the members' positivity, so it adds nothing beyond W_L(x); this is Weil 1952 for Groessencharacters. Separately, for E x chi_-3 it cannot be 'the trivial member fails first' by some mechanism: it is just a higher conductor.",
  "The averaged form with the same f for every chi keeps only n = 1 mod r on the prime side. For r > x it is pure arch plus pole, and the arch and pole data of E and zeta_K are identical, so the form is provably blind. For r = 3 it is POSITIVE for E at x = 45 (+0.345), where E alone is -0.655: the averaging hides the counterfeit.",
  "The Euler product enters nowhere nonlinearly. Twisting is linear (chi is completely multiplicative), and twisted FEs are linear conditions on the Hecke-stable space. This is dead by the linearity barrier."
 ],
 "linearity_or_classP_violation": "Yes. Every step is linear in the Dirichlet series: twisting, twisted FEs, and the character average. The argument goes through verbatim for E, because E satisfies the hypotheses of Weil's GL(2) converse theorem. The converse theorem outputs automorphy, not the Hecke-eigen property, and E is automorphic but not an eigenform. It fails multiplicativity already at a(6) = 2 while a(2)a(3) = 0.\n\nOn D, the proposer's 'correction' to the linearity barrier needs a nuance. For r = +-2 mod 5 I find W1 = -W2 exactly, with D = a L(chi4) + b L(chi4bar). So D x psi still satisfies AN FE, but its dual is the series a L(chi4 psibar) - b L(chi4bar psibar) rather than D x psibar. What fails is twist-compatibility of D's self-duality, which is what the converse theorem needs. D still inherits every linear identity of its two components.\n\nThe right refinement of the barrier:\n- The linear-identity barrier holds for both counterfeits.\n- The 'self-dual under all twists' test separates D (the weak counterfeit) but not E.\n- E is the strong counterfeit and should be the reference control in the barrier statement.",
 "counterfeit_check": "All code is my own, in .../scratchpad/hodge3/converse_skeptic/: rootnum.py, win.py, run1-3.py. win.py is an independent Hermitian window form: cos^2-tapered exponential basis, analytic transforms, digamma arch, -E'/E coefficients from lattice counting.\n\nSanity checks:\n- The E decomposition matches coefficientwise for n <= 3000.\n- zeta at x = 2 is positive (2.2e-3).\n\nE versus x_E ~ 19.82. The taper subspace delays detection, and the delay shrinks as K grows, consistent with 19.82 on the full class:\n- K = 8: E goes negative between x = 26 and 35.\n- K = 16: E is +1.3e-4 at x = 21 and -4.9e-4 at x = 22.\n- K = 24: E is +2.0e-3 at x = 20 and -2.6e-4 at x = 21.\n- zeta_K stays positive throughout.\n\nTwists (K = 16):\n- E x chi_-3 is positive at x = 22, 35, 70 (9.6e-2, 1.6e-2, 1.2e-4). The matching zeta_K x chi_-3 values are 0.32, 5.0e-2, 2.5e-4.\n- E x (order-6 chi mod 7) is 0.97 at x = 22 and 0.37 at x = 35.\n- The averaged form, r = 3: E is +0.668 at x = 35 and +0.345 at x = 45; E alone at x = 45 is -0.655.\n\nSo the counterfeit passes the family test wherever the family differs from E itself. The mechanism does not fail for E beyond 19.82 except through the trivial member. It is refuted as a separator.\n\nD: the twisted FE with dual D x psibar holds iff r = +-1 mod 5 (r = 4, 9, 11 pass; 3, 7, 8, 13 fail). The D-window threshold near 31 was not reproduced (float64 near-null, as the proposer also reported).",
 "numerics_reproduced": "Yes, independently, with different code and a different basis.\n\nReproduced:\n- Twisted-FE pattern: E passes all primitive twists; D passes iff r = +-1 mod 5.\n- E negative near x ~ 20-21, converging toward 19.82 as K grows; zeta_K positive.\n- E x chi_-3 and E x chi mod 7 positive through x = 35/70.\n- Averaged r = 3 form for E positive at x = 45: +0.345, matching the proposer's +0.34.\n- E alone at x = 45: -0.655, matching the proposer's figure.\n\nBlindness of the averaged form for r > x: verified structurally (only n = 1 survives the character sum, and arch and pole data coincide), not rerun numerically.\n\nNot reproduced: the D window threshold near 31 (float64 limits) and the E x chi_-3 far scan at x = 199.",
 "novelty": "None as a mechanism. The all-characters explicit formula and positivity criterion are Weil 1952 / Connes 1999. That converse theorems give automorphy and not the eigen property is standard (Weil 1967; JPSS; Cogdell-PS). Family 1-level density with restricted Fourier support is Ozluk-Snyder, Iwaniec-Luo-Sarnak, Hughes-Rudnick and Katz-Sarnak.\n\nWhat is new to the project:\n- The explicit 'converse-theorem barrier' with E as the witness.\n- The D nuance, which is really about twist-compatibility of self-duality.\n- The numerics.\n\nCaveat: my web-search budget was exhausted, so none of the citations (Conrey-Farmer IMRN 1995, Farmer-Wilson, Booker 2019, Booker-Krishnamurthy, Kaczorowski-Perelli) were re-verified online by me either. They are plausible from memory but unverified.",
 "what_is_real": "1. The CONVERSE-THEOREM BARRIER: no criterion built only from twisted FEs, or from twist-averaged window forms, can separate zeta_K from E. The algebraic proof via root numbers is already sketched in rootnum.py. It is kernel-formalizable at finite level, since it rests on Gauss-sum identities for characters of coprime conductor.\n\n2. The hierarchy of counterfeits:\n   - D is caught by twist-compatibility of the FE, a linear-in-coefficients condition once the dual is fixed to be the twist.\n   - E is caught only by the Hecke-eigen / multiplicativity condition, which is quadratic (a(6) = 2 but a(2)a(3) = 0).\n   - The project's barrier statements should therefore use E as the reference strong counterfeit.\n\n3. Conductor monotonicity of margins (twists behave like the genuine function) is an empirical observation. It is not a mechanism. E x chi generically has off-line zeros too, so its twisted forms must eventually go negative at larger x; the tests simply do not reach that.\n\nThe proposed pivot (a 'Hecke-eigen quadratic constraint coupled to the FE') is just class P / Selberg-class GRH restated. It is not yet a mechanism and needs a concrete positivity statement before it counts.",
 "next_step_if_survives": "It does not survive. The single most informative next step is to record the converse-theorem barrier in the barrier ledger, with E as the witness, as a finite, kernel-checkable lemma. The lemma: for all primitive chi mod r with (r, 20) = 1, w(chi)w(chi chi_-20) = w(chi chi_-4)w(chi chi_5), with matching parity sets. That formally closes off every twisted-FE and family-average route.\n\nThen, if the quadratic pivot is pursued, the first test is concrete. Take the wave-1 EFW Lane-2 Galerkin set-up (Euler shape + truncated FE) and add the Hecke relations a(m)a(n) = sum_{d | (m,n)} chi(d) a(mn/d^2) for n <= x as hard constraints. The question is whether the constrained minimum of the window form stays positive past x = 19.82 while E, which violates the relations at n = 6, is excluded."
}
```
