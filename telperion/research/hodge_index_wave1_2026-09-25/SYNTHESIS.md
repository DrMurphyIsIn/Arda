# Hodge index for Spec ℤ: synthesis of five angles (arakelov, squareroot, amplify, flow, reflection)

**Bottom line.** No mechanism survived. None of the five gives a reason for positivity at all scales. What they do give is a set of sharp barriers. Together these barriers say where the missing Hodge index has to live: in a coupling of the Euler product to the functional equation across all primes at once. No known arithmetic surface has an intersection form that provides that. `conjecture1_proved = False`.

## 1. What died, and why

- **arakelov (Hecke Castelnuovo–Severi).** On the X_0(N) mod p reduction, Eichler–Shimura plus Castelnuovo–Severi gives *local* purity (Ramanujan). It does not give global purity. Local purity with the Γ-factor, conductor and pole held fixed fails to imply W(x) beyond x_P ≈ 5.05, using ζ_K data. The explicit negative witness is α₂ = −1, α₃ = β₃ = −1, α₅ = −1, with λ_min ≤ −0.29 at x = 6. An independent run reproduced this. The mechanism dies long before x_E ≈ 19.82.
- **squareroot (Bochner / log-cosh).** For ζ we have u = 0, so the only square root is the zero side, which is circular. The t\*(x) "prediction" is a tautology: the path is affine in t, so any positive-definite base point crosses t = 1 exactly at x_E.
- **amplify (convolution / tensor powers).** Theorem A is true, but it only restates RH on a thin cone of test functions. The measured amplification deficit per power, about ½ log x, is exactly the gap between the trivial bound and square-root cancellation. Towers act additively: Q_{ζ_K} = Q_ζ + Q_{L(χ)}.
- **flow (Krein / de Branges scale flow).** Monotonicity, continuity and the parity slope-jump rule all hold for every moment sequence, so the flow cannot tell ζ from a counterfeit. The structural core is already published by Suzuki (arXiv:2606.09096, abstract verified). E fails between x = 16 and 21, a stretch where E has no atom at all.
- **reflection (ferromagnet / Lee–Yang / Bost–Connes).** E has c_E(n) ≥ 0 for every n < 36 and is still Weil-negative from 19.82; D has negative couplings from n = 3 on and stays positive to about 31. Sign-ferromagnetism is therefore neither sufficient nor necessary. Lee–Yang and Bost–Connes stop at σ > 1 (the β = 1 transition). The minimizer-sign conjecture T3 is refuted by ζ_{Q(√−163)}: it has an Euler product, yet its minimizer has 2 sign changes at x = 8 through 80, while all its λ are positive.

## 2. Survivors

There are none as mechanisms. Ranked by (value if true) × (tractability), these are the true statements left over.

| Rank | Statement | Status | Gap | RH in disguise? |
|---|---|---|---|---|
| 1 | **Local-Euler barrier (LEB).** With Γ_R(s)Γ_R(s+1), conductor 20 and the pole fixed, some locally pure Euler datum is Weil-negative at x = 6. The same holds for the purity box at x ∈ (6, 7) and for the Euler-shaped adversary at x ∈ (7, 8). ζ_K itself stays positive to x ≥ 26. | Proved numerically twice with independent code. Rayleigh quotients are upper bounds, so each negative value is a genuine negative witness. | Needs Arb/Lean certification of one Gram vector. | No. It is a theorem-shaped barrier. |
| 2 | **Sign barrier (SB).** c_E(n) ≥ 0 for all n < 36, and λ_min(Q_E, x = 22) < 0. So no argument that uses only coupling sign plus FE and growth proves W(x). | Reproduced independently: first negative coefficient c_E(36) = −7.167; x = 22 gives −5.4e−4. | Arb certificate. | No. |
| 3 | **Theorem A (cone criterion).** RH for L holds iff s_k(f) = W((f^{\*k})\*(f^{\*k})~) ≥ 0 for every Lipschitz f supported in a fixed window x and every k. It holds for any L with FE and a Hadamard product. | Proof checked. Two fixes are needed: a generic phase g₀, and a mean-square almost-periodicity argument for ties. | Lean formalization. | Yes, it is an equivalence. |
| 4 | **Weight identity.** c_E = ½(c_{ζ_K} + c_{L_G}) + coeff[−d/ds log cosh u], where u = ½ log(ζ_K/L_G) is supported on the non-principal-class primes. There is an analogous cos identity for D. | Verified to 1e−30. | Decidable coefficient arithmetic. | No. It is anatomy, not positivity. |
| 5 | **Markov form.** Q − Pole is a Beurling–Deny Dirichlet form when c ≥ 0 on the window, so its ground state is positive. Even-sector W(x) is then equivalent to ind(Q₀) = 1 plus one Schur scalar (the project's Lemma H). | Elementary. | None. | No, but E already fails through the Schur scalar alone while still at index 1. |

**Combined meta-result, worth stating.** Every input tested fails to separate ζ_K from E at x ≈ 19.82:

- linear-in-c inputs (flow, Poisson/Voronoi): fooled by linearity;
- sign of c(n): SB;
- local Euler shape plus purity: LEB, which fails already at x ≈ 5 to 8, before E does;
- zero-powering: the amplification deficit.

Only the full conjunction survives: Euler product coupled globally to the functional equation, i.e. class P. At these scales the positivity of ζ_K comes from *global FE balance*. The Euler product only provides the rigidity that pins the data to ζ_K.

## 3. Counterfeit-sensitive criteria

**What is available.** Any RH-equivalent is trivially "sensitive" to E and D, because they have off-line zeros. Theorem A is sensitive from *every* base window, however small. Its certified witnesses are E at (x, k) = (19, 3), (12, 4), (8, 5) and D at (31, 3), (8, 6). But the sensitivity comes from zeros, not from the Euler product, so it is not the object we want.

**The one criterion here that uses multiplicativity by construction** is stated as a precise open conjecture. Nothing tested it.

> **Conjecture EFW (Euler-FE window rigidity).** Let 𝒫_x(Γ, q, pole) be the set of coefficient sequences c(n), n ≤ x, that satisfy all three of the following:
> (i) Euler shape: c(p^k) = log p · Σ α_{p,i}^k with |α_{p,i}| = 1, and c(n) = 0 off prime powers;
> (ii) the Guinand–Weil identity for every test function supported in the window, but with its arithmetic side truncated at x;
> (iii) the fixed Γ-factor, conductor and pole.
> Define μ(x) = inf over 𝒫_x of λ_min(Q_x).
> Conjecture: μ(x) ≥ 0 for all x ≤ X(q), where X(q) → ∞.

This criterion is nonlinear through (i) and global through (ii). LEB shows that dropping (ii) makes μ(x) < 0 at x ≈ 5. E is excluded by (i) at n = 4 and n = 6.

- **If μ(x) stays positive through 19.82 at conductor 20**, EFW is the first object that couples the two halves of class P at finite scale.
- **If μ(x) goes negative**, the result is a strictly stronger barrier: even Euler shape plus FE plus Ramanujan does not force W(x) at finite x. The proof would then need infinitely many constraints, i.e. the full class-P uniqueness.

Either outcome is informative.

## 4. Build lanes

**Lane 1: certified barrier ledger (kernel-checkable, low risk).**

- Arb + Lean certificates for:
  - (a) the LEB witness at x = 6, as a rational Gram/Rayleigh check;
  - (b) SB: c_E ≥ 0 for n < 36 (decidable), plus λ_min(Q_E, 22) < 0 through the existing FWindow;
  - (c) the log-cosh weight identity (decidable);
  - (d) one Theorem A witness, E at (x = 8, k = 5), which needs n ≤ 32768.
- Resolve the D control in Arb (dps ≥ 40) at x ∈ {28, 31, 35}. All five teams hit float64 noise (about 1e−14) for D beyond x ≈ 20, so the D horizon near 31 is still *unverified*.
- File everything as negative controls, next to the linearity and class-P barriers.

**Lane 2: the EFW experiment, followed by the Suzuki map.**

- Solve for μ(x) over x ∈ [5, 25] at conductor 20.
  - Parametrize the Satake angles.
  - Impose (ii) as linear constraints, using a basis of test functions supported outside the window.
  - Minimize λ_min by multistart, with an exact Galerkin check on each candidate.
  - Controls: ζ_K must be feasible and positive. E must be infeasible. Compare against the unconstrained LEB horizon of about 5.
- In parallel, read Suzuki arXiv:2606.09096 in full. Check whether his a → ∞ screw-function conjecture carries any structure that is nonlinear in c. If it does, EFW should be phrased in his operators.

## 5. Calibrated verdict

| Question | Estimate |
|---|---|
| Any of the five angles leads to RH | < 0.5% combined |
| EFW stays positive through 19.82 at conductor 20 | ≈ 20–30% |
| If it does: extends to a provable statement | < 2% |
| Lane 1 kernel-certified within weeks | ≈ 60–70% |

The EFW odds are low because the near-null saturation of ζ (λ_min ~ 1e−16 at x ≥ 5) suggests that finite truncations of the functional equation leave slack that an adversary can use.

What Lane 1 delivers is a certified map of which inputs cannot work: local purity, coupling signs, linear summation formulas, and powering zeros. That is the negative half of a Hodge index theorem for Spec ℤ. The positive half would be an intersection form on some "Spec ℤ × Spec ℤ" whose index theorem reads the functional equation and the Euler product together. Nothing here constructs that form, and nothing found in this run suggests how to.

Web search was exhausted in this run, so all citations except Suzuki arXiv:2606.09096 (abstract checked) are from memory and unverified. Scripts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/`.