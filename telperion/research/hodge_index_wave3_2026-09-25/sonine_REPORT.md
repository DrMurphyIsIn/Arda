# Hodge index WAVE3: angle `sonine`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Wave 3, angle `sonine`: adelic Sonine / co-Poisson spaces

**Verdict: DEAD as a positivity mechanism.** The angle does leave two things: an exact dictionary, and a sharper, pole-free Local-Euler barrier. `conjecture1_proved = False`.

## 0. What I read

- `hodge/SYNTHESIS_WAVE1.md` in full. `hodge3/SYNTHESIS_WAVE2.md` does not exist.
- `frob/SYNTHESIS.md`.
- `cf/B/bcore.py`.
- The wave-1 arakelov/LEB scripts and the independent skeptic code `wf.py`.
- Connes–Consani arXiv:2006.13771, pp. 1–4 (PDF read directly).

## 1. The mechanism made exact

**Setup.**
- S is a finite set of places with ∞ ∈ S.
- A_S = ℝ × ∏_{p∈S} ℚ_p, and Γ_S is the group of S-units ±∏p^k.
- By the product formula, |q|_S = 1 for q ∈ Γ_S. So the self-dual Fourier transform F_S = ⊗_v F_v commutes with Γ_S and descends to X_S = A_S/Γ_S (Connes 1999).
- On the unramified, even sector (K_S = {±1}×∏ℤ_p^* invariant), Γ_S\A_S^*/K_S ≅ ℝ_+^* through the module. With the half-density normalization this gives H = L²(ℝ, du), u = log|x|_S.

**Proposition 1 (S-adelic Sonine space = Toeplitz kernel).**

(a) F_S = J ∘ M_{ρ_S}, where J is the reflection u ↦ −u and M_{ρ_S} is the Fourier multiplier (t dual to u)

  ρ_S(t) = ∏_{v∈S} ρ_v(½+it),

with ρ_v the Tate local gamma factor of the unramified vector. For example, ρ_p(s) = (1−p^{−s})/(1−p^{s−1}), and ρ_∞ is a ratio of Γ_ℝ factors; conductor and ramified primes contribute ε-phases p^{−a it}.

(b) Take the cutoff P_Λ = 1_{u ≤ log Λ} (it is Γ_S-invariant). The Sonine space

  Son_S(Λ) = ker P_Λ ∩ ker(F_S P_Λ F_S^*)

equals ker T_{Λ^{2it} ρ_S}. This is the kernel of the Toeplitz operator with that symbol on the Hardy space H²₊ = 𝓕L²(0,∞).

Proof sketch:
- φ ∈ ker P_1 means supp φ ⊂ (0,∞), i.e. φ̂ ∈ H²₊.
- F_Sφ vanishing on u < 0 means M_{ρ_S}φ is supported in u < 0, i.e. ρ_S φ̂ ∈ H²₋.
- Together these say exactly that P₊(ρ_S φ̂) = 0.

**The "tensor product over places" is a product of Toeplitz symbols.** The Euler product enters here and only here. Toeplitz kernels of products are not additive, so this is the one genuinely nonlinear object.

**Proposition 2 (Weil = phase derivative).**

  Σ_{v∈S} W_v(g∗g̃) = (1/2π) ∫ |ĝ(t)|² (−d/dt arg ρ_S(t)) dt, plus the log Λ cutoff term.

For example, arg ρ_p(½+it) = 2 Σ_k p^{−k/2} sin(kt log p)/k, whose derivative gives the prime-power terms. This is additive over places, hence linear in c.

For inner symbols ρ = Ī, Son = K_I is a model space. Its reproducing-kernel diagonal on ℝ is φ_I′/2π, so the Sonin trace equals the Weil form exactly and is again linear. The nonlinearity lives only in the non-inner part of ρ_S (the Riemann–Hilbert factorization ρ = Ī·h̄/h).

**Proposition 3 (the kill).**

(i) Tr(ϑ(g) Π_{Son_S} ϑ(g)*) ≥ 0 for every symbol, because it is the trace of a positive operator.

(ii) Hence any Connes–Consani-type inequality W_S(g∗g*) ≥ Tr(ϑ(g)Π_Sϑ(g)*) − c|ĝ(0)|² implies W_S ≥ 0 on the CC class {ĝ(±i/2) = 0, ĝ(0) = 0}.

(iii) Every object in the semilocal framework (H, F_S, P_Λ, ϑ, W_S, Π_S) is a function of the local symbols {ρ_v}_{v∈S} alone.

(iv) At finite S, the only Poisson summation available is the S-unit product formula. The global functional equation comes from Poisson summation over ℚ inside 𝔸_ℚ. There the global symbol ∏_v ρ_v = Λ(1−s)/Λ(s) ≡ 1: the Toeplitz kernel is trivial and all the information sits in the cokernel, i.e. the zeros. That is W itself, so it is circular.

(v) So the framework is equally valid for any datum with unitary local Tate symbols at the places in S, including pure Euler data that are not L-functions. If such a datum is Weil-negative on the CC class at window x, with S ⊇ {p < x}, then no argument internal to the S-adelic Sonine framework can prove CC-class positivity at x. T2 below exhibits such data from x ≈ 12–13.

## 2. Where the Euler product enters

Only through ρ_S = ∏ρ_v, which is nonlinear through Son_S = ker T_{ρ_S}. But the nonlinearity is local-data-only. It cannot see whether the local data at 3, 7, 11, 13 belong to a global L-function of conductor 20. By the rules of this wave, a mechanism that is nonlinear but not global is dead: it is exactly the wave-1 LEB situation.

## 3. Tests run

Scripts are in `scratchpad/hodge3/sonine/`. The main code is the bcore Galerkin (Neumann basis). It is cross-checked with the independent skeptic `wf.py` (smooth Chebyshev basis). λ values are Gram-normalized Rayleigh–Ritz upper bounds, so any negative value is a genuine negative witness.

**T1: semilocal ladder** (`ladder.py`)

Setup:
- Q_S = Pole + Arch − Σ_{n S-smooth} c(n) terms.
- S = {∞}, {∞,2}, {∞,2,3}, {∞,2,3,5}, all p < x.
- Data: ζ_K; E truncated to S-smooth n; the LEB witness (α₂ = −1, α₃ = β₃ = −1, α₅ = −1).

Results:
- **x = 6:** the LEB witness is −0.338 in the full class (odd sector, reproducing wave 1) but **+2.22 on the CC class**. Its wave-1 negativity is entirely the pole direction. In the odd sector the pole term is −2|F(i/2)|², a negative rank-one term, which is the hyperbolic block of the Hodge-index analogy.
- **ζ_K, S = {∞}, full class, odd sector:** −0.0255 at x = 12, −0.83 at x = 19, −1.38 at x = 25. Pole + archimedean alone is not positive. No local-to-global positivity from small S exists in the pole class.
- **Monotonicity in S does not hold.** The prime-term matrices P_n are indefinite, so adding or removing c ≥ 0 terms moves λ both ways.
- **Detecting E at 19.82: no S-truncation does it.** On the CC class, E_S with S = {∞,2,3,5} is −0.039 at x = 25 while E itself is +0.228 in the same sector. Truncating a counterfeit to S is not a meaningful control.

**T2: CC-class horizons** (`cc_scan.py`, `strict.py`, `indep14.py`)

Class A: CC class (ĝ(±i/2) = 0 and ĝ(0) = 0), where the Connes–Consani theorem lives.

| datum | x | N | λ_min |
|---|---|---|---|
| ζ_K | 20.5 | 32–40 | 1.47 |
| ζ_K | 23.5 | 32–40 | 1.26 |
| ζ_K | 28 | 24 | 1.00 |
| ζ_K | 36 | 16 | 0.83 |
| ζ_K | 45 | 16 | 0.11 |
| E | 22.5 | 40 | +0.235 |
| E | 23.5 | 40 | +0.0139 |
| E | 23.5 | 32 | +0.0196 |
| E | 24 | 24 | **−0.0123** |
| E | 28 | 24 | −0.155 |
| E, independent code | 24 | 14 | +0.24 |
| E, independent code | 28 | 14 | −0.08 |

So x_E^CC ∈ (23.5, 24]. On the pole-free class without the ĝ(0) condition: +0.0049 at x = 23.5 (N = 32), −0.143 at x = 28.

**Worst pure-local data on the CC class.** The Γ-factor, conductor 20 and pole are kept; only unramified primes are varied, using degree-2 unitary Satake data (e^{±iθ} pairs or inert).

| x | λ_min | local data |
|---|---|---|
| 12 | +0.282 | |
| 13 | **−0.0257** | {3:−1, 7:+1, 11:−1, 13:+1}, α = β |
| 14 | −0.557 | |
| 16 | −1.05 | |

(Values at N = 24.)

Independent code, witness {3:−, 7:+, 11:−, 13:−}: −0.128, −0.303, −0.406 at N = 10, 14, 18 for x = 14, and −0.989 at x = 16. ζ_K in the same code at x = 14 is +1.76, against +1.71 from bcore.

If the ramified factors at 2 and 5 are also varied, the horizon is x ∈ (11, 12): +0.211 at x = 11, −0.145 at x = 12 (N = 24).

Class B: full class (pole kept):
- E: +9.96e−4 at x = 19.5 and −2.83e−4 at x = 20.5 (N = 24), consistent with x_E ≈ 19.82.
- The pure-local horizon is ≈ 5.05 (wave 1).

**Reading.**
- On the class where the Sonin theorem applies, local purity fails at x ≈ 12–13 and E at x ≈ 23.6.
- In the pole class, local purity fails at ≈ 5 and E at 19.82.
- The LEB therefore survives the passage to the Sonin/CC class, with the same ordering, roughly doubled in x.
- E's pole-class horizon at 19.82 is pulled in from ≈ 23.6 by the pole/Schur block, consistent with the project's Lemma H.
- **Conductor slack.** Conductor enters as log(Q/20) × Gram, so the x = 14 witness needs Q ≥ 20·e^{0.557} ≈ 35 to become positive. Any pair of Dirichlet characters (χ₁ even, χ₂ odd) realizing that sign pattern at 3, 7, 11, 13 plausibly has conductor far above 35. This "EFW-lite" check was not run.

**T3: ζ itself** (`zeta_cc.py`)
- ζ is near-null on all classes from x ≈ 5: CC ≈ 1e−9 at x = 5, then float noise.
- ζ_K has O(1) CC margins up to x ≈ 36.
- Near-null behaviour is therefore not a pole-only effect for ζ. It tracks zero density against the Paley–Wiener type A/π (Landau sampling density). This is a heuristic explanation, not certified.

**D control.** Float64 noise (|λ| ~ 1e−15) at x = 22–40 on both the plain and CC classes. Unresolved, as in wave 1.

## 4. Literature

**Verified.**
- Connes–Consani, arXiv:2006.13771 (read directly). Theorem 1: for g supported in [2^{−1/2}, 2^{1/2}] with ĝ(i/2) = ĝ(0) = 0, W_∞(g∗g*) ≥ Tr(ϑ(g)Sϑ(g)*). Eq. (5) allows ĝ(0) ≠ 0 at the cost of −c|ĝ(0)|², with 13 < c < 17. The authors propose running this for {∞, 2, …, p} with support in (p^{−1}, p). Proposition 3 plus T2 shows that program cannot be closed by local structure past x ≈ 12. It needs a global input that the semilocal space does not contain.
- Burnol:
  - "Sur les espaces de Sonine associés par de Branges…", arXiv:math/0208121 (title verified).
  - "Entrelacement de co-Poisson", arXiv:math/0407443, Ann. Inst. Fourier 57 (2007) 525–602 (verified).
  - "On Fourier and Zeta(s)", arXiv:math/0112254, Forum Math. 16 (2004) (verified).

**From memory, unverified** (web-search budget exhausted):
- de Branges (1968), sections on Sonine spaces.
- Connes 1999 (Selecta).
- Makarov–Poltoratski, Toeplitz kernels and the uncertainty principle. Proposition 1 is likely known in substance; the S-adelic product-symbol form is probably folklore.

## 5. Odds and deliverables

**Odds.** Mechanism leads to RH: < 0.2%. The global version is circular: the global symbol is ≡ 1, so the content is the zeros.

**Deliverables.**
1. The dictionary: S-adelic Sonine space = ker T_{∏ρ_v}; semilocal Weil = −d arg ρ_S; Sonin trace ≥ 0.
2. **CC-class Local-Euler barrier.** Pure unitary local data with ζ_K's Γ-factor and conductor are Weil-negative on the Connes–Consani test class from x ≈ 13, with λ ≈ −0.56 at x = 14 and ≈ −1 at x = 16. Large margins at small N make this cheap to certify in Arb/Lean (about 60%). It refutes the Connes–Consani semilocal program as a local-to-global argument.
3. **Pole-block diagnosis.** E's 19.82 horizon and ζ_K's small full-class margins sit in the pole/Schur block. On the primitive (CC) class, E survives to about 23.6 and ζ_K has O(1) margin at conductor 20. A wave-4 Hodge-index attempt should split the problem literally: primitive class, then Schur scalar.
4. **Hand-off.** EFW-lite: minimal conductor of a global character pair realizing each local sign pattern, compared with Q_req(x). This is the finite shadow of the global FE coupling that the Sonine framework lacks.

## Adversarial verdict

```json
{
 "angle": "sonine (adelic Sonine / co-Poisson spaces, S-adelic Toeplitz-symbol dictionary). Adversarial skeptic review.",
 "survives": false,
 "fatal_flaws": [
  "There is no positivity mechanism. Proposition 3(i)-(ii) is a tautology: the trace of a positive operator is >= 0, and an inequality W_S >= Sonin trace - c|g^(0)|^2 then gives W_S >= 0 on the class where g^(0) = 0. The whole content sits in the assumed Connes-Consani-type inequality, and that inequality is proved only at the archimedean place.",
  "The semilocal program is circular on the window. With support in (1/x, x) and S containing every p <= x, sum_{v in S} W_v(h) equals the global Weil functional minus the pole terms. So semilocal positivity on the window is exactly the pole-free W(x), not a route to it.",
  "The Euler-product nonlinearity is trivial in the Sonine space (skeptic sharpening). Each finite-place symbol is rho_p = conj(h_p)/h_p with h_p(t) = 1 - p^{-1/2} p^{it}, an invertible outer function (bounded, and |h_p| >= 1 - p^{-1/2} > 0 on the half-plane). Hence ker T_{phi conj(H)/H} = H * ker T_phi. So Son_S(Lambda) = H_S * Son_inf(Lambda) under a bounded invertible multiplication. The finite primes change only the metric of the Sonine space, never its structure. The claimed 'nonlinear via Riemann-Hilbert factorization' content amounts to the conjugation by H_S alone.",
  "The Euler product enters only through local symbols. The proposer says so, and it triggers the wave-1 Local-Euler barrier: nonlinear but not global.",
  "An error in the proposer's own kill argument (claims (iii) and (v)). The literal S-adelic space X_S = A_S/Gamma_S does carry a global input: Gamma_S-invariance, i.e. S-unit reciprocity. In the GL1 setting, a sector character must satisfy prod_v chi_v(p) = 1 for each p in S. That forces the unramified values at S-primes to be those of a genuine Hecke (Dirichlet) character. In addition, a degree-2 datum with a pole must be isobaric zeta*L(chi), so alpha_p = 1. Therefore the pure-local witness {3:(-1,-1), 11:(-1,-1), ...} is NOT an object of the S-adelic framework. The x ~ 13 barrier refutes proofs that go only through the local symbols rho_v (the proposer's dictionary). It does not refute the Connes-Consani framework itself: inside it, the data are genuine Dirichlet L-functions, where positivity is GRH on the window, so the framework is equivalent to the problem rather than refuted by a counterfeit.",
  "Minor: 'global symbol == 1' is only formal. prod_p rho_p does not converge on Re s = 1/2, so the S -> all limit is not a Toeplitz operator with symbol 1. The functional equation acts as a regularization of a divergent product."
 ],
 "linearity_or_classP_violation": "- The Weil form is additive over places (Proposition 2, the phase derivative), hence linear in c.\n- The Sonine space depends on the local symbols multiplicatively, but I showed the finite-prime factors act by an invertible outer multiplier. So the nonlinearity is a change of metric, not new structure.\n- Every ingredient the proposer uses is a function of the local data {rho_v}. By the class-P / fooling lemma and the Local-Euler barrier, any argument through these ingredients goes through verbatim for any unitary local data, and in particular for the pure-local counterfeits. My own code confirms these are CC-negative from x ~ 13.\n- E and D have no product symbol, so they are excluded by definition, not by any positivity step. Excluding a counterfeit by definition is not a counterfeit control.\n- The one genuinely global input in the true S-adelic setup is Gamma_S reciprocity. The proposal discards it when passing to the log-module sector, and it does not supply the functional equation in any case.",
 "counterfeit_check": "All runs use my own independent code: scratchpad/hodge3/sonine_skeptic/sk.py.\n- Basis: (1-v^2)^2 P_j(v).\n- The arch term is a direct frequency-side quadrature with digamma, converged in the frequency cutoff Tmax to ~1e-7.\n- E coefficients come from direct lattice-point counting, not the divisor formula.\n- All numbers below are Rayleigh-Ritz upper bounds, so a negative value is a genuine witness.\n\nFull class, E (pole kept):\n- Even sector: +2.09e-3 at x = 19.5 (N=16); -2.42e-4 at x = 20.5 (N=22).\n- This matches the claimed x_E ~ 19.82 and the proposer's -2.83e-4 at x = 20.5.\n- Odd sector at x = 20.5 stays positive.\n\nCC class (g^(0) = g^(\u00b1i/2) = 0), E:\n- Even sector: +4.5e-2 (N=28) and +1.87e-2 (N=36) at x = 23.5; -1.80e-2 (N=28) and -3.25e-2 (N=36) at x = 24.\n- This confirms x_E^CC in (23.5, 24].\n- Pole-free class without the g^(0) condition: +4.35e-3 at x = 23.5 and -5.6e-2 at x = 24 (N=36).\n\nzeta_K:\n- CC margins are O(1): about 2.2 at x = 11-14, 1.5/1.09 (even/odd) at x = 20.5, and >= 0.9 at x = 24. Confirmed.\n\nPure-local witness {3:-, 7:+, 11:-, 13:+} (alpha = beta), CC odd sector:\n- x = 13: +0.026 (N=20), -0.0054 (N=30), -0.0217 (N=40). This converges toward the claimed -0.0257 (N=24 in their code).\n- x = 14: -0.21. At x = 16: -0.37.\n\nExhaustive search over {alpha=beta=\u00b11, inert} at the unramified primes:\n- Positive up to x = 12.5 (+0.26).\n- -0.022 at x = 13, -0.49 at x = 14, -1.03 at x = 16.\n- The horizon over this discrete class is \u2248 13, consistent with the claimed (12, 13] for the strict class. A continuous-theta search could push it slightly lower.\n\nDiscrepancy: my first run had a bug. Its odd-sector constraint used Im f^(i/2), which is identically 0 for real f. With it, the witness appeared negative at x = 11. After the fix, the \u2248 13 horizon holds. The proposer's numbers survive.\n\nD: not attempted. Float64 near-null, as in every prior wave; the x_D ~ 31 prediction remains unverified by anyone.",
 "numerics_reproduced": "Yes, with independent code (different basis and quadrature scheme, E from lattice counts).\n- E full-class threshold in (19.5, 20.5]: reproduced.\n- E CC-class threshold in (23.5, 24]: reproduced.\n- zeta_K O(1) CC margins: reproduced.\n- Pure-local CC barrier from x \u2248 13: reproduced, -0.022 at x = 13 (N=40) and -0.49 at x = 14 (N=20).\n- Magnitudes at x = 14 are somewhat smaller than the claimed -0.557, a basis/N effect. Signs and horizons agree.\n- D: not reproduced; float noise.\n\nScripts: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/sonine_skeptic/{sk.py, t0.py, t1.py, t2.py, t3.py}. No processes were left running.",
 "novelty": "Low.\n- Proposition 1 (Sonine space = Toeplitz kernel, Fourier = reflection composed with the Tate gamma-factor multiplier) is standard in substance: Burnol's co-Poisson work, de Branges, Makarov-Poltoratski Toeplitz kernels.\n- Proposition 3 is elementary.\n- Connes-Consani arXiv:2006.13771 is verified (title, authors and abstract fetched, Jun 2020). The abstract itself says positivity comes from the compressed scaling trace and that the method extends to the semi-local case 'where Weil positivity would imply RH'. The proposer's claim that the semilocal version equals pole-free W(x) on the window is thus consistent with the authors' framing.\n- Burnol arXiv ids were not re-verified by me; my web-search budget was exhausted, and the proposer verified three of them.\n- Possibly new, as a numerical fact: the CC-class local-symbol barrier at x \u2248 13 against E's CC horizon of \u2248 23.6. I would re-scope its meaning, since it rules out symbol-only arguments, not the S-adelic framework.\n- My outer-multiplier observation Son_S = H_S * Son_inf is elementary and likely implicit in Burnol.",
 "what_is_real": "1. The exact dictionary.\n   - The Tate local symbols are rho_p = conj(h_p)/h_p with h_p invertible outer.\n   - The S-adelic Sonine space is H_S * (archimedean Sonine space). The finite primes are an invertible outer change of metric (skeptic sharpening).\n   - The semilocal Weil form is the phase derivative of rho_S.\n   - Consequence: the Sonine/co-Poisson structure contributes no arithmetic information beyond the local symbols.\n2. The certified-candidate barrier, reproduced independently. On the Connes-Consani class, with zeta_K's Gamma factor, conductor 20 and ramified factors fixed, unitary local Satake data at the unramified primes are Weil-negative from x \u2248 13: {3:-, 7:+, 11:-} gives -0.022 at x = 13, and -0.49 at x = 14. zeta_K keeps margin ~2. Correct scope: this refutes every argument that factors through the local symbols alone. It does NOT refute the Connes-Consani framework, whose Gamma_S reciprocity excludes these data.\n3. Pole-block diagnosis, reproduced. E's full-class horizon 19.82 moves to \u2248 23.6-24 on the pole-free/CC class, and zeta_K's small full-class margins (~1e-3) become O(1) there. So the pole/Schur scalar drives E's early failure. This is real, and it supports a literal Hodge-index split: primitive class plus a pole block.",
 "next_step_if_survives": "The proposal does not survive. The most informative next step is the reciprocity-constrained version of the barrier, i.e. EFW-lite done properly. Restrict the local data to those allowed by Gamma_S reciprocity: isobaric zeta * L(chi) with chi a Dirichlet character, and ask whether pole-free CC-class positivity at x = 13-24 can fail for any genuine data. Every such chi should give positivity, since it is GRH on a window. The real question is whether the conductor needed to realize the negative local sign patterns ({3:-, 7:+, 11:-, 13:-} etc.) grows faster than Q_req(x) = 20*exp(|lambda|). If min conductor(x) >> Q_req(x) with a computable gap, that is the first finite-scale quantity where a global input (reciprocity) visibly outruns local purity. Also Arb-certify the x = 14 CC witness (-0.49), since it has a large margin at small N."
}
```
