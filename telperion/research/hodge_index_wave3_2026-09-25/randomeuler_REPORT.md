# Hodge index WAVE3: angle `randomeuler`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Wave 3, angle randomeuler: is Weil positivity typical for random Euler products?

**Verdict: DEAD as a positivity mechanism.** Positivity is *atypical*: P(W(x)) → 0. True L-functions are not typical members of the random ensemble. They sit on the *boundary* of the positivity set and become extreme outliers as x grows. The run also produced one exact identity, a three-way growth split and a GRH-consistency ledger, all useful as barriers and diagnostics. conjecture1_proved = False.

Scripts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/randomeuler/`:
- `recore.py`: the core; wraps bcore read-only.
- `r1_cube.py`: exhaustive cube.
- `r2_true.py`: true fields.
- `r3_mc.py`: Monte Carlo.
- `r4_place.py`: placement of true L-functions and E.
- `r5_deg1.py`: D control.
- `r6_dmin.py`: GRH-consistency ledger.
- `r7_large.py`: large x.
- `r8_flip.py`: flips.

All runs were single-process; nothing is left running.

## 0. Setup and validation

The form is Q_x(c) = Pole + Arch − Σ_{n≤x} c(n) n^{-1/2} P_n, on the Neumann cos/sin sector basis with N modes, taking the minimum over both parities. P_n is computed by 400-point Gauss–Legendre quadrature.

Validation:
- The comb matches bcore to 2e-14.
- It reproduces λ_ZK(20) = 4.606e-3, λ_E(20.5) = −4.16e-4 and λ_D(8) = 7.41e-6, as in the wave-1 logs.
- Convergence from N=48 to 64 to 80: medians agree to 1e-3, and the lower tail (the part that decides positivity) is converged. The upper tail at x ≥ 120 is not.

## 1. Exact identity: the conductor is a scalar shift

Arch contains gram·(Σ c0), with c0 = log(q/π) in the Γ_R(s+1) family. Hence

**Q_x(c; q) = Q_x(c; 1) + (log q)·‖f‖²**, verified to 2.2e-15.

Define the **effective log-conductor** ℓ(c,x) := −λ_min Q_x(c; 1). Then:
- **W(x) ⟺ ℓ(c,x) ≤ log q.**
- ℓ is nondecreasing in x, because the test classes are nested.
- ℓ is exactly a Mestre (1986) / Odlyzko–Poitou–Serre explicit-formula lower bound for the conductor, computed from the first x coefficients.

So the Weil criterion reads: *RH ⟺ the explicit-formula conductor bound never overshoots the true conductor.* It is also a windowed version of Lagarias's criterion Re ξ'/ξ > 0 on Re s > 1/2.

## 2. The ensembles

**Degree 2 (main ensemble).** The datum is ζ(s)·L(s,ε) with ε_p = ±1 i.i.d.:
- c(p^k) = log p·(1 + ε_p^k);
- Γ_R(s)Γ_R(s+1), pole at s = 1;
- ζ_K for K = Q(√−5) is one vertex, ε = χ_{−20}.

This is the right model: it is a real, degree-2 Euler product with a genuine pole, and it is the "random quadratic character".

**Degree 1 (control for D).** c(p^k) = log p·ε_p^k with Γ_R(s+1) and no pole.

**E and D** are placed in the same ℓ coordinates.

## 3. Results

### 3.1 Exhaustive cube at conductor 20 (ramified p = 2, 5 fixed as in ζ_K)

| x | vertices | P(pos) | λ_ZK | ZK's rank from the bottom among positive vertices | max λ | λ(mean datum) |
|---|---|---|---|---|---|---|
| 12 | 8 | 1.000 | 1.6e-1 | – | 1.08 | 1.15 |
| 14 | 16 | 0.875 | 7.4e-2 | 2nd | 1.07 | 1.09 |
| 16 | 16 | 0.812 | 3.4e-2 | **1st** | 1.06 | 1.03 |
| 20 | 64 | 0.688 | 4.6e-3 | 2nd | 1.06 | 0.96 |
| 22 | 64 | 0.656 | 1.7e-3 | **1st** | 1.04 | 0.92 |
| 25 | 128 | 0.578 | 3.9e-4 | **1st** | 1.04 | 0.88 |

ζ_K hugs the boundary. The other positive vertices have λ = O(0.1–1).

Two-sided rigidity at x = 25: flipping ε_p at p = 3, 7, 11, 13, 17 or 19 sends λ negative, in both directions (for example ε_3: +→− gives −0.109, and ε_11: −→+ gives −0.47). Only ε_23 survives (+8.1e-4). The reason is that 23 sits at the window edge.

### 3.2 Monte Carlo over all primes: ℓ quantiles

| x | 5% | median | 95% | P(pos at q=20) | P(pos at q=163) | ZK's quantile | Q(√−163)'s quantile | E's quantile | ℓ(mean datum) |
|---|---|---|---|---|---|---|---|---|---|
| 10 | 1.75 | 2.33 | 4.06 | 0.83 | 1.00 | 0.64 | 0.26 | 0.58 | 2.03 |
| 20 | 2.29 | 3.11 | 4.97 | 0.45 | 0.95 | 0.45 | 0.38 | 0.45 | 2.42 |
| 40 | 2.78 | 3.82 | 6.12 | 0.108 | 0.85 | 0.108 | 0.67 | 0.53 | 2.80 |
| 60 | 3.13 | 4.19 | 6.58 | 0.031 | 0.77 | 0.031 | 0.63 | 0.76 | 3.01 |
| 120 | 3.80 | 5.06 | 7.99 | 0.0007 | 0.51 | 0.0007 | 0.48 | 0.87 | 3.37 |
| 200 | 4.30 | 5.62 | 8.47 | 0.0000 | – | 0.0000 | – | 0.96 | 3.64 |

(The q=163 and Q(√−163) columns come from the x ≤ 120 run; they were not computed at x = 200.)

What the table shows:
- **Random growth.** The median ℓ ≈ 1.1 log x − 0.2, so the effective conductor of a random Euler product is about x. Heuristically, the prime sum Σ ε_p log p p^{−1/2−it} has standard deviation of order log x at the window's resolution.
- **Mean datum.** ζ(s)ζ(2s)^{1/2} has ℓ = 0.52 log x + 0.99, which matches the predicted slope of ½. That slope comes from the half-order centre pole of ζ(2s)^{1/2}, which enters as −½|F(0)|² with |F(0)|² ≤ log x·‖f‖². By concavity, E[λ] ≤ λ(E Q), which is negative at q = 20 for x ≳ 59.
  - This is the Weil-form shadow of the support-2 barrier for the quadratic family: the family-averaged form is positive only for x ≲ D²e^{−2}. The Özlük–Snyder / Katz–Sarnak link is from memory.

### 3.3 True imaginary-quadratic fields

Margin log|d| − ℓ(c_d, x):

| d | x=5 | x=10 | x=20 | x=30 | x=50 |
|---|---|---|---|---|---|
| −3 | 3.8e-5 | 3e-10 | float noise | – | – |
| −4 | 6.4e-4 | 7.9e-8 | 1.8e-14 | – | – |
| −7 | 6.5e-2 | 7.3e-5 | 2.1e-9 | 3.1e-13 | – |
| −20 | 1.08 | 0.37 | 4.6e-3 | 2.2e-5 | 1.4e-8 |
| −163 | 3.58 | 3.06 | 2.23 | 1.48 | 0.54 |

All 13 discriminants tested (−3 to −163) have margin ≥ 0 at every x, decreasing monotonically to 0. The boundary law ℓ ↑ log q is the known near-null phenomenon of Connes–Consani (arXiv:2106.01715).

### 3.4 GRH-consistency ledger

Every ±1 vertex on primes ≤ x is realized by some χ_d, where d < 0 is a fundamental discriminant with d ≡ 1 (mod 4) and d coprime to the primes ≤ x. GRH for χ_d implies ℓ(ε,x) ≤ log|d_min(ε)|.

| x | vertices | realized | violations | min slack | median slack | corr(ℓ, log d_min) |
|---|---|---|---|---|---|---|
| 25 | 512 | all (m < 2e6) | **0** | 0.017 | 4.7 | 0.00 |
| 40 | 4096 | all (m < 3e7) | **0** | 0.007 | 6.4 | 0.00 |

The vertices with the smallest d are tight, e.g. d = −43: ℓ = 3.749 vs log 43 = 3.761; d = −31: 3.417 vs 3.434. So the window form "sees" the conductor only for the arithmetic realization with small conductor. For a generic vertex, ℓ ~ log x reflects the resolution of the window, not log d_min ~ π(x) log 2.

### 3.5 Counterfeits

**E** (conductor 20):

| x | ℓ_E | margin vs log 20 |
|---|---|---|
| 5 | 1.51 | +1.48 |
| 10 | 2.48 | +0.52 |
| 15 | 2.92 | +0.075 |
| 20 | 2.99586 | **−1.30e-4** |
| 25 | 3.146 | −0.15 |
| 50 | 4.31 | −1.31 |
| 120 | 6.71 | – |
| 200 | 8.64 | – |

- This reproduces x_E ≈ 19.8.
- After death, ℓ_E grows like a power of x, roughly a + b·x^{0.433}, where 0.433 is the off-line displacement β − ½ of E's zero at 0.933 + 15.67i. For comparison, random growth is about log x.
- E's quantile goes 0.45 → 0.96, so E is supra-random, not typical.

**D** (degree-1 odd, conductor 5):
- The random degree-1 ensemble has P(ℓ ≤ log 5) = 0 from x = 8 on; its median is 2.34 at x = 10 and 3.59 at x = 31.
- D has ℓ = log 5 to within 1e-14 at every x from 8 to 40. It is an extreme outlier and looks arithmetic.
- D's failure near 31 is **not resolved**: at N = 48 the top Galerkin frequency is about 83, below the height 85.7 of its off-line zero, and float64 is at its noise floor anyway. This matches wave 1.

## 4. What died, and the lessons

1. **Typicality is dead.** P(W(x)) → 0 for random Euler products, even though they are a.s. zero-free in σ > ½ (Bohr–Jessen/Bagchi). This is a **Denjoy–Weil split**: zero-freeness of an Euler product does not imply Weil positivity. The FE is what converts zero-freeness into positivity. So any "derandomize via the FE" route reduces to Denjoy: random-like prime sums imply GRH, which is exactly as hard as RH.
2. **Three-way split of ℓ growth**, a diagnostic for counterfeits:
   - arithmetic L (FE, zeros on the line): bounded, ℓ ↑ log q;
   - random Euler: ℓ ≍ log x;
   - FE counterfeit with an off-line zero of displacement δ: ℓ grows like x^δ.
3. **The "counterfeits are typical" law is REFUTED.**
   - For E it predicts death where the random median crosses log 20, x ≈ 18.4, against the actual 19.82.
   - D is not typical at all; it is an extreme outlier from x = 8.
   - A counterfeit's death is set by the height and displacement of its off-line zero, not by statistics.
4. **Random-Euler barrier (REB), extending LEB.** Euler shape, Ramanujan purity, the pole, the Γ-factor and a.s. zero-freeness together still give P(W(x)) → 0. The coupling to the FE has to be *exact*: ζ_K is two-sidedly rigid in the Hamming cube at x = 25.

## 5. Theorem-shaped by-products

- **(T1)** Q_x(c;q) = Q_x(c;1) + log q·‖f‖². Exact, and ready for Lean now.
- **(C1)** Boundary conjecture: sup_x ℓ(c_L, x) = log q_L for every L in class P.
  - The ≤ direction is GRH.
  - The ≥ direction is the near-null phenomenon. It should be provable unconditionally from the density of zeros vs Paley–Wiener approximation, in the manner of Connes–Consani prolate functions.
  - If proved, C1 says the conductor is *determined* by Weil positivity: "the conductor is the Weil-positivity threshold". That is a clean, Hodge-flavoured statement: over function fields the genus plays the role of log q in the Oesterlé/Ihara explicit-formula bounds. **But it is not a proof of positivity.**
- **(L1)** A certified ledger: 0 GRH-consistency violations over 4608 vertices, plus E's ℓ crossing at x = 20 (margin −1.3e-4, which needs Arb).

## 6. Literature

- **Verified (WebFetch):**
  - Harper, arXiv:1703.06654;
  - Connes–Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715 (tiny eigenvalues of the windowed Weil form approximate the zeros; this is the boundary law);
  - Connes–Consani–Moscovici, arXiv:2310.18423.
- **From memory, UNVERIFIED** (the WebSearch budget was exhausted):
  - Mestre, Compositio Math. 58 (1986);
  - Odlyzko, Poitou and Serre discriminant bounds;
  - Lagarias, Acta Arith. 89 (1999);
  - Bagchi 1981 and Bohr–Jessen;
  - Denjoy 1931;
  - Özlük–Snyder and Katz–Sarnak.
- I know of no prior computation of Weil-form positivity *statistics* for random Euler products. The ingredients are classical, so the novelty is modest.

## 7. Odds

| Question | Estimate |
|---|---|
| Typicality or probabilistic mechanism | ~0% (refuted) |
| Derandomization leading to RH | < 0.5% |
| C1 (≥ direction) provable unconditionally | ~60% |
| C1 useful toward RH | < 1% |
| T1 and L1 certified within days | ~85% |

**Recommendation for wave 4:** stop looking for positivity among statistical properties of the prime data. The exact FE coupling is the only thing that pins ℓ. The object to construct is a form whose index theorem reads "ℓ ≤ log q". Over function fields that is the Hodge index theorem with 2g − 2 = deg K on C × C.

## Adversarial verdict

```json
{
 "angle": "randomeuler (skeptic): is Weil positivity typical for random Euler products?",
 "survives": false,
 "fatal_flaws": [
  "The proposal already declares itself dead, and the refutation holds up: P(W(x)) -> 0 for random +-1 Euler products at fixed q, which I reproduced. It is a weak test, though. Every +-1 vertex on primes <= x is a real character chi_d with |d| roughly exp(pi(x) log 2). Under GRH it is Weil-positive at its own conductor and not at q = 20. So P(pos at fixed q) -> 0 is exactly what GRH plus counting predicts, and the typicality hypothesis was never posed in a form the ensemble could confirm.",
  "The Monte Carlo model is misspecified. It draws eps_2 and eps_5 at random while fixing q = 20, but ramified primes should have eps = 0. With 2 and 5 held at 0, P(pos) moves a lot: 0.657 vs 0.410 at x=20, 0.282 vs 0.102 at x=40, 0.113 vs 0.022 at x=60, 0.007 vs 0.000 at x=120 (N=48, 400 samples). The median ell also drops by about 0.5 (2.67 vs 3.16 at x=20). The qualitative decay to 0 survives. The quantitative claims do not, including the 'median crosses log 20 at x ~ 18.4' prediction for E.",
  "T1 is not a finding. Q_x(c;q) = Q_x(c;1) + log q * ||f||^2 is the conductor term of the explicit formula, log q * g(0) with g = f*f~ and g(0) = ||f||^2. 'W(x) <=> ell <= log q' is Weil's criterion restated. 'ell = Mestre bound' is the standard GRH-conditional Mestre/Odlyzko explicit-formula bound with a positive-definite test function.",
  "C1 (sup_x ell = log q) is GRH exactly in the <= direction. The >= direction is easy and unconditional: every zero has |Re gamma| >= gamma_1 > 0 and |Im gamma| <= 1/2. So a Paley-Wiener f whose transform is concentrated in |xi| < gamma_1/2, with f^(+-i/2) forced to 0 by one linear constraint, has leakage of order e^{-cA}, and lambda_min -> 0. The 60% odds are miscalibrated (it is roughly 95% and routine). C1 therefore adds nothing beyond Weil's criterion.",
  "The 'Random-Euler barrier' is mis-framed. The random vertices are genuine Euler products with a functional equation, at conductor |d_min|, not q. The proposal's own ledger shows 0 GRH-consistency violations over 4608 vertices. What the ensemble shows is 'wrong declared conductor => not positive'. It does not show 'Euler product + purity + zero-freeness is insufficient'. It adds nothing to wave 1's Local-Euler barrier (LEB) or the class-P conclusion."
 ],
 "linearity_or_classP_violation": "No positivity mechanism is proposed, so no step actually has to separate zeta_K from E; E and D enter only as placements of the diagnostic ell. The ensemble does use the Euler product nonlinearly (c(p^k) = log p (1 + eps_p^k)). But conditioning on the functional equation at a fixed conductor collapses the ensemble to the genuine characters, which by the converse theorem are class P. So the random element vanishes exactly where it would have to do work: 'derandomize via FE' is class P plus Weil's criterion, with nothing probabilistic left. As a mechanism for W(x) it would need GRH-level input (Denjoy), so it is circular.",
 "counterfeit_check": "Reproduced with my own code, which builds the comb from a closed-form translation integral rather than the proposal's Gauss-Legendre quadrature. N=48, generalized lambda_min, minimum over both parities.\n- E: lambda_E = +6.43e-4 (x=19.5), +1.07e-4 (19.8), -2.19e-5 (19.9), -1.2993e-4 (20.0, matching the claimed -1.30e-4), -4.34e-4 (20.5; claimed -4.16e-4). So E dies between 19.8 and 19.9, consistent with x_E ~ 19.82.\n- After death ell_E - log 20 = 0.865 (x=40), 1.88 (60), 3.71 (120). That gives ell_E(120) = 6.71, matching the claim, and power-like growth consistent with an off-line displacement delta = 0.433.\n- zeta_K stays positive but collapses to the boundary: 4.59e-3 (x=20; claimed 4.606e-3), 1.5e-7 (40), 4.2e-10 (60), 3.0e-15 (120). eps = chi_{-20} reproduces zeta_K to all digits.\n- D: I did not re-run it. The proposal itself admits D's death near 31 is unresolved (N=48 top frequency ~83 < 85.7, and float64 noise), so the D control is still open.",
 "numerics_reproduced": "Yes, independently. Script: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/randomeuler_skeptic/sk1.py (usage: sk1.py N x1,x2,...; single process, finished in about 1 s per x).\n- zeta_K, E and the chi-vertex reproduce the claims as listed under the counterfeit check.\n- All-random Monte Carlo (400 samples) matches the proposal: P(pos) = 0.41, 0.10, 0.022, 0.000 at x = 20, 40, 60, 120, against the claimed 0.45, 0.108, 0.031, 0.0007. Median ell = 3.16, 3.87, 4.24, 5.03, against 3.11, 3.82, 4.19, 5.06.\n- The ramified-fixed model (eps_2 = eps_5 = 0, the correct choice for q = 20) gives materially higher P(pos): 0.66, 0.28, 0.11, 0.007. The decay to 0 is confirmed; the proposal's quantitative ensemble numbers are model-dependent.",
 "novelty": "Low.\n- T1 is the textbook conductor term of the explicit formula.\n- ell is the GRH-conditional Mestre/Odlyzko conductor bound: Mestre, Compositio Math. 58 (1986) 209-232; Odlyzko-Poitou-Serre.\n- The windowed Lagarias analogy is apt: Lagarias, Acta Arith. 89 (1999).\n- The boundary / near-null law is Connes-Consani, arXiv:2106.01715.\n- 'Random Euler products are zero-free but that does not give positivity' is Bagchi (1981 thesis) and Bohr-Jessen universality, combined with Denjoy's heuristic.\n- Also cited: Harper, arXiv:1703.06654.\nI checked these citations from memory (reliable) and did not re-search the web. The only new item is the empirical positivity statistics over the +-1 cube and the GRH-consistency ledger. Those are modest and mostly confirm GRH-predicted behaviour.",
 "what_is_real": "1. The numerics are correct and reproducible. E crosses between x = 19.8 and 19.9. zeta_K is a boundary point (lambda_min around 1e-15 at x=120) and is two-sidedly rigid under single-prime flips. P(pos at fixed q) -> 0 for random +-1 Euler products, including under the correct ramified-fixed model.\n2. The 0-violation GRH-consistency ledger (ell(eps,x) <= log|d_min(eps)| over 4608 vertices, tight only for small |d|) is a useful sanity harness for the window-form code.\n3. The three-way growth diagnostic is a clean way to present what is known: bounded ell -> log q for true L-functions, roughly log x for random vertices at the wrong conductor, and roughly x^delta for off-line counterfeits (delta = beta - 1/2 enters through |f^(gamma - i delta)|^2 ~ e^{2 delta A}). It is not new.\n4. The lesson that holds up: the archimedean datum (the declared conductor and the functional equation) must match the Euler data EXACTLY. Randomness and statistics of the prime data carry no positivity information, and the random angle has nothing to offer.",
 "next_step_if_survives": "It does not survive. The single most informative next step is to close the loophole the proposal left: build the ensemble CONDITIONED on the functional equation at fixed conductor. By the converse theorem that ensemble is exactly the genuine characters or automorphic forms of conductor <= q, so the 'random' angle reduces to class P and should be retired. Record the corrected ramified-fixed Monte Carlo numbers and the classification 'T1 = explicit-formula conductor term, C1 = GRH (>= direction trivial)' in the wave-3 synthesis, so later waves do not re-derive them as findings. If one certificate is wanted, run an Arb certification of E's sign change on [19.8, 19.9] at N >= 48; it adds only precision to the known x_E."
}
```
