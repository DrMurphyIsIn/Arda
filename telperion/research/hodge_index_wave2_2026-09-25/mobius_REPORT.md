# Hodge index WAVE2: angle `mobius`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Möbius / Nyman–Beurling angle: final report

conjecture1_proved = False. The angle is **dead as a source of Weil positivity**. What survives is a diagnostic: a verified counterfeit detector that uses multiplicativity nonlinearly, plus quantitative comparisons.

Scripts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/mobius/`:
- `coeffs.py`: coefficients and Dirichlet inverses for zeta, zeta_K (K = Q(sqrt -5)), E and D.
- `mertens.py`, `fit.py`: Mertens sums and the fit to off-line zeros.
- `nb.py`: optimal Báez-Duarte distances.
- `mol.py`: Möbius-mollified distances.
- `pick.py`: Hardy-space lower bounds.

All runs used a single process, and all have finished.

## 0. Setup (exact, for a general L)
Let L(s) = Σ a_n n^{-s}, with a pole at s = 1 of residue r (r = 0 for D). Set A(x) = Σ_{n≤x} a_n and Φ_L(x) = A(x) − r x. Then

∫_0^∞ Φ_L(x) x^{-s-1} dx = L(s)/s on θ < σ < 1.

Mellin–Plancherel on σ = 1/2 turns (1/2π)∫|·|² dt into ∫|·|² dx/x², and χ = 1_{[1,∞)} has Mellin transform 1/s. So the Báez-Duarte distance is

d_N(L)² = inf_c ∫|1 − L(s)A_c(s)|² |ds|/(2π|s|²) = inf_c ∫_0^∞ |χ(x) − Σ_{k≤N} c_k Φ_L(x/k)|² dx/x².

For fixed coefficients c this equals ∫|χ − S_{c*a}(x) + rCx|² dx/x², where S_{c*a} is the summatory function of the Dirichlet convolution c*a and C = Σ c_k/k.

Residues used: zeta 1; zeta_K π/√5; E π/(2√5) (E = (ζ_K + L(χ₋₄)L(χ₅))/2, a(1) = 1, the same convention as bcore.py); D 0 (D has τ = 0.2841, coefficients periodic mod 5).

Numerics: exact piecewise structure on unit intervals, Gauss quadrature, chunked TSQR with the target column appended, so every nested d_N comes from one R factor. The tail beyond X = 1e6 was estimated from the empirical mean over [X/2, X], with mean-square growth x^0 (zeta, D) or x^{1/2} (zeta_K, E).

**Validation:** zeta gives d_100² · log 100 = 0.0469. This matches the BDBLS/Burnol constant 2 + γ − log 4π = 0.0461.

## 1. M1: a theorem about all bounded multiplicative functions implying W(x). DEAD
Wanted: a statement X, proved for every bounded multiplicative f by Halász / Matomäki–Radziwiłł / Tao methods, such that X(μ) implies W(x).

1. W(x) for all x is RH, which is Littlewood's M(x) = O(x^{1/2+ε}). So X(μ) would have to give a power saving.
2. Take f_δ(p) = −1 except f_δ(p) = +1 on a set of primes of relative density δ. Then f_δ does not pretend to 1 (D(f,1;x)² ~ 2δ log log x → ∞), yet by Wirsing Σ_{n≤x} f_δ(n) ≍ x (log x)^{-2δ}.
3. So any X that holds for every bounded non-pretentious multiplicative function carries at most a log-power saving, and can only reach RH through an extra input that f_δ lacks: the analytic continuation plus functional equation.
4. The FE alone is already defeated by the class-P / fooling barrier. So the missing theorem must use FE and Euler product **jointly** (in effect, GRH for the Selberg class). M-R/Tao technology uses no FE.
5. Second obstruction: M-R/Halász conclusions do not change when f is modified on a set of primes with Σ 1/p < ∞. W(x) at a fixed x is a finite statement about Λ(n), n ≤ x (equivalently, a function of μ restricted to [1, x], since Λ = μ * log), and it is sensitive to every prime up to x.

**Verdict: no such X exists in the robust, universal form requested.**

## 2. M2: Möbius-mollified Nyman–Beurling distance. A true discriminator, but not a reason
Definition: D_N(L) = ‖χ − Σ_{k≤N} c_k Φ_L(x/k)‖², with c_k = b_L(k)(1 − log k/log N) and b_L = a_L^{*−1}.

**Where the Euler product enters.** Only through b = a^{*-1}, which is a nonlinear function of L. The inverse of D is not the combination of the two automorphic inverses, so this gets past the linearity barrier.

**Why E and D fail.** Each off-line zero ρ contributes to M_L(x) = Σ_{n≤x} b_L(n) a term 2 Re(x^ρ / (ρ L'(ρ))), of size about x^β. The mollifier V_N then grows like N^{β−1/2} on the line, so D_N grows roughly like N^{2β−1}/log²N.

**Tests run.**

(a) Mertens sums up to 2e6. The table gives max|M|/√x over [x/2, x]:

| x | ζ | ζ_K | E | D |
|---|---|---|---|---|
| 1e3 | 0.47 | 1.63 | 3.90 | 0.74 |
| 1e4 | 0.43 | 1.48 | 7.23 | 0.90 |
| 1e5 | 0.46 | 2.27 | 21.3 | 1.91 |
| 1e6 | 0.38 | 2.20 | 52.5 | 3.11 |

Fit to the predicted off-line-zero term:
- **E:** ρ = 0.9329697 + 15.6682495i (findroot, |E(ρ)| = 5e-22), c = 1/(ρE'(ρ)) = 0.00509 − 0.03285i. Regression coefficient on the prediction: 0.952 (1 would be exact). The leftover residual keeps growing, driven by E's other off-line zeros (13 listed up to height 100, the next at 0.9377 + 29.98i).
- **D:** ρ = 0.8085172 + 85.6993485i, c = 0.00187 − 0.00910i. Regression coefficient 0.998.

(b) Mollified distance D_N:

| N | ζ | ζ_K | E | D |
|---|---|---|---|---|
| 1e2 | 0.178 | 0.272 | 0.469 | 0.0446 |
| 3e2 | 0.117 | 0.194 | **0.488** | 0.0363 |
| 1e3 | 0.081 | 0.163 | 0.588 | 0.0311 |
| 1e4 | 0.047 | 0.115 | 1.51 | **0.0267** |
| 3e4 | 0.038 | 0.096 | 2.88 | 0.0275 |
| 1e5 | 0.031 | 0.084 | 6.24 | 0.0320 |

The prediction is confirmed:
- zeta and zeta_K decrease monotonically.
- E turns upward at N* ≈ 100–300. Its growth rate is consistent with N^{0.866}/log²N (predicted ×4.7 from 1e4 to 1e5; observed ×4.1).
- D turns upward at N* ≈ 1e4.

Where the failure happens:
- log N* is about 5.3 for E, against log x_E = 2.99 for the Weil window.
- log N* is about 9.2 for D, against log x_D ≈ 3.4.

The ordering is the same as for the Weil thresholds (E is caught first), but the Weil windows are much sharper.

(c) Optimal d_N (arbitrary coefficients, N ≤ 100). All four decrease:

| | ζ | ζ_K | E | D |
|---|---|---|---|---|
| d_100² | 0.0102 | 0.102 | 0.196 | 0.0337 |

The optimal distance does not discriminate at feasible N.

Rigorous lower bound: 1 − E·A has the value 1 at each off-line zero. Multiply by the unimodular factor (s−1)/s to remove the pole, and use the H²(σ > 1/2) kernel 1/(w + w̄'). Pick interpolation over all 13 listed off-line zeros of E and their conjugates gives

d_N(E)² ≥ 0.0121 for every N (0.00697 from the first pair alone).

For D the bound is ≥ 1.68e-4. With the observed d² log N ≈ 0.9 for E, a visible plateau needs log N ≳ 74. With the zeta-like constant 0.046 it would be log N ≳ 4, but E's constant is clearly not zeta-like. For D a plateau needs log N > 274.

In general, Nyman–Beurling excludes an off-line zero at height T only when d_N² < ~2(β−½)/T², that is, log N ≳ 0.05 T²/(β−½). The weight 1/|s|² makes it the most heavily smoothed window possible: its resolution is exponentially worse than Weil windows, which catch E at log x ≈ 3.

**Honest status of M2.** "D_N → 0" together with "b_L is tame" is equivalent to RH for L (Littlewood / BCF / de Roton). The multiplicative input only guarantees tameness where the Euler product converges, i.e. in the Bohr lift on the infinite polydisc (Nikolski 2012: Euler-product cyclicity is automatic only in the absolute-convergence region). The critical strip is reached only through analytic continuation, which is a linear operation. This is the same wall found in the four frameworks: multiplicativity is visible where it is not needed, and linear information is all that is available where it is needed. **No positivity mechanism comes out of this angle.**

## 3. Useful by-products
1. A rigorous, cheap, nonlinear counterfeit detector: the turning point N* of D_N, or the growth exponent of M_L. It is multiplicativity-sensitive and passes for zeta and zeta_K.
2. A quantitative statement of how far Nyman–Beurling is from Weil windows: resolution scales like log N ~ T² versus log x ~ O(1) for E.
3. The observation that W(x) is a function of μ restricted to [1, x] alone. This makes "find a convex property P of finite multiplicative sequences with P ⟹ W(x)" a well-posed finite question: the admissible weight vectors (Λ(n))_{n<x} form a spectrahedron C_x. It is a possible handoff to a Hodge/spectrahedron angle.

## 4. Literature
Web search budget was exhausted, so these are cited from memory and were **not** re-verified this session.
- Nyman 1950 (thesis, Uppsala); Beurling, PNAS 41 (1955).
- Báez-Duarte, Rend. Mat. Acc. Lincei 14 (2003).
- Báez-Duarte, Balazard, Landreau, Saias, Adv. Math. 149 (2000).
- Burnol, Adv. Math. 170 (2002).
- Vasyunin 1995.
- de Roton, Trans. AMS 359 (2007): NB criterion for the Selberg class.
- Bettin, Conrey, Farmer, IMRN 2013.
- Noor, Adv. Math. 2019.
- Nikolski, Ann. Inst. Fourier 62 (2012).
- Matomäki–Radziwiłł, Ann. of Math. 183 (2016).
- Tao, Forum Math. Pi 4 (2016).
- Halász 1968; Granville–Soundararajan; Wirsing 1967.

I know of no prior computation of mollified Nyman–Beurling distances for Epstein or Davenport–Heilbronn counterfeits. Novelty is minor.

## 5. Odds
- M1: below 1% (refuted).
- M2 as a proof route: below 1% (equivalent to RH, not a reason for it).
- Value short of RH: a diagnostic, plus the finite-sequence reformulation in §3.3.

conjecture1_proved = False.

## Adversarial verdict

```json
{
 "angle": "mobius (skeptic review): M\u00f6bius, Nyman\u2013Beurling and B\u00e1ez-Duarte, and the multiplicative-function theorems of Hal\u00e1sz, Matom\u00e4ki\u2013Radziwi\u0142\u0142 and Tao, as a source of Weil positivity",
 "survives": false,
 "fatal_flaws": [
  "M2 is circular. 'D_N -> 0 with a tame Dirichlet inverse' is equivalent to RH for L (Nyman\u2013Beurling, B\u00e1ez-Duarte, Littlewood's criterion M(x) = O(x^{1/2+eps})). It is an RH-equivalent criterion, not a reason for W(x). The proposer concedes this, and I confirm it.",
  "M2 gets past the linearity barrier only vacuously. The nonlinear map a -> a^{*-1} is simply 1/L. It detects zeros of L, which is exactly what the Littlewood criterion does. It separates E and D from zeta only because E and D already have off-line zeros. No step derives positivity from multiplicativity. A hypothetical non-Euler-product L with all its zeros on the line would pass the detector, so calling it 'multiplicativity-sensitive' overstates what it does.",
  "M1 has an internal error, though its conclusion stands. f_delta is defined as 'f(p) = -1 except +1 on density delta', but the stated facts (D(f,1;x)^2 ~ 2 delta log log x, and partial sums of size x (log x)^{-2 delta}) belong to the opposite choice, f(p) = +1 except -1 on density delta. With the definition as written, Selberg\u2013Delange gives partial sums of size x (log x)^{2 delta - 2} and D(f,1)^2 ~ 2(1 - delta) log log x. Either family has no power saving, so the conclusion survives. The refutation itself is the standard fact that universal theorems for bounded multiplicative functions give only o(x) or log-power savings.",
  "The ordering 'E before D, matching the Weil thresholds' rests on two data points. Any zero-sensitive statistic orders E (beta = 0.933, height 15.7) ahead of D (beta = 0.809, height 85.7). Nothing ties it to the Weil thresholds x_E ~ 19.82 or x_D ~ 31. The resolution is in fact far worse: log N* is about 5 against log x_E of about 3.",
  "The D turn-up at N* ~ 1e4 is not independently confirmed at N <= 3e4. My independent frequency-side integration (to T = 300) gives D_N = 0.0265 at N = 1e4 and 0.0274 at N = 3e4, but the whole difference sits inside the tail estimate (0.0019 -> 0.0029). Without the tail the values are flat (0.0246 vs 0.0245). The proposer's N = 1e5 value (0.0320) is needed; I did not independently reproduce it.",
  "Citation error: Bettin\u2013Conrey\u2013Farmer's 'An optimal choice of Dirichlet polynomials for the Nyman\u2013Beurling criterion' (arXiv:1211.5191) was published in Sovrem. Probl. Mat. 16, Steklov Math. Inst. (2012), 38\u201344, not IMRN 2013. Its result is conditional on RH plus a bound on a sum over zeros. The de Roton (Trans. AMS 2007), Nikolski (2012) and Noor (2019) citations could not be verified: the web search budget was exhausted and the AMS page returned 403."
 ],
 "linearity_or_classP_violation": "M1: the universal multiplicative theorems (Hal\u00e1sz, Matom\u00e4ki\u2013Radziwi\u0142\u0142, Tao) use no functional equation. They cannot see the interaction between the functional equation and the Euler product that the class-P / fooling barrier says is required, and they give no power saving. The angle is dead, and correctly killed. M2: the Dirichlet inverse is nonlinear, so D is not fooled in the literal sense. But the separation is a readout of zero locations (M_L(x) is dominated by x^rho/(rho L'(rho)) at off-line zeros), not a positivity argument. Asked 'would the argument go through verbatim for E?', the answer is that there is no argument, only a criterion that E fails because E already violates RH. The linearity barrier is sidestepped, not overcome.",
 "counterfeit_check": "Reproduced with my own code: sk_coef.py, sk_fit.py, sk_Lvals.py and sk_mol.py in scratchpad/hodge2/mobius_skeptic/. The definitions are my own: E = r_{x^2+5y^2}(n)/2, zeta_K = zeta * L(chi_{-20}), D with period-5 coefficients (1, tau, -tau, -1, 0), tau = 0.284079. Mertens growth, max|M|/sqrt x on [x/2, x]: E goes 3.89, 7.23, 21.3, 52.5, 65.6 for x = 1e3 to 2e6; D goes 0.744, 0.898, 1.91, 3.11, 3.70; zeta stays at 0.38\u20130.47; zeta_K at 1.5\u20132.3. This matches the proposer to every printed digit. The off-line zeros check out: findroot gives E: rho = 0.932969697 + 15.66824953i and D: rho = 0.808517182 + 85.69934849i. Regression of M on 2 Re(x^rho/(rho L'(rho))): 0.949 for E, 0.998 for D. The correlations are only 0.80 and 0.74, so the other off-line zeros matter. The E upturn is confirmed independently. On the Mellin/frequency side, D_N(E) = 0.463, 0.481, 0.577, 0.826, 1.49, 2.79 for N = 1e2, 3e2, 1e3, 3e3, 1e4, 3e4, against the proposer's physical-side values 0.469, 0.488, 0.588, ..., 1.51, 2.88, which agree within my tail error. zeta and zeta_K decrease monotonically, matching the proposer: zeta 0.178 -> 0.038, zeta_K 0.271 -> 0.095. The D upturn is marginal at N <= 3e4 (see flaws). The Pick bound checks out by hand: a single off-line zero gives d^2 >= |rho-1|^2 (2 beta - 1)/|rho|^4 ~ 0.0035 for E's first zero, about 0.007 for the conjugate pair, consistent with the proposer's 0.00697. Predicted failure point: E at log N* ~ 5 (N* ~ 100\u2013300), not near x_E ~ 19.82; D not before N ~ 1e4\u20131e5, not near x_D ~ 31. The criterion does fail for both counterfeits, but it gives no quantitative prediction of the Weil thresholds.",
 "numerics_reproduced": "Yes, independently and with a different method for the key quantity. The Mertens sums and the zero fits match exactly. I computed the mollified distance by integrating on the Mellin side, (1/pi) \u222b_0^300 |1 - L V_N|^2 / |s|^2 dt with a tail estimate, where the proposer integrated on the physical side. The results agree to about 1\u20133% for zeta, zeta_K and E. D's upturn between 1e4 and 3e4 is within the tail uncertainty and is not independently established below N = 1e5.",
 "novelty": "Low. Nyman\u2013Beurling and B\u00e1ez-Duarte are RH equivalents, and extensions to the Selberg class exist (de Roton, recalled but not verified). The Littlewood / Mertens-growth detection of off-line zeros for Epstein and Davenport\u2013Heilbronn functions is essentially folklore. The only new item is a numerical table of mollified NB distances for E and D. Its message, that NB resolves an off-line zero at height T only when log N >~ T^2 while Weil windows need log x ~ O(1), is a useful quantitative remark, but minor.",
 "what_is_real": "(1) The negative result for M1 is correct: universal theorems for bounded multiplicative functions give no power saving, cannot see the functional equation, and are insensitive to sparse changes at the primes. The f_delta sign convention needs fixing. (2) The counterfeit-detector numerics are real and reproducible: the Mertens growth of the Dirichlet inverse for E and D is driven by their listed off-line zeros, and E's mollified-distance upturn is confirmed by an independent method. (3) The Pick/H^2 lower bound d_N(E)^2 >= ~0.007 from the first pair is correct, and it shows the NB criterion's resolution is exponentially coarser than the Weil windows. (4) The observation worth keeping: W(x) is affine in the weights (Lambda_L(n))_{n<=x}, so the admissible set C_x is a spectrahedron. For an Euler product these weights are supported on prime powers; for E, the coefficients of -E'/E are nonzero at non-prime-powers (for example n = 6, from a_E(6) = 2). This gives a precise, finite, NONLINEAR question: does the prime-power-support constraint, intersected with the functional-equation constraints, force the vector into C_x? That is the only piece of this angle that points at a mechanism, and it should be handed to the Hodge/spectrahedron angle.",
 "next_step_if_survives": "The angle does not survive as a mechanism. The single most informative next step is the spectrahedral handoff. At x = 20 (E's threshold), compute how far E's Weil vector Lambda_E|_{[1,20]} lies from the boundary of C_20. Then compute the vector obtained by zeroing its non-prime-power entries (n = 6, 10, 12, 14, 15, 18, 20, ...), and check whether that projection alone restores positivity. A yes would identify prime-power support, which is where the Euler product acts, as the finite-x discriminator. A no kills that thread. It should also be checked against D at x ~ 31\u201335, whose -D'/D coefficients are likewise not supported on prime powers."
}
```
