The artifact is the hypothesis-free small-width region of the Gaussian Wall widened from lam0 = 1e-7 to lam <= 3/2000 (and 1/1000 with larger margin): an unconditional inequality about one explicit test function's prime-side functional, involving no zeros; NOT a proof of anything about RH.

# Audit testimony: E6Bridge30 (rvm_bridge island, the Gaussian window)

Auditor: auditor-forward (blind, adversarial). Date: 2026-09-22.
Island: telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned fbdc36bb.
File: E6Bridge30.lean (965 lines, namespace RvMBridge30, 58 declarations, imports E6Bridge11, E6Bridge16).
Probes (mine): Probes/Audit30_Auditor_Axioms.lean, Probes/Audit30_Probes.lean. The author's
Probes/Audit30_Axioms.lean (41 lines, 38 of the 58 declarations) was read, not relied on.
Spec: docs/GAUSS_WINDOW_DESIGN_2026-09-22.md section 7; numerics research/gauss_window_numerics.py.
conjecture1_proved = False.

## 1. Verdict

PASS. One sentence: the pole floor -e^{lam/2}/2, the sup cap e^{-1}/(2 lam), the window mass
rho e^{-1}/lam, the monotone psiR, the series-plus-integral-tail rational floors with N = 40 and
gamma <= 0.58112, the layer-cake invariant and the twelve-band assembly are all correct as
written, every numerical constant is verified against mpmath with the stated slack, the final
margins are +0.1688 (lam <= 1/1000) and +0.0517 (lam <= 3/2000) in units of A, the registry node
MM_gaussian_positivity_small_lam_3e3 is byte-identical, and the same twelve-band data provably
cannot reach 1/500 (the margin flips sign at lam ~ 1.66e-3).

No findings. Two remarks in section 8.

## 2. Kernel evidence (my runs)

Probes/Audit30_Auditor_Axioms.lean: 81/81 `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(all 58 RvMBridge30 declarations, mechanically extracted, plus 23 inputs: gaussianExplicitFormula,
norm_primeSide_le, bumpR_nonneg, integrable_bumpR, integral_bumpR, integrable_bumpR_mul_psiR,
psiR_eq, gaussA_pos, integral_archIntegrand_eq, autocorr_gaussPhi, autocorrGauss_zero,
weilKernel_zero_eq_gaussTest, weilKernel_one_eq_gaussTest, gaussTest_conj,
Zeta23.MuFields.re_digamma_vertical / re_digamma_mono / summable_re_terms,
Real.eulerMascheroniConstant_lt_eulerMascheroniSeq', Real.log_two_gt_d9, Real.exp_one_gt_d9,
Real.pi_gt_d6, Real.pi_lt_d6, RvMBridge11.gaussian_positivity_small_lam). Verbatim:

    'RvMBridge30.gaussian_positivity_small_lam_3e3' depends on axioms: [propext, Classical.choice, Quot.sound]

Token grep (sorry/admit/native_decide/axiom/opaque/unsafe/implemented_by/extern/partial/set_option):
nothing. Built .olean exists; in lakefile defaultTargets and AxiomGuardRvMBridge.lean:184. Only
my probes were built.

## 3. Registry byte comparison

missions/mirrormere/lean/Statements/MM_gaussian_positivity_small_lam_3e3.lean:

    theorem gaussian_positivity_small_lam_3e3 (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 3 / 2000) :
        0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re := by sorry

E6Bridge30 line 956: byte-IDENTICAL (python). Node toml: status draft, closure_clean false,
depends_on MM_gaussian_positivity_small_lam (the E6Bridge11/13 node at lam₀ = 1e-7, proved).
The definitions are E6Bridge6's `zeroSide H = ∑' ρ, zeroMult ρ * H (gammaOf ρ)` and
`gaussTest c lam z = (z - c)^2 exp(-2 lam (z - c)^2)`; `GaussianExplicitFormula` (E6Bridge11:74) is
the identity Re zeroSide (gaussTest c lam) = Re(archSide - primeSide)(autocorr (gaussPhi c lam))
for all c and lam > 0, proved from E6Bridge10.zeroSide_gaussTest_eq.

## 4. Mathematics re-derived by hand (memo step numbers)

Step 1, pole floor. Re gaussTest(i/2) = E [(c² - 1/4) cos θ + c sin θ] with θ = 2 lam c,
E = e^{-2 lam (c² - 1/4)} <= e^{lam/2} (since c² >= 0); the other pole is the conjugate. Near case
|θ| <= 1 < pi/2: cos θ >= 0, sin θ has the sign of c so c sin θ >= 0, bracket >= -(1/4) cos θ >= -1/4,
so P >= -E/2 >= -e^{lam/2}/2 (probe 3, abstract). Far case |θ| > 1: |c| > 1/(2 lam) >= 25;
bracket >= -(c² + 1/4) - |c| >= -2c² (needs c² - |c| - 1/4 >= 0, true for |c| >= 25);
E · 2c² = e^{lam/2} · 2c² e^{-2 lam c²} and 8c² <= e^{|c|} <= e^{2 lam c²} because 2 lam c² =
|c| (2 lam |c|) >= |c| and e^{|c|} >= |c|⁴/24 >= 8c² for |c| >= 25 (probe 4); so E·2c² <= e^{lam/2}/4
and P >= -e^{lam/2}/4. Checked. The bound is attained at c = 0 (P(0) = -e^{lam/2}/2), so it is
sharp; numerically min_c P = -e^{lam/2}/2 exactly for lam = 3/2000, 1/50, 0.2, 0.3, 0.35 (the
lemma only claims lam <= 1/50, which is all the file uses).
Step 3, bumpR <= e^{-1}/(2 lam): with y = 2 lam (r-c)², bumpR = (1/(2 lam)) y e^{-y} and
y e^{-y} <= e^{-1} from y <= e^{y-1}. Checked.
Step 4, window: |Ioo(-rho, rho)| = 2 rho times the sup gives rho e^{-1}/lam. Checked.
Step 5, psiR even and increasing in |r|: Zeta23's re_digamma_vertical (a = 1/4, t = r/2) is even
in t; re_digamma_mono gives monotonicity on t >= 0. Checked.
Step 6, the rational floor. psiR r = -gamma - a/(a²+t²) + Σ_{n>=0} f_n with f_n = serF t n >= 0
(serF_nonneg: (x+5/4)/((x+5/4)²+t²) <= 1/(x+5/4) <= 1/(x+1)). Drop the tail beyond N + M (nonneg),
and for N <= n < N+M use the antitone step: serF t is decreasing in x on [0, inf) (the file's
closed-form difference identity; numerically no violation on a grid for t = 0..10), so
AntitoneOn.integral_le_sum_Ico gives ∫_N^{N+M} f <= Σ_{n ∈ [N, N+M)} f(n); the FTC with
G(x) = (1/2) log((x+5/4)²+t²) - log(x+1), G' = -f (checked by differentiation), gives
∫_N^{N+M} f = G(N) - G(N+M). Then G(N) >= (1/2)(1 - (N+1)²/((N+5/4)²+t²)) by log X >= 1 - 1/X and
G(N+M) <= (1/2)(X - 1) by log X <= X - 1 with X = ((N+M+5/4)²+t²)/(N+M+1)²; with M = 10⁶ the
latter is ~ 2.5e-7 + t²/2e12. Checked. gamma <= 0.58112: H_128 = 5.4331470926 <= 5.4331471 and
log 128 = 7 log 2 > 7 · 0.6931471803 = 4.8520302621, so H_128 - log 128 < 0.5811168 <= 0.58112;
Mathlib's eulerMascheroniConstant_lt_eulerMascheroniSeq' supplies gamma < H_n - log n. Checked.
I recomputed all 21 rational floors (9 eight-band incl. r = 0, 12 twelve-band) in exact rational
arithmetic from the file's formula with N = 40, M = 10⁶, gamma_up = 0.58112 and compared with
mpmath's digamma:

    edge   file floor   my rigorous floor   exact psiR
    0      -4.2315      -4.231469           -4.227454
    0.5    -2.1913      -2.191291           -2.187275
    0.9    -1.0532      -1.053173           -1.049155
    1.5    -0.3405      -0.340420           -0.336398
    2.4     0.1691       0.169141            0.173172
    3.6     0.5804       0.580436            0.584488
    5.1     0.9303       0.930391            0.934480
    6.9     1.2333       1.233341            1.237496
    8.9     1.4881       1.488117            1.492377
    11.1    1.7090       1.709038            1.713459
    13.5    1.9046       1.904647            1.909314
    16.1    2.0804       2.080479            2.085511
    18.9    2.2403       2.240326            2.245898
    (eight-band edges 0.6, 1.4, 2.9, 8, 11.6, 16, 21.1 likewise: file <= rigorous <= exact)

Every file floor is <= the rigorous value and every rigorous value is <= the exact psiR; every
floor is within 0.001 of its rigorous value (rounded down to 4 decimals), and probe 12 shows the
floor at 18.9 raised by 0.001 is NOT certified by the same bound. The floors are tight to the method;
the method itself is ~0.004 to 0.006 below the truth (the gamma slack 0.0039 plus the tail).
Step 7, the layer cake. Cake c lam φ ρ B := an integrable minorant ℓ of psiR, constant = φ on
|r| >= ρ, with ∫ bumpR ℓ >= B. Base: ℓ = φ_0 (valid since φ_0 <= psiR 0 <= psiR r). Step: ℓ' =
ℓ + (φ' - φ)(1 - 1_{|r| < ρ'}); on |r| >= ρ' it equals φ' <= psiR ρ' <= psiR r, inside it is ℓ;
∫ bumpR ℓ' = ∫ bumpR ℓ + (φ' - φ)(M - ∫_{|r|<ρ'} bumpR) >= B + (φ' - φ)(M - ρ' e^{-1}/lam) using
φ' >= φ and step 4. Telescoping over the bands gives φ_K M - Σ (φ_k - φ_{k-1}) ρ_k e^{-1}/lam.
cake_integral: ∫ bumpR ℓ <= ∫ bumpR psiR (integral_mono, bumpR >= 0). Checked. The band sums:
bandSum = Σ (φ_k - φ_{k-1}) ρ_k = 27.44863 (eight) and bandSum12 = 22.90515 (twelve), both
recomputed exactly and equal to the file's 2744863/100000 and 458103/20000 (probe 6 re-derives
the latter by norm_num from the decimal floors).
Step 8, assembly. archSide real part (E6Bridge16 decomposition) = pole terms - A log pi +
(1/2pi) ∫ bumpR psiR, so F/A >= -pole/A + φ_K - cap · bandSum - log pi - |primes|/A with
cap = e^{-1}/(2 pi lam A) = 4 sqrt(2/pi) e^{-1} sqrt(lam) (probe 5 proves this identity). Constants:

    lam       cap exact  (file)   pole/A exact (file)   |primes|/A exact (file)   log pi (file)
    1/1000    0.037128   0.0375   0.0003172    0.001    5.8e-12       0.006      1.144730 1.1448
    3/2000    0.045473   0.0455   0.0005829    0.0006   1.3e-7        0.001      1.144730 1.1448

all file constants are valid upper bounds. The prime bound uses norm_primeSide_le (needs
log 2/(16 lam) >= 2: 43.3 and 28.9) with e^y >= y⁴/24 at y >= 30 (64·24/30⁴ = 0.0019 <= 0.006)
resp. e^y >= y⁶/720 at y >= 20 (64·720/20⁶ = 0.00072 <= 0.001). log pi <= 1.1448 via
e^{1.1448} = e · e^{0.1448} >= 2.718281828 · 1.155808 = 3.14181 > pi. Margins:
eight bands: -0.001 + 2.3499 - 0.0375 · 27.44863 - 1.1448 - 0.006 = +0.16878 (probe 7);
twelve bands: -0.0006 + 2.2403 - 0.0455 · 22.90515 - 1.1448 - 0.001 = +0.05172 (probe 7).
With exact constants the margins are 0.1857 and 0.0534. Monotonicity in lam: cap ~ sqrt(lam),
pole ~ lam^{3/2} e^{lam/2}, primes ~ e^{-c/lam} all decrease as lam decreases, so the single
constant set at the threshold covers 0 < lam <= threshold; the file consumes only lam <= 3/2000
(resp. 1/1000) and lam > 0 in each cap. Checked.

## 5. Sharpness and non-vacuity (numerics, mpmath)

- The twelve-band assembly with exact constants has margin 0 at lam* = 0.0016575; at lam = 1/600
  it is -0.0030 and at 1/500 it is -0.108. So 3/2000 = 0.0015 is within 10% of what these floors
  and edges can certify. Probe 8 proves in Lean that the same rational data with the cap at
  lam = 1/500 (0.0525) gives a NEGATIVE margin; probe 11 shows the theorem is refused at lam <= 1/500.
- Truth versus bound at lam = 3/2000: the bump-weighted average <psiR>_B is 2.229, 2.226, 2.201,
  1.987, 2.285 at c = 0, 1, 3, 10, 30, against the layer-cake bound 1.199; F/A is 1.084, 1.083,
  1.076, 1.015, 1.281. At lam = 1/1000: averages 2.43 .. 2.23 against the bound 1.390; F/A ~ 1.22
  to 1.29. The theorem is far from vacuous; the layer cake loses about 1.0 in units of A, which is
  the price of c-uniformity (the memo's section 8 ceiling discussion).
- The pole floor is attained at c = 0 and holds numerically far beyond the stated lam <= 1/50.

## 6. Probes (Probes/Audit30_Probes.lean)

Expected successes, all elaborated: chain re-composition (1); 3/2000 subsumes 1/1000 and the
E6Bridge11 existential (2); pole near-case algebra (3); far-case Taylor step (4); cap identity
cap = 4 e^{-1} sqrt(2 pi) sqrt(lam)/pi · A (5); bandSum12 from decimal floors (6); both margins
positive (7); margin negative with the 1/500 cap (8); the tail sum nonnegative (9); gamma bound
consumed (10). Expected failures, each at the intended point:

    Probes/Audit30_Probes.lean:70:51: linarith failed     -- theorem at lam <= 1/500
    Probes/Audit30_Probes.lean:74:51: unsolved goals      -- floor 2.2413 at r = 18.9 not certified
    Probes/Audit30_Probes.lean:82:28: unsolved goals      -- pole_floor at lam = 1/40 (> 1/50)

## 7. Overclaim grep

E6Bridge30.lean lines 55-56: "Nothing here proves RH: the theorem is an unconditional statement
about one explicit test function's prime-side functional; it involves no zeros.
conjecture1_proved = False." Design memo lines 3 and 466 carry the same flag. No "RH proved"
or zero-location language anywhere.

## 8. Remarks (not defects)

- The header (lines 14-15) says "eight bands" following the memo; the registry node is the
  twelve-band stretch (section G). Both are in the file and both are kernel-clean; the docstring
  of section G says so.
- The author's probe covers 38 of 58 declarations; mine covers all 58 plus 23 inputs.

## 9. What this does and does not establish

Established, unconditionally: F(c, lam) = Re zeroSide (gaussTest c lam) >= 0 for every centre c
and every 0 < lam <= 3/2000, through the Gaussian explicit formula, i.e. Weil positivity of one
explicit family of test functions in the small-width region. This is the wall's free region
widened from 1e-7 to 1.5e-3 in lam; it says nothing about zeros (the inequality is proved on the
prime side, where no zero appears) and nothing about RH. NOT a proof of anything about RH.
conjecture1_proved = False.
