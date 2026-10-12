> **SUPERSEDED (2026-10-11):** the statement is already kernel-proved on main in a stronger form (`KWin_Bridge.weil_positivity_prime_free_window`: full IsWeilTest class, pole terms kept, 2L ≤ log 2; KWin2 extends to 2L ≤ 1), and the user chose a conceptual (Connes-Consani) proof instead of this certificate route; see `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`.

# Archimedean rung blueprint: pole-free Weil positivity on the prime-free window (2026-10-11)

Branch `mm/archimedean-rung`, island `telperion/examples/rvm_bridge/lean` (Mathlib v4.32.0 pin
through Zeta23).  `conjecture1_proved = False`.  Nothing here is RH progress: it is the
archimedean theorem of Yoshida (1992) in the form quoted by Connes-Consani (2021, p. 2), with a
proof route chosen so that the kernel can check it.

Every number in this document is **numerical / certified-in-script, not kernel-checked**.
"Certified-in-script" means exact rational arithmetic (python-flint `fmpq`), with the psiR floors
cross-checked against arb digamma enclosures.  Scripts live in
`telperion/research/arch_rung/` (section 6).

## 0. Headline

* **The statement's class is one condition, and its margin is 0.072, not 0.547.**  The Lean
  hypothesis `paperFT g (I / 2) = 0` is a single complex condition, `∫ g(u) e^{-u/2} du = 0`.
  It already kills both pole terms (E6Bridge31 `poles_vanish`).  Earlier project notes quote a
  margin of 0.547 at L = (log 2)/2.  That figure is for the two-condition class
  `∫ g e^{±u/2} = 0` (`mineig_vanishing` in `prime_free_window_numerics.py`).  On the
  one-condition class, the minimum of Q/‖g‖² at L = (log 2)/2 is **0.07233** (arb,
  section 1.3).  The statement stays true up to L ≈ 0.3716.  Lean routes must budget against
  0.072.
* **Literature check (CC 2006.13771, read from the PDF).**  CC quote Yoshida's theorem on p. 2:
  W∞(f) ≥ 0 for positive-definite f supported in (1/2, 2) whose Fourier transform vanishes at
  ±i/2.  Equivalently, Q_W(g) ≥ 0 on g supported in [2^{-1/2}, 2^{1/2}] with ĝ(i/2) = 0.  That
  is exactly the one-condition class.  CC Thm 1 adds ĝ(0) = 0 only because it proves the
  stronger Sonin-trace inequality.  Thm 6.11 drops ĝ(0) = 0 at the price of −c|ĝ(0)|², with
  c = 4γ/log 2, and Rem 6.12 shows the best c satisfies 13 < c < 17.  Our target is Yoshida's
  plain positivity, not the trace inequality.
* **Full rung: closes with a 36×36 rational certificate.**  The chosen route is "R" (sections
  2-3): r-space psiR floors, a Taylor-moment relaxation of the low frequencies, Bessel, and an
  LDLᵀ certificate.  It is verified in exact rationals at L₁ = 1733/5000 ≥ (log 2)/2.

  | config | log π bound | grid | M | margin (exact, ×‖g‖²) | script time |
  |---|---|---|---|---|---|
  | **A** | existing `log_pi_le` (1.159) | 121 floors, h = 1/4, R = 30 | 36 | **0.01454** | 4.5 s |
  | **B** | new lemma log π ≤ 1.1455 | same | 36 | **0.02804** | 4.5 s |
  | C | new lemma | 97 floors, R = 24 | 32 | 0.02230 | 2.4 s |

  The exact LDLᵀ has all pivots positive.  A Lean-sized rounded certificate also closes: the
  LDLᵀ of C − δI is rounded to 1e-12, and the residual is diagonally dominant with slack 0.0139.
  Its entries are at most about 30 digits.
* **Intermediate rung: L = 7/25 = 0.28, no matrix.**  The chosen route is "B": pole-free
  Cauchy-Schwarz caps D(r)², then a layer cake (bathtub).  The exact-rational margin is
  **+0.04205** with 43 psiR floors and 168 cap sub-bands.  L = 29/100 also closes, with margin
  +0.0085, or +0.0220 with the new log π lemma.  The route's own exact threshold is L ≈ 0.3053.
  This beats the 0.236 that was targeted.

## 1. Statements and numerical truth

### 1.1 Conventions (checked against the source)

* `paperFT g z = ∫ u, g u * cexp (I * z * u)` (Zeta23 `Defs.lean:44`).  So
  `paperFT g (I / 2) = ∫ g(u) e^{-u/2} du` and `paperFT g (-I / 2) = ∫ g(u) e^{u/2} du`.
* `weilKernel (autocorr g) 0 = paperFT g (I/2) * conj (paperFT g (-I/2))` and
  `weilKernel (autocorr g) 1 = paperFT g (-I/2) * conj (paperFT g (I/2))` (E6Bridge31:258-277).
  So `paperFT g (I/2) = 0` alone kills both pole terms (`poles_vanish`, E6Bridge31:685).
* On that class, `archSide_autocorr_poleFree` (E6Bridge31:699) gives

      Re archSide (autocorr g) = Q(g) := −log π · mass g + (1/2π) ∫ hsq g r · psiR r dr,

  with `hsq g r = ‖paperFT g r‖²`, `psiR r = Re ψ(1/4 + i r/2)` (E6Bridge11:728), and
  `mass g = ∫ ‖g‖²`.
* For tsupport g ⊆ [−L, L] and 2L ≤ log 2, `weilForm_autocorr_eq_archSide` (E6Bridge31:109)
  gives weilForm = archSide, since the prime side vanishes.
* Complex g is harmless.  The form has a real symmetric kernel, so Q(a + ib) = Q(a) + Q(b), and
  the constraint splits into real and imaginary parts.  The certificate is a real symmetric
  matrix applied to complex moment vectors.

### 1.2 Lean statements

Both rungs go in a new module.  The registry statement is in MMDefs vocabulary (`WeilExplicit.*`)
and `paperFT` is Zeta23's.  If the registry cannot import Zeta23, state the condition as
`∫ u, g u * Complex.exp (-(u : ℂ) / 2) = 0` and add a one-line bridge lemma
(`paperFT_I_half_eq`, below).

```lean
/-- Bridge: the pole-free condition in elementary form. -/
lemma paperFT_I_half_eq (g : ℝ → ℂ) :
    paperFT g (I / 2) = ∫ u : ℝ, g u * Complex.exp (-(u : ℂ) / 2)       -- I * (I/2) * u = -u/2

/-- FULL RUNG (Yoshida 1992; Connes-Consani 2021 p. 2): pole-free Weil positivity on the whole
prime-free window. -/
theorem weil_positivity_poleFree_window (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : 2 * L ≤ Real.log 2) (hsupp : tsupport g ⊆ Set.Icc (-L) L)
    (h0 : paperFT g (I / 2) = 0) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re

/-- ... which closes the named Prop of E6Bridge31:662. -/
theorem primeFreeWindowPositivityPoleFree_holds : RvMBridge31.PrimeFreeWindowPositivityPoleFree

/-- INTERMEDIATE RUNG: no finite-matrix certificate. -/
theorem weil_positivity_poleFree_mid (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : L ≤ 7 / 25) (hsupp : tsupport g ⊆ Set.Icc (-L) L)
    (h0 : paperFT g (I / 2) = 0) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re
```

Notes for the implementers:

* For the intermediate rung, 2L ≤ log 2 follows from L ≤ 7/25 with `Real.log_two_gt_d9`.
* For L < 0, pass through L' = max L 0 as in E6Bridge31:705.
* The full rung is proved at the rational half-width L₁ = 1733/5000 = 0.3466.  Since
  (log 2)/2 = 0.346574 < L₁ (`Real.log_two_lt_d9`), the hypothesis 2L ≤ log 2 gives
  tsupport g ⊆ [−L₁, L₁].  The certificate is stated at L₁.  Stage 0 still uses the real L.
* The internal workhorse is the quantitative form at L₁:
  `margin * mass g ≤ (archSide (autocorr g)).re`, with `margin = 0.01454` (config A) or
  `0.02804` (config B).

### 1.3 Numerical truth (pole-free class, one condition)

λ_min of Q/‖g‖² on {∫ g e^{-u/2} = 0, supp g ⊆ [−L, L]}.  The u-space engine is
`polefree_numerics.py` (Legendre N = 30).  The arb cross-check uses the gate-0 engine
`weil_arb.py` restricted to c^⊥ (`arb_polefree_check.py`, 256 bits).

| L | one condition (Lean class) | both conditions ∫ g e^{±u/2} = 0 | no condition, poles dropped |
|---|---|---|---|
| 0.10 | +1.3300 | +1.7922 | +0.0726 |
| 0.20 | +0.6331 | +1.0985 | −0.668 |
| 0.236 | +0.4655 | +0.9326 | −0.850 |
| 0.25 | +0.4070 | +0.8749 | −0.915 |
| **0.28 (intermediate)** | **+0.2915** | | |
| 0.29 | +0.2556 | | |
| 0.30 | +0.2209 | +0.6920 | −1.120 |
| **(log 2)/2** | **+0.07233** (arb: [0.07233354838 ± 4.9e-12] at N = 30, [0.07235285667 ± 2.9e-12] at N = 20) | +0.5470 | −1.286 |
| 0.3466 = L₁ | +0.07225 | | |
| 0.36 | +0.0330 | +0.5088 | −1.330 |
| 0.40 | −0.0768 | +0.4028 | −1.453 |

* **Threshold of the one-condition statement:** L* = 0.37161.
* **Caveats.**
  * A restricted-basis minimum is an upper bound on the true infimum.  It is converged here: N = 20 → 30 changes it by 2e-5, and the r-space and u-space evaluations agree.
  * The arb balls enclose the assembled matrix.  The quadrature truncation is checked by refinement, not enclosed.
  * The r-space evaluation clipped at R = 150 gives 0.07071 (`rspace_scan.py` (a)).  That is consistent from below.

## 2. Proof routes

Every route starts from the same reduction:
Q(g) = −log π·mass + (1/2π)∫ hsq·psiR, valid on the pole-free class (E6Bridge31:699).
"Threshold" means the largest L at which the route's inequality chain stays positive.

| route | idea | threshold in L | Lean verdict |
|---|---|---|---|
| U0: E6Bridge34 chain + pole-free bound on the mean | E6Bridge33 `Eb_ge`, plus \|∫g\|² ≤ (2L − 4 tanh(L/2))‖g‖² from the constraint | **0.147** | cheapest, but too short |
| U: u-space Galerkin on Σ_b e^{−b\|u\|} | Q ≥ H_{N₀}‖g‖² − Σ_{b∈B_{N₀}}⟨g, K_b g⟩ (E6Bridge32 `re_arch_integral_ge`, verbatim), then bound λ_max(ΣK_b) on c^⊥ | truncated form positive only for N₀ ≥ 15 at (log 2)/2 (table below) | rejected (below) |
| Q: CC Q-trick + sine Galerkin | g = h' − h/2 ⇔ pole-free; symbol (r² + 1/4)(psiR − log π) on h ∈ H¹₀; −Δ diagonal in the sine basis | sharp in principle | rejected (below) |
| J: Q-trick + Jensen + Wirtinger | the symbol σ_{N₀}(r) = (r² + 1/4)(phi_{N₀}(r) − log π) is convex in r²; tangent line at (π/2L)² plus Wirtinger | π/(2 r₀) → 0.2497; 0.2328 at N₀ = 10, 0.2438 at N₀ = 20 | intermediate candidate; needs Wirtinger (not in Mathlib) |
| **B: CS caps + bathtub** | \|ĝ(r)\|² ≤ ‖g‖² D(r)², D² = min_c ∫\|e^{iru} − c e^{−u/2}\|²; fill the low-psiR region first | exact 0.3053; Lean-faithful 0.28 (+0.042) or 0.29 (+0.0085) | **intermediate rung** |
| **R: r-space floors + Taylor moments + Bessel + LDLᵀ** | step minorant of psiR; low frequencies through M Legendre moments; a finite certificate | closes at (log 2)/2 with margin 0.0145 to 0.028 | **full rung** |

**Route U truncation data.**  This is the truncated form λ_min at L = (log 2)/2, one condition,
from `polefree_numerics.py` (2):

| N₀ | λ_min |
|---|---|
| 0 | −1.77 |
| 5 | −0.184 |
| 10 | −0.0355 |
| 15 | +0.0097 |
| 20 | +0.0299 |
| 30 | +0.0478 |
| 40 | +0.0555 |

**Why route U is rejected.**
* The truncation phi_{N₀} loses about 1/N₀ of a margin of only 0.072.
* What remains is an *upper* bound on the top eigenvalue of a sum of 16 to 40 exponential kernels with b up to 80.  Galerkin gives lower bounds on eigenvalues, so an upper bound needs a tail lemma.
* The large-b kernels have boundary layers of width 1/b that polynomial or degenerate-kernel tails cannot capture.

**Why route Q is rejected.**
* The sine basis needs Parseval for sine series, which is AddCircle Fourier plus odd extension.
* Its K_b entries carry the transcendental π/log 2.
* Its tail suffers from the same boundary layers.
* It offers nothing route R does not, at higher analytic cost.

**Why R for the full rung.**  Every analytic ingredient is one-dimensional and already on the
island or in Mathlib:
* Plancherel `integral_hsq`;
* the psiR floor pattern `psiR_ge_rational` plus `psiR_mono`;
* `sq_l1_le`;
* `Complex.exp_bound'`.

All transcendental numbers enter through four scalar bounds: γ, log π, π, and the psiR floors.
Everything else is exact rational data.

**Why B for the intermediate rung.**  It needs no matrix and reuses the CakeW layer cake almost
verbatim.  Its new analysis is a Cauchy-Schwarz cap and Taylor bounds for sin, cos and sinh.  It
reaches 0.28 to 0.29, against about 0.24 for J, and J would also need Wirtinger.  B and R share
the floors, the pole-free plumbing and the assembly.

### 2.1 Route R: the inequality chain (full rung)

Parameters (config A/B): L = L₁ = 1733/5000, grid r_j = j/4 for j = 0..120 (R = r_J = 30),
M = 36, η = 1/10000, ρ = 1000, κ = 1524601/1000000.

Notation:
* m̃_k := ∫ g(u) P_k(u/L) du, the Legendre moments (k < M).
* w_k := (2k+1)/(2L).
* t^j = Σ_k S_{jk} P_k(t), with S = T⁻¹, where T_{kj} is the coefficient of t^j in P_k.
* Q_k(r) := Σ_{j ≡ k (2)} (−1)^{(j−k)/2} (rL)^j S_{jk}/j!, a real polynomial of parity k.
* q_k(r) := i^k Q_k(r).

* **(S1) floors.**  f_j ≤ psiR(r_j), with f_j = the `psiR_ge_rational r_j 40 10^6` value rounded
  down to 1e-6 (γ ≤ 0.58112).  By `psiR_mono`, psiR(r) ≥ f_j for |r| ≥ r_j.  Set
  s_j := f_j − LOGPI_UP and d_j := s_J − s_j ≥ 0.
* **(S2) step minorant + Plancherel.**
  Q(g) ≥ s_J·mass − (1/2π) Σ_{j<J} d_j ∫_{r_j ≤ |r| < r_{j+1}} hsq g.
* **(S3) Taylor.**  For |r| ≤ R:
  `paperFT g r = Σ_k q_k(r) m̃_k + E(r)` with `‖E(r)‖ ≤ 2·l1 g·(|r|L)^M/M!`.
  This is `Complex.exp_bound'` at x = i r u, with side condition |x|/(M+1) ≤ 1/2, i.e.
  R·L ≤ (M+1)/2 (10.4 ≤ 18.5 ✓), plus the identity u^j = L^j Σ_k S_{jk} P_k(u/L).
* **(S4) split.**  |a + b|² ≤ (1+η)|a|² + (1+1/η)|b|².  Integrated over the bands:
  `(1/2π) Σ d_j ∫_band hsq ≤ (1+η)·(1/2π)·m̃* Zs m̃ + (1+1/η)·EPS·mass`.
  * Zs_{kl} = 2 i^{l−k} Σ_{a,b} Q_k[a] Q_l[b] μ_{a+b} when k + l is even, and 0 otherwise.  It
    is real, symmetric, and block-diagonal by parity.
  * μ_n = Σ_j d_j (r_{j+1}^{n+1} − r_j^{n+1})/(n+1).
  * EPS = 4·2L/(2π_lo)·2 L^{2M} Σ_j d_j (r_{j+1}^{2M+1} − r_j^{2M+1}) / ((2M+1)(M!)²).
  * EPS uses l1² ≤ 2L·mass (`sq_l1_le`).  Value: EPS = 7.9e-13.
* **(S5) Bessel.**  mass g ≥ Σ_k w_k |m̃_k|².
* **(S6) constraint.**  c_k := q_k(i/2) = Σ_j (−L/2)^j S_{jk}/j!, which is rational.  From
  paperFT g (I/2) = 0 and `exp_bound'` at x = −u/2:
  |Σ_k c_k m̃_k| ≤ l1·DELTA, with DELTA = 2(L/2)^M/M! = 2.1e-69.
* **(S7) certificate.**  C := 2π_lo κ W + 2π_lo ρ c cᵀ − (1+η) Zs ⪰ 0, where W = diag(w) and
  π_lo = 3.14159.  This gives (1+η)(1/2π) m̃* Zs m̃ ≤ κ Σ w_k|m̃_k|² + ρ|cᵀm̃|².
* **(S8) margin.**  Q(g) ≥ (s_J − κ − (1+1/η)EPS − 2Lρ·DELTA²) mass.
  * Config A: s_J = 1.539149, margin = 0.014548.
  * Config B: s_J = 1.552649, margin = 0.028048.

**Validation (`validate.py`, float, independent of the exact build).**  The checks were run on
the u-space minimiser and on six random smooth pole-free tests.  All 28 checks pass for config A
and for config B:
* the Taylor error is within its bound (4e-8 against 1.7e-5);
* Bessel holds (ratio 1.000000);
* (S7) holds (1.5197 ≤ 1.5246 on the minimiser);
* the step form on the minimiser is 0.0206 ≥ 0.0145.

### 2.2 Route B: the inequality chain (intermediate rung)

* **(B-a) cap.**  For pole-free g and any c ∈ ℂ, ĝ(r) = ∫ g(u)(e^{iru} − c e^{−u/2}) du.
  Cauchy-Schwarz on [−L, L] with the optimal c = A(r)/(2 sinh L), where
  A(r) = ∫_{−L}^{L} e^{(ir − 1/2)u} du, gives
  |ĝ(r)|² ≤ mass·D(r)², with
  D(r)² = 2L − |A|²/(2 sinh L) = 2L − 2(sinh²(L/2) + sin²(rL)) / ((r² + 1/4) sinh L).
  This uses |sinh(x + iy)|² = sinh²x + sin²y.
* **(B-b) sub-band caps.**  On [a, b] (a ≥ 0), D(r)² ≤ S(a, b) := min(S₁, S₂), where:
  * S₁ = 2L − 2(SH2 + m(a, b)) / ((b² + 1/4)·SHL).
    * m is a lower bound for sin²(rL) on the band.  It uses T7(x) = x − x³/6 + x⁵/120 − x⁷/5040 ≤ sin x on [0, π/2], sin x = sin(π − x), and the minimum of the endpoints by concavity on [0, π].  m = 0 past π.
  * S₂ = 2L − 2X/SHL, with
    X = L² + (SH2 − L²/4)/(b² + 1/4) − (bL)⁴/3/(b² + 1/4) + 2(aL)⁶/45/(a² + 1/4) − (bL)⁸/315/(b² + 1/4).
    * This comes from sin²x ≥ x² − x⁴/3 + 2x⁶/45 − x⁸/315 for all real x, which follows from cos y ≤ 1 − y²/2 + y⁴/24 − y⁶/720 + y⁸/40320.
    * Each piece is monotone on the band.  S₂ is cancellation-aware and is the one that matters at small r, where D² ≈ L³/6.
  * SH2 = (x + x³/6 + x⁵/120 + x⁷/5040)² with x = L/2, so SH2 ≤ sinh²(L/2).
  * SHL = L + L³/6 + L⁵/120 + 1.6·L⁷/5040, so SHL ≥ sinh L.
* **(B-c) cumulative caps.**  C_k := Σ over sub-bands below ρ_k of 2S(b − a), so
  ∫_{|r|<ρ_k} hsq ≤ C_k·mass.
* **(B-d) layer cake.**  This is CakeW with the window bound 2ρS replaced by C_k.  For K with
  C_K ≤ 2π_lo:
  (1/2π) ∫ hsq·psiR ≥ mass·[φ_K − (1/(2π_lo)) Σ_{k ≤ K} (φ_k − φ_{k−1}) C_k].
* **(B-e) instance.**  L = 7/25, floors every 1/4 on [0, 10.5] (43 floors, `psiR_ge_rational`
  N = 40), 4 sub-bands per floor band (168 used), LOGPI_UP = 1.159.
  BOUND = +0.042052 (exact rational).

**Validation.**
* Every rational cap dominates the sampled exact D² (min(S − D²) = +2.8e-9).
* On 20 random pole-free tests, C_k‖g‖² − ∫_{|r|<ρ_k} hsq ≥ +1.5e-6 for every k.
* For Lean, round each sub-band cap *up* to a 1e-9 grid.  The exact cumulative sums have
  thousand-digit denominators.

## 3. Certificates

### 3.1 Full rung (route R): exact data the Lean side needs

| datum | what | size (config A/B) | how produced | how Lean gets it |
|---|---|---|---|---|
| grid r_j | j/4, j = 0..120 | 121 rationals | fixed | literal |
| floors f_j | `psiR_ge_rational r_j 40 10^6` rounded down to 1e-6 | 121 | exact in script, arb-checked | 121 one-line lemmas `le_trans _ (psiR_ge_rational ...); norm_num` (the E6Bridge30:428 pattern) |
| LOGPI_UP | 1.159 (A) or 1.1455 (B) | 1 | | A: `log_pi_le` (exists).  B: new 3-term series lemma (§4) |
| Legendre table T | coefficients of P_0..P_35 | ≈ 340 nonzero rationals | Bonnet recurrence | computable `def` in Lean (recurrence), checked by `decide` |
| S = T⁻¹ | monomial → Legendre | ≈ 340 nonzero | exact inverse | data, check `T * S = 1` by `decide +kernel` |
| Q_k, c_k | Taylor-in-Legendre polynomials, constraint vector | 36 polys of degree < 36; 36 rationals | formulas in §2.1 | computable from S and L |
| μ_n, Zs | band moments n < 72; 36×36 symmetric matrix | about 660 nonzero entries, each a sum of up to 324 products | exact | computable `def`; equality to the integral is the analytic lemma R6 |
| κ, η, ρ | 1524601/10⁶, 1/10⁴, 10³ | 3 | chosen | literals |
| certificate | C − δI = L̃ D̃ L̃ᵀ rounded (entries to 1e-12) + residual diagonally dominant, slack 0.0139 | 630 L̃ entries + 36 D̃, ≤ 30 digits each | `cert_exact.py` → `cert_A.json`, `cert_B.json` | literal data; check by a reflective Bool checker under `decide +kernel` |
| EPS, DELTA | 7.9e-13 and 2.1e-69 upper bounds | 2 | exact | `norm_num` on the closed forms (factorials of 36) |

**Certificate format.**  The check is pure ℚ arithmetic.  A sound reflective checker
`certOK : CertData → Bool` should test three things:
1. C = 2π_lo κ W + 2π_lo ρ ccᵀ − (1+η)Zs, computed from the data.
2. Res := C − L̃D̃L̃ᵀ, with all D̃_i ≥ 0.
3. Res_ii ≥ Σ_{j≠i} |Res_ij| for every i.

Soundness lemma: `certOK d = true → ∀ m : Fin M → ℂ, 0 ≤ re (star m ⬝ C ⬝ m)`.  The proof is
Σ D̃_i|(L̃ᵀm)_i|² plus Gershgorin.  The project already kernel-checks rational PSD data with
`decide +kernel` (the P-vs-NP ladder: Petersen in about 20 s; `decide +kernel` reduces `Rat`).
`native_decide` is NOT allowed: the axiom gate is exactly [propext, Classical.choice, Quot.sound].

**Tail lemma, i.e. the high frequencies.**  There is no separate eigenvalue tail.  For
|r| ≥ R the step minorant is the constant s_J, and Plancherel (`integral_hsq`) supplies all of
the mass.  Every function's high-frequency part is therefore credited at s_J = 1.539 (A).  The
finite matrix carries only the band-limited correction on |r| < R.  The relaxation error is
controlled by EPS through the Taylor remainder.  Bessel is the only place where "the rest of g"
appears, and it enters with the right sign.

**Runtime.**  The build takes 0.2 s, the exact LDLᵀ 1.7 s, and the rounded certificate 2.5 s,
in python-flint.  The first prototype (R = 40, M = 56, 160 bands) closed with margin 0.0335
(log π ≤ 1.1448) in 26 s.

**Robustness and choice of parameters** (`explore.py`; margins with log π ≤ 1.159):
* R = 20, h = 1/4: +0.0035.
* R = 24, h = 1/4: +0.0098 (M ≥ 32).
* R = 30, h = 1/4: +0.0155 (M ≥ 36).
* R = 40, h = 1/4: +0.0203 (M ≥ 44).
* h = 1/2 fails at R ≤ 30.  Geometric coarsening at high r also fails, because the minimiser
  has real spectral mass at r ~ 10 to 30.
* M is set by R·L ≤ (M+1)/2 and by EPS being negligible.
* Loss budget from the true 0.0723:
  * clipping at R = 30 costs about 0.014;
  * the step discretisation costs about 0.024;
  * the floor slack is about 0.008 (γ bound 0.0039, plus the serG tail at large r);
  * log π costs 0.0142 (A) or 0.0007 (B).

### 3.2 Intermediate rung (route B): data

* 43 floors, as above but on [0, 10.5].
* 168 sub-band caps S(a, b), each a closed rational expression in (a, b, L) plus T7 values.
* 43 cumulative sums C_k.
* One final rational inequality.

There is no matrix.  The full data is in `intermediate_L7_25.json`.

## 4. Lemma DAG, module split, sizes

Estimated sizes are Lean lines, by analogy with E6Bridge31-34 (3119 lines for the L ≤ 1/10
result).  "Reuse" names island lemmas; "new" is new analysis.

**E6Bridge35: shared pole-free plumbing and floors.**  About 350 lines plus floor data.
* `paperFT_I_half_eq` (20 lines).
* `re_archSide_poleFree` (40 lines): Re archSide = −log π·mass + (1/2π)∫ hsq·psiR.  Reuses `archSide_autocorr_poleFree`.
* `support_mono_L1` (20 lines): 2L ≤ log 2 ⇒ tsupport ⊆ [−L₁, L₁].  Uses `Real.log_two_lt_d9`.
* The floor family `psiR_floor_q (j)` for the 121 (R) and 43 (B) grid points.  Each is about 4 lines, all generated.
  * The B-grid floors are a subset of the R-grid floors.
  * Reuses `psiR_ge_rational`, `eulerMascheroni_le`.
* `log_pi_le_tight` (40 lines, optional; needed for config B): log π ≤ 1.1455.
  * Write log π = 2 log 2 + log(1 − x) with x = 1 − π/4 ∈ [0.2146, 0.2147].
  * Use −log(1−x) ≥ x + x²/2 + x³/3, i.e. Mathlib `Real.abs_log_sub_add_sum_range_le` or the derivative argument, together with `Real.log_two_lt_d9` and `Real.pi_gt_d6`.

**E6Bridge36: step minorant (R) and generalised layer cake (B).**  About 250 lines.
* `integral_hsq_mul_psiR_ge_step` (120 lines, new, generic over a finite grid): given
  0 = r₀ < … < r_J, f_j ≤ psiR r_j, and f_j ≤ f_J,
  ∫ hsq·psiR ≥ f_J ∫ hsq − Σ_j (f_J − f_j) ∫_{r_j ≤ |r| < r_{j+1}} hsq.
  * Pointwise step ≤ psiR by `psiR_mono`, then `integral_mono`, then linearity over indicators.
* `cakeW_step_gen` (50 lines): `cakeW_step` with `hwin : ∫ r in Ioo (−ρ') ρ', μ r ≤ C` in place of `hμS`.  A copy-edit of E6Bridge31:453.

**E6Bridge37: Taylor-moment representation (R).**  About 500 lines plus generated data.  Parallel agent A.
* `legP`, `legS`, `taylorQ`, `consC` (100 lines): computable ℚ data and its `decide` checks.
* `paperFT_taylor` (90 lines, new): for real r with |r|·L ≤ (M+1)/2 and tsupport ⊆ [−L, L],
  ‖paperFT g r − Σ_{j<M} (I r)^j/j! ∫ g u^j‖ ≤ 2·l1 g·(|r|L)^M/M!.
  Uses `Complex.exp_bound'` inside the integral.
* `taylor_legendre` (120 lines): for z : ℂ, Σ_{j<M} (I z)^j/j! ∫ g u^j = Σ_k (I^k Q_k(z)) m̃_k.
  This is a polynomial identity from the data.  State it for complex z, so the same lemma serves the constraint at z = I/2.
* `constraint_small` (50 lines): paperFT g (I/2) = 0 ⇒ ‖Σ c_k m̃_k‖ ≤ l1 g·DELTA.
* `normSq_add_le_split` (15 lines).

**E6Bridge38: band integrals, EPS, Bessel (R).**  About 450 lines.  Parallel agent B.
* `band_integral_quadform` (180 lines, the heaviest symbolic lemma):
  Σ_j d_j ∫_{r_j ≤ |r| < r_{j+1}} ‖Σ_k I^k Q_k(r) m̃_k‖² = re(Σ_{kl} conj m̃_k Zs_kl m̃_l).
  * Polynomial integration on intervals via `integral_pow` and linearity.
  * Odd-parity cross terms cancel over the symmetric bands.
* `band_integral_taylor_err` (60 lines): the EPS bound, via `sq_l1_le`.
* `bessel_legendre` (120 lines): mass g ≥ Σ_k (2k+1)/(2L)‖m̃_k‖².
  * Expand 0 ≤ ∫_{[−L,L]} ‖g − Σ a_k P_k(u/L)‖² with a_k = w_k m̃_k.
  * Orthogonality ∫_{−1}^{1} P_j P_k = δ_jk·2/(2k+1) is checked on the data as one matrix identity by `decide +kernel`.
* `exp_bound` side conditions (30 lines).

**E6Bridge39: certificate (R).**  About 200 lines plus data (`cert_A.json` / `cert_B.json`).  Parallel agent C.
* `certOK` checker and its soundness (Gershgorin + LDLᵀ, generic) (150 lines).
* `certA_ok : certOK certA = true` by `decide +kernel`.  This is the main compile-time risk (§5).

**E6Bridge40: assembly (R).**  About 250 lines.
* `re_archSide_ge_margin_L1` (150 lines): chains S1-S8 at L₁, with the margin as a rational.
* `weil_positivity_poleFree_window`, `primeFreeWindowPositivityPoleFree_holds` (60 lines).
* AxiomGuard entries (10 lines).

**E6Bridge41: intermediate rung (B).**  About 600 lines plus data.  Parallel agent D, who can start at once.
* `paperFT_poleFree_cs` (80 lines): ‖paperFT g r‖² ≤ mass g·∫_{[−L,L]} ‖e^{iru} − c e^{−u/2}‖².
  Cauchy-Schwarz via Mathlib `inner_mul_le_norm_mul_norm` on L², or `integral_mul_le_Lp_mul_Lq_of_nonneg`.
* `D2_closed_form` (120 lines): with the optimal c, the integral equals
  2L − 2(sinh²(L/2) + sin²(rL))/((r² + 1/4) sinh L).
  Uses the complex exponential integral on an interval and |sinh(x + iy)|².
* `sin_sq_ge_poly8`, `sin_ge_T7`, `sinh_bounds` (150 lines).
  * Taylor bounds by the derivative-monotonicity induction, in the style of Mathlib `sin_ge_sub_cube`.
  * Mathlib provides `sin_ge_sub_cube`, `one_sub_sq_div_two_le_cos` and `mul_le_sin`.  The degree-8 cos bound is new.
* `D2_le_cap` (100 lines): generic in (a, b), the two cases S₁ and S₂.
* `cum_caps_L7_25` (60 lines + data): sums with caps rounded up.
* Layer cake through `cakeW_step_gen` (43 steps), floors, final `norm_num` (100 lines).

**Dependencies:**

```
35 ──┬── 36 ──┬── 41 (intermediate, B)
     │        └───────────────┐
     ├── 37 ──┐               │
     │        ├── 38 ──┐      │
     └────────┘        ├── 40 (full, R)
              39 ──────┘
```

**Parallelism.**
* 35 and 36 come first (one agent, about 1 day).
* Then four agents run independently: 37 (A), 38 (B), 39 (C), 41 (D).
  * 38 needs only the *statements* of 37's data definitions.  Fix the data `def`s first, in a tiny shared file `ArchRungData.lean`, so that A, B and C build against the same names.
  * 39 depends on the data only and can be developed against `cert_C` (the smaller instance) first.
* 40 is the last, short step.
* Total is about 2600 lines plus generated data, comparable to E6Bridge31-34.

## 5. Risks, footguns, non-claims

**Risks.**
* **Kernel cost of the certificate check (largest risk).**
  * The Zs matrix needs about 200k big-rational operations.  Entries of Q_k carry denominators up to 35!·L^35.
  * Mitigations:
    * compute Zs inside a single reflective checker (no `norm_num` over 660 entries);
    * use config C (M = 32, 97 floors);
    * split by parity: Zs is block-diagonal into two 18×18 blocks, and only the rank-1 ρccᵀ couples them, which can be Schur-eliminated by hand;
    * if `decide +kernel` still times out, move the rational LDLᵀ to a Comparator-judged emitter.  Do this only with an explicit decision, since it changes the trust story.
* **Floor count.**  There are 121 instances of `psiR_ge_rational` with N = 40.  E6Bridge30 compiles 20 of them.  Expect several minutes of `norm_num`.  Generate the lemmas, do not hand-write them.
* **Margins are thin in absolute terms** (0.0145 for A).  Every rational bound must be the one the script used: γ ≤ 0.58112, π_lo = 3.14159, log π ≤ 1.159 or 1.1455, floors rounded to 1e-6.  Do not substitute weaker Mathlib constants (for example `Real.pi_gt_d2`) without rerunning `cert_exact.py`.
* **Precision of the hyperbolic bounds in B.**  D² at r ≈ 0 is a cancellation of size about L³/6 = 0.0037.  SH2 and SHL must be accurate to about 1e-8 relative (degree-7 Taylor).  The crude S₁ alone makes the intermediate rung fail (BOUND −0.15 at L = 0.28).

**Footguns** (from the memory note and this session):
* `simp` on `(-(b:ℂ) + I*ω).re` makes no progress under `open Complex`.  Use `simp only [Complex.add_re, …]`.
* `rw [integral_add hf hg]` fails when hf was built by `.add`.  State the integrability explicitly.
* `Integrable.mono'` needs an ℝ-valued majorant.
* `integrableOn_const` takes the finiteness autoParam positionally.
* `timeout` is not available on this macOS: do not wrap `lake build`.
* Bare `omega` cannot close a real subtraction goal.
* `decide +kernel` reduces `Rat` and plain `decide` does not.
* `gh pr edit` fails on projectCards.  Use `gh api -X PATCH`.

**Mathematical footguns.**
* The Legendre moment uses P_k(u/L), *not* the normalised φ_k.  w_k = (2k+1)/(2L).
* q_k(r) = i^k Q_k(r).  The sign (−1)^{(j−k)/2} lives in Q_k.  Zs carries the factor i^{l−k} = ±1.
* Bands are two-sided, |r| ∈ [r_j, r_{j+1}), hence the factor 2.
* `Complex.exp_bound'` needs |x|/(M+1) ≤ 1/2.  Do not use `norm_exp_sub_sum_le_norm_mul_exp`: it has no factorial and is useless here.
* The constraint is ∫ g e^{−u/2}.  Mixing the sign with ∫ g e^{+u/2} changes nothing numerically (by symmetry), but it breaks the proof of `poles_vanish`.

**What this rung does NOT give.**
* **Pole-free class only.**  The goal node `MM_weil_positivity_prime_free_window` keeps the rank-2 indefinite pole terms.  Its margin is 1.3e-3 (the zero-sum floor), and this route does not reach it.  (Correction: that full-class statement is already kernel-proved on main by `KWin_Bridge.weil_positivity_prime_free_window`, node proved/judged/granted 2026-09-24; it implies the pole-free rung as a corollary.)
* **No prime is involved.**  2L ≤ log 2 is exactly the window where `primeSide (autocorr g) = 0`.  By the gate-0 ladder, Davenport-Heilbronn passes every rung below L ≈ 1.86, so this rung cannot separate ζ from DH.  It is a statement about the Γ factor only.
* It is not semilocal positivity, it is not CC's Sonin-trace inequality (Thm 1 / 6.11), and it says nothing about zeros.

`conjecture1_proved = False`.

## 6. Reproduce

All scripts are in `telperion/research/arch_rung/`.  Set PY=~/hodge-engine/venv/bin/python.
BLAS threads are pinned to 1 inside every script.

```
$PY polefree_numerics.py 30          # §1.3 table, route-U truncation table, Jensen thresholds
$PY arb_polefree_check.py 0.34657359027997264 30 256   # arb margin (uses ~/arda-research/gate0/weil_ladder)
$PY rspace_scan.py                   # r-space cross-check, clipping/step losses, bathtub threshold 0.305
$PY cert_exact.py A                  # full-rung certificate, config A (also B, C, full) -> cert_A.json
$PY validate.py A                    # float validation of S3/S5/S7/S8 on test functions
$PY explore.py                       # margin vs (R, grid, M)
$PY intermediate_rung.py --final     # intermediate rung L = 7/25 (+ 29/100) -> intermediate_L7_25.json
```
