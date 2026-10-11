# Stage S9 notes: the certified prolate engine (2026-10-11)

Branch `mm/arch-s9`, island `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2).
`conjecture1_proved = False`.  Nothing here is RH progress.

## 1. What is certified

The operator is CC's time-band limiting operator (arXiv:2006.13771, (68)) on even functions, with
c = 2π, written on [0, 1]:

    T f(ω) = ∫_0^1 2 cos(2π x ω) f(x) dx      (= ∫_{-1}^{1} f(x) e^{2πixω} dx for even f),

with CC's normalisation ∫_0^1 ξ² = 1.  Even prolates are exactly the eigenfunctions of T on even
functions: T ξ_n = λ(n) ξ_n.

For **every** continuous ξ with T ξ = λ ξ and ∫_0^1 ξ² = 1, Lean proves the following
(module `ArchS9_Prolate`):

| theorem | statement |
|---|---|
| `prolate_localization` | either \|λ\| ≤ d0Q ≈ 9.70e-22, or λ lies in one of 13 windows \|λ − θ_n\| ≤ w0q n, n = 0..12 |
| `prolate_window` | in window n: \|λ − θ_n\| ≤ w2q n ≈ 6.73e-43; (∫_0^1 ξ ψ_n)² ≥ pi1q n; and for one sign s = ±1, for every ω ∈ [0, 2], \|λ ξ(ω) − s θ_n ψ_n(ω)\| ≤ Vq n and \|λ ξ′(ω) − s θ_n ψ_n′(ω)\| ≤ Vdq n |
| `prolate_simple` | two unit eigenfunctions with eigenvalues in the same window are not orthogonal, so each window carries a one-dimensional eigenspace |

Here ψ_n (`psiS n`) is an explicit even polynomial of degree 78 with rational coefficients
(`ArchS9_Data.tabB`, integers over 10^80), and θ_n (`Data.thq n`) is an explicit rational.

Precision achieved (all kernel-checked; values from the generator log):

| n | θ_n ≈ λ(n) | eigenvalue error w2q | 1 − pi1q | Vq (λξ on [0,2]) | Vdq (λξ′ on [0,2]) |
|---|---|---|---|---|---|
| 0 | 9.9997137627e-01 | 6.73e-43 | 1.0e-39 | 4.86e-31 | 1.96e-29 |
| 1 | −9.7948473467e-01 | 6.73e-43 | 1.0e-39 | 4.86e-31 | 1.96e-29 |
| 2 | 5.2408589623e-01 | 6.73e-43 | 1.0e-39 | 4.86e-31 | 1.96e-29 |
| 3 | −5.8976589182e-02 | 6.73e-43 | 1.0e-39 | 4.86e-31 | 1.96e-29 |
| 4 | 2.7323287431e-03 | 6.73e-43 | 2.0e-39 | 4.86e-31 | 1.96e-29 |
| 5 | −7.6291359284e-05 | 6.73e-43 | 4.2e-38 | 4.86e-31 | 1.96e-29 |
| 6 | 1.4394698909e-06 | 6.73e-43 | 2.2e-36 | 4.87e-31 | 1.96e-29 |
| 7 | −1.9624451023e-08 | 6.73e-43 | 1.6e-34 | 5.07e-31 | 1.97e-29 |
| 8 | 2.0250134696e-10 | 6.73e-43 | 1.6e-32 | 7.81e-31 | 2.23e-29 |
| 9 | −1.6371179747e-12 | 6.73e-43 | 1.9e-30 | 4.71e-30 | 6.15e-29 |
| 10 | 1.0650757994e-14 | 6.73e-43 | 2.9e-28 | 6.32e-29 | 6.89e-28 |
| 11 | −5.6968131026e-17 | 6.73e-43 | 5.5e-26 | 9.60e-28 | 1.10e-26 |
| 12 | 2.5494950457e-19 | 6.73e-43 | 1.2e-23 | 1.51e-26 | 1.84e-25 |

Against the blueprint targets (section 5: λ_n to about 1e-9, ξ_n and ξ_n′ on [0, 2] to about 1e-8,
n ≤ 10):

* λ_n is certified to 6.7e-43 absolute, for n ≤ 12.
* ξ_n(ω) = (λξ)(ω)/λ.  The absolute error is at most (Vq + |θ_n ψ_n(ω)|·w2q/|θ_n|)/(|θ_n| − w2q).
  For n = 10 that is about 6e-15.  For n = 12 it is about 6e-8, because |λ_12| ≈ 2.5e-19.
* ξ_n′ is certified the same way.  For n = 10 the error is about 7e-14.
* The quantities CC actually consume, λ_n ξ_n and λ_n ξ_n′, are certified uniformly to below 2e-25
  on [0, 2].

The relation to CC's numbers: θ_0..θ_5 = 0.9999714, −0.9794847, 0.5240859, −0.0589766,
0.0027323, −7.629e-5, matching CC's values after (68) and `prolate_cc.py`.  The float64 script
is wrong from n = 10 on (it prints λ_10 ≈ 1.4e-14 and λ_11 ≈ 2.7e-14).  The certified values are
λ_10 = 1.0650757994e-14 and λ_11 = −5.6968131026e-17.

## 2. How (the design, and why it differs from the W route)

The blueprint suggested certifying eigenvectors of Slepian's commuting differential operator W in
the Legendre basis, then linking χ_n to λ_n.  That route leaves Slepian's commutation and
simplicity theorem open, which needs singular Sturm–Liouville theory.  CC consume only λ_n and
ξ_n, never χ_n.  S9 therefore certifies the integral operator T directly, so **no analytic link
remains open between the certified data and T**:

1. **Taylor split** (`ArchS9_Analysis.T_sub_le`, reusing KWin_Taylor's `cos_sub_tayl_le`).
   2cos(2πxω) = Σ_{j<40} aC_j (ωx)^{2j} + R, with \|R\| ≤ 4(2πX)^{80}/80! for ω ∈ [0, X].
   The bound is 4.0e-55 for X = 1 and 4.8e-31 for X = 2.  The polynomial part is a rank-40
   operator acting through the moments m_j(f) = ∫_0^1 x^{2j} f.
2. **Exact rank-40 decomposition** (`ArchS9_Frame.rankJ_identity`).  The generator
   eigen-decomposes the Galerkin pencil diag(aR)·Hilbert at 400 digits and rounds it to rationals.
   With E := diag(aR) − BᵀΘB, the algebraic identity
   T f = Σ_n θ_n ⟨f, ψ_n⟩ ψ_n + errF f holds for every f.  Lean bounds
   \|errF f(ω)\| ≤ (η + Σ_j\|aC_j − aR_j\| X^{2j} + Σ_{jk}\|E_jk\| X^{2j}) ∫\|f\|.
   The π-dependence of aC_j is handled by monotonicity between the endpoints of a 45-digit π
   enclosure (`ArchS9_Pi`, proved with Mathlib's sqrtTwoAddSeries witness tactic).
3. **Kernel checks** (`decide +kernel`).
   * The Gram matrix of the ψ's is within γ = 9e-81 of I (820 entries, integer arithmetic).
   * The 40 row sums of \|E\| are bounded.
   * The constants ζ, ε and C are checked, plus 13 windows (two refinement rounds each) and the
     value bounds.
4. **Elementary frame** (`ArchS9_Frame`, no spectral theorem).  For a unit eigenfunction ξ with
   p_n = ⟨ξ, ψ_n⟩:
   * (P1) \|p_n\| ≤ 1 + γ.
   * (P2) \|(λ − θ_m) p_m\| ≤ ε = 6.7e-43.
   * (P3) (\|λ\| − ζ1)² ≤ Σ θ_m² p_m² + C, by Minkowski and Cauchy–Schwarz.

   Gap arguments then give localization, the tight eigenvalue windows and p_n² ≈ 1.  The value
   formula λξ(ω) = Σ θ_m p_m ψ_m(ω) + errF ξ(ω) gives values on [0, 2], including (1, 2] (the
   eigen-relation, as the blueprint asked).  Its ω-derivative, by differentiation under the
   integral sign (`hasDerivAt_T`), gives ξ′.

The truncated W matrix is used only as a cross-check.  `prolate_cc.py` (Legendre/W route) and the
Galerkin route agree on λ_0..λ_10 to all 15 printed digits.

## 3. What is open (for S6 / S10)

* **Existence of the eigenfunctions** is not proved here.  The theorems are a-posteriori: every
  eigenfunction is localized, and within a window it is unique up to sign and certified.  That
  each window actually contains an eigenvalue needs the spectral theorem for the compact
  self-adjoint operator T (or for P₁P̂₁P₁), which is stage S6.  The certificate gives S6 what it
  needs to conclude: once an orthonormal eigenbasis {ξ_k} with Σ λ_k² = ∫∫K² is available, an
  empty window n would put θ_n's mass on eigenvalues of size at most d0Q.  (P2) together with
  the residual of ψ_n excludes that.  That short argument has not been written in Lean.
* **Regularity hypothesis.**  The theorems assume ξ is continuous on ℝ.  Any L² eigenfunction with
  λ ≠ 0 has the continuous (indeed entire) representative T ξ/λ, so S6 must hand over that
  representative.
* **Slepian's PS_{2n,0}(2π, ·)** and the differential eigenvalues χ_n are not identified with these
  eigenfunctions.  CC's proof does not need either.
* **The tail n > 12.**  `prolate_localization` bounds every other eigenvalue by
  \|λ\| ≤ 9.70e-22.  That is the input S10 needs for the B3-type tail of the series (99).
  Bounds on λ_n ξ_n for n > 12 come from the eigen-relation (\|λξ(ω)\| ≤ 2 ∫\|ξ\|), as `abs_T_le`.

## 4. Kernel and build times (shared machine, load about 20)

Filled in from the build log; see the table at the end of this file.

## 5. Lean footguns met

* The elaborator times out on one `List (List ℤ)` literal with 1600 large entries.  Split it into
  one `def` per row with `set_option maxHeartbeats 0`.
* `Fraction(q+1, 10^d).numerator` is NOT q+1 when 10 divides q+1.  The first π generator printed
  numerator/10^d, which stated a false upper bound, and the tactic reported `⊢ False` after 80
  steps.  Print q and q+1 directly.
* `convert h using 1` on HasDerivAt goals produced `instAddCommGroup = …` side goals.  Rewrite the
  derivative value with an explicit equation instead.
* `ip_sum_left` / `ip_sq_le` need the function arguments given explicitly (`(g := fun n ω => …)`).
  Otherwise unification picks `(fun x => c) * ψ` and fails.
* `(continuous_K_mul hf).comp (Continuous.prodMk_right ω)` as an IntervalIntegrable witness hit a
  200k-heartbeat isDefEq timeout in one place.  `by unfold K; fun_prop` is instant.
* `decide +kernel` on `Finset.sum (range 40)` over `List.getD` data is fast enough: one Gram row of
  40 entries, each a 1600-term sum of 100-digit integer products, takes 12 s.
