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

## 3. Interface with S5-S10 (module `ArchS9_Bridge`), and what is still open

**From L² to continuous: proved.**
* `continuous_representative`: suppose ξ is only interval-integrable on [0,1], for example any
  representative of an element of `Lp 2` on (0,1) as S5/S6 produce.  Suppose also T ξ = λ ξ a.e.
  on (0,1] with λ ≠ 0.
* Then ξc := T ξ / λ is continuous, satisfies T ξc = λ ξc **everywhere**, equals ξ a.e. on
  (0,1], and has ip ξc ξc = ip ξ ξ.
* The continuity step is `continuous_T_of_integrable` (dominated convergence; the kernel is
  continuous and bounded by 2).
* So every theorem below applies to S6's eigenvectors through ξc.  ξc is also CC's ξ_n^an: it
  equals ξ_n on [0,1] and is λ⁻¹ F ξ_n on (1,∞).

**Dictionary to CC (arXiv:2006.13771 (66)-(68)).**
* CC's even prolate PS on [−1,1] satisfies ∫_{-1}^{1} PS(x) e^{2πixω} dx = λ(n) PS(ω).  Restricted
  to [0,1] it is an eigenfunction of `T` with eigenvalue λ(n), because for even PS the integral
  equals ∫_0^1 2cos(2πxω) PS(x) dx.
* CC's ξ_n = PS/‖PS‖ with ‖·‖² = ∫_0^1 \|·\|² is our normalisation `ip ξ ξ = 1`.
* The θ_n are CC's **signed** λ(n): θ_0 > 0, θ_1 < 0, and so on.  They are not λ(n)².
  P₁P̂₁P₁ on even functions has the eigenvalues λ(n)² with the same eigenvectors (CC after (68)),
  and that is the operator S6 diagonalises.
* S7/S8/S10 consume λ(n)²/(1−λ(n)²), ξ_n, ξ_n′ on [1/2, 2], and ξ_n(1).  All of these are
  covered by `prolate_window` and `prolate_S8_fields`.

**Symmetry of T: proved.**  `T_symm` gives ip (T f) g = ip f (T g) for continuous f and g, by
Fubini on [0,1]².

**Completeness: proved, given S6's Parseval.**
* `psi_residual`: sup_[0,1] \|T ψ_n − θ_n ψ_n\| ≤ rhoQ = 6.72e-43, using the kernel check
  `res_ok`.
* `prolate_window_occupied`: for any orthonormal family of continuous eigenfunctions (e_k, λ_k)
  in which ψ_n satisfies Parseval (`HasSum (fun k => ip ψ_n (e k)²) (ip ψ_n ψ_n)`), some λ_k
  lies in window n.  The proof is Bessel plus T_symm: an empty window would force
  ‖ψ_n‖² ≤ ρ²/w0² < 1 − γ.
* `prolate_spectrum_complete` assembles three facts for such a family:
  1. every λ_k is either at most d0Q ≈ 9.70e-22 in absolute value, or lies in a window;
  2. each of the 13 windows contains **exactly one** k, so no eigenvalue is missing or doubled;
  3. that λ_k is within w2q n ≈ 6.7e-43 of θ_n.
* Parseval for ψ_n holds when the e_k form a complete orthonormal basis of L²(0,1).  That is
  S6's spectral theorem for the compact self-adjoint T.  **This is the only remaining input.**
  S9 does not prove that an eigenbasis exists.

**S8's `ProlateData` fields (`prolate_S8_fields`), for n ≤ 12.**  For the eigenfunction ξ of
window n:
* λ² < 1 (kernel check `lam_ok`: \|θ_n\| + w2q n < 1);
* ξ is C¹ on ℝ;
* on [0, 2] ⊇ [e^{−T}, e^T] (for T ≤ log 2), \|ξ\| ≤ MxQ n and \|ξ′\| ≤ MdQ n.

The bounds are crude.  They use absolute coefficient sums of ψ_n at 2, roughly 1e3 to 1e17
(n = 0 to 12; for example MxQ 10 ≈ 2.6e13 against a true sup of about 4.4e10).  They are good for
S8's finiteness and summability on the head, not for numerics.  S10 should evaluate the explicit
polynomials θ_n ψ_n, whose error is below 2e-25, instead of these sup bounds.

**In S8's variable (`prolate_phi_values`).**
* S8 defines phi n := λ⁻¹ · 2∫₀¹ ξ_n(y) cos(2πxy) dy, which is `fun x => T ξ x / λ`.
* For the eigenfunction of window n, Lean proves phi = ξ.  On [1/2, 2], the range S10's kernel χ
  on [0, log 2] uses, \|λ phi(x) − s θ_n ψ_n(x)\| ≤ Vq n and \|λ phi′(x) − s θ_n ψ_n′(x)\| ≤ Vdq n.
* phi_n(1) is the case x = 1.  The weight w_n = λ²/(1 − λ²) uses λ² < 1 from `prolate_S8_fields`.
* So S10 can read off phi_n and phi_n′ directly as ±θ_n ψ_n/λ, up to errors below 2e-25/\|λ\|.

**Still open.**
* The eigenbasis or Parseval input above (stage S6).
* The tail n > 12 of S8's `summable_wMN` and of CC's series (99).  S9 bounds every eigenvalue
  outside the windows by 9.70e-22.  Uniform bounds on ξ_n^an for n > 12 must come from the
  eigen-relation (\|λ ξ(ω)\| ≤ 2∫\|ξ\| ≤ 2, `abs_T_le`, and likewise for ξ′ with 4π) plus a
  B3-type bound on Σ_{n>12} λ_n².  That is S10's job; nothing in S9 blocks it.
* Slepian's PS_{2n,0}(2π,·) and the differential eigenvalues χ_n are not identified with these
  eigenfunctions.  CC's proof does not need them.  The W matrix is used only in the generator, as
  a cross-check that agrees to 15 digits.

## 4. Kernel and build times (shared machine, load about 20)

The kernel checks are split into small modules.  Each module is built alone with
`lake build <M>`.  The times are lake's per-module build times, including about 25 s of Mathlib
import overhead.  No single check comes near 10 minutes, so no precision reduction was needed.

| module | content | build time |
|---|---|---|
| ArchS9_Pi | 45-digit π bounds (80 witness steps each, norm_num) | 39 s |
| ArchS9_Analysis | analytic core | 49 s |
| ArchS9_Frame | generic frame | 42 s |
| ArchS9_Data | data elaboration (166 KB of literals) | 43 s |
| ArchS9_CertMisc | constants, 13 windows, localization, negative control | 38 s |
| ArchS9_CertE | 40 rows of E | 46 s |
| ArchS9_CertGram1 | Gram rows 0-5 (225 entries) | 87 s |
| ArchS9_CertGram2 | Gram rows 6-12 (217 entries) | 73 s |
| ArchS9_CertGram3 | Gram rows 13-21 (207 entries) | 82 s |
| ArchS9_CertGram4 | Gram rows 22-39 (171 entries) | 90 s |
| ArchS9_CertRes | residual constant ρ | 16 s |
| ArchS9_Prolate | soundness and main theorems | 37 s |
| ArchS9_Bridge | bridge, completeness, S8 fields (includes `lam_ok`) | 18-29 s |
| ArchS9_Guard | 51 `#print axioms` | 31-35 s |

The total is about 10 minutes of sequential builds.  A profiled single Gram row of 40 entries
spends 12.2 s in the kernel.  Peak memory was never an issue.

**Axioms.**  `lake env lean ArchS9_Guard.lean` prints exactly
[propext, Classical.choice, Quot.sound] for 50 declarations.  `Data.lc_ok` depends on no axioms.

**Size.**  The Lean code is 2595 lines over 15 modules; ArchS9_Data has 191 lines and 166 KB of
generated literals.  The generators are gen_s9.py (298 lines), gen_pi.py (41) and gen_s9_res.py
(12).

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
