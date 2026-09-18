/-
RvMBraggBridge — MIRRORMERE W3b (the Bragg bridge): the finite-height explicit formula,
DIFFRACTION FORM.

The scoping doc `GW_OS_BRAGG_SCOPING_2026-09-12.md` §3 asks for the kernel-verified statement
that the finite-volume diffraction pattern of the certified zeta zeros has its prime side equal
to an explicit sum of Bragg oscillations at the log-prime-power frequencies.  `RvMDiffractionCore`
already supplies the two structural bricks:

  * `rect_explicit_formula` (brick 6) — the finite Guinand–Weil identity for a box with right edge
    in `Re > 1`: `2πi·Σ_ρ d(ρ)·g(ρ) = (bottom) − (top) − i·Σ'_n ∫ g·term(Λ,·,n) − i·(left)`, with the
    right (prime) edge carried term-by-term in von Mangoldt.
  * `integral_vonMangoldt_term` (brick 7) — the closed form of each prime-power edge integral:
    for `n ≥ 2`, `∫_{T0}^{T1} term(Λ,σ+iy,n) dy = (term(σ+iT1) − term(σ+iT0))/(−i·log n)`, a pure
    oscillation of frequency `log n` (nonzero exactly at prime powers, amplitude `Λ(n)·n^{−σ}/log n`).

This file WELDS them.  Specialize the explicit formula to the DIFFRACTION WEIGHT `g ≡ 1` (the
counting weight — the zero side becomes the box divisor count, exactly the finite diffraction
functional `F_T` of §3), and substitute the closed form term-by-term.  The result:

  `rect_bragg_prime_edge` — the `g ≡ 1` right edge IS `Σ'_n braggTerm n`, an explicit atomic comb;
  `rect_explicit_formula_bragg` — THE BRIDGE: the finite explicit formula in diffraction form,

      `2πi · (box zero-count)  =  (bottom edge) − (top edge)
                                   − i · Σ'_n braggTerm(σ₁,T0,T1,n)
                                   − i · (left edge)`,

    the zero side an integer count of ζ-zeros (with multiplicity), the prime side an explicit,
    closed-form Bragg comb, the two horizontal edges + the left edge carried as HONEST remainders
    (no limit taken — the finite form).  `braggTerm n = 0` for `n ∈ {0,1}` and for every non-prime-
    power `n` (`Λ(n) = 0`), so the comb is supported exactly on `{log p^k}` — the Bragg peaks.

This is the diffraction-form finite explicit formula: kernel-verified, unconditional, over ζ's
ACTUAL divisor in the box (nothing assumed about the zeros).  The classical `T → ∞` limit — which
would send the horizontal remainders to zero against a decaying test weight — is NOT taken here;
it needs the `|ζ′/ζ| = O(log² T)` zero-avoiding-corridor bound, flagged in the scoping doc as a
separate campaign.  The remainders stand as explicit integrals.  conjecture1_proved = False.
-/
import Mathlib
import RvMDiffractionCore

open Complex MeasureTheory Real
open scoped Topology

namespace DiffractionCore

/-- **The Bragg oscillation term** (diffraction weight `g ≡ 1`): the closed-form value of the
    `n`-th prime-power edge integral `∫_{T0}^{T1} term(Λ, σ₁+iy, n) dy`.  A pure oscillation of
    frequency `Real.log n`, amplitude governed by `Λ(n)·n^{−σ₁}/log n`; zero unless `n` is a prime
    power (`Λ(n) = 0` otherwise) and zero for `n ∈ {0,1}`.  These are the Bragg peaks of the finite
    diffraction pattern, prime-side, in explicit arithmetic form. -/
noncomputable def braggTerm (sigma1 T0 T1 : ℝ) (n : ℕ) : ℂ :=
  (LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) ((sigma1 : ℂ) + T1 * I) n
      - LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) ((sigma1 : ℂ) + T0 * I) n)
    / (-(I * (Real.log n : ℂ)))

/-- `braggTerm` vanishes at `n = 0`: `LSeries.term _ _ 0 = 0`. -/
theorem braggTerm_zero (sigma1 T0 T1 : ℝ) : braggTerm sigma1 T0 T1 0 = 0 := by
  simp [braggTerm, LSeries.term_zero]

/-- `braggTerm` vanishes at `n = 1`: `Λ(1) = 0`. -/
theorem braggTerm_one (sigma1 T0 T1 : ℝ) : braggTerm sigma1 T0 T1 1 = 0 := by
  simp only [braggTerm]
  rw [LSeries.term_of_ne_zero (by norm_num), LSeries.term_of_ne_zero (by norm_num)]
  simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- `braggTerm` vanishes off the prime powers: `Λ(n) = 0` when `n` is not a prime power, so both
    `LSeries.term`s vanish.  The comb is supported exactly on `{n : IsPrimePow n}` — the Bragg
    peaks at `k·log p`. -/
theorem braggTerm_eq_zero_of_not_isPrimePow (sigma1 T0 T1 : ℝ) {n : ℕ}
    (hn : ¬ IsPrimePow n) : braggTerm sigma1 T0 T1 n = 0 := by
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℂ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply]
    simp [hn]
  simp only [braggTerm]
  by_cases h0 : n = 0
  · simp [h0, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero h0, LSeries.term_of_ne_zero h0, hΛ]
    simp

/-- **The diffraction-weight (`g ≡ 1`) right edge is the Bragg comb.**  Along the right edge
    `Re = σ₁ > 1`, the term-by-term prime expansion of `rect_explicit_formula` collapses (weight
    `1`) to the explicit sum of closed-form Bragg oscillations `Σ'_n braggTerm n`.  Each summand is
    `integral_vonMangoldt_term` (brick 7); the `n ∈ {0,1}` terms both vanish. -/
theorem rect_bragg_prime_edge (sigma1 T0 T1 : ℝ) :
    (∑' n : ℕ, (∫ y in T0..T1,
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            ((sigma1 : ℂ) + ↑y * I) n))
      = ∑' n : ℕ, braggTerm sigma1 T0 T1 n := by
  refine tsum_congr fun n => ?_
  -- case on n: 0, 1, or ≥ 2
  match n with
  | 0 =>
      rw [braggTerm_zero]
      simp [LSeries.term_zero]
  | 1 =>
      rw [braggTerm_one]
      have : (fun y : ℝ =>
          LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) ((sigma1 : ℂ) + ↑y * I) 1)
          = fun _ : ℝ => (0 : ℂ) := by
        funext y
        rw [LSeries.term_of_ne_zero (by norm_num)]
        simp [ArithmeticFunction.vonMangoldt_apply_one]
      rw [this, intervalIntegral.integral_zero]
  | (Nat.succ (Nat.succ k)) =>
      have hn2 : 2 ≤ k + 2 := by omega
      rw [integral_vonMangoldt_term sigma1 T0 T1 hn2]
      rfl

/-- **THE BRAGG BRIDGE — the finite-height explicit formula in diffraction form.**

    Specializing `rect_explicit_formula` to the diffraction weight `g ≡ 1` (the counting weight):
    the LEFT (zero) side is `2πi` times the box zero-count of ζ over its ACTUAL divisor (with
    multiplicity), and the RIGHT edge is the explicit closed-form Bragg comb `Σ'_n braggTerm n`
    (supported on prime powers).  The two horizontal edges and the left edge are carried as HONEST
    explicit remainders — no `T → ∞` limit is taken (that needs the `|ζ′/ζ| = O(log² T)` corridor
    bound, out of scope).

      `2πi · Σ_ρ d(ρ)  =  (bottom edge) − (top edge)  −  i·Σ'_n braggTerm(σ₁,T0,T1,n)  −  i·(left edge)`

    This is the diffraction functional of §3 at finite height, kernel-verified and unconditional.
    conjecture1_proved = False. -/
theorem rect_explicit_formula_bragg
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1) (hσ1 : 1 < sigma1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    2 * ↑π * I * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ)
      = (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        - I • (∑' n : ℕ, braggTerm sigma1 T0 T1 n)
        - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I)) := by
  -- The explicit formula at the diffraction weight `g ≡ 1`.
  have hEF := rect_explicit_formula sigma0 sigma1 T0 T1 hsig hT hσ1 c R hbox_ball hs1
    (fun _ => (1 : ℂ)) isOpen_univ (differentiableOn_const 1) (Set.subset_univ _)
    hnzb hnzt hnzl hins
  -- Collapse the `g ≡ 1` factors on every edge (bottom, top, left) and reindex the prime edge.
  simp only [one_mul] at hEF
  -- The zero side: `d(ρ)·1 = d(ρ)`.
  have hzero : ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) * 1)
      = ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) := by
    refine Finset.sum_congr rfl fun ρ _ => by rw [mul_one]
  rw [hzero] at hEF
  -- The prime edge: replace the term-by-term integral with the closed-form Bragg comb, inside hEF.
  rw [rect_bragg_prime_edge sigma1 T0 T1] at hEF
  exact hEF
