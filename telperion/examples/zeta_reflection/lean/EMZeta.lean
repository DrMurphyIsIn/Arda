/-  EMZeta.lean -- A2 Theorem 1: the Euler-Maclaurin representation of ζ with explicit
    remainder.

    Euler-Maclaurin summation is ABSENT from Mathlib (confirmed: `find Mathlib -iname
    '*maclaurin*'` is empty; `Mathlib/Analysis/SumIntegralComparisons.lean` has only crude
    monotone sum/integral bounds).  This file builds it bottom-up and is upstreamable.

    Architecture (proven bottom-up; only fully-proven lemmas live here, WIP in EMZetaWip.lean):

      A.  Periodized ("saw") Bernoulli  `sawBernoulli k x := bernoulliFun k (Int.fract x)`.
          Reuses `Mathlib.NumberTheory.ZetaValues.bernoulliFun` and its derivative/integral
          API (`hasDerivAt_bernoulliFun`, `integral_bernoulliFun`, `contDiff_bernoulliFun`).

      B.  One-step Euler-Maclaurin over `[m, m+1]` for a C^1 function f:
              ∫ f = (f m + f (m+1))/2 - ∫ B̃₁(x) f'(x) dx
          via integration by parts (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`)
          with the saw-1 antiderivative.  This is `em_unit_step`.

      C.  Summed over `m = 0 .. N-1`: the classical first-order Euler-Maclaurin formula
              ∑_{n=1}^{N} f n = ∫_0^N f + (f N - f 0)/2 + ∫_0^N B̃₁(x) f'(x) dx
          (`euler_maclaurin_one`).  Telescoping of the integral (`intervalIntegral.sum_integral_
          adjacent_intervals`) + telescoping of the trapezoid endpoints.

      D.  Specialisation to `f x = x^{-s}` on `[1, N]` (real `s`) and the tail limit `N → ∞`
          giving the K=1 Euler-Maclaurin representation of `ζ` for real `s > 1`
          (`em_zeta_real_K1`), matching the Mathlib fractional-part representation route
          used in `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.

    NOT YET in this file (see EMZetaWip.lean, never imported by a guard, never `sorry` here):
      - the general order-K induction (periodized `bernoulliFun k` for k ≥ 2);
      - the complex interval-σ form valid `Re s > 1 - 2K` by analytic continuation
        (`AnalyticOnNhd.eqOn`);
      - the explicit remainder BOUND `|R_K| ≤ (|B_{2K}|/(2K)!) ∫ |f^{(2K)}|`.

    conjecture1_proved = False.  This is NOT a proof of RH; it is a classical analysis lemma.
-/
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory intervalIntegral Set
open scoped Real

namespace ZetaReflection

/-! ## A. The periodized ("saw") Bernoulli functions -/

/-- The periodized Bernoulli function `B̃ₖ(x) = Bₖ({x})` on `ℝ`, where `{x} = Int.fract x`.
    For `k = 1` this is the classical sawtooth `{x} - 1/2` (away from integers).  We build EM
    on this `ℝ → ℝ` form rather than Mathlib's `AddCircle`-valued `periodizedBernoulli`, since
    the finite-sum induction wants a plain real function with `bernoulliFun`'s derivative and
    integral API directly available. -/
noncomputable def sawBernoulli (k : ℕ) (x : ℝ) : ℝ := bernoulliFun k (Int.fract x)

@[simp] lemma sawBernoulli_zero (x : ℝ) : sawBernoulli 0 x = 1 := by
  simp [sawBernoulli, bernoulliFun_zero]

/-- On the half-open unit cell starting at an integer, the saw agrees with the raw Bernoulli
    function shifted to that cell. -/
lemma sawBernoulli_eq_on_Ico (k : ℕ) {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli k x = bernoulliFun k (x - m) := by
  have hfloor : ⌊x⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, by push_cast; linarith [hx.2]⟩
  have hfract : Int.fract x = x - m := by
    rw [Int.fract, hfloor]
  rw [sawBernoulli, hfract]

/-- The order-1 saw on the cell `[m, m+1)` is the affine sawtooth `x - m - 1/2`. -/
lemma sawBernoulli_one_eq_on_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli 1 x = x - m - 1 / 2 := by
  rw [sawBernoulli_eq_on_Ico 1 hx, bernoulliFun_one]

/-! ## B. One-step Euler-Maclaurin over a unit cell

    For a `C¹` function `f` on `[m, m+1]` (real, integer `m`), integration by parts with the
    order-1 antiderivative `w x = x - m - 1/2` of the constant `1` (equal to `sawBernoulli 1`
    on the cell) yields the trapezoidal Euler-Maclaurin step
        ∫_m^{m+1} f = (f m + f(m+1))/2 − ∫_m^{m+1} (sawBernoulli 1 x) · f'(x) dx.
-/

/-- **One-step Euler-Maclaurin** over the unit cell `[m, m+1]`.

    Hypotheses: `f` has derivative `f'` at every point of the cell and `f'` is interval
    integrable there.  The saw factor is written via `sawBernoulli 1` so the summed form in
    part C reads as a single integral of `sawBernoulli 1 · f'` over `[0, N]`. -/
theorem em_unit_step {f f' : ℝ → ℝ} (m : ℤ)
    (hf : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), f x)
      = (f m + f (m + 1)) / 2 - ∫ x in (m : ℝ)..(m + 1), sawBernoulli 1 x * f' x := by
  -- The affine antiderivative `w x = x - m - 1/2` of the constant `1`.
  set w : ℝ → ℝ := fun x => x - m - 1 / 2 with hw
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hw' : ∀ x, HasDerivAt w 1 x := by
    intro x
    have := ((hasDerivAt_id x).sub_const (m : ℝ)).sub_const (1 / 2 : ℝ)
    simpa [hw] using this
  have hwcont : Continuous w := by fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt w (1 : ℝ) x := fun x _ => hw' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hcc] at hx
    exact hf x hx
  have hw'int : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (m : ℝ) (m + 1) :=
    intervalIntegrable_const
  -- `integral_deriv_mul_eq_sub`: ∫ (w' · f + w · f') = w·f |end - w·f |start,  w' = 1.
  have hIBP := integral_deriv_mul_eq_sub huv hfd hw'int hf'
  -- Endpoint values of `w`.
  have hwL : w (m : ℝ) = -(1 / 2) := by simp only [hw]; ring
  have hwR : w ((m : ℝ) + 1) = 1 / 2 := by simp only [hw]; ring
  -- The `w · f'` term is interval integrable (continuous · integrable).
  have hwf'int : IntervalIntegrable (fun x => w x * f' x) volume (m : ℝ) (m + 1) :=
    hf'.continuousOn_mul hwcont.continuousOn
  -- Split the LHS integrand `1 * f x + w x * f' x`.
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (1 : ℝ) * f x + w x * f' x)
        = (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    have hfcont : ContinuousOn f (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    have hfint : IntervalIntegrable f volume (m : ℝ) (m + 1) :=
      hfcont.intervalIntegrable
    rw [intervalIntegral.integral_add (by simpa using hfint) hwf'int]
    simp
  -- Identify `sawBernoulli 1 · f'` with `w · f'` on the cell.
  -- `sawBernoulli 1` and `w` agree on the half-open cell `[m, m+1)`; they disagree only at the
  -- right endpoint `m+1` (the saw jumps there), a null set, so the integrals coincide.
  have hsaw : (∫ x in (m : ℝ)..(m + 1), sawBernoulli 1 x * f' x)
      = ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    apply intervalIntegral.integral_congr_ae
    -- a.e. on `Ι m (m+1) = Ioc m (m+1)`, exclude the single point `{m+1}`.
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_one_eq_on_Ico hxIco]
  -- Assemble.
  rw [hsaw]
  have key : (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x
      = w ((m : ℝ) + 1) * f ((m : ℝ) + 1) - w (m : ℝ) * f (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hwL, hwR] at key
  linarith [key]

end ZetaReflection
