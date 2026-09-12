/-
RvMBacklundPartition — Backlund S(T)=O(log T), PR 4b: the partition + sum.

Two steps that turn the per-piece confinement (PR 4a) into the counted bound.

  * `argChangeHoriz_abs_lt_pi_of_re_sign` — the confinement bound `|argChangeHoriz f| < π` holds when
    `Re f` is one sign on the segment, POSITIVE *or* NEGATIVE.  On a `Re f < 0` piece we apply PR 4a to
    `-f` (which has `Re > 0`); the net argument change is unchanged because `logDeriv (-f) = logDeriv f`
    (`logDeriv_const_mul` with `a = -1`).  This is exactly what lets us use the `F_T` sign-change
    partition of `[1/2,2]`, where `Re ζ` alternates sign but is nonzero on each open piece.

  * `argChangeHoriz_abs_le_partition` — given a partition `σ 0 < σ 1 < … < σ n` with `logDeriv f`
    integrable on each piece and `|argChangeHoriz f T (σ k) (σ (k+1))| ≤ π` on each, the total
    `|argChangeHoriz f T (σ 0) (σ n)| ≤ n·π`.  Proof: integral additivity
    (`sum_integral_adjacent_intervals`) makes the total the sum of the pieces; triangle inequality
    (`Finset.abs_sum_le_sum_abs`) + the per-piece `≤ π` gives `n·π`.

Composed: partitioning `[1/2,2]` at the `≤ count` zeros of `F_T` (PR 3b) into `≤ count+1` pieces, each
with `|argChangeHoriz ζ| < π`, gives `|argChangeHoriz ζ T 2 (1/2)| ≤ π·(count+1)` — the horizontal half
of Backlund's `S(T)` bound.  Constructing that specific partition from `F_T`'s finite zero set (and
counting it) is PR 4c; this file is the reusable summation engine.  conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundConfine

open Complex MeasureTheory intervalIntegral

namespace Backlund

/-- **Either-sign confinement.**  If `Re f` is one sign (positive *or* negative) all along the
    horizontal segment, the net argument change is `< π` in absolute value.  The `Re f < 0` case
    reduces to PR 4a via `f ↦ -f` (`logDeriv` is invariant, so `argChangeHoriz` is unchanged). -/
theorem argChangeHoriz_abs_lt_pi_of_re_sign (f : ℂ → ℂ) (T x0 x1 : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) (Set.uIcc x0 x1))
    (hsign : (∀ x ∈ Set.uIcc x0 x1, 0 < (f ((x : ℂ) + (T : ℂ) * I)).re) ∨
             (∀ x ∈ Set.uIcc x0 x1, (f ((x : ℂ) + (T : ℂ) * I)).re < 0)) :
    |DiffractionCore.argChangeHoriz f T x0 x1| < Real.pi := by
  -- logDeriv is invariant under `f ↦ -f`
  have hln : ∀ w : ℂ, logDeriv (fun z => -f z) w = logDeriv f w := by
    intro w
    simpa [neg_one_mul] using logDeriv_const_mul (f := f) w (-1 : ℂ) (by norm_num)
  rcases hsign with hpos | hneg
  · exact argChangeHoriz_abs_lt_pi_of_rePos f T x0 x1 hdiff hcont hpos
  · -- apply PR 4a to `-f`, then transport back along `logDeriv (-f) = logDeriv f`
    have hdiff' : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℂ (fun z => -f z) ((x : ℂ) + (T : ℂ) * I) :=
      fun x hx => (hdiff x hx).neg
    have hcont' : ContinuousOn (fun x : ℝ => logDeriv (fun z => -f z) ((x : ℂ) + (T : ℂ) * I))
        (Set.uIcc x0 x1) := hcont.congr (fun x _ => hln _)
    have hpos' : ∀ x ∈ Set.uIcc x0 x1, 0 < ((fun z => -f z) ((x : ℂ) + (T : ℂ) * I)).re := by
      intro x hx; simp only [Complex.neg_re]; exact neg_pos.mpr (hneg x hx)
    have h4 := argChangeHoriz_abs_lt_pi_of_rePos (fun z => -f z) T x0 x1 hdiff' hcont' hpos'
    -- argChangeHoriz (-f) = argChangeHoriz f  (same integrand)
    have harg : DiffractionCore.argChangeHoriz (fun z => -f z) T x0 x1
        = DiffractionCore.argChangeHoriz f T x0 x1 := by
      unfold DiffractionCore.argChangeHoriz
      exact congrArg Complex.im (intervalIntegral.integral_congr (fun x _ => hln _))
    rwa [harg] at h4

/-- **Partition summation.**  Over a partition `σ 0 < σ 1 < … < σ n`, if `logDeriv f` is integrable on
    each piece and the argument change on each piece is `≤ π`, then the total argument change over
    `[σ 0, σ n]` is `≤ n·π`. -/
theorem argChangeHoriz_abs_le_partition (f : ℂ → ℂ) (T : ℝ) (σ : ℕ → ℝ) (n : ℕ)
    (hint : ∀ k < n, IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I))
              volume (σ k) (σ (k + 1)))
    (hpiece : ∀ k < n, |DiffractionCore.argChangeHoriz f T (σ k) (σ (k + 1))| ≤ Real.pi) :
    |DiffractionCore.argChangeHoriz f T (σ 0) (σ n)| ≤ n * Real.pi := by
  -- the total is the sum of the pieces (integral additivity + Im linear over the finite sum)
  have hsum : DiffractionCore.argChangeHoriz f T (σ 0) (σ n)
      = ∑ k ∈ Finset.range n, DiffractionCore.argChangeHoriz f T (σ k) (σ (k + 1)) := by
    unfold DiffractionCore.argChangeHoriz
    rw [← intervalIntegral.sum_integral_adjacent_intervals hint, Complex.im_sum]
  rw [hsum]
  calc |∑ k ∈ Finset.range n, DiffractionCore.argChangeHoriz f T (σ k) (σ (k + 1))|
      ≤ ∑ k ∈ Finset.range n, |DiffractionCore.argChangeHoriz f T (σ k) (σ (k + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, Real.pi :=
        Finset.sum_le_sum (fun k hk => hpiece k (Finset.mem_range.mp hk))
    _ = n * Real.pi := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Backlund
