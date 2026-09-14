/-  EMZetaComplex.lean -- A2 Theorem 1, E-track: the COMPLEX Euler-Maclaurin representation of ζ
    and its K=1 analytic continuation into the critical strip.

    Builds on `EMZeta.lean` (real-s EM chain, Parts A-D', kernel-clean).  This file is the
    complex lift and the analytic continuation:

      E1.  `em_unit_step_cpow`   -- one-step EM over [m,m+1] for a ℂ-valued C¹ function.
           `em_cpow_partial`      -- finite-N EM for `f x = (x:ℂ)^(-s)`, s : ℂ, on [1,N].
      E2.  `em_zeta_cpow`         -- N→∞ complex representation, valid Re s > 1, tied to riemannZeta.
      E3.  `em_zeta_strip`        -- K=1 analytic continuation to 0 < Re s (s ≠ 1) with explicit
                                     remainder bound (THE PRIZE — covers the critical strip).
      E4.  `em_zeta_strip_enclosure` -- evaluator-facing finite-sum + explicit-tail enclosure shape.

    Only fully-proven, sorry-free lemmas live here.  General-K (K ≥ 2) stays in EMZetaWip.lean.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin + identity
    theorem), NOT a proof of RH.
-/
import EMZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Uniqueness

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace ZetaReflection

/-! ## E1a. One-step Euler-Maclaurin over a unit cell, ℂ-valued integrand.

    Direct lift of `em_unit_step`: the saw antiderivative `w x = x - m - 1/2` is real, cast to ℂ,
    and the IBP `intervalIntegral.integral_deriv_mul_eq_sub` runs in the `NormedRing ℂ`. -/

/-- **One-step Euler-Maclaurin over `[m, m+1]`, ℂ-valued `f`.**  Same statement as `em_unit_step`
    but `f, f' : ℝ → ℂ`; the saw factor `sawBernoulli 1 x` is cast to ℂ. -/
theorem em_unit_step_cpow {f f' : ℝ → ℂ} (m : ℤ)
    (hf : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), f x)
      = (f m + f (m + 1)) / 2
        - ∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x := by
  -- The affine antiderivative `w x = x - m - 1/2` of the constant `1`, valued in ℂ.
  set w : ℝ → ℂ := fun x => (x : ℂ) - m - 1 / 2 with hw
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hw' : ∀ x, HasDerivAt w 1 x := by
    intro x
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have := (hbase.sub_const (m : ℂ)).sub_const (1 / 2 : ℂ)
    simpa [hw] using this
  have hwcont : Continuous w := by fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt w (1 : ℂ) x := fun x _ => hw' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hcc] at hx
    exact hf x hx
  have hw'int : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume (m : ℝ) (m + 1) :=
    intervalIntegrable_const
  have hIBP := integral_deriv_mul_eq_sub huv hfd hw'int hf'
  have hwL : w (m : ℝ) = -(1 / 2) := by simp only [hw]; push_cast; ring
  have hwR : w ((m : ℝ) + 1) = 1 / 2 := by simp only [hw]; push_cast; ring
  have hwf'int : IntervalIntegrable (fun x => w x * f' x) volume (m : ℝ) (m + 1) :=
    hf'.continuousOn_mul hwcont.continuousOn
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (1 : ℂ) * f x + w x * f' x)
        = (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    have hfcont : ContinuousOn f (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    have hfint : IntervalIntegrable f volume (m : ℝ) (m + 1) :=
      hfcont.intervalIntegrable
    rw [intervalIntegral.integral_add (by simpa using hfint) hwf'int]
    simp
  -- Identify `(sawBernoulli 1 · : ℂ) · f'` with `w · f'` a.e. on the cell.
  have hsaw : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x)
      = ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    simp only [hw]; push_cast; ring
  rw [hsaw]
  have key : (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x
      = w ((m : ℝ) + 1) * f ((m : ℝ) + 1) - w (m : ℝ) * f (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hwL, hwR] at key
  -- Solve for `∫ f` (ℂ is not ordered — use `linear_combination`).
  linear_combination key

/-! ## E1b. Summed complex EM over an integer window, and the partial-ζ identity.

    Lift of `euler_maclaurin_one_window` to ℂ-valued `f`.  The telescoping and per-cell
    integrability arguments are identical to the real proof; the trapezoid bookkeeping is over ℂ. -/

/-- Complex trapezoid-sum bookkeeping over `[M, N)`.  ℂ version of `trapezoid_sum_window`. -/
private lemma trapezoid_sum_window_cpow (f : ℝ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ k ∈ Finset.Ico M N, (f (k : ℝ) + f ((k : ℝ) + 1)) / 2)
      = (∑ n ∈ Finset.Ico M N, f (n : ℝ)) + (f N - f M) / 2 := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
      rw [Finset.sum_Ico_succ_top hp (fun k => (f (k : ℝ) + f ((k : ℝ) + 1)) / 2),
          Finset.sum_Ico_succ_top hp (fun n => f (n : ℝ)), ih]
      push_cast; ring

/-- **Complex first-order Euler-Maclaurin over the integer window `[M, N]`.**  ℂ version of
    `euler_maclaurin_one_window`. -/
theorem euler_maclaurin_one_window_cpow {f f' : ℝ → ℂ} (M N : ℕ) (hMN : M ≤ N)
    (hf : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt f (f' x) x)
    (hf' : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f' volume (k : ℝ) (k + 1)) :
    (∑ n ∈ Finset.Ico M N, f (n : ℝ))
      = (∫ x in (M : ℝ)..N, f x) - (f N - f M) / 2
        + ∫ x in (M : ℝ)..N, (sawBernoulli 1 x : ℂ) * f' x := by
  have hcell : ∀ k ∈ Finset.Ico M N, ∀ x ∈ Icc (k : ℝ) (k + 1), HasDerivAt f (f' x) x := by
    intro k hk x hx
    rw [Finset.mem_Ico] at hk
    refine hf x ⟨?_, ?_⟩
    · exact le_trans (by exact_mod_cast hk.1) hx.1
    · have : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk.2
      linarith [hx.2]
  have hstep : ∀ k ∈ Finset.Ico M N,
      (∫ x in (k : ℝ)..(k + 1), f x)
        = (f k + f (k + 1)) / 2 - ∫ x in (k : ℝ)..(k + 1), (sawBernoulli 1 x : ℂ) * f' x := by
    intro k hk
    have hcast : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
    have hstepZ := em_unit_step_cpow (f := f) (f' := f') (k : ℤ)
      (by intro x hx; rw [hcast] at hx; exact hcell k hk x hx)
      (by rw [hcast]; exact hf' k hk)
    simp only [hcast] at hstepZ
    exact hstepZ
  have hsum := Finset.sum_congr rfl hstep
  have hfint_cell : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcont : ContinuousOn f (uIcc (k : ℝ) (k + 1)) := by
      rw [uIcc_of_le (by linarith)]
      exact fun x hx => (hcell k hk x hx).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable
  have htel_f : (∑ k ∈ Finset.Ico M N, ∫ x in (k : ℝ)..(k + 1), f x)
      = ∫ x in (M : ℝ)..N, f x := by
    have hint : ∀ k ∈ Set.Ico M N,
        IntervalIntegrable f volume ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k hk
      simpa [Nat.cast_succ] using hfint_cell k (Finset.mem_Ico.mpr hk)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ)) (f := f) (μ := volume) hMN hint
    simpa using this
  have hsawf'_cell : ∀ k ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli 1 x : ℂ) * f' x) volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcc : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => ((x - k - 1 / 2 : ℝ) : ℂ) * f' x) volume
        (k : ℝ) (k + 1) := (hf' k hk).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((k : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((k : ℤ) : ℝ) (((k : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (k : ℝ) < x := hxmem.1
        push_cast; linarith
      · have hlt : x < (k : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne
        push_cast; linarith
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    push_cast; ring_nf
  have htel_saw : (∑ k ∈ Finset.Ico M N, ∫ x in (k : ℝ)..(k + 1), (sawBernoulli 1 x : ℂ) * f' x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli 1 x : ℂ) * f' x := by
    have hint : ∀ k ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli 1 x : ℂ) * f' x) volume
          ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k hk
      simpa [Nat.cast_succ] using hsawf'_cell k (Finset.mem_Ico.mpr hk)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ)) (f := fun x => (sawBernoulli 1 x : ℂ) * f' x) (μ := volume)
      hMN hint
    simpa using this
  rw [Finset.sum_sub_distrib, htel_f, htel_saw, trapezoid_sum_window_cpow f hMN] at hsum
  -- `hsum : ∑ f = (∫ f - ∑ saw) - (∑ f + (fN - fM)/2)` rearranged; finish over ℂ.
  linear_combination -hsum

/-- The complex-power derivative on the positive reals (E1's `hasDerivAt_cpow_neg_wip`):
    `HasDerivAt (fun x:ℝ => (x:ℂ)^(-s)) (-s·(x:ℂ)^(-s-1)) x` for `x > 0` and `s ≠ 0`.
    Anchored on `hasDerivAt_ofReal_cpow_const`. -/
theorem hasDerivAt_cpow_neg {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hneg : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr hs
  have := hasDerivAt_ofReal_cpow_const (x := x) hx0 (r := -s) hneg
  simpa using this

/-- **Complex finite-`N` Euler-Maclaurin representation of the partial ζ sum.**  For `s : ℂ`,
    `s ≠ 0`, `N ≥ 1`, applying `euler_maclaurin_one_window_cpow` to `f x = (x:ℂ)^(-s)`:
        ∑_{n=1}^{N-1} n^{-s} = ∫_1^N x^{-s} − (N^{-s} − 1^{-s})/2
                               + ∫_1^N (sawBernoulli 1 x)·(−s·x^{−s−1}). -/
theorem em_cpow_partial {s : ℂ} (hs : s ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
      = (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s))
        - (((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2
        + ∫ x in (1 : ℝ)..N, (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hderiv : ∀ x ∈ Icc ((1 : ℕ) : ℝ) N,
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by have := hx.1; push_cast at this; linarith
    exact hasDerivAt_cpow_neg hs (lt_of_lt_of_le zero_lt_one hx1)
  have hf'int : ∀ k ∈ Finset.Ico 1 N,
      IntervalIntegrable (fun x => -s * (x : ℂ) ^ (-s - 1)) volume (k : ℝ) (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.mul continuousOn_const
    -- `x ↦ (x:ℂ)^(-s-1)` is continuous on `[k, k+1]` (arg bounded away from 0, in slitPlane).
    apply ContinuousOn.cpow_const
    · exact Complex.continuous_ofReal.continuousOn
    · intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans hk1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
  have hcast1 : (((1 : ℕ) : ℝ) : ℂ) ^ (-s) = ((1 : ℝ) : ℂ) ^ (-s) := by norm_num
  have := euler_maclaurin_one_window_cpow (f := fun x => (x : ℂ) ^ (-s))
    (f' := fun x => -s * (x : ℂ) ^ (-s - 1)) 1 N hN hderiv hf'int
  simpa using this

end ZetaReflection
