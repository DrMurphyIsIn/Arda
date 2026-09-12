/-
RvMBacklundCount — Backlund S(T)=O(log T), PR 4c (count): the capstone assembly.

Combines every 4c/4b brick into the horizontal argument-variation bound: the net argument change of `f`
along `[a,b]+iT` is at most `(number of Re-f zeros + 1)·π`.

  * `argChangeHoriz_abs_le_card_zeros` — `f` differentiable, `logDeriv f` continuous, and `f ≠ 0` on the
    segment, `Z` a finite superset of the real zeros of `Re f(·+iT)` ⟹
    `|argChangeHoriz f T a b| ≤ (Z.card + 1)·π`.

Assembly: `exists_monotone_partition_of_finite` (4c-order) sorts `Z` into a partition; on each open piece
`Re f ≠ 0` (`Z` captures all zeros), so `Re f` is one sign on the closed piece (`re_one_sign_of_ne_zero_Ioo`,
4c-sign-on-closed), whence the piece's argument change is `≤ π` (`argChangeHoriz_abs_le_pi_of_re_sign'`,
4c-nonstrict — the endpoints may be zeros); degenerate zero-width pieces contribute `0`
(`integral_same`).  Summing over the `≤ Z.card + 1` pieces (`argChangeHoriz_abs_le_partition`, 4b) gives
the bound.  For `f = ζ`, `Z =` the `F_T` real zeros (finite by 4c-finiteness) and `Z.card ≤` the PR 3b
Jensen `O(log T)` count — that final numeric wiring is the remaining step of PR 5.
conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundConfineNonstrict
import RvMBacklundSignClosed
import RvMBacklundPartition
import RvMBacklundOrder

open Complex MeasureTheory intervalIntegral

namespace Backlund

/-- **Argument variation ≤ (zero count + 1)·π.**  The horizontal half of Backlund's `S(T)` bound. -/
theorem argChangeHoriz_abs_le_card_zeros (f : ℂ → ℂ) (T a b : ℝ) (hab : a ≤ b) (Z : Finset ℝ)
    (hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, f ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hZsub : ∀ z ∈ Z, z ∈ Set.Icc a b)
    (hZzero : ∀ x ∈ Set.Icc a b, (f ((x : ℂ) + (T : ℂ) * I)).re = 0 → x ∈ Z) :
    |DiffractionCore.argChangeHoriz f T a b| ≤ (Z.card + 1) * Real.pi := by
  -- continuity of x ↦ Re f(x+iT) along the segment (via the path-composite derivative)
  have hfcont : ContinuousOn (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) (Set.Icc a b) := by
    intro x hx
    have hpath : HasDerivAt (fun t : ℝ => (t : ℂ) + (T : ℂ) * I) 1 x := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
      exact h1.add_const _
    exact (((hdiff x hx).hasDerivAt).scomp x hpath).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn (fun x : ℝ => (f ((x : ℂ) + (T : ℂ) * I)).re) (Set.Icc a b) :=
    Complex.continuous_re.comp_continuousOn hfcont
  -- partition {a,b} ∪ Z
  obtain ⟨N, σ, hmono, hσ0, hσN, hNcard, hσIcc, hnb⟩ :=
    exists_monotone_partition_of_finite Z a b hab hZsub
  -- geometry of a piece
  have hpiecele : ∀ k, σ k ≤ σ (k + 1) := fun k => hmono (Nat.le_succ k)
  have hsubIcc : ∀ k, Set.Icc (σ k) (σ (k + 1)) ⊆ Set.Icc a b :=
    fun k => Set.Icc_subset_Icc (hσIcc k).1 (hσIcc (k + 1)).2
  have hsubuIcc : ∀ k, Set.uIcc (σ k) (σ (k + 1)) ⊆ Set.Icc a b := by
    intro k; rw [Set.uIcc_of_le (hpiecele k)]; exact hsubIcc k
  -- integrability on each piece
  have hint : ∀ k, k < N → IntervalIntegrable
      (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) volume (σ k) (σ (k + 1)) :=
    fun k _ => (hcont.mono (hsubuIcc k)).intervalIntegrable
  -- per-piece confinement
  have hpiece : ∀ k, k < N →
      |DiffractionCore.argChangeHoriz f T (σ k) (σ (k + 1))| ≤ Real.pi := by
    intro k hk
    by_cases hstrict : σ k < σ (k + 1)
    · -- Re f is one sign on the (closed) piece: no zero strictly inside
      have hgopen : ∀ x ∈ Set.Ioo (σ k) (σ (k + 1)), (f ((x : ℂ) + (T : ℂ) * I)).re ≠ 0 := by
        intro x hx hzero
        have hxZ : x ∈ Z := hZzero x (hsubIcc k (Set.Ioo_subset_Icc_self hx)) hzero
        rcases hnb k hk x hxZ with h | h
        · exact absurd hx.1 (not_lt.mpr h)
        · exact absurd hx.2 (not_lt.mpr h)
      have huIcc : Set.uIcc (σ k) (σ (k + 1)) = Set.Icc (σ k) (σ (k + 1)) :=
        Set.uIcc_of_le (hpiecele k)
      have hdiff' : ∀ x ∈ Set.uIcc (σ k) (σ (k + 1)), DifferentiableAt ℂ f ((x : ℂ) + (T : ℂ) * I) := by
        rw [huIcc]; exact fun x hx => hdiff x (hsubIcc k hx)
      have hcont' : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I))
          (Set.uIcc (σ k) (σ (k + 1))) := hcont.mono (hsubuIcc k)
      have hne' : ∀ x ∈ Set.uIcc (σ k) (σ (k + 1)), f ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
        rw [huIcc]; exact fun x hx => hne x (hsubIcc k hx)
      have hsign' : (∀ x ∈ Set.uIcc (σ k) (σ (k + 1)), 0 ≤ (f ((x : ℂ) + (T : ℂ) * I)).re) ∨
          (∀ x ∈ Set.uIcc (σ k) (σ (k + 1)), (f ((x : ℂ) + (T : ℂ) * I)).re ≤ 0) := by
        rw [huIcc]
        exact re_one_sign_of_ne_zero_Ioo (fun x => (f ((x : ℂ) + (T : ℂ) * I)).re) (σ k) (σ (k + 1))
          hstrict (hgcont.mono (hsubIcc k)) hgopen
      exact argChangeHoriz_abs_le_pi_of_re_sign' f T (σ k) (σ (k + 1)) hdiff' hcont' hne' hsign'
    · -- degenerate zero-width piece: argument change is 0
      have heq : σ k = σ (k + 1) := le_antisymm (hpiecele k) (not_lt.mp hstrict)
      rw [heq]
      have h0 : DiffractionCore.argChangeHoriz f T (σ (k + 1)) (σ (k + 1)) = 0 := by
        unfold DiffractionCore.argChangeHoriz
        rw [intervalIntegral.integral_same, Complex.zero_im]
      rw [h0, abs_zero]; exact Real.pi_pos.le
  -- sum over the pieces
  have hbound := argChangeHoriz_abs_le_partition f T σ N hint hpiece
  rw [hσ0, hσN] at hbound
  calc |DiffractionCore.argChangeHoriz f T a b| ≤ (N : ℝ) * Real.pi := hbound
    _ ≤ ((Z.card : ℝ) + 1) * Real.pi := by
        apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
        exact_mod_cast hNcard

end Backlund
