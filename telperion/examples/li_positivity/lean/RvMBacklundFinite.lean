/-
RvMBacklundFinite — Backlund S(T)=O(log T), PR 4c (finiteness): F_T's real zeros are finite.

The partition of `[1/2,2]` (needed for the summed confinement bound, PR 4b/4c) is cut at the zeros of
`F_T = Re ζ(·+iT)` on the segment.  This file proves that set is FINITE, and — crucially — does so by
injecting it into the PR 3b complex divisor support, which sets up the eventual count `pieces ≤ Jensen+1`.

  * `backlundAux_real_zeros_finite` — `{σ ∈ [1/2,2] | F_T σ = 0}` is finite.

Route (reuses PR 3b, no real-analytic isolated-zeros machinery): `F_T` is analytic on `closedBall 2 (7/4)`
and `F_T(2) ≠ 0` (PR 3a/3b), so on the compact ball its divisor has finite support
(`MeromorphicOn.divisor_support_finite_of_subset`).  A real zero `σ ∈ [1/2,2]` gives a complex point
`↑σ ∈ closedBall 2 (3/2)` with `F_T ↑σ = 0`; its analytic order is `≠ 0` (`analyticOrderAt_ne_zero`,
from `F_T ↑σ = 0`) and `≠ ⊤` (else the identity theorem forces `F_T ≡ 0`, contradicting `F_T(2) ≠ 0`), so
`↑σ` is in the divisor support.  `Complex.ofReal` injects the real zeros into that finite set.
conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundJensen
import RvMBacklundCenter

open Complex MeasureTheory

namespace Backlund

/-- **`F_T`'s real zeros on `[1/2,2]` are finite.**  They inject (via `Complex.ofReal`) into the finite
    support of `F_T`'s divisor on `closedBall 2 (3/2)`. -/
theorem backlundAux_real_zeros_finite {T : ℝ} (hT : 4 ≤ T) :
    {σ : ℝ | σ ∈ Set.Icc (1 / 2 : ℝ) 2 ∧ backlundAux T (σ : ℂ) = 0}.Finite := by
  -- F_T analytic on the big ball; nonzero at the centre 2
  have hana74 : AnalyticOnNhd ℂ (backlundAux T) (Metric.closedBall (2 : ℂ) (7 / 4)) :=
    backlundAux_analyticOnNhd_ball hT
  have hpre : IsPreconnected (Metric.closedBall (2 : ℂ) (7 / 4)) :=
    (convex_closedBall _ _).isPreconnected
  have hF2ne : backlundAux T (2 : ℂ) ≠ 0 := by
    have hge := backlundAux_two_norm_ge T
    have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    rw [h2] at hge
    intro hz; rw [hz, norm_zero] at hge
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  -- the divisor on the smaller ball has finite support
  have hsub : Metric.closedBall (2 : ℂ) (3 / 2) ⊆ Metric.closedBall (2 : ℂ) (7 / 4) :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hana32 : AnalyticOnNhd ℂ (backlundAux T) (Metric.closedBall (2 : ℂ) (3 / 2)) := hana74.mono hsub
  have hsupp : (MeromorphicOn.divisor (backlundAux T) (Metric.closedBall (2 : ℂ) (3 / 2))).support.Finite :=
    hana74.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall _ _) hsub
  -- inject the real zeros into the divisor support
  refine Set.Finite.of_finite_image (f := ((↑) : ℝ → ℂ)) (hsupp.subset ?_) Complex.ofReal_injective.injOn
  rintro z ⟨σ, ⟨hσIcc, hσ0⟩, rfl⟩
  rw [Function.mem_support]
  -- membership facts for ↑σ
  obtain ⟨hσ1, hσ2⟩ := hσIcc
  have hmem32 : (σ : ℂ) ∈ Metric.closedBall (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hmem74 : (σ : ℂ) ∈ Metric.closedBall (2 : ℂ) (7 / 4) := hsub hmem32
  have hAA : AnalyticAt ℂ (backlundAux T) (σ : ℂ) := hana32 _ hmem32
  -- analytic order at ↑σ is nonzero and finite
  have ho_ne0 : analyticOrderAt (backlundAux T) (σ : ℂ) ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hAA, hσ0⟩
  have ho_neTop : analyticOrderAt (backlundAux T) (σ : ℂ) ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hEqOn : Set.EqOn (backlundAux T) 0 (Metric.closedBall (2 : ℂ) (7 / 4)) :=
      hana74.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hmem74 htop
    exact hF2ne (hEqOn (Metric.mem_closedBall_self (by norm_num)))
  -- hence the divisor value is nonzero: lift the (finite, nonzero) order to ℕ
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hana32 hmem32]
  lift analyticOrderAt (backlundAux T) (σ : ℂ) to ℕ using ho_neTop with k
  rw [ENat.map_natCast]
  simpa using ho_ne0

end Backlund
