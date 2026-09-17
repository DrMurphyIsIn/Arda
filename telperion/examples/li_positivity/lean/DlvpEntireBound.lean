/- PHASE 4 (dVP frontier, obligation (i-b') COMPOSITION): the entire part `E = logDeriv g` at the
   centre of a disk is bounded by the oscillation of `log‖g‖`.

   Composes the two (i-b') atoms:
     * `DlvpLogBranch.log_branch_of_analytic_nonvanishing` — the analytic branch `h` with
       `deriv h = logDeriv g` and `(h z).re = log‖g z‖`;
     * `DlvpBCDeriv.norm_deriv_le_of_re_le` — `‖deriv h c‖ ≤ 2 M'/(R-r)` from `Re h - Re h(c) ≤ M'`.

   Combining, `Re h = log‖g‖` turns the real-part hypothesis into a bound on `log‖g‖`:

     `norm_logDeriv_le_of_log_norm_le` :  g holomorphic zero-free on `ball c R`,
        `log‖g z‖ - log‖g c‖ ≤ M'` (`M' > 0`) throughout, `0 < r < R`
        ⟹  `‖logDeriv g c‖ ≤ 2 M'/(R - r)`.

   This is the FULL analytic content of obligation (i-b') for a general zero-free `g`: it isolates
   the SOLE remaining ζ-specific input as the boundary growth `log‖g‖ ≤ A·L`.  Feeding `M' = A·L`
   gives `‖E‖ ≤ 2 A·L/(R-r) = O(L)`.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpLogBranch
import DlvpBCDeriv

open Complex Metric

namespace ZeroFreeBridge

/-- **Obligation (i-b') composition.**  For a holomorphic zero-free `g` on `ball c R` whose
    `log‖g‖` exceeds its central value by at most `M' > 0` throughout the disk, the entire part
    `logDeriv g` at the centre is bounded: `‖logDeriv g c‖ ≤ 2 M'/(R - r)` for any `0 < r < R`. -/
theorem norm_logDeriv_le_of_log_norm_le {g : ℂ → ℂ} {c : ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM' : 0 < M')
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hbound : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g c‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hcball : c ∈ ball c R := mem_ball_self hR
  obtain ⟨h, hh, _hhc, _hexp, hre⟩ := log_branch_of_analytic_nonvanishing hR hg hne
  -- the branch is holomorphic on the disk, with `deriv h = logDeriv g`.
  have hh_diff : DifferentiableOn ℂ h (ball c R) :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have hderiv_c : deriv h c = logDeriv g c := (hh c hcball).deriv
  -- `Re h - Re h(c) ≤ M'` from `Re h = log‖g‖`.
  have hre_bound : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ M' := by
    intro z hz
    rw [hre z hz, hre c hcball]
    exact hbound z hz
  have := norm_deriv_le_of_re_le hr hrR hh_diff hM' hre_bound
  rwa [hderiv_c] at this

end ZeroFreeBridge
