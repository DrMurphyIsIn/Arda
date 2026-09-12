/- PHASE 4 (dVP frontier, item 2 — the concrete `hAL` shape): reduce the packed region hypothesis
   `(∑ |divisor|)/(R-‖z‖) + Bg ≤ A·L` to its two O(L) analytic inputs + a choice of `A`.

   `hAL_concrete` is the exact shape `dlvp_zeta_region_of_bc_sums` / `bc_sum_concrete` consume.
   It combines `sum_abs_divisor_eq` (|divisor|=divisor since ≥0) with `hAL_arith`, so what remains for
   item 2 is exactly:

     (i)  the ZERO-COUNT bound  `∑ divisor (ζ(c₀+·)) (ball 0 R) ≤ Ccount·L`  — from
          `zeta_zero_count_strip`, after the RECONCILIATION: the Jensen count is `∑ᶠ divisor ζ
          (closedBall c₀ |r|)` on an INNER radius `r`, while the hAL sum is `∑ over toFinset` of the
          RECENTRED divisor on `ball 0 R`.  Chain: `∑_{toFinset} = ∑ᶠ` (support) → translate pointwise
          (`divisor_comp_const_add_apply`) + reindex the finsum by the shift `v = c₀+u` → domain
          monotonicity `ball c₀ R ⊆ closedBall c₀ r` (`r = R`, outer radius `R' > R`, divisor ≥ 0).
     (ii) the ENTIRE-PART bound `Bg ≤ CBg·L` — from `norm_logDeriv_g_le_wired`
          (`Bg = 4·Aζ''·(R+‖z‖)/(R-‖z‖)²`, `Aζ'' = log U'' − log(2−π²/6) = O(log|c₀.im|) = O(L)`).

   Then `A ≥ Ccount/(R-‖z‖) + CBg` closes it.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpHALArith
import DlvpZetaCountStrip

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **The concrete `hAL`.**  `(∑ |divisor|)/(R-‖z‖) + Bg ≤ A·L` from the O(L) zero-count bound
    `S ≤ Ccount·L`, the entire-part bound `Bg ≤ CBg·L`, `‖z‖ < R`, and `A ≥ Ccount/(R-‖z‖) + CBg`. -/
theorem hAL_concrete {c₀ z : ℂ} {R L A Ccount CBg Bg : ℝ}
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite)
    (hz : ‖z‖ < R)
    (hdivnn : ∀ u ∈ hfin.toFinset,
      0 ≤ divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u)
    (hcount : (∑ u ∈ hfin.toFinset,
        (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℝ)) ≤ Ccount * L)
    (hBg : Bg ≤ CBg * L) (hL0 : 0 ≤ L)
    (hA : Ccount / (R - ‖z‖) + CBg ≤ A) :
    (∑ u ∈ hfin.toFinset,
        |(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℝ)|) / (R - ‖z‖) + Bg
      ≤ A * L := by
  rw [sum_abs_divisor_eq hfin.toFinset
    (fun u => divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u) hdivnn]
  exact hAL_arith hcount (by linarith) hBg hL0 hA

end ZeroFreeBridge
