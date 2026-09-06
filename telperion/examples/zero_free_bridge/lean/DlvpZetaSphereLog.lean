/- PHASE 4 (dVP frontier, ζ boundary growth — the ζ-GROWTH sphere bound `hζbound`, obligation (1)):
   assemble the entire-part decomposition's first named input.

   `norm_logDeriv_le_of_boundary_split` (`DlvpBoundaryDecomp`) needs, as its first sphere hypothesis,
   the log-OSCILLATION bound `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ` on `sphere c R`.  This file produces it, with
   an EXPLICIT `Aζ = O(log|c|)`, by combining the two ζ magnitude facts already in the corpus:

     * UPPER  `‖ζ z‖ ≤ U` on the sphere            (`DlvpZetaDisk.zeta_sphere_bound`, `O(|c|)`);
     * LOWER  `‖ζ c‖ ≥ 2 - π²/6 > 0` at the centre  (`DlvpZetaLower.zeta_norm_ge_two_sub`, `Re c ≥ 2`).

   Since `R + 1 < c.re`, every sphere point has `Re z ≥ c.re - R > 1`, so `ζ z ≠ 0`
   (`DlvpZetaDisk.zeta_ne_zero_of_one_lt_re`) and `log‖ζ z‖` is genuine; `Real.log` monotonicity then
   gives `log‖ζ z‖ - log‖ζ c‖ ≤ log U - log(2 - π²/6) =: Aζ`.  `Aζ = O(L)` because `log U = O(log|c|)`
   and the lower constant is `O(1)`.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaLower
import DlvpZetaDisk

open Complex Metric

namespace ZeroFreeBridge

/-- **The ζ-growth sphere bound `hζbound`.**  On `sphere c R` about a centre with `Re c ≥ 2` and
    `R + 1 < c.re`, the log-oscillation of ζ is bounded by an explicit `Aζ = O(log|c|)`:
    `log‖ζ z‖ - log‖ζ c‖ ≤ log U - log(2 - π²/6)`,
    `U = (‖c‖+R)/(c.re-R-1) + (‖c‖+R)/(c.re-R)`. -/
theorem zeta_sphere_log_bound (c : ℂ) (R : ℝ) (hR : 0 < R) (hcR : R + 1 < c.re) (hc2 : 2 ≤ c.re)
    {z : ℂ} (hz : z ∈ sphere c R) :
    Real.log ‖riemannZeta z‖ - Real.log ‖riemannZeta c‖
      ≤ Real.log ((‖c‖ + R) / (c.re - R - 1) + (‖c‖ + R) / (c.re - R))
        - Real.log (2 - Real.pi ^ 2 / 6) := by
  -- sphere geometry: ‖z - c‖ = R, hence Re z > 1
  have hnorm : ‖z - c‖ = R := by
    rw [← Complex.dist_eq]; exact Metric.mem_sphere.mp hz
  have hzre : (1 : ℝ) < z.re := by
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [hnorm] at h1
    have h2 : (z - c).re = z.re - c.re := by simp
    rw [h2] at h1
    have := (abs_le.mp h1).1
    linarith
  -- ζ z ≠ 0 on the sphere, so log‖ζ z‖ is genuine
  have hzpos : (0 : ℝ) < ‖riemannZeta z‖ :=
    norm_pos_iff.mpr (zeta_ne_zero_of_one_lt_re z hzre)
  -- UPPER: log‖ζ z‖ ≤ log U
  have hupper : ‖riemannZeta z‖ ≤ (‖c‖ + R) / (c.re - R - 1) + (‖c‖ + R) / (c.re - R) :=
    zeta_sphere_bound c R hR hcR hz
  have hlogU : Real.log ‖riemannZeta z‖
      ≤ Real.log ((‖c‖ + R) / (c.re - R - 1) + (‖c‖ + R) / (c.re - R)) :=
    Real.log_le_log hzpos hupper
  -- LOWER: log(2 - π²/6) ≤ log‖ζ c‖
  have hlower : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta c‖ := zeta_norm_ge_two_sub hc2
  have hlogL : Real.log (2 - Real.pi ^ 2 / 6) ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log two_sub_pi_sq_div_six_pos hlower
  linarith

end ZeroFreeBridge
