/- PHASE 4 (dVP frontier, rung 2 analytic core — ζ zero-count, UNCONDITIONAL): ζ on a disk
   about `2 + iγ`, the Jensen zero-count applied to ζ, and its boundary bound discharged.

   Obligation (ii) of BC-SUM needs the number of ζ-zeros in a disk near the 1-line to be
   `O(log|γ|)`.  Mathlib v4.32's Jensen count `AnalyticOnNhd.sum_divisor_le`
   (`Mathlib.Analysis.Complex.JensenFormula`) has three hypotheses for `f = ζ`:
     * ζ analytic on the closed disk avoiding `s = 1`  — `zeta_analyticOnNhd_disk`;
     * `ζ c ≠ 0`                                       — `zeta_ne_zero_of_one_lt_re`;
     * a boundary bound `‖ζ‖ ≤ M` on the sphere        — `zeta_sphere_bound` (from
       `zeta_strip_bound`).
   `zeta_zero_count_le` wires the first two in (taking the boundary bound); `zeta_sphere_bound`
   supplies the third with an EXPLICIT `M = (‖c‖+R)/(c.re-R-1) + (‖c‖+R)/(c.re-R)` (`O(|γ|)` for
   `c = 2+iγ`); `zeta_zero_count_unconditional` combines them into a hypothesis-free
   `O(log|γ|)` count.

   This discharges the ZERO-COUNT half of obligation (ii).  The remaining core: the
   partial-fraction split ζ'/ζ = Z + E via the `divisor` (obligation (i)) and
   `borel_caratheodory_deriv` bounding `E`.  conjecture1_proved = False (NOT a proof of RH).
-/
import StripBound

open Complex MeromorphicOn

namespace ZeroFreeBridge

/-- ζ is nonzero right of the 1-line (`Re s > 1`) — the `f c ≠ 0` hypothesis of Jensen's
    `sum_divisor_le` at a disk center like `2 + iγ`. -/
theorem zeta_ne_zero_of_one_lt_re (c : ℂ) (hc : 1 < c.re) : riemannZeta c ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (le_of_lt hc)

/-- ζ is analytic on any closed disk that avoids the pole `s = 1` — the `AnalyticOnNhd`
    hypothesis of Jensen's `sum_divisor_le` / `circleAverage_log_norm`. -/
theorem zeta_analyticOnNhd_disk (c : ℂ) (r : ℝ) (h1 : (1 : ℂ) ∉ Metric.closedBall c r) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c r) := by
  have hsub : Metric.closedBall c r ⊆ {(1 : ℂ)}ᶜ := by
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact h1 hs
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun s hs =>
    (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton).mono hsub

/-- Concrete boundary bound for ζ on a sphere about a center `c` right of the 1-line
    (`c.re > R + 1`), from the crude `zeta_strip_bound`.  For `c = 2+iγ`, `R < 1` this is
    `O(|γ|)` — the `M` for the Jensen zero-count. -/
theorem zeta_sphere_bound (c : ℂ) (R : ℝ) (hR : 0 < R) (hcR : R + 1 < c.re)
    {z : ℂ} (hz : z ∈ Metric.sphere c R) :
    ‖riemannZeta z‖ ≤ (‖c‖ + R) / (c.re - R - 1) + (‖c‖ + R) / (c.re - R) := by
  have hzc : ‖z - c‖ = R := by
    rw [Metric.mem_sphere, Complex.dist_eq] at hz; exact hz
  have hre_dist : |z.re - c.re| ≤ R := by
    calc |z.re - c.re| = |(z - c).re| := by rw [Complex.sub_re]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      _ = R := hzc
  have hzre : c.re - R ≤ z.re := by have := (abs_le.mp hre_dist).1; linarith
  have hd1 : 0 < c.re - R - 1 := by linarith
  have hd2 : 0 < c.re - R := by linarith
  have hzre_pos : 0 < z.re := by linarith
  have hzne1 : z ≠ 1 := by
    intro h; rw [h] at hzre; simp only [Complex.one_re] at hzre; linarith
  have hsb := zeta_strip_bound (⟨hzre_pos, hzne1⟩ : z ∈ stripDomain)
  have hznorm : ‖z‖ ≤ ‖c‖ + R := by
    calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = ‖c‖ + R := by rw [hzc]; ring
  have hz1 : c.re - R - 1 ≤ ‖z - 1‖ := by
    calc c.re - R - 1 ≤ z.re - 1 := by linarith
      _ = (z - 1).re := by rw [Complex.sub_re, Complex.one_re]
      _ ≤ |(z - 1).re| := le_abs_self _
      _ ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have hb1 : ‖z‖ / ‖z - 1‖ ≤ (‖c‖ + R) / (c.re - R - 1) := by gcongr
  have hb2 : ‖z‖ / z.re ≤ (‖c‖ + R) / (c.re - R) := by gcongr
  linarith [hsb, hb1, hb2]

/-- **Jensen zero-count for ζ** (boundary bound as a hypothesis). -/
theorem zeta_zero_count_le (c : ℂ) (r R M : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (h1 : (1 : ℂ) ∉ Metric.closedBall c |R|) (hc : 1 < c.re)
    (hbound : ∀ z ∈ Metric.sphere c |R|, ‖riemannZeta z‖ ≤ M) :
    ∑ᶠ u, divisor riemannZeta (Metric.closedBall c |r|) u
      ≤ Real.log (M / ‖riemannZeta c‖) / Real.log (R / r) :=
  (zeta_analyticOnNhd_disk c |R| h1).sum_divisor_le hr hrR hM
    (zeta_ne_zero_of_one_lt_re c hc) hbound

/-- **UNCONDITIONAL Jensen zero-count for ζ.**  Discharging the boundary bound via
    `zeta_sphere_bound`: for a center `c` with `|R| + 1 < c.re` (e.g. `c = 2+iγ`, `|R| < 1`),
    the number of ζ-zeros in the inner disk is bounded by an EXPLICIT `O(log|γ|)` quantity —
    no boundary-bound hypothesis.  This discharges the zero-count half of obligation (ii). -/
theorem zeta_zero_count_unconditional (c : ℂ) (r R : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hcR : |R| + 1 < c.re) (h1 : (1 : ℂ) ∉ Metric.closedBall c |R|) :
    ∑ᶠ u, divisor riemannZeta (Metric.closedBall c |r|) u
      ≤ Real.log (((‖c‖ + |R|) / (c.re - |R| - 1) + (‖c‖ + |R|) / (c.re - |R|)) / ‖riemannZeta c‖)
          / Real.log (R / r) := by
  have hRpos : 0 < |R| := lt_trans hr hrR
  have hc : 1 < c.re := by linarith
  have hcre_norm : c.re ≤ ‖c‖ := Complex.re_le_norm c
  have hd1 : 0 < c.re - |R| - 1 := by linarith
  have hd2 : 0 < c.re - |R| := by linarith
  have hterm1 : 0 ≤ (‖c‖ + |R|) / (c.re - |R| - 1) :=
    div_nonneg (by positivity) hd1.le
  have hterm2 : 1 ≤ (‖c‖ + |R|) / (c.re - |R|) := by
    rw [le_div_iff₀ hd2]; linarith
  have hM : 1 ≤ (‖c‖ + |R|) / (c.re - |R| - 1) + (‖c‖ + |R|) / (c.re - |R|) := by linarith
  refine zeta_zero_count_le c r R _ hr hrR hM h1 hc ?_
  intro z hz
  exact zeta_sphere_bound c |R| hRpos hcR hz

end ZeroFreeBridge
