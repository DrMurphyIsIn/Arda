/- PHASE 4 (dVP frontier, rung 2 analytic core — first ζ ingredients): ζ on a disk about
   `2 + iγ`, and the Jensen zero-count applied to ζ.

   Obligation (ii) of BC-SUM (the entire-part bound) needs the number of ζ-zeros in a disk
   near the 1-line to be `O(log|γ|)`.  Mathlib v4.32 provides the Jensen count
   `AnalyticOnNhd.sum_divisor_le` (`Mathlib.Analysis.Complex.JensenFormula`); its three
   hypotheses for `f = ζ` on a disk centered at `c` (with `Re c > 1`, e.g. `c = 2 + iγ`) are:
     * ζ analytic on the closed disk avoiding the pole `s = 1`  — `zeta_analyticOnNhd_disk`;
     * `ζ c ≠ 0`                                                — `zeta_ne_zero_of_one_lt_re`;
     * a boundary bound `‖ζ‖ ≤ M` on the outer sphere            — from `zeta_strip_bound`.
   `zeta_zero_count_le` wires the first two into `sum_divisor_le`, taking the boundary bound
   as a hypothesis; with `M = C|γ|` (from `zeta_strip_bound`, `‖s‖/‖s-1‖ + ‖s‖/Re s ~ C|γ|`
   on the sphere) the count is `O(log|γ|)`.

   These are the first genuinely-analytic ζ facts of the dVP frontier (not reductions).  The
   remaining core: the quantitative `M` (sphere geometry of `zeta_strip_bound`), the
   partial-fraction split ζ'/ζ = Z + E (obligation (i), via the divisor), and
   `borel_caratheodory_deriv` bounding `E`.  conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

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

/-- **Jensen zero-count for ζ.**  Applying `AnalyticOnNhd.sum_divisor_le` to ζ on a disk
    about a center `c` right of the 1-line: the number of ζ-zeros (with multiplicity) in the
    inner disk of radius `|r|` is `≤ log(M/‖ζ c‖)/log(R/r)`, given a boundary bound `‖ζ‖ ≤ M`
    on the outer sphere of radius `|R|`.  With `M = C|γ|` from `zeta_strip_bound` this is the
    `O(log|γ|)` count the de la Vallee Poussin argument needs. -/
theorem zeta_zero_count_le (c : ℂ) (r R M : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (h1 : (1 : ℂ) ∉ Metric.closedBall c |R|) (hc : 1 < c.re)
    (hbound : ∀ z ∈ Metric.sphere c |R|, ‖riemannZeta z‖ ≤ M) :
    ∑ᶠ u, divisor riemannZeta (Metric.closedBall c |r|) u
      ≤ Real.log (M / ‖riemannZeta c‖) / Real.log (R / r) :=
  (zeta_analyticOnNhd_disk c |R| h1).sum_divisor_le hr hrR hM
    (zeta_ne_zero_of_one_lt_re c hc) hbound

end ZeroFreeBridge
