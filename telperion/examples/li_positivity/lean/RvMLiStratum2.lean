/-
RvMLiStratum2 — the finite→infinite exhaustion: λ_n as the limit of finite
partial sums of the paired zero-summand.

STRATUM 2 of the N(T) ↔ λ_n bridge.  Upstream proves (under the standard genus-one
hypotheses) that the Li coefficient is an ABSOLUTELY convergent sum over the paired
zeros:  `taylorCoeff riemannXi n = ½ ∑'_ρ liPairedSummand n ρ`, with
`Summable (liPairedSummand n ·)`.  Absolute convergence means the sum is the limit
of its finite partial sums along ANY cofinal exhaustion of the zero set by finite
subsets.  This file lands that limit:

  * `liCoeff_isLimit_partialSums` : the finite partial sums
    `S ↦ ½ ∑_{ρ∈S} liPairedSummand n ρ` converge (along the `atTop` filter of
    finite subsets of the zeros) to `taylorCoeff riemannXi n`.

This is the exhaustion half of Stratum 2: every finite partial sum is a term-count
away from `λ_n`, and the finite partial sum over a box's zeros is exactly what the
weighted argument principle (`analytic_weighted_count_eq_winding`, Stratum 1)
computes.  What remains for the FULL finite-box realisation (honestly flagged, not
built here): (a) a keyhole for the Li weight's pole at `s=0`, and (b) matching
`MeromorphicOn.divisor riemannXi` box-support to the upstream `NontrivialZero`
index, so that a height-`T` box IS one of these finite exhausting subsets.  Neither
is a research obstruction.  NOTE: the counting function N(T) is NOT load-bearing
for THIS limit — upstream's absolute convergence carries it; N(T) only measures how
many terms each partial sum has.

conjecture1_proved = False.
-/
import LiPositivity
import Lc.LiCriterion.GenusOnePairedSumFormula

namespace RvMLiStratum2

open Filter Topology

/-- **The exhaustion limit (Stratum 2).**  Under the standard genus-one hypotheses
    (`hgenus`: `Summable (1/‖ρ‖²)`, discharging order ≤ 1; `hhad`: the Hadamard
    shifted-product factorisation of `ξ`), the finite partial sums of the paired Li
    summand converge to the Li coefficient:

      `S ↦ ½ ∑_{ρ∈S} liPairedSummand n ρ   ⟶   taylorCoeff riemannXi n`

    along the `atTop` filter of finite subsets of the nontrivial zeros.  Immediate
    from upstream absolute summability (`summable_Li_paired_summand_of_genus_one`)
    and the paired-sum formula.  conjecture1_proved = False. -/
theorem liCoeff_isLimit_partialSums (n : ℕ)
    (hgenus : Summable (fun ρ : LiCriterion.NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ,
      LiCriterion.riemannXi s = Complex.exp a * LiCriterion.xiE1ShiftedProd s) :
    Tendsto
      (fun S : Finset LiCriterion.NontrivialZero =>
        (2⁻¹ : ℂ) * ∑ ρ ∈ S, LiCriterion.liPairedSummand n ρ)
      atTop (𝓝 (LiCriterion.taylorCoeff LiCriterion.riemannXi n)) := by
  -- upstream: absolutely convergent paired sum + its value
  have hsum : Summable (fun ρ : LiCriterion.NontrivialZero => LiCriterion.liPairedSummand n ρ) :=
    LiCriterion.summable_Li_paired_summand_of_genus_one hgenus n
  have hval : LiCriterion.taylorCoeff LiCriterion.riemannXi n
      = (2⁻¹ : ℂ) * ∑' ρ : LiCriterion.NontrivialZero, LiCriterion.liPairedSummand n ρ :=
    LiCriterion.paired_sum_formula_of_standard_hypotheses hgenus hhad n
  -- `HasSum` IS the Tendsto of finite partial sums; scale by ½ and rewrite the target.
  have hHS := hsum.hasSum
  have hmul := hHS.const_mul (2⁻¹ : ℂ)
  rw [← hval] at hmul
  exact hmul

end RvMLiStratum2
