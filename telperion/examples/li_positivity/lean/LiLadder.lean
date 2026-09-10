/-
LiLadder — the Li ladder as a REDUCTION of RH to its tail.

Hand-written companion to the GENERATED `LiPositivity` rungs (NOT emitted by
telperion, so exempt from the regeneration diff).

Each `li_rung_n` certifies one entry of a finite PREFIX
`0 ≤ (taylorCoeff riemannXi n).re` for `n < N` — each modulo its Arb enclosure
hypothesis, the documented trust seam.  This file states precisely what a
certified prefix BUYS:

  * `li_rh_iff_tail` — given the prefix `0..N-1` nonneg, RH is EQUIVALENT to the
    infinite TAIL `∀ n ≥ N`.  The tail is still infinite: **no finite prefix
    proves RH.**  This restates the upstream equivalence relative to the prefix;
    it proves NEITHER side.
  * `li_tail_peel` — certifying one more rung extends the prefix by one, so the
    ladder composes rung-by-rung.

conjecture1_proved = False.
-/
import LiPositivity

namespace LiPositivity

open LiCriterion

/-- **The ladder as a reduction of RH to its tail.**  Given a certified prefix
    (rungs `0..N-1` nonneg), `RiemannHypothesis` is EQUIVALENT to the tail
    condition `∀ n ≥ N, 0 ≤ (taylorCoeff riemannXi n).re`.

    Peeling a verified prefix reduces RH to what remains — and the tail is still
    infinite, so no finite prefix (however long) proves RH.  This proves NEITHER
    side of RH; it only restates `li_criterion_rh_iff` relative to the certified
    prefix.  conjecture1_proved = False. -/
theorem li_rh_iff_tail (N : ℕ)
    (hpre : ∀ n, n < N → 0 ≤ (taylorCoeff riemannXi n).re) :
    RiemannHypothesis ↔ ∀ n, N ≤ n → 0 ≤ (taylorCoeff riemannXi n).re := by
  rw [li_criterion_rh_iff]
  constructor
  · intro h n _
    exact h n
  · intro htail n
    rcases lt_or_ge n N with hlt | hge
    · exact hpre n hlt
    · exact htail n hge

/-- **The ladder composes**: certifying rung `N` extends a length-`N` prefix to
    length `N+1`.  So the reduction `li_rh_iff_tail` advances one rung at a time,
    each step consuming exactly one Arb-certified rung. -/
theorem li_tail_peel (N : ℕ)
    (hpre : ∀ n, n < N → 0 ≤ (taylorCoeff riemannXi n).re)
    (hN : 0 ≤ (taylorCoeff riemannXi N).re) :
    ∀ n, n < N + 1 → 0 ≤ (taylorCoeff riemannXi n).re := by
  intro n hn
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hn) with hlt | heq
  · exact hpre n hlt
  · rw [heq]; exact hN

/-- **The empty prefix is the base case**: with no rungs certified (`N = 0`), the
    reduction is vacuous — RH ⇔ the full ladder, exactly `li_criterion_rh_iff`.
    Makes explicit that the ladder starts at "RH ⇔ everything" and each certified
    rung peels one entry off the front. -/
theorem li_rh_iff_tail_zero :
    RiemannHypothesis ↔ ∀ n, 0 ≤ (taylorCoeff riemannXi n).re := by
  have h := li_rh_iff_tail 0 (fun n hn => absurd hn (Nat.not_lt_zero n))
  simpa using h

end LiPositivity
