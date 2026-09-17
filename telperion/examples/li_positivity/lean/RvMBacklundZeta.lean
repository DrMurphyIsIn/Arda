/-
RvMBacklundZeta — Backlund S(T)=O(log T), PR 5: the ζ instantiation of the horizontal bound.

Instantiates the abstract capstone (PR 4c-count, `argChangeHoriz_abs_le_card_zeros`) at `f = riemannZeta`,
discharging the ζ-specific plumbing and carrying the two genuinely-analytic facts as honest hypotheses.

  * `zeta_argChangeHoriz_abs_le` — the net argument change of `ζ` along `[1/2,2]+iT` is at most
    `(number of Re-ζ zeros on the segment + 1)·π`.

Discharged here: `hdiff` (`differentiableAt_riemannZeta`, since `[1/2,2]+iT` avoids the pole `s=1` for
`T ≥ 4`); `hZsub`/`hZzero` (the zero set is `F_T`'s real zeros, finite by PR 4c-finiteness, and
`F_T ↑x = ↑(Re ζ(x+iT))` by `backlundAux_ofReal`, so `Re ζ = 0 ⟺ F_T ↑x = 0`).  Carried (both true,
standard): `hζne` — `ζ ≠ 0` on the segment (the genuine `S(T)`-jump subtlety) — and `hlogcont` —
`logDeriv ζ` continuous on the segment.

Remaining for the full `S(T) = O(log T)` (a further arc, not this PR): the zero count `≤` the PR 3b
Jensen `O(log T)` bound (`card ≤ Σ divisor`, via the PR 4c-finiteness divisor injection), and the vertical
argument-change assembly relating `argChangeHoriz`/`argChangeVert` to `riemannS`.
conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundCount
import RvMBacklundFinite

open Complex MeasureTheory

namespace Backlund

/-- **The horizontal argument variation of `ζ` is bounded by its `Re`-zero count.**  For `T ≥ 4`, with
    `ζ ≠ 0` and `logDeriv ζ` continuous along `[1/2,2]+iT`, the net argument change of `ζ` there is at
    most `(the number of real zeros of `F_T = Re ζ(·+iT)` on `[1/2,2]` + 1)·π`. -/
theorem zeta_argChangeHoriz_abs_le {T : ℝ} (hT : 4 ≤ T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hlogcont : ContinuousOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2)) :
    |DiffractionCore.argChangeHoriz riemannZeta T (1 / 2) 2|
      ≤ ((backlundAux_real_zeros_finite hT).toFinset.card + 1) * Real.pi := by
  -- points of the segment avoid the pole s = 1 (their imaginary part is T ≠ 0)
  have hne1 : ∀ x : ℝ, ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x h
    have him := congrArg Complex.im h
    simp at him
    linarith
  refine argChangeHoriz_abs_le_card_zeros riemannZeta T (1 / 2) 2 (by norm_num)
    ((backlundAux_real_zeros_finite hT).toFinset) ?_ hlogcont hζne ?_ ?_
  · -- hdiff
    exact fun x _ => differentiableAt_riemannZeta (hne1 x)
  · -- hZsub: the zero set lies in [1/2,2]
    intro z hz
    exact ((backlundAux_real_zeros_finite hT).mem_toFinset.mp hz).1
  · -- hZzero: Re ζ(x+iT) = 0 ⟹ x is an F_T zero
    intro x hx hzero
    rw [(backlundAux_real_zeros_finite hT).mem_toFinset]
    exact ⟨hx, by rw [backlundAux_ofReal, hzero, Complex.ofReal_zero]⟩

end Backlund
