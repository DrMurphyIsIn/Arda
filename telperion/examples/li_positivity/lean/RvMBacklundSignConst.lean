/-
RvMBacklundSignConst — Backlund S(T)=O(log T), PR 4c (first piece): sign-constancy ⟹ confinement.

The per-piece confinement of PR 4b (`argChangeHoriz_abs_lt_pi_of_re_sign`) asks for the disjunction
"`Re f > 0` everywhere on the piece OR `Re f < 0` everywhere".  A partition of `[1/2,2]` cut at the
zeros of `F_T = Re ζ(·+iT)` delivers something weaker and more natural: `Re f ≠ 0` on each *open*
piece.  This file bridges the gap.

  * `argChangeHoriz_abs_lt_pi_of_re_ne_zero` — if `Re f` is continuous and NONVANISHING along the
    segment, then `|argChangeHoriz f T x0 x1| < π`.

Proof: a continuous real function that is never zero on the connected set `[[x0,x1]]` cannot take both
signs (else IVT — `intermediate_value_uIcc` — would force a zero), so `Re f` is one sign there; then
PR 4b's either-sign confinement applies.  This reduces the per-piece hypothesis to exactly the output
of partitioning at the sign changes.  Assembling the actual partition from `F_T`'s finite zero set and
counting it against the PR 3b Jensen bound is the remaining piece of PR 4c.  conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundPartition

open Complex MeasureTheory intervalIntegral

namespace Backlund

/-- **Nonvanishing ⟹ confinement.**  If `Re f` is continuous and nowhere zero along the horizontal
    segment, the net argument change of `f` there is `< π` in absolute value. -/
theorem argChangeHoriz_abs_lt_pi_of_re_ne_zero (f : ℂ → ℂ) (T x0 x1 : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) (Set.uIcc x0 x1))
    (hcontf : ContinuousOn (fun x : ℝ => (f ((x : ℂ) + (T : ℂ) * I)).re) (Set.uIcc x0 x1))
    (hne : ∀ x ∈ Set.uIcc x0 x1, (f ((x : ℂ) + (T : ℂ) * I)).re ≠ 0) :
    |DiffractionCore.argChangeHoriz f T x0 x1| < Real.pi := by
  set g : ℝ → ℝ := fun x => (f ((x : ℂ) + (T : ℂ) * I)).re with hg
  -- `g` continuous and nonvanishing on the connected segment ⟹ one sign
  have hsign : (∀ x ∈ Set.uIcc x0 x1, 0 < g x) ∨ (∀ x ∈ Set.uIcc x0 x1, g x < 0) := by
    by_contra h
    push_neg at h
    obtain ⟨⟨a, ha, hga⟩, ⟨b, hb, hgb⟩⟩ := h
    -- hga : g a ≤ 0, with g a ≠ 0 ⟹ g a < 0;  hgb : 0 ≤ g b, with g b ≠ 0 ⟹ 0 < g b
    have hga' : g a < 0 := lt_of_le_of_ne hga (hne a ha)
    have hgb' : (0 : ℝ) < g b := lt_of_le_of_ne hgb (Ne.symm (hne b hb))
    -- IVT on [[a,b]] ⊆ [[x0,x1]] hits 0
    have hsub : Set.uIcc a b ⊆ Set.uIcc x0 x1 := Set.uIcc_subset_uIcc ha hb
    have hmem : (0 : ℝ) ∈ Set.uIcc (g a) (g b) :=
      Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hga', le_of_lt hgb'⟩)
    obtain ⟨c, hc, hgc⟩ := intermediate_value_uIcc (hcontf.mono hsub) hmem
    exact hne c (hsub hc) hgc
  exact argChangeHoriz_abs_lt_pi_of_re_sign f T x0 x1 hdiff hcont hsign

end Backlund
