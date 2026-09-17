/-
RvMBacklundSignClosed — Backlund S(T)=O(log T), PR 4c (sign-on-closed): the bridge from 4c-order to
4c-nonstrict.

The partition (PR 4c-order) guarantees no forbidden point (= zero of `Re ζ`) strictly inside each open
piece.  The non-strict confinement (PR 4c-nonstrict) needs `Re ζ` one sign on the CLOSED piece.  This
file supplies the missing analytic step: a continuous real function that is nonzero on an open interval
is one sign on the CLOSED interval (the endpoints, possible zeros, are sign-compatible limits).

  * `re_one_sign_of_ne_zero_Ioo` — `g` continuous on `[x0,x1]`, `g ≠ 0` on `(x0,x1)` (with `x0 < x1`) ⟹
    `0 ≤ g` on `[x0,x1]` OR `g ≤ 0` on `[x0,x1]`.

Proof: at the midpoint `g ≠ 0`; if `g` took the opposite sign anywhere on `[x0,x1]`, IVT
(`intermediate_value_uIcc`) between the midpoint and that point would produce a zero strictly inside
`(x0,x1)` — contradiction.  conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundConfineNonstrict

namespace Backlund

open Set in
/-- **Sign-constancy on the closed interval from nonvanishing on the open interval.** -/
theorem re_one_sign_of_ne_zero_Ioo (g : ℝ → ℝ) (x0 x1 : ℝ) (hlt : x0 < x1)
    (hcont : ContinuousOn g (Set.Icc x0 x1))
    (hopen : ∀ x ∈ Set.Ioo x0 x1, g x ≠ 0) :
    (∀ x ∈ Set.Icc x0 x1, 0 ≤ g x) ∨ (∀ x ∈ Set.Icc x0 x1, g x ≤ 0) := by
  set m : ℝ := (x0 + x1) / 2 with hm
  have hm_mem : m ∈ Set.Ioo x0 x1 := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  -- one-directional core, reused on g and -g
  have key : ∀ (h : ℝ → ℝ), ContinuousOn h (Set.Icc x0 x1) →
      (∀ x ∈ Set.Ioo x0 x1, h x ≠ 0) → 0 < h m → ∀ q ∈ Set.Icc x0 x1, 0 ≤ h q := by
    intro h hcont_h hopen_h hhm q hq
    by_contra hcon
    push_neg at hcon
    have hsub : Set.uIcc m q ⊆ Set.Icc x0 x1 :=
      Set.uIcc_subset_Icc (Set.mem_Icc_of_Ioo hm_mem) hq
    have hmem0 : (0 : ℝ) ∈ Set.uIcc (h m) (h q) :=
      Set.mem_uIcc.mpr (Or.inr ⟨hcon.le, hhm.le⟩)
    obtain ⟨c, hc, hgc⟩ := intermediate_value_uIcc (hcont_h.mono hsub) hmem0
    have hcm : c ≠ m := by rintro rfl; exact (ne_of_gt hhm) hgc
    have hcq : c ≠ q := by rintro rfl; exact (ne_of_lt hcon) hgc
    rw [Set.mem_uIcc] at hc
    have hcIoo : c ∈ Set.Ioo x0 x1 := by
      rcases hc with ⟨hml, hlq⟩ | ⟨hql, hlm⟩
      · exact ⟨lt_of_lt_of_le hm_mem.1 hml, lt_of_lt_of_le (lt_of_le_of_ne hlq hcq) hq.2⟩
      · exact ⟨lt_of_le_of_lt hq.1 (lt_of_le_of_ne hql (Ne.symm hcq)),
          lt_of_le_of_lt hlm hm_mem.2⟩
    exact hopen_h c hcIoo hgc
  rcases lt_or_gt_of_ne (hopen m hm_mem) with hlt' | hgt'
  · right
    intro x hx
    have hneg : 0 ≤ (-g) m := by simp; linarith
    have := key (-g) hcont.neg (fun y hy => neg_ne_zero.mpr (hopen y hy)) (by simpa using hlt') x hx
    simpa using this
  · left
    exact key g hcont hopen hgt'

end Backlund
