/-
  R4-R7 campaign, PHASE 7: the SIZE-FREE tree->hub reduction is TRIVIAL (honest scope marker).

  `StraightProgress` (R47R7Straighten) asks: every positive-defect tree admits an `Aobj`-non-
  decreasing, `strDefect`-decreasing step to SOME tree `t'`.  Because `t'` is UNRESTRICTED (no
  size / vertex-count constraint), this is TRIVIALLY TRUE: take `t'` to be a large near-star
  backbone, whose `strDefect` is `0` and whose `Aobj = (26/23)·(621/64)^K` is unbounded
  (`nearstar_arms_Aobj`).  Hence the SIZE-FREE `tree_to_hub` (`∀ t, ∃ s, Aobj t ≤ Aobj (backboneU s)`)
  holds unconditionally.

  IMPORTANT SCOPE NOTE.  This closes only the SIZE-FREE reduction, which feeds the OLD, ill-posed
  capstone `conjecture1_of_layers` (fixed `tieU`; unusable because `Aobj ~ ρ_B^n` is unbounded).
  The WELL-POSED capstone `conjecture1_of_layers_fixedN` requires a SIZE-PRESERVING witness
  (`stateSize s = usize t`).  The genuine mathematical content -- a same-vertex-count straightening
  move that does not decrease `Aobj` -- is the SIZE-PRESERVING obligation (`StraightProgress_sized`,
  a separate line of work).  This file exists to record, in-repo, that the size-free version is
  trivial, so it is never mistaken for the hard result.

  Genuine proof (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7Decode
import R3Cert.R47NearStarValue

namespace R3Cert
namespace Step3

open RTree

/-- **`StraightProgress` is trivial** (size-free): any positive-defect tree steps to a large
    near-star backbone of not-smaller `Aobj` and zero defect.  The `t'` is unconstrained in size,
    and `Aobj (backboneU [(replicate K 5, 0)]) = (26/23)·(621/64)^K` is unbounded in `K`. -/
theorem straightProgress_trivial : StraightProgress := by
  intro t ht
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Aobj t) (by norm_num : (1 : ℝ) < 621 / 64)
  refine ⟨backboneU [(List.replicate (n + 1) 5, 0)], ?_, ?_⟩
  · rw [nearstar_arms_Aobj (n + 1) (Nat.succ_pos n)]
    have h2 : (621 / 64 : ℝ) ^ n ≤ (621 / 64) ^ (n + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    have h3 : (621 / 64 : ℝ) ^ (n + 1) ≤ (26 / 23) * (621 / 64) ^ (n + 1) := by
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 621 / 64) (n + 1)]
    linarith [hn, h2, h3]
  · rw [strDefect_backboneU]; exact Nat.pos_of_ne_zero ht

/-- **The size-free `tree_to_hub`, UNCONDITIONAL.**  Every tree is `Aobj`-dominated by some
    hub-backbone.  Trivial (a large near-star dominates any fixed `Aobj`); see the scope note --
    the well-posed capstone needs the SIZE-PRESERVING version. -/
theorem tree_to_hub : ∀ t : UTree, ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) :=
  tree_to_hub_of_progress straightProgress_trivial

end Step3
end R3Cert
