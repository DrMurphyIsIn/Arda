/-
  Problem A, Stage A1: the STUCK-PAIR characterization for the m >= 3 multi-hub front.

  The capstone consumes `Hdom` only on OrderedStep-STUCK states (`chain_to_normalForm` collapses
  everything else, Aobj-monotonically).  This file characterizes stuckness structurally: at EVERY
  adjacent hub pair of a stuck Balanced state, the ordering-designated donor is DE-LOADED -- it
  carries strictly fewer than `5 - load` five-arms, so the topped-up split `hsplit` of the
  applicable merge constructor cannot be formed.  (The two ordering side conditions are jointly
  exhaustive, so ONE of the two merge orientations always applies unless its split fails.)

  Consequences packaged here:
    * `exists_split_iff_count` -- the `hsplit` precondition is EXACTLY a five-count inequality;
    * `OrderedStep.append_left` / `stuck_suffix` -- stuckness restricts to every suffix, so the
      characterization holds at every backbone position, not just the head;
    * `stuck_pair_deloaded` / `stuck_pair_dichotomy` -- the per-pair de-loaded-donor laws.
  Note the `load = 5` corner: `5 - load = 0` makes the split trivially formable, so a stuck
  state's hubward-ordered pairs necessarily have `load < 5` -- the dichotomy captures this as an
  impossible (`count < 0`) branch.

  This is the structural half of the length >= 3 reduction (plan stage A1); the value bound
  `stuck_mhub_le_tie` (A3) remains the open core.  Genuine proofs (no `sorry`).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47StepMono

namespace R3Cert
namespace Step3

open RTree

/-! ### The split precondition as a five-count inequality -/

/-- The topped-up split `hsplit` exists iff the donor carries at least `k` five-arms. -/
theorem exists_split_iff_count (l : List ℕ) (k : ℕ) :
    (∃ others, l.Perm (List.replicate k 5 ++ others)) ↔ k ≤ l.count 5 := by
  constructor
  · rintro ⟨others, hperm⟩
    have := hperm.count_eq 5
    simp [List.count_append] at this
    omega
  · intro hk
    exact (List.replicate_sublist_iff.mpr hk).exists_perm_append

/-! ### Stuckness restricts to suffixes -/

/-- `OrderedStep` lifts along any prefix (iterated `tail`). -/
theorem OrderedStep.append_left (pre : List Hub) {s u : List Hub} (h : OrderedStep s u) :
    OrderedStep (pre ++ s) (pre ++ u) := by
  induction pre with
  | nil => exact h
  | cons hd tl ih => exact ih.tail

/-- A stuck state is stuck at every suffix. -/
theorem stuck_suffix (pre : List Hub) {s : List Hub}
    (h : ∀ u, ¬ OrderedStep (pre ++ s) u) : ∀ u, ¬ OrderedStep s u :=
  fun _ hu => h _ (hu.append_left pre)

/-! ### The stuck-pair laws -/

/-- **A1: the stuck-pair characterization.**  In an OrderedStep-stuck Balanced state, at every
    adjacent hub pair the ordering-designated donor is DE-LOADED: whenever the hubward ordering
    holds, hub B carries fewer than `5 - cb` five-arms; whenever the anti-hubward ordering holds,
    hub A carries fewer than `5 - cA` five-arms. -/
theorem stuck_pair_deloaded {pre : List Hub} {armsA : List ℕ} {cA : ℕ} {armsB : List ℕ} {cb : ℕ}
    {rest : List Hub}
    (hbal : Balanced (pre ++ (armsA, cA) :: (armsB, cb) :: rest))
    (hstuck : ∀ u, ¬ OrderedStep (pre ++ (armsA, cA) :: (armsB, cb) :: rest) u) :
    (armsB.length + (tailU rest).length ≤ armsA.length → armsB.count 5 < 5 - cb)
      ∧ (armsA.length + 1 ≤ armsB.length + (tailU rest).length → armsA.count 5 < 5 - cA) := by
  have hstuck' := stuck_suffix pre hstuck
  have hcb : cb ≤ 5 := (hbal (armsB, cb) (by simp)).2
  have hcA : cA ≤ 5 := (hbal (armsA, cA) (by simp)).2
  constructor
  · intro hord
    by_contra hcount
    push_neg at hcount
    obtain ⟨others, hsplit⟩ := (exists_split_iff_count armsB (5 - cb)).mpr hcount
    exact hstuck' _ (OrderedStep.merge hcb hsplit hord)
  · intro hord
    by_contra hcount
    push_neg at hcount
    obtain ⟨othersA, hsplit⟩ := (exists_split_iff_count armsA (5 - cA)).mpr hcount
    exact hstuck' _ (OrderedStep.mergeRev hcA hsplit hord)

/-- **The per-pair dichotomy.**  The two ordering side conditions are jointly exhaustive, so at
    every adjacent pair of a stuck Balanced state, EITHER the hubward ordering holds with a
    de-loaded B, OR the anti-hubward ordering holds with a de-loaded A. -/
theorem stuck_pair_dichotomy {pre : List Hub} {armsA : List ℕ} {cA : ℕ} {armsB : List ℕ}
    {cb : ℕ} {rest : List Hub}
    (hbal : Balanced (pre ++ (armsA, cA) :: (armsB, cb) :: rest))
    (hstuck : ∀ u, ¬ OrderedStep (pre ++ (armsA, cA) :: (armsB, cb) :: rest) u) :
    (armsB.length + (tailU rest).length ≤ armsA.length ∧ armsB.count 5 < 5 - cb)
      ∨ (armsA.length + 1 ≤ armsB.length + (tailU rest).length ∧ armsA.count 5 < 5 - cA) := by
  obtain ⟨h1, h2⟩ := stuck_pair_deloaded hbal hstuck
  by_cases h : armsB.length + (tailU rest).length ≤ armsA.length
  · exact Or.inl ⟨h, h1 h⟩
  · exact Or.inr ⟨by omega, h2 (by omega)⟩

end Step3
end R3Cert
