/-
RvMBacklundOrder — Backlund S(T)=O(log T), PR 4c (ordering): finite forbidden set ⟹ monotone partition.

Pure order-theory combinatorics (no analysis).  Given a finite set `Z` of "forbidden" points inside
`[a,b]` (for us: the zeros of `F_T = Re ζ(·+iT)` on `[1/2,2]`, finite by PR 4c-finiteness), we sort
`{a,b} ∪ Z` into a monotone partition `σ : ℕ → ℝ` of `[a,b]` with at most `Z.card + 1` pieces, no
forbidden point strictly inside any open piece.

  * `exists_monotone_partition_of_finite` — the partition-existence lemma.

Feeds `argChangeHoriz_abs_le_partition` (PR 4b): applied to `Z =` the `F_T`-zeros, each open piece is
`F_T`-zero-free, so `Re ζ` is one sign there (PR 4c-sign), and the `≤ (Z.card+1)·π` bound follows.  The
count `Z.card ≤` the PR 3b Jensen bound and the confinement/integrability discharge (the `ζ ≠ 0` `S(T)`
subtlety, and a non-strict `Re ≥ 0 ⟹ arg ∈ [-π/2,π/2]` variant needed because the piece endpoints ARE
zeros) are PR 4c-count.  conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundFinite

namespace Backlund

open Finset in
/-- **Monotone partition from a finite forbidden set.**  If `Z ⊆ [a,b]` is finite, there is a monotone
    `σ : ℕ → ℝ` with `σ 0 = a`, `σ N = b`, `N ≤ Z.card + 1`, every `σ k ∈ [a,b]`, and no point of `Z`
    lies strictly between consecutive partition points. -/
theorem exists_monotone_partition_of_finite (Z : Finset ℝ) (a b : ℝ) (hab : a ≤ b)
    (hZ : ∀ z ∈ Z, z ∈ Set.Icc a b) :
    ∃ (N : ℕ) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = a ∧ σ N = b ∧ N ≤ Z.card + 1 ∧
      (∀ k, σ k ∈ Set.Icc a b) ∧
      (∀ k, k < N → ∀ z ∈ Z, z ≤ σ k ∨ σ (k + 1) ≤ z) := by
  classical
  set S : Finset ℝ := insert a (insert b Z) with hS
  have haS : a ∈ S := by simp [hS]
  have hbS : b ∈ S := by simp [hS]
  have hne : S.Nonempty := ⟨a, haS⟩
  -- a lower-bounds, b upper-bounds S
  have hlb : ∀ x ∈ S, a ≤ x := by
    intro x hx
    simp only [hS, Finset.mem_insert] at hx
    rcases hx with heq | heq | hx
    · exact heq.ge
    · rw [heq]; exact hab
    · exact (hZ x hx).1
  have hub : ∀ x ∈ S, x ≤ b := by
    intro x hx
    simp only [hS, Finset.mem_insert] at hx
    rcases hx with heq | heq | hx
    · rw [heq]; exact hab
    · exact heq.le
    · exact (hZ x hx).2
  have hmin : S.min' hne = a := le_antisymm (S.min'_le a haS) (S.le_min' hne a hlb)
  have hmax : S.max' hne = b := le_antisymm (S.max'_le hne b hub) (S.le_max' b hbS)
  set m := S.card with hm
  have hmpos : 0 < m := Finset.card_pos.mpr hne
  set e : Fin m ↪o ℝ := S.orderEmbOfFin rfl with he
  have hemem : ∀ i : Fin m, e i ∈ S := by intro i; rw [he]; exact orderEmbOfFin_mem S rfl i
  set σ : ℕ → ℝ := fun k => if hk : k < m then e ⟨k, hk⟩ else b with hσdef
  have hσeq : ∀ k (hk : k < m), σ k = e ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hσb : ∀ k, ¬ k < m → σ k = b := fun k hk => dif_neg hk
  -- every value is in [a,b]
  have hmemIcc : ∀ k, σ k ∈ Set.Icc a b := by
    intro k
    by_cases hk : k < m
    · rw [hσeq k hk]; exact ⟨hlb _ (hemem _), hub _ (hemem _)⟩
    · rw [hσb k hk]; exact ⟨hab, le_refl b⟩
  refine ⟨m - 1, σ, ?_, ?_, ?_, ?_, hmemIcc, ?_⟩
  · -- Monotone σ
    intro k l hkl
    by_cases hl : l < m
    · have hk : k < m := lt_of_le_of_lt hkl hl
      rw [hσeq k hk, hσeq l hl]
      exact e.monotone (Fin.mk_le_mk.mpr hkl)
    · rw [hσb l hl]; exact (hmemIcc k).2
  · -- σ 0 = a
    rw [hσeq 0 hmpos, he, orderEmbOfFin_zero (rfl : S.card = m) hmpos]; exact hmin
  · -- σ (m-1) = b
    have hlt : m - 1 < m := Nat.sub_lt hmpos Nat.one_pos
    rw [hσeq (m - 1) hlt, he,
      show (⟨m - 1, hlt⟩ : Fin m) = ⟨m - 1, Nat.sub_lt hmpos (Nat.succ_pos 0)⟩ from rfl,
      orderEmbOfFin_last (rfl : S.card = m) hmpos]
    exact hmax
  · -- N ≤ Z.card + 1
    have h1 : (insert b Z).card ≤ Z.card + 1 := Finset.card_insert_le _ _
    have h2 : m ≤ (insert b Z).card + 1 := Finset.card_insert_le _ _
    omega
  · -- nothing of Z strictly between σ k and σ (k+1)
    intro k hk z hz
    have hk1 : k + 1 < m := by omega
    have hk0 : k < m := by omega
    by_contra hcon
    push_neg at hcon
    obtain ⟨hlt1, hlt2⟩ := hcon
    rw [hσeq k hk0] at hlt1
    rw [hσeq (k + 1) hk1] at hlt2
    -- z ∈ S is in the range of e
    have hzS : z ∈ S := by rw [hS]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    have hzrange : z ∈ Set.range e := by rw [he, range_orderEmbOfFin S rfl]; exact hzS
    obtain ⟨j, hj⟩ := hzrange
    rw [← hj] at hlt1 hlt2
    have hkj : (⟨k, hk0⟩ : Fin m) < j := e.lt_iff_lt.mp hlt1
    have hjk : j < (⟨k + 1, hk1⟩ : Fin m) := e.lt_iff_lt.mp hlt2
    have hkj' : k < (j : ℕ) := hkj
    have hjk' : (j : ℕ) < k + 1 := hjk
    omega

end Backlund
