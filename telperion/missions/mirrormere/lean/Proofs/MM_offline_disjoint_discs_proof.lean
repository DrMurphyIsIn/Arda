/-
  Proofs.MM_offline_disjoint_discs_proof -- AUTHORED proof of node
  MM_offline_disjoint_discs (Routes-roadmap E4b, QC_RECURRENCE section 4.3).

  Kernel-verified locally on rh/routes-node-proofs against the v4.32.0 toolchain
  (leanprover/lean4:v4.32.0). `#print axioms offline_disjoint_discs` =
  [propext, Classical.choice, Quot.sound], 0 sorryAx. Pure Mathlib metric
  topology; imports Mathlib only. conjecture1_proved = False.

  Content: finitely many distinct points strictly inside the open critical strip
  (0 < re < 1) admit closed discs of one common positive radius that are pairwise
  disjoint (distinct centres) and each contained in the strip. Radius is a third
  of the minimum over the finite set C = {1} ∪ {distinct pairwise distances} ∪
  {boundary gaps min(re, 1-re)}; disjointness via Metric.closedBall_disjoint_closedBall
  (r + r < dist), strip containment via |s.re - z.re| ≤ dist s z ≤ r
  (Complex.abs_re_le_norm). Empty/singleton benign (1 ∈ C keeps C nonempty).
-/
import Mathlib

theorem offline_disjoint_discs (S : Finset ℂ)
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ S, ∀ w ∈ S, z ≠ w → Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧
      (∀ z ∈ S, Metric.closedBall z r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) := by
  classical
  -- distinct pairwise distances
  let D : Finset ℝ := ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)
  -- distance of each centre to the strip boundary
  let B : Finset ℝ := S.image (fun z => min z.re (1 - z.re))
  -- the combined constraint set, kept nonempty by 1
  let C : Finset ℝ := insert (1 : ℝ) (D ∪ B)
  have hDmem : ∀ x, x ∈ D ↔ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ dist a b = x := by
    intro x
    simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hne⟩, rfl⟩; exact ⟨a, ha, b, hb, hne, rfl⟩
    · rintro ⟨a, ha, b, hb, hne, rfl⟩; exact ⟨(a, b), ⟨⟨ha, hb⟩, hne⟩, rfl⟩
  have hCpos : ∀ x ∈ C, 0 < x := by
    intro x hx
    simp only [C, Finset.mem_insert, Finset.mem_union] at hx
    rcases hx with h1 | hD' | hB'
    · rw [h1]; exact one_pos
    · obtain ⟨a, _, b, _, hne, rfl⟩ := (hDmem x).mp hD'
      exact dist_pos.mpr hne
    · simp only [B, Finset.mem_image] at hB'
      obtain ⟨z, hz, rfl⟩ := hB'
      obtain ⟨hz0, hz1⟩ := hstrip z hz
      exact lt_min hz0 (by linarith)
  have hCne : C.Nonempty := ⟨1, by simp [C]⟩
  set m := C.min' hCne with hm
  have hmpos : 0 < m := hCpos _ (C.min'_mem hCne)
  refine ⟨m / 3, by positivity, ?_, ?_⟩
  · -- pairwise disjointness of closed discs
    intro z hz w hw hne
    apply Metric.closedBall_disjoint_closedBall
    have hdD : dist z w ∈ D := (hDmem _).mpr ⟨z, hz, w, hw, hne, rfl⟩
    have : m ≤ dist z w :=
      C.min'_le _ (by simp only [C, Finset.mem_insert, Finset.mem_union]; right; left; exact hdD)
    linarith
  · -- each disc stays inside the strip
    intro z hz s hs
    have hsdist : dist s z ≤ m / 3 := by rw [Metric.mem_closedBall] at hs; exact hs
    have hbB : min z.re (1 - z.re) ∈ B := by simp only [B, Finset.mem_image]; exact ⟨z, hz, rfl⟩
    have hmle : m ≤ min z.re (1 - z.re) :=
      C.min'_le _ (by simp only [C, Finset.mem_insert, Finset.mem_union]; right; right; exact hbB)
    have hre : |s.re - z.re| ≤ dist s z := by
      have := Complex.abs_re_le_norm (s - z)
      simpa [Complex.dist_eq, Complex.sub_re] using this
    obtain ⟨hz0, hz1⟩ := hstrip z hz
    have h1 : m ≤ z.re := le_trans hmle (min_le_left _ _)
    have h2 : m ≤ 1 - z.re := le_trans hmle (min_le_right _ _)
    have hb := abs_le.mp (le_trans hre hsdist)
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
