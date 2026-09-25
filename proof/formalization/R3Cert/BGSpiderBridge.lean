/-
  BG spider reduction: bridge from the cavity objective `piRoot` to the matching objective `Aobj`
  (2026-09-24).

  `toU` sends a `Branch` (cavity recursion, `R3Cert.BGSCL`) to the bare rooted tree `UTree`
  (`R3Cert.Step3`, `R47Tree.lean`), whose `Aobj = Ztot (dtRealize t)` is the degree-weighted matching sum
  `Σ_M ∏_{ij∈M} 1/(deg i · deg j)` = per(L)/∏deg.  Proved:

  * `dtSub_toU` — for every planted branch, the realized non-root subtree has
    `Ztot = T_b = (cav b).2` and `Zopen = U_b = (cav b).1`;
  * `Aobj_toU_node` — `Aobj (node (map toU cs)) = piRoot cs`;
  * `spider_dominates_of_maxDegreeRoot_Aobj` — the combined spider theorem restated for `Aobj`.

  No `sorry`; standard axioms.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.R47Tree
import R3Cert.BGSpiderLowDegree

namespace R3Cert
namespace BGSCL

open Step3 RTree

mutual
  /-- `Branch → UTree`, shape-preserving. -/
  def toU : Branch → UTree
    | .node cs => UTree.node (toUList cs)
  def toUList : List Branch → List UTree
    | [] => []
    | c :: t => toU c :: toUList t
end

theorem toUList_length : ∀ cs : List Branch, (toUList cs).length = cs.length
  | [] => by simp [toUList]
  | c :: t => by simp [toUList, toUList_length t]

theorem udeg_toU (c : Branch) : (udeg (toU c) : ℝ) = (bcc c : ℝ) + 1 := by
  cases c with
  | node cs => simp [toU, udeg, bcc, toUList_length]

/-- Children facts: `Popen` of the realized children is `∏ T_c`, and the cavity sum is `Σ y_c / d`. -/
theorem children_facts (d : ℕ) (hd : 0 < d) :
    ∀ cs : List Branch,
      (∀ c ∈ cs, Ztot (dtSub (toU c)) = (cav c).2 ∧ Zopen (dtSub (toU c)) = (cav c).1) →
      Popen (dtChildren d (toUList cs)) = (cs.map (fun c => (cav c).2)).prod ∧
      ((dtChildren d (toUList cs)).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum
        = (cs.map bY).sum / (d : ℝ)
  | [], _ => by simp [toUList, dtChildren_nil, Popen]
  | c :: t, h => by
      have hc := h c (by simp)
      have ht := children_facts d hd t (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      simp only [toUList, dtChildren_cons, Popen, List.map_cons, List.prod_cons, List.sum_cons]
      rw [hc.1, hc.2, ht.1, ht.2, udeg_toU]
      refine ⟨rfl, ?_⟩
      have hT := btotal_pos c
      have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
      unfold bY bh
      field_simp

/-- **The realized non-root subtree has `Ztot = T_b`, `Zopen = U_b`.** -/
theorem dtSub_toU (b : Branch) :
    Ztot (dtSub (toU b)) = (cav b).2 ∧ Zopen (dtSub (toU b)) = (cav b).1 := by
  refine scl_of_child_step bsize bchildren
    (fun b => Ztot (dtSub (toU b)) = (cav b).2 ∧ Zopen (dtSub (toU b)) = (cav b).1)
    bchildren_bsize_lt (fun a hIH => ?_) b
  cases a with
  | node cs =>
    have hIH' : ∀ c ∈ cs, Ztot (dtSub (toU c)) = (cav c).2 ∧ Zopen (dtSub (toU c)) = (cav c).1 :=
      fun c hc => hIH c (by simpa only [bchildren] using hc)
    have hf := children_facts (cs.length + 1) (by omega) cs hIH'
    have hne : ∀ p ∈ dtChildren (cs.length + 1) (toUList cs), Ztot p.2 ≠ 0 := by
      intro p hp
      have hPpos : Popen (dtChildren (cs.length + 1) (toUList cs)) ≠ 0 := by
        rw [hf.1]; exact (prodT_pos cs).ne'
      -- a factor of a nonzero product is nonzero
      have key : ∀ (l : List (ℝ × RTree)), Popen l ≠ 0 → ∀ q ∈ l, Ztot q.2 ≠ 0 := by
        intro l
        induction l with
        | nil => intro _ q hq; simp at hq
        | cons x r ih =>
            intro hl q hq
            obtain ⟨w, c'⟩ := x
            simp only [Popen] at hl
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact left_ne_zero_of_mul hl
            · exact ih (right_ne_zero_of_mul hl) q hq'
      exact key _ hPpos p hp
    have hM := Matched_factor _ hne
    have hlen : ((toUList cs).length : ℕ) = cs.length := toUList_length cs
    simp only [toU, dtSub_node, hlen, Ztot, Zopen]
    rw [hM, hf.1, hf.2]
    simp only [cav, cavAgg_fst, cavAgg_snd]
    push_cast
    constructor <;> first | rfl | ring | simp

/-- **Bridge:** `Aobj (node (map toU cs)) = piRoot cs`. -/
theorem Aobj_toU_node (cs : List Branch) : Aobj (toU (Branch.node cs)) = piRoot cs := by
  have hIH : ∀ c ∈ cs, Ztot (dtSub (toU c)) = (cav c).2 ∧ Zopen (dtSub (toU c)) = (cav c).1 :=
    fun c _ => dtSub_toU c
  rcases Nat.eq_zero_or_pos cs.length with h0 | hpos
  · have : cs = [] := List.length_eq_zero_iff.mp h0
    subst this
    simp [Aobj, toU, toUList, dtRealize_node, dtChildren_nil, Ztot, Popen, Matched, piRoot]
  · have hf := children_facts cs.length hpos cs hIH
    have hne : ∀ p ∈ dtChildren cs.length (toUList cs), Ztot p.2 ≠ 0 := by
      intro p hp
      have hPpos : Popen (dtChildren cs.length (toUList cs)) ≠ 0 := by
        rw [hf.1]; exact (prodT_pos cs).ne'
      have key : ∀ (l : List (ℝ × RTree)), Popen l ≠ 0 → ∀ q ∈ l, Ztot q.2 ≠ 0 := by
        intro l
        induction l with
        | nil => intro _ q hq; simp at hq
        | cons x r ih =>
            intro hl q hq
            obtain ⟨w, c'⟩ := x
            simp only [Popen] at hl
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact left_ne_zero_of_mul hl
            · exact ih (right_ne_zero_of_mul hl) q hq'
      exact key _ hPpos p hp
    have hM := Matched_factor _ hne
    have hlen : ((toUList cs).length : ℕ) = cs.length := toUList_length cs
    simp only [Aobj, toU, dtRealize_node, hlen, Ztot]
    rw [hM, hf.1, hf.2]
    unfold piRoot
    ring

/-- **The combined spider theorem for the matching objective `Aobj`.** -/
theorem spider_dominates_of_maxDegreeRoot_Aobj (cs : List Branch) (hk2 : 2 ≤ cs.length)
    (hcap : ∀ c ∈ cs, maxCh c + 1 ≤ cs.length) (hN : 491 ≤ bsizeList cs)
    (hna : cs.length ≤ 23 ∨ ∃ c ∈ cs, ¬ IsAtom c) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧
      Aobj (toU (Branch.node cs)) < Aobj (toU (Branch.node (spiderB a q))) := by
  obtain ⟨a, q, hq, hs, hlt⟩ := spider_dominates_of_maxDegreeRoot cs hk2 hcap hN hna
  exact ⟨a, q, hq, hs, by rw [Aobj_toU_node, Aobj_toU_node]; exact hlt⟩

end BGSCL
end R3Cert
