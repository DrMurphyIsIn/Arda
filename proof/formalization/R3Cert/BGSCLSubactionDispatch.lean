/-
  Top-level dispatch for `IsSubaction ρwit` (Wave 1 portion, 2026-09-04).

  Assembles the per-degree SUBACTION cells (`BGSCLSubaction`, `BGSCLSubactionDeg3`,
  `BGSCLSubactionDeg3Mid`) into the single obligation `IsSubaction ρwit` that
  `ceiling_of_witness` needs.  The dispatcher `rcases` the child list `cs` by length
  (node degree `= |cs| + 1`) and, within each length, by the children's `bcc` classes,
  applying the matching cell.  Child order is canonicalized by `subaction_perm`
  (permutation invariance of the (SUB) predicate) so the 9 ordered degree-3 pairs reduce
  to the 6 canonical `subaction_deg3_*` cells.

  CANONICALIZATION CONVENTION (shared with the deg-4 wave):
    child classes by `bcc`:  L = 0,  deg-2 = 1,  deg-3 = 2,  deg-4 = 3,  H = (4 ≤ bcc);
    canonical child order = non-decreasing `bcc`.

  WAVE 1 SCOPE:  `subaction_perm` + the degree-1/2/3 arms are fully proven (no `sorry`).
  The degree-4 arm (`cs.length = 3`) and the tail arm (`cs.length ≥ 4`) are left as clearly
  marked `sorry` PLACEHOLDERS, wired in Wave 2 once the `subaction_deg4_*` cells and
  `tail_wrapper` land.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionDeg3
import R3Cert.BGSCLSubactionDeg3Mid

namespace R3Cert
namespace BGSCL

open Real

/-! ### Permutation invariance of the (SUB) predicate. -/

/-- `ρwit` reads only through `bcc (node cs) = |cs|` and `bY (node cs)` (which, by `bY_node`,
    depends only on `|cs|` and `(cs.map bY).sum`); hence it is invariant under permuting the
    children.  A `List.Perm` fixes both `|cs|` and `(cs.map bY).sum`, so `ρwit` agrees. -/
theorem ρwit_node_perm {cs cs' : List Branch} (h : cs.Perm cs') :
    ρwit (Branch.node cs) = ρwit (Branch.node cs') := by
  have hlen : cs.length = cs'.length := h.length_eq
  have hbY : (cs.map bY).sum = (cs'.map bY).sum := (h.map bY).sum_eq
  have hbYnode : bY (Branch.node cs) = bY (Branch.node cs') := by
    rw [bY_node, bY_node, hlen, hbY]
  rw [ρwit, ρwit]
  simp only [bcc, hlen, hbYnode]

/-- **Permutation invariance of (SUB).**  The subaction inequality at a hub `node cs` transports
    across any permutation of the children: the log-term (through `(cs.map bY).sum` and `|cs|`), the
    node `ρwit` (`ρwit_node_perm`), and the RHS `(cs.map ρwit).sum` are each Perm-invariant. -/
theorem subaction_perm {cs cs' : List Branch} (h : cs.Perm cs')
    (hsub : (Real.log (1 + (cs'.map bY).sum / ((cs'.length : ℝ) + 1)) - FSTAR)
        + ρwit (Branch.node cs') ≤ (cs'.map ρwit).sum) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
        + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have hlen : cs.length = cs'.length := h.length_eq
  have hbY : (cs.map bY).sum = (cs'.map bY).sum := (h.map bY).sum_eq
  have hrho : (cs.map ρwit).sum = (cs'.map ρwit).sum := (h.map ρwit).sum_eq
  have hnode : ρwit (Branch.node cs) = ρwit (Branch.node cs') := ρwit_node_perm h
  rw [hbY, hlen, hnode, hrho]
  exact hsub

/-! ### Class helpers. -/

/-- A child with `bcc = 0` is the leaf `node []`. -/
theorem eq_leaf_of_bcc_zero {c : Branch} (hc : bcc c = 0) : c = Branch.node [] := by
  cases c with
  | node cs =>
    simp only [bcc, List.length_eq_zero_iff] at hc
    rw [hc]

/-! ### Degree-1 arm (`cs = []`). -/

/-- Degree-1 dispatch: the leaf node. -/
theorem subaction_deg1 :
    (Real.log (1 + (([] : List Branch).map bY).sum / ((([] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node []) ≤ (([] : List Branch).map ρwit).sum :=
  subaction_nil

/-! ### Degree-2 arm (`cs = [c]`). -/

/-- Degree-2 dispatch: one child, cased by `bcc c` — leaf ⇒ `subaction_cherry`,
    deg-2 ⇒ `subaction_deg2_deg2child`, deg-≥3 ⇒ `subaction_deg2_highchild`. -/
theorem subaction_deg2 (c : Branch) :
    (Real.log (1 + (([c] : List Branch).map bY).sum / ((([c] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c]) ≤ (([c] : List Branch).map ρwit).sum := by
  rcases (show bcc c = 0 ∨ bcc c = 1 ∨ 2 ≤ bcc c by omega) with h | h | h
  · -- leaf child
    rw [eq_leaf_of_bcc_zero h]
    exact subaction_cherry
  · exact subaction_deg2_deg2child c h
  · exact subaction_deg2_highchild c h

/-! ### Degree-3 arm (`cs = [c1, c2]`).

  Canonicalize the ordered pair `(bcc c1, bcc c2)` over the classes {L = 0, deg-2 = 1, H = ≥2}
  to non-decreasing order via `subaction_perm (List.Perm.swap ..)`, reducing the 9 ordered
  profiles to the 6 canonical cells:
    LL  → subaction_broom_d3,          LD2 → subaction_deg3_leaf_deg2,
    LH  → subaction_deg3_leaf_high,    D2D2→ subaction_deg3_deg2children,
    D2H → subaction_deg3_deg2_high,    HH  → subaction_deg3_highchildren. -/

/-- The canonical (non-decreasing) degree-3 cell for classes `(k1, k2)` with `k1 ≤ k2` classwise.
    Handles the 6 canonical orderings; callers use `subaction_perm` to canonicalize. -/
theorem subaction_deg3_canon (c1 c2 : Branch)
    (hle : bcc c1 = 0 ∧ bcc c2 = 0
         ∨ bcc c1 = 0 ∧ bcc c2 = 1
         ∨ bcc c1 = 0 ∧ 2 ≤ bcc c2
         ∨ bcc c1 = 1 ∧ bcc c2 = 1
         ∨ bcc c1 = 1 ∧ 2 ≤ bcc c2
         ∨ 2 ≤ bcc c1 ∧ 2 ≤ bcc c2) :
    (Real.log (1 + (([c1, c2] : List Branch).map bY).sum
        / ((([c1, c2] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2]) ≤ (([c1, c2] : List Branch).map ρwit).sum := by
  rcases hle with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · -- (L, L)
    rw [eq_leaf_of_bcc_zero k1, eq_leaf_of_bcc_zero k2]
    exact subaction_broom_d3
  · -- (L, deg-2)
    rw [eq_leaf_of_bcc_zero k1]
    exact subaction_deg3_leaf_deg2 c2 k2
  · -- (L, high)
    rw [eq_leaf_of_bcc_zero k1]
    exact subaction_deg3_leaf_high c2 k2
  · -- (deg-2, deg-2)
    exact subaction_deg3_deg2children c1 c2 k1 k2
  · -- (deg-2, high)
    exact subaction_deg3_deg2_high c1 c2 k1 k2
  · -- (high, high)
    exact subaction_deg3_highchildren c1 c2 k1 k2

/-- Degree-3 dispatch: two children, canonicalized to non-decreasing `bcc` via `subaction_perm`. -/
theorem subaction_deg3 (c1 c2 : Branch) :
    (Real.log (1 + (([c1, c2] : List Branch).map bY).sum
        / ((([c1, c2] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2]) ≤ (([c1, c2] : List Branch).map ρwit).sum := by
  -- classify each child
  rcases (show bcc c1 = 0 ∨ bcc c1 = 1 ∨ 2 ≤ bcc c1 by omega) with h1 | h1 | h1 <;>
  rcases (show bcc c2 = 0 ∨ bcc c2 = 1 ∨ 2 ≤ bcc c2 by omega) with h2 | h2 | h2
  -- canonical (already non-decreasing) cases: apply directly
  · exact subaction_deg3_canon c1 c2 (Or.inl ⟨h1, h2⟩)
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inl ⟨h1, h2⟩))
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  -- (deg-2, L) → swap to (L, deg-2)
  · exact subaction_perm (List.Perm.swap c2 c1 []) (subaction_deg3_canon c2 c1 (Or.inr (Or.inl ⟨h2, h1⟩)))
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
  -- (high, L) → swap to (L, high)
  · exact subaction_perm (List.Perm.swap c2 c1 []) (subaction_deg3_canon c2 c1 (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
  -- (high, deg-2) → swap to (deg-2, high)
  · exact subaction_perm (List.Perm.swap c2 c1 []) (subaction_deg3_canon c2 c1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))))
  -- (high, high)
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))

/-! ### Top-level dispatch. -/

/-- **`IsSubaction ρwit`** — the single remaining obligation of `ceiling_of_witness`, assembled by
    dispatching on child-list length (node degree) and, within each degree, on the children's
    `bcc` classes.  Degrees 1/2/3 are fully discharged (Wave 1); the degree-4 and tail arms are
    Wave-2 placeholders. -/
theorem isSubaction_ρwit : IsSubaction ρwit := by
  intro cs
  rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, rest⟩⟩⟩⟩
  · -- degree 1: cs = []
    exact subaction_deg1
  · -- degree 2: cs = [c1]
    exact subaction_deg2 c1
  · -- degree 3: cs = [c1, c2]
    exact subaction_deg3 c1 c2
  · -- degree 4: cs = [c1, c2, c3]
    -- WAVE2: exact subaction_perm-canonicalized subaction_deg4_* (35 cells over classes {L,2,3,4,H})
    sorry
  · -- degree ≥ 5: cs = c1 :: c2 :: c3 :: c4 :: rest  (tail)
    -- WAVE2: exact tail_wrapper cs (by omega)
    sorry

end BGSCL
end R3Cert
