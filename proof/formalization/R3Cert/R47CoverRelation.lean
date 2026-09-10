/-
  The covering relation for `Hnorm`: `CoverR = FlpStepAt ∪ AdjLeafStep`, proven to REFINE
  `StraightStep_sized`.  This is the exact input format for `straightProgress_sized_of_coverage`
  (BGSCLFlpStepAt): with a coverage proof `∀ t, strDefect t ≠ 0 → ∃ t', CoverR t t'`, `Hnorm` follows
  via `hnorm_of_coverage`.

  Two proven straightening classes are assembled here:
    * `FlpStepAt` (BGSCLFlpStepAt) -- the sibling multi-flip class (`FlpStepAt.straightStep`);
    * `AdjLeafStep` (this file) -- the adjacent leaf move (`R47AdjLeafStep.adjLeaf_straightStep`).

  The refinement half (`CoverR.straightStep`) is COMPLETE and kernel-clean.  The remaining open obligation
  to close `Hnorm` is COVERAGE for `CoverR` -- and, empirically, the residual past these two classes is the
  whole-hub / k-star relocation family, whose `Aobj`-monotonicity fails the local `G1` lift-gain and needs a
  global monomer-dimer inequality (see `proof/verification/REALOBLB_TYPEW_B0_FINDINGS.md`).

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLFlpStepAt
import R3Cert.R47AdjLeafStep

namespace R3Cert
namespace Step3

open RTree

/-- The adjacent leaf move as a whole-tree relation: at a child `par_w = node (flpLeaf :: par_v :: Other)`
    with `par_v = node (flpLeaf :: Bv)`, `Bv` a nonempty cherry list and `1 ≤ npCount Other`, extend the
    sibling leaf and drop the relocated leaf. -/
def AdjLeafStep (t t' : UTree) : Prop :=
  ∃ (pre post Bv Other : List UTree),
    Bv ≠ [] ∧ (∀ x ∈ Bv, isCherry x = true) ∧ 1 ≤ npCount Other ∧
    t = UTree.node (pre ++ UTree.node (flpLeaf :: UTree.node (flpLeaf :: Bv) :: Other) :: post) ∧
    t' = UTree.node (pre ++ UTree.node (UTree.node (flpStem :: Bv) :: Other) :: post)

theorem AdjLeafStep.straightStep {t t' : UTree} (h : AdjLeafStep t t') : StraightStep_sized t t' := by
  obtain ⟨pre, post, Bv, Other, hBv, hcherry, hOther, rfl, rfl⟩ := h
  exact adjLeaf_straightStep pre post Bv Other hBv hcherry hOther

/-- **The covering relation**: a straightening step is a sibling multi-flip OR an adjacent leaf move. -/
def CoverR (t t' : UTree) : Prop := FlpStepAt t t' ∨ AdjLeafStep t t'

/-- **`CoverR` refines `StraightStep_sized`** -- both classes are proven straightening steps. -/
theorem CoverR.straightStep {t t' : UTree} (h : CoverR t t') : StraightStep_sized t t' := by
  rcases h with h | h
  · exact h.straightStep
  · exact h.straightStep

/-- **Hnorm from `CoverR` coverage.**  With a coverage proof for `CoverR`, every tree is `Aobj`-dominated
    by a hub-backbone of its own vertex count.  (The coverage hypothesis is the sole remaining open
    obligation; the refinement is discharged by `CoverR.straightStep`.) -/
theorem hnorm_of_coverR_coverage
    (hcov : ∀ t : UTree, strDefect t ≠ 0 → ∃ t', CoverR t t') :
    ∀ t : UTree, ∃ s : List Hub, usize (backboneU s) = usize t ∧ Aobj t ≤ Aobj (backboneU s) :=
  hnorm_of_coverage CoverR (fun h => CoverR.straightStep h) hcov

end Step3
end R3Cert
