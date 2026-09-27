/-
  R3Cert.R47BGConjecture -- the PINNED statement of the campaign's Brualdi-Goldwasser conjecture 1.

  The problem.  Brualdi and Goldwasser (1984) asked for the maximum of the Laplacian ratio
  `pi(T) = per(L(T)) / prod_v deg(v)` over trees on `n` vertices.  It is open: Pant (2026,
  arXiv 2605.14176) refuted the Wu-Dong-Lai subdivided-star answer with infinite families of
  multi-hub caterpillars.  `Aobj t` IS that ratio for the realized tree (`pi_utree`, R47Tree.lean).

  Campaign conjecture 1 (a structural answer).  At every size the maximum is attained on a
  multi-hub cherry-backbone `backboneU s`, which reduces the BG problem to an optimization over
  hub states.  That is `BGBackboneConjecture` below.

  Why this file exists.  The earlier capstones `conjecture1_of_HnormMulti` and
  `conjecture1_of_HnormMulti_of_wholehub` (R47HnormMulti.lean) conclude
  `∀ t, Aobj t ≤ Aobj (tie (usize t))` for a FREE `tie : ℕ → UTree`, under a hypothesis
  `HdomMulti`.  With `tie n` chosen as a per-size maximizer over ALL trees, that conclusion holds
  with no mathematics at all, so the free-tie form says nothing until `tie` is pinned.  The
  statement here quantifies over backbones directly.  `bgBackbone_of_backboneTie` shows exactly
  which pinning makes the free-tie form equivalent to it: `tie n` must itself be a backbone.

  What is proved here: the pinned statement follows from the whole-hub straightening `hwh`
  (`bgBackbone_of_wholehub`) and from the coverage assembly (`bgBackbone_of_extended_coverage`,
  whose FOUR hypotheses -- three move-class interfaces and coverage -- are all still open).
  conjecture1_proved = False.  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.R47HnormMulti
import R3Cert.R47HwhAssembly

namespace R3Cert
namespace Step3

open RTree

/-- **Campaign conjecture 1, pinned.**  Every tree is `Aobj`-dominated by a multi-hub
    cherry-backbone with the same number of vertices; equivalently, the per-size maximum of the
    Brualdi-Goldwasser Laplacian ratio is attained on a backbone.  OPEN. -/
def BGBackboneConjecture : Prop :=
  ∀ t : UTree, ∃ s : List Hub, stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)

/-- The `usize (backboneU s)` form (what `hnorm_of_coverage` produces) implies the pinned
    `stateSize` form.  The empty state realizes the single vertex, which the size-1 hub
    `[([], 0)]` also realizes. -/
theorem bgBackbone_of_usizeForm
    (h : ∀ t : UTree, ∃ s : List Hub, usize (backboneU s) = usize t ∧ Aobj t ≤ Aobj (backboneU s)) :
    BGBackboneConjecture := by
  intro t
  obtain ⟨s, hsz, hle⟩ := h t
  rcases eq_or_ne s [] with rfl | hne
  · have hb0 : backboneU ([] : List Hub) = UTree.node [] := rfl
    have ht1 : usize t = 1 := by
      rw [hb0, usize_node, usizeList_nil] at hsz; omega
    refine ⟨[([], 0)], ?_, ?_⟩
    · rw [ht1]; rfl
    · rw [show backboneU [([], 0)] = UTree.node [] from rfl, ← hb0]; exact hle
  · exact ⟨s, by rw [← usize_backboneU_of_ne_nil hne]; exact hsz, hle⟩

/-- **The one-obligation reduction.**  The size-preserving straightening `StraightProgress_sized`
    (every tree with positive structural defect admits a same-size, `Aobj`-non-decreasing,
    defect-lowering step; OPEN) implies the pinned conjecture.  Coverage plus the three move-class
    interfaces is one way to supply it (`bgBackbone_of_extended_coverage`). -/
theorem bgBackbone_of_straightProgress (h : StraightProgress_sized) : BGBackboneConjecture :=
  bgBackbone_of_usizeForm (tree_to_hub_sized h)

/-- The whole-hub straightening `hwh` (open) implies the pinned conjecture. -/
theorem bgBackbone_of_wholehub
    (hwh : ∀ t : UTree, strDefect t ≠ 0 → RerootMinimal t → (¬ ∃ t', FlpStepAt t t') →
        ∃ t', CoverR t t') :
    BGBackboneConjecture :=
  hnormMulti_of_wholehub hwh

/-- **The coverage assembly, pinned.**  Three move classes, each refining to a
    `StraightStep_sized` (`hgdom`, `hpiece`, `hsymstar`), plus coverage of every defective tree,
    imply the pinned conjecture.  All four hypotheses are open for general trees: the certificates
    in `R47HwhB1Partial`, `R47HwhLeafDecomp`/`R47HwhAdjDecomp`/`R47HwhPieceDecomp` and
    `R47HwhSymStarGenCert` establish the Aobj inequalities on the corresponding cavity/closed-form
    models, and wiring them into `StraightStep_sized` (the cavity-to-`Aobj` bridge) is not done. -/
theorem bgBackbone_of_extended_coverage
    (P_gdom P_piece P_symstar : UTree → Prop)
    (hgdom    : ∀ t : UTree, P_gdom t    → ∃ t', StraightStep_sized t t')
    (hpiece   : ∀ t : UTree, P_piece t   → ∃ t', StraightStep_sized t t')
    (hsymstar : ∀ t : UTree, P_symstar t → ∃ t', StraightStep_sized t t')
    (Hcoverage : ∀ t : UTree, strDefect t ≠ 0 → P_gdom t ∨ P_piece t ∨ P_symstar t) :
    BGBackboneConjecture :=
  bgBackbone_of_usizeForm
    (hwh_of_extended_coverage P_gdom P_piece P_symstar hgdom hpiece hsymstar Hcoverage)

/-- The free-tie capstone is a corollary of the pinned statement, for any `tie` that dominates
    every backbone of its size. -/
theorem conjecture1_of_bgBackbone (tie : ℕ → UTree) (h : BGBackboneConjecture)
    (HdomMulti : ∀ s : List Hub, Aobj (backboneU s) ≤ Aobj (tie (stateSize s))) :
    ∀ t : UTree, Aobj t ≤ Aobj (tie (usize t)) :=
  conjecture1_of_HnormMulti tie h HdomMulti

/-- **Which pinning gives the free-tie form content.**  If `tie n` is a backbone of size `n` for
    every `n`, the free-tie conclusion implies the pinned conjecture.  Without that side condition
    the free-tie conclusion is satisfied by a per-size maximizer over all trees and carries no
    information about backbones. -/
theorem bgBackbone_of_backboneTie (tie : ℕ → UTree)
    (hbb : ∀ n : ℕ, ∃ s : List Hub, stateSize s = n ∧ tie n = backboneU s)
    (h : ∀ t : UTree, Aobj t ≤ Aobj (tie (usize t))) :
    BGBackboneConjecture := by
  intro t
  obtain ⟨s, hsz, htie⟩ := hbb (usize t)
  exact ⟨s, hsz, htie ▸ h t⟩

end Step3
end R3Cert
