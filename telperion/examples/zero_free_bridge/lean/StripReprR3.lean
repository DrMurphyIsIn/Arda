/- (R3) DISCHARGE for `zeta_fract_repr_of`: the strip domain

       stripDomain = {s : ℂ | 0 < s.re} \ {1}

   is preconnected.  This is one of the three hypotheses the conditional assembly
   `zeta_fract_repr_of` (in StripRepr.lean) consumes; discharging it removes the
   `IsPreconnected stripDomain` obligation entirely.

   PROOF.  A single interior point is removed from an open right half-plane, so a
   two-convex-piece cover is impossible (a convex set cannot exclude an interior
   point while covering a neighbourhood of it).  We use FOUR convex half-plane
   pieces and glue them at shared points:

       A = {0 < re} ∩ {re < 1}      B = {0 < re} ∩ {0 < im}
       C = {0 < re} ∩ {im < 0}      D = {1 < re}

   A ∪ B ∪ C ∪ D excludes exactly the point 1 = (1,0): a point of the half-plane
   with re = 1 lies in B or C unless im = 0, and (1,0) is in none of the four.
   Each piece is convex (intersection of half-spaces), hence preconnected, and the
   union is glued in the order ((A ∪ B) ∪ C) ∪ D at (1/2, 1), (1/2, -1), (2, 1).

   A gap-filler FEEDING input (R); NOT a proof of RH.  conjecture1_proved = False.
-/
import StripRepr

open Set

namespace ZeroFreeBridge

private def pA : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1}
private def pB : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}
private def pC : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0}
private def pD : Set ℂ := {s : ℂ | 1 < s.re}

/-- (R3) The punctured open right half-plane `{0 < Re s} \ {1}` is preconnected. -/
theorem isPreconnected_stripDomain : IsPreconnected stripDomain := by
  -- Each convex piece is preconnected.
  have preA : IsPreconnected pA :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have preB : IsPreconnected pB :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have preC : IsPreconnected pC :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have preD : IsPreconnected pD := (convex_halfSpace_re_gt 1).isPreconnected
  -- Gluing points.
  have g1  : (⟨1/2, 1⟩ : ℂ) ∈ pA := by
    norm_num [pA, Set.mem_inter_iff, Set.mem_setOf_eq]
  have g1' : (⟨1/2, 1⟩ : ℂ) ∈ pB := by
    norm_num [pB, Set.mem_inter_iff, Set.mem_setOf_eq]
  have preAB : IsPreconnected (pA ∪ pB) :=
    IsPreconnected.union (⟨1/2, 1⟩ : ℂ) g1 g1' preA preB
  have g2  : (⟨1/2, -1⟩ : ℂ) ∈ pA ∪ pB :=
    Or.inl (by norm_num [pA, Set.mem_inter_iff, Set.mem_setOf_eq])
  have g2' : (⟨1/2, -1⟩ : ℂ) ∈ pC := by
    norm_num [pC, Set.mem_inter_iff, Set.mem_setOf_eq]
  have preABC : IsPreconnected ((pA ∪ pB) ∪ pC) :=
    IsPreconnected.union (⟨1/2, -1⟩ : ℂ) g2 g2' preAB preC
  have g3  : (⟨2, 1⟩ : ℂ) ∈ (pA ∪ pB) ∪ pC :=
    Or.inl (Or.inr (by norm_num [pB, Set.mem_inter_iff, Set.mem_setOf_eq]))
  have g3' : (⟨2, 1⟩ : ℂ) ∈ pD := by
    norm_num [pD, Set.mem_setOf_eq]
  have preABCD : IsPreconnected (((pA ∪ pB) ∪ pC) ∪ pD) :=
    IsPreconnected.union (⟨2, 1⟩ : ℂ) g3 g3' preABC preD
  -- The union is exactly `stripDomain`.
  have heq : stripDomain = ((pA ∪ pB) ∪ pC) ∪ pD := by
    ext s
    simp only [stripDomain, pA, pB, pC, pD, Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Complex.ext_iff,
      Complex.one_re, Complex.one_im]
    constructor
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy s.re 1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
      · have him : s.im ≠ 0 := by rintro h0; exact hne ⟨h, h0⟩
        rcases lt_or_gt_of_ne him with h2 | h2
        · exact Or.inl (Or.inr ⟨hre, h2⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hre, h2⟩))
      · exact Or.inr h
    · rintro ((( ⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h)
      · exact ⟨h1, by rintro ⟨he, _⟩; linarith⟩
      · exact ⟨h1, by rintro ⟨_, he⟩; linarith⟩
      · exact ⟨h1, by rintro ⟨_, he⟩; linarith⟩
      · exact ⟨by linarith, by rintro ⟨he, _⟩; linarith⟩
  rw [heq]; exact preABCD

end ZeroFreeBridge
