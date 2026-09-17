/-
ReflectionDetect — the DETECT-half kernel: invariance is not blindness.

Companion to ReflectionForced (the FORCED-half: per-zero functionals built from the
Klein four-group symmetry are constant on reflection pairs — orientation-blindness is a
theorem).  This file certifies the complementary half of the corrected kill lemma
(sweep-4 replication wbba5wa6f): the reflection-INVARIANT mirrored pair weight

    W_x(β) = x^(β−1/2) + x^(1/2−β) = 2·cosh((β−1/2)·log x)

DETECTS off-line-ness — W_x(β) > 2 exactly when β ≠ 1/2 (any x > 1) — even though it is
symmetric under the mirror β ↦ 1−β (so it cannot detect orientation), and even though the
mirrored PRODUCT is identically 1 (products are blind; sums detect).  Composed with the
same-ordinate mirror partner (OrdinateInsensitivity.same_ordinate_partner /
LambdaConjugation.same_ordinate_mirror_partner), every off-line completed-zeta zero pair
carries a strict, sign-definite weight excess over the on-line value at its own height.

The corrected kill lemma, in kernel-visible halves:
  FORCED-half (ReflectionForced): invariant functionals cannot ORIENT within a pair.
  DETECT-half (this file):        invariant functionals CAN detect a pair's off-line-ness.
The wall is therefore neither invariance nor blindness: the excess lives at exp(δ·u)
against an unconditional prime-side error exp(Θ·u) with Θ ~ 1 — extracting it uniformly
in height IS square-root cancellation.  conjecture1_proved = False.  A wall-visibility
certificate, not an RH route.
-/
import Mathlib

open Real

namespace ReflectionDetect

/-- The mirrored pair weight in cosh form: for `0 < x`,
`x^(β−1/2) + x^(1/2−β) = 2·cosh((β−1/2)·log x)`. -/
theorem pair_weight_eq_two_cosh (x β : ℝ) (hx : 0 < x) :
    x ^ (β - 1/2) + x ^ (1/2 - β) = 2 * cosh ((β - 1/2) * Real.log x) := by
  rw [rpow_def_of_pos hx, rpow_def_of_pos hx, Real.cosh_eq,
    show Real.log x * (β - 1/2) = (β - 1/2) * Real.log x by ring,
    show Real.log x * (1/2 - β) = -((β - 1/2) * Real.log x) by ring]
  ring

/-- **Invariance** — the weight is symmetric under the mirror `β ↦ 1−β`. -/
theorem pair_weight_reflection_invariant (x β : ℝ) :
    x ^ ((1 - β) - 1/2) + x ^ (1/2 - (1 - β)) = x ^ (β - 1/2) + x ^ (1/2 - β) := by
  rw [show (1 - β) - 1/2 = 1/2 - β by ring, show 1/2 - (1 - β) = β - 1/2 by ring]
  ring

/-- **Blind products** — mirrored weights multiply to exactly `1`: the product channel
carries no off-line information whatsoever.  (This is the true content behind the
committed kill lemma's overgeneralization.) -/
theorem mirrored_product_blind (x β : ℝ) (hx : 0 < x) :
    x ^ (β - 1/2) * x ^ ((1 - β) - 1/2) = 1 := by
  rw [← Real.rpow_add hx, show (β - 1/2) + ((1 - β) - 1/2) = 0 by ring, Real.rpow_zero]

/-- **Detection (strict form)** — for `1 < x` the invariant pair weight strictly exceeds
its on-line value `2` exactly when `β ≠ 1/2`. -/
theorem two_lt_pair_weight_iff (x β : ℝ) (hx : 1 < x) :
    2 < x ^ (β - 1/2) + x ^ (1/2 - β) ↔ β ≠ 1/2 := by
  have hx0 : 0 < x := lt_trans one_pos hx
  rw [pair_weight_eq_two_cosh x β hx0]
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  constructor
  · intro h hβ
    rw [hβ] at h
    simp at h
  · intro hβ
    have hne : (β - 1/2) * Real.log x ≠ 0 :=
      mul_ne_zero (fun hh => hβ (by linarith)) hlog
    have := Real.one_lt_cosh.mpr hne
    linarith

/-- **The critical line is exactly the equality locus** — `W_x(β) = 2 ↔ β = 1/2`. -/
theorem pair_weight_eq_two_iff (x β : ℝ) (hx : 1 < x) :
    x ^ (β - 1/2) + x ^ (1/2 - β) = 2 ↔ β = 1/2 := by
  have hx0 : 0 < x := lt_trans one_pos hx
  constructor
  · intro h
    by_contra hβ
    have := (two_lt_pair_weight_iff x β hx).mpr hβ
    linarith
  · intro h
    rw [pair_weight_eq_two_cosh x β hx0, h]
    norm_num

/-- **Off-line mirror pairs carry a detectable excess** — stated at the coordinates of
the same-ordinate partner `1 − conj ρ` (whose zero-hood, for a completed-zeta zero `ρ`
with `0 < Re ρ`, is the sibling certificate `same_ordinate_partner`): whenever
`Re ρ ≠ 1/2` and `1 < x`, the invariant weight sum over the pair strictly exceeds the
on-line double's value `2`.  Detection without orientation: the functional sees THAT the
pair is off-line, never WHICH member is which. -/
theorem offline_pair_detectable (ρ : ℂ) (x : ℝ) (hx : 1 < x) (hoff : ρ.re ≠ 1 / 2) :
    2 < x ^ (ρ.re - 1/2) + x ^ ((1 - starRingEnd ℂ ρ).re - 1/2) := by
  have hre : (1 - starRingEnd ℂ ρ).re = 1 - ρ.re := by simp
  rw [hre, show (1 : ℝ) - ρ.re - 1/2 = 1/2 - ρ.re by ring]
  exact (two_lt_pair_weight_iff x ρ.re hx).mpr hoff

end ReflectionDetect

#print axioms ReflectionDetect.pair_weight_eq_two_cosh
#print axioms ReflectionDetect.pair_weight_reflection_invariant
#print axioms ReflectionDetect.mirrored_product_blind
#print axioms ReflectionDetect.two_lt_pair_weight_iff
#print axioms ReflectionDetect.pair_weight_eq_two_iff
#print axioms ReflectionDetect.offline_pair_detectable
