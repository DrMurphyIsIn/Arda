/- HAND-AUTHORED (not telperion-generated): the generic quadratic-form
   grouping lemma — the "fiberwise dance" extracted after appearing three
   times (Xor3Structure.block_quadform_nonneg, Hsq.hsq_of_subsetForm twice
   nested, Hsq.subsetForm_d1's restriction), before a fourth hand-rolling
   in the 3XOR duality layer.

   Statement: a double sum of c a * c b * K (g a) (g b) over any finite
   index regroups as the same form over the image of g with fiber-summed
   coefficients.  This is the coefficient-collapse step of every
   pseudoexpectation-on-squares reduction (multilinearization by support,
   parity-mask grouping, ...).  Candidate for the Telperion prelude
   library (requires_prelude mechanism). -/
import Mathlib

namespace QuadForm

/-- Fiberwise regrouping of a quadratic form along `g`. -/
theorem sum_mul_sum_fiberwise {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (g : ι → κ) (c : ι → ℚ) (K : κ → κ → ℚ) :
    ∑ a ∈ s, ∑ b ∈ s, c a * c b * K (g a) (g b)
    = ∑ S ∈ s.image g, ∑ T ∈ s.image g,
        (∑ a ∈ s.filter (g · = S), c a)
          * (∑ b ∈ s.filter (g · = T), c b) * K S T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun a (ha : a ∈ s) => Finset.mem_image_of_mem g ha)
    (fun a => ∑ b ∈ s, c a * c b * K (g a) (g b))]
  refine Finset.sum_congr rfl fun S _ => ?_
  have inner : ∀ a ∈ s.filter (g · = S),
      ∑ b ∈ s, c a * c b * K (g a) (g b)
      = c a * ∑ T ∈ s.image g,
          (∑ b ∈ s.filter (g · = T), c b) * K S T := by
    intro a ha
    have haS : g a = S := (Finset.mem_filter.mp ha).2
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun b (hb : b ∈ s) => Finset.mem_image_of_mem g hb)
      (fun b => c a * c b * K (g a) (g b))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbT : g b = T := (Finset.mem_filter.mp hb).2
    rw [haS, hbT]
    ring
  rw [Finset.sum_congr rfl inner, ← Finset.sum_mul]
  exact (Finset.mul_sum _ _ _).trans
    (Finset.sum_congr rfl fun T _ => by ring)

/-- Zero-extension: a fiber-grouped coefficient vanishes off the image, so
the grouped form extends from the image to any superset (e.g. `univ`). -/
theorem grouped_extend {κ : Type*} [DecidableEq κ]
    (P Q : Finset κ) (hPQ : P ⊆ Q) (x : κ → ℚ) (K : κ → κ → ℚ)
    (hx : ∀ S ∈ Q, S ∉ P → x S = 0) :
    ∑ S ∈ P, ∑ T ∈ P, x S * x T * K S T
    = ∑ S ∈ Q, ∑ T ∈ Q, x S * x T * K S T := by
  rw [← Finset.sum_subset hPQ]
  · refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Finset.sum_subset hPQ]
    intro T hTQ hTP
    rw [hx T hTQ hTP, mul_zero, zero_mul]
  · intro S hSQ hSP
    refine Finset.sum_eq_zero fun T _ => ?_
    rw [hx S hSQ hSP, zero_mul, zero_mul]

end QuadForm

#print axioms QuadForm.sum_mul_sum_fiberwise
#print axioms QuadForm.grouped_extend
