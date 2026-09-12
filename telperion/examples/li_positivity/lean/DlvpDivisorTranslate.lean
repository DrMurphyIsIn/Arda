/- PHASE 4 (dVP frontier, the divisor-TRANSLATION lemma — item 3 core): `divisor` commutes with a
   constant shift.  `bc_sum_blaschke` is centred at `0`, so ζ enters as `f = ζ(c₀+·)` and its divisor is
   `divisor (ζ(c₀+·)) (ball 0 R)`; the Herglotz-sum reindexing needs this to be `divisor ζ (ball c₀ R)`
   evaluated at the shifted point.

   `divisor f U z = (meromorphicOrderAt f z).untop₀` (`divisor_apply`), and the meromorphic order is
   invariant under a translation `g = (c₀+·)` because `deriv g = 1 ≠ 0`
   (`meromorphicOrderAt_comp_of_deriv_ne_zero`).  Hence

     `divisor (fun w => f (c₀+w)) U' u = divisor f U (c₀+u)`

   whenever both sides are in-domain and `f` is meromorphic on `U`.  This is the last uncertain-API
   piece of the ζ instantiation, and it is a direct consequence of the Mathlib order-composition API.
   conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

open Complex MeromorphicOn

namespace ZeroFreeBridge

/-- **Divisor under a constant shift.**  `divisor (fun w => f (c₀+w)) U' u = divisor f U (c₀+u)`. -/
theorem divisor_comp_const_add_apply {f : ℂ → ℂ} {U U' : Set ℂ} (c₀ : ℂ)
    (hf : MeromorphicOn f U) (hf' : MeromorphicOn (fun w => f (c₀ + w)) U')
    {u : ℂ} (hu' : u ∈ U') (hu : c₀ + u ∈ U) :
    divisor (fun w => f (c₀ + w)) U' u = divisor f U (c₀ + u) := by
  rw [divisor_apply hf' hu', divisor_apply hf hu]
  congr 1
  have hg : AnalyticAt ℂ (fun w => c₀ + w) u := by fun_prop
  have hg' : deriv (fun w => c₀ + w) u ≠ 0 := by
    rw [deriv_const_add']; simp
  have hcomp : (fun w => f (c₀ + w)) = f ∘ (fun w => c₀ + w) := rfl
  rw [hcomp, meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

/-- **Herglotz-sum reindexing.**  The recentred Herglotz sum (over the recentred zero set `s`) equals
    the original-coordinate sum (over `s.image (c₀+·)`, the true zeros): the divisor translates and
    `(c₀+z) - (c₀+u) = z - u`.  This turns `bc_sum_blaschke`'s output sum into the form
    `hzero_of_blaschke` / `herglotz_re_ge` consume. -/
theorem herglotz_sum_reindex {f : ℂ → ℂ} {U U' : Set ℂ} (c₀ z : ℂ)
    (hf : MeromorphicOn f U) (hf' : MeromorphicOn (fun w => f (c₀ + w)) U')
    (s : Finset ℂ) (hs_dom : ∀ u ∈ s, u ∈ U' ∧ c₀ + u ∈ U) :
    (∑ u ∈ s, (divisor (fun w => f (c₀ + w)) U' u : ℂ) / (z - u))
      = ∑ ρ ∈ s.image (fun u => c₀ + u), (divisor f U ρ : ℂ) / ((c₀ + z) - ρ) := by
  rw [Finset.sum_image (fun x _ y _ h => add_left_cancel h)]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  obtain ⟨hu', hu_dom⟩ := hs_dom u hu
  rw [divisor_comp_const_add_apply c₀ hf hf' hu' hu_dom]
  congr 1
  ring

end ZeroFreeBridge
