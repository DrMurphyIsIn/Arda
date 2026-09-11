/-
RvMLeibniz — Phase 4c: the Leibniz/Pascal sum step (combinatorial crux of the product rule).

Mathlib has the norm bound `norm_iteratedFDeriv_mul_le` but not the Leibniz *equality*; its
combinatorial heart is the binomial reindexing below.

  * `leibniz_sum_step` — `∑_{k≤n} C(n,k)(a(k+1)b(n−k) + a k·b(n+1−k)) = ∑_{k≤n+1} C(n+1,k)·a k·b(n+1−k)`.

conjecture1_proved = False.
-/
import Mathlib

open Finset

namespace RvMWeierstrass

/-- **The Leibniz/Pascal sum step.** -/
theorem leibniz_sum_step (n : ℕ) (a b : ℕ → ℂ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (a (k + 1) * b (n - k) + a k * b (n + 1 - k))
      = ∑ k ∈ range (n + 2), ((n + 1).choose k : ℂ) * (a k * b (n + 1 - k)) := by
  -- shift the `a k` half of the left sum: `k → k+1` (using `C(n,n+1) = 0` on the tail)
  have key : ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (a k * b (n + 1 - k))
      = (∑ k ∈ range (n + 1), (n.choose (k + 1) : ℂ) * (a (k + 1) * b (n - k)))
          + a 0 * b (n + 1) := by
    rw [Finset.sum_range_succ' (fun k => (n.choose k : ℂ) * (a k * b (n + 1 - k))) n]
    rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℂ) * (a (k + 1) * b (n - k))) n]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.choose_succ_self,
      Nat.cast_zero, zero_mul, add_zero]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hb : n + 1 - (k + 1) = n - k := by omega
    rw [hb]
  -- expand the left sum, substitute `key`, and combine via Pascal
  simp only [mul_add, Finset.sum_add_distrib]
  rw [key, Finset.sum_range_succ' (fun k => ((n + 1).choose k : ℂ) * (a k * b (n + 1 - k))) (n + 1)]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Nat.choose_succ_succ n k]
  have hb : n + 1 - (k + 1) = n - k := by omega
  rw [hb]
  push_cast
  ring

/-- **Leibniz product rule for `iteratedDerivWithin`** on an open set (Mathlib gap). -/
theorem iteratedDerivWithin_mul {n : ℕ} {s : Set ℂ} (hs : UniqueDiffOn ℂ s) {f g : ℂ → ℂ}
    (hf : ContDiffOn ℂ ⊤ f s) (hg : ContDiffOn ℂ ⊤ g s) {x : ℂ} (hx : x ∈ s) :
    iteratedDerivWithin n (fun y => f y * g y) s x
      = ∑ k ∈ range (n + 1), (n.choose k : ℂ)
          * (iteratedDerivWithin k f s x * iteratedDerivWithin (n - k) g s x) := by
  have hdf : ∀ (m : ℕ) {y}, y ∈ s → DifferentiableWithinAt ℂ (iteratedDerivWithin m f s) s y :=
    fun m _ hy => hf.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast WithTop.coe_lt_top (m : ℕ∞)) hs _ hy
  have hdg : ∀ (m : ℕ) {y}, y ∈ s → DifferentiableWithinAt ℂ (iteratedDerivWithin m g s) s y :=
    fun m _ hy => hg.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast WithTop.coe_lt_top (m : ℕ∞)) hs _ hy
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDerivWithin_succ]
    have hEqOn : Set.EqOn (iteratedDerivWithin n (fun y => f y * g y) s)
        (fun y => ∑ k ∈ range (n + 1), (n.choose k : ℂ)
          * (iteratedDerivWithin k f s y * iteratedDerivWithin (n - k) g s y)) s :=
      fun y hy => ih hy
    rw [derivWithin_congr hEqOn (ih hx),
      derivWithin_fun_sum (A := fun k y => (n.choose k : ℂ)
          * (iteratedDerivWithin k f s y * iteratedDerivWithin (n - k) g s y))
        (fun k _ => ((hdf k hx).mul (hdg (n - k) hx)).const_mul _)]
    have hterm : ∀ k ∈ range (n + 1),
        derivWithin (fun y => (n.choose k : ℂ)
          * (iteratedDerivWithin k f s y * iteratedDerivWithin (n - k) g s y)) s x
          = (n.choose k : ℂ) * (iteratedDerivWithin (k + 1) f s x * iteratedDerivWithin (n - k) g s x
              + iteratedDerivWithin k f s x * iteratedDerivWithin (n + 1 - k) g s x) := by
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      have hb : n - k + 1 = n + 1 - k := by omega
      have hd : DifferentiableWithinAt ℂ
          (fun y => iteratedDerivWithin k f s y * iteratedDerivWithin (n - k) g s y) s x :=
        (hdf k hx).mul (hdg (n - k) hx)
      rw [derivWithin_const_mul (n.choose k : ℂ) hd,
        derivWithin_fun_mul (hdf k hx) (hdg (n - k) hx),
        ← iteratedDerivWithin_succ, ← iteratedDerivWithin_succ, hb]
    rw [Finset.sum_congr rfl hterm]
    exact leibniz_sum_step n (fun j => iteratedDerivWithin j f s x)
      (fun j => iteratedDerivWithin j g s x)

/-- **Leibniz product rule for `iteratedDeriv`** at an interior point of a pole-free open set. -/
theorem iteratedDeriv_mul_of_isOpen {n : ℕ} {s : Set ℂ} (hs : IsOpen s) {f g : ℂ → ℂ}
    (hf : ContDiffOn ℂ ⊤ f s) (hg : ContDiffOn ℂ ⊤ g s) {x : ℂ} (hx : x ∈ s) :
    iteratedDeriv n (fun y => f y * g y) x
      = ∑ k ∈ range (n + 1), (n.choose k : ℂ) * (iteratedDeriv k f x * iteratedDeriv (n - k) g x) := by
  rw [← iteratedDerivWithin_of_isOpen hs hx, iteratedDerivWithin_mul hs.uniqueDiffOn hf hg hx]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [iteratedDerivWithin_of_isOpen hs hx, iteratedDerivWithin_of_isOpen hs hx]

end RvMWeierstrass
