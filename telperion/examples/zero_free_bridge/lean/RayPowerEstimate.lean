/- RayPowerEstimate -- a reusable lemma pack for estimates of complex/real powers on positive-real
   rays. These primitives recurred 20+ times across the strip-representation work (StripReprR1/R2,
   the tail bound, ZetaLogBound) -- each re-derived by hand, costing rounds. Collected here so future
   zeta / Dirichlet-L-function growth-bound work imports them instead of re-proving.

   This is a LEMMA PACK (a Lean support library), NOT a Telperion certificate emitter: there is no
   untrusted-computation-to-re-verify, just a stable set of reusable moves. Compile-checked as its own
   CI target. A gap-filler; NOT a proof of RH. conjecture1_proved = False.
-/
import Mathlib

open Complex MeasureTheory

namespace RayPowerEstimate

/-- `‖(x:ℂ)^s‖ = x^(Re s)` for real `x > 0` (thin, discoverable name for the recurring move). -/
theorem norm_cpow_ofReal {x : ℝ} (hx : 0 < x) (s : ℂ) : ‖(x : ℂ) ^ s‖ = x ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx s

/-- `‖(n:ℂ)^(-s)‖ = n^(-Re s)` for `n ≥ 1` (the natCast base, as in partial sums `∑ n^{-s}`). -/
theorem norm_natCast_cpow_neg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]

/-- `‖(N:ℂ)^(1-s)‖ ≤ 1` for `Re s ≥ 1`, `N ≥ 1` (the pole-numerator bound). -/
theorem norm_natCast_cpow_one_sub_le_one {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(N : ℂ) ^ (1 - s)‖ ≤ 1 := by
  have hnR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < (N : ℝ) := by linarith
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  apply Real.rpow_le_one_of_one_le_of_nonpos hnR
  simp only [Complex.sub_re, Complex.one_re]; linarith

/-- `(x:ℂ)^(-s) * x = (x:ℂ)^(1-s)` for `x ≠ 0` (the Abel-collection step). -/
theorem cpow_neg_mul_self {x : ℂ} (hx : x ≠ 0) (s : ℂ) : x ^ (-s) * x = x ^ (1 - s) := by
  rw [← Complex.cpow_one x, ← Complex.cpow_add _ _ hx, Complex.cpow_one]; congr 1; ring

/-- `|Im s| ≤ ‖s - 1‖` (the pole-denominator bound). -/
theorem abs_im_le_norm_sub_one (s : ℂ) : |s.im| ≤ ‖s - 1‖ := by
  have h : (s - 1).im = s.im := by simp
  calc |s.im| = |(s - 1).im| := by rw [h]
    _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _

/-- `‖((r:ℝ):ℂ)‖ ≤ 1` from `0 ≤ r ≤ 1` (the bounded-numerator move, e.g. `Int.fract`). -/
theorem norm_ofReal_le_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : ‖((r : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg h0]; exact h1

/-- `x^a` is integrable on `Ioi c` when it decays (`a < -1`, `c > 0`) -- the tail-decay primitive. -/
theorem integrableOn_Ioi_rpow_neg {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi c) :=
  integrableOn_Ioi_rpow_of_lt ha hc

end RayPowerEstimate
