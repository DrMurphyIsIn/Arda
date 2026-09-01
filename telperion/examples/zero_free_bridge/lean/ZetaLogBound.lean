/- SHARP NEAR-LINE GROWTH BOUND (WORK IN PROGRESS): `|ζ(σ+it)| ≤ C·(1 + log|t|)`
   for `1 ≤ σ ≤ 2`, `|t| ≥ 2` — the upgrade that improves the zero-free-region rate.

   The elementary region (`riemannZeta_zero_free_poly`, `Re s > 1 - c/|t|⁵`) is limited by the
   CRUDE growth bound `|ζ| ≤ C|t|` (`zeta_strip_bound`). Replacing it with the sharp
   `|ζ| ≤ C·log|t|` cascades through `zeta_deriv_bound → zeta_hcauchy → zeta_strip_2t_bound`
   and improves the exponent from `|t|⁻⁵` toward the de la Vallée Poussin `1 - c/log|t|` region —
   WITHOUT touching the Hadamard wall.

   METHOD: truncated Euler–Maclaurin at `N ∼ |t|`, reusing the R1 Abel-summation machinery.
   From `zeta_fract_repr` (ζ(s) = s/(s-1) - s∫_{x>1}{x}x^{-s-1}) and the FINITE Abel identity
   (`sum_mul_eq_sub_integral_mul₀`, f=x^{-s}, c 0=0, c(n≥1)=1) one gets, for Re s > 1, N ≥ 1:

       ζ(s) = Σ_{n=1}^N n^{-s} + N^{1-s}/(s-1) - s·∫_{x>N} {x} x^{-s-1} dx.        (TRUNC)

   With N = ⌊|t|⌋, σ ∈ [1,2]:
     • |Σ_{n=1}^N n^{-s}| ≤ Σ n^{-σ} ≤ Σ 1/n ≤ 1 + log N ≤ 1 + log|t|      (σ ≥ 1)
     • |N^{1-s}/(s-1)| = N^{1-σ}/|s-1| ≤ 1/|t|                              (N^{1-σ} ≤ 1, |s-1| ≥ |t|)
     • |s·∫_{x>N}{x}x^{-s-1}| ≤ |s|·N^{-σ}/σ ≤ |s|/N ≤ C                     (N ≥ |t|/2, |s| ≤ 2|t|)
   ⟹ |ζ(σ+it)| ≤ C·(1 + log|t|).

   STATUS: WIP SKELETON. Sub-obligations isolated as `sorry`; NOT a discharge until sorry-free.
   A gap-filler FEEDING the region rate, NOT a proof of RH. conjecture1_proved = False.
-/
import StripReprAssembled

open MeasureTheory Filter Topology Set

namespace ZeroFreeBridge

/-- The tail integral `∫_{x>N} {x} x^{-(s+1)} dx`, as a function of the cutoff `N`. -/
private noncomputable def fractTail (s : ℂ) (N : ℝ) : ℂ :=
  ∫ x in Set.Ioi N, ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)

/-- (TRUNC) truncated Euler–Maclaurin representation of ζ on `Re s > 1` at integer cutoff `N ≥ 1`.
    Derived from the finite Abel identity and `zeta_fract_repr`. -/
theorem zeta_trunc {s : ℂ} (hs : 1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1)
        - s * fractTail s (N : ℝ) := by
  sorry

/-- Partial-sum bound: `‖Σ_{n=1}^N n^{-s}‖ ≤ 1 + log N` for `Re s ≥ 1`, using Mathlib's
    `harmonic_le_one_add_log` (`harmonic n ≤ 1 + log n`) after `‖n^{-s}‖ = n^{-σ} ≤ 1/n`. -/
theorem norm_partial_sum_le {s : ℂ} (hs : 1 ≤ s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1 + Real.log N := by
  calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
        rw [← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
          ← Real.rpow_neg_one (n : ℝ)]
        refine Real.rpow_le_rpow_of_exponent_le hnR ?_
        simp only [Complex.neg_re]; linarith
    _ = (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- `‖N^{1-s}‖ ≤ 1` for `Re s ≥ 1`, `N ≥ 1` (the numerator of the pole term). -/
theorem norm_cpow_one_sub_le_one {s : ℂ} (hs : 1 ≤ s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖(N : ℂ) ^ (1 - s)‖ ≤ 1 := by
  have hnR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < (N : ℝ) := by linarith
  rw [← Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  apply Real.rpow_le_one_of_one_le_of_nonpos hnR
  simp only [Complex.sub_re, Complex.one_re]; linarith

/-- `|Im s| ≤ ‖s - 1‖` (the pole-term denominator bound). -/
theorem abs_im_le_norm_sub_one (s : ℂ) : |s.im| ≤ ‖s - 1‖ := by
  have : (s - 1).im = s.im := by simp
  calc |s.im| = |(s - 1).im| := by rw [this]
    _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _

/-- The tail term `‖s · ∫_{x>N} {x} x^{-s-1}‖` is bounded by `‖s‖ / (Re s · N^{Re s})`. -/
theorem norm_tail_term_le {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖s * fractTail s (N : ℝ)‖ ≤ ‖s‖ / (s.re * (N : ℝ) ^ s.re) := by
  sorry

/-- THE SHARP NEAR-LINE BOUND: `|ζ(σ+it)| ≤ C·(1 + log|t|)` for `1 ≤ σ ≤ 2`, `|t| ≥ 2`.
    (The explicit `C` is filled in during discharge.) -/
theorem zeta_log_bound {σ t : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ∃ C : ℝ, 0 < C ∧
      ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ C * (1 + Real.log |t|) := by
  sorry

end ZeroFreeBridge
