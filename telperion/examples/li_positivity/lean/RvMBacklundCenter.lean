/-
RvMBacklundCenter — Backlund S(T)=O(log T), PR 3a: the Jensen center lower bound.

The Jensen zero-count of the auxiliary `F_T` needs a positive lower bound `‖F_T(c)‖ ≥ const` at the disk
centre.  Take `c = 2` (real): `F_T(2) = Re ζ(2+iT)` (PR 1), and on `Re s ≥ 2` the Dirichlet tail is
`≤ π²/6 − 1`, so `Re ζ(2+iT) ≥ 1 − (π²/6 − 1) = 2 − π²/6 > 0`.  This is the Re-analogue of the on-island
`ZeroFreeBridge.zeta_norm_ge_two_sub` (which bounds `‖ζ‖`); we need the REAL PART, since `F_T(2)` is real.

  * `re_zeta_two_ge` — `2 − π²/6 ≤ Re ζ(2+iT)`.
  * `backlundAux_two_norm_ge` — `2 − π²/6 ≤ ‖F_T(2)‖`  (the Jensen denominator).

conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundAux
import DlvpZetaLower

open Complex

namespace Backlund

/-- **Re ζ ≥ 2 − π²/6 on the `Re = 2` line.**  The real-part analogue of `zeta_norm_ge_two_sub`. -/
theorem re_zeta_two_ge (T : ℝ) :
    2 - Real.pi ^ 2 / 6 ≤ (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)).re := by
  set s : ℂ := ((2 : ℝ) : ℂ) + (T : ℂ) * I with hs
  have hsre : s.re = 2 := by rw [hs]; simp
  have h1 : (1 : ℝ) < s.re := by rw [hsre]; norm_num
  have hzeta : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
    zeta_eq_tsum_one_div_nat_add_one_cpow h1
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hsum_c : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr h1
  have hsumf : Summable f := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).mpr hsum_c
    simpa [hf, Nat.cast_add, Nat.cast_one] using h
  have hsplit : riemannZeta s = f 0 + ∑' n : ℕ, f (n + 1) := by
    rw [hzeta]; exact hsumf.tsum_eq_zero_add
  have hf0 : f 0 = 1 := by simp [hf]
  set Tt : ℂ := ∑' n : ℕ, f (n + 1) with hTt
  -- real part: Re ζ = 1 + Re Tt ≥ 1 − ‖Tt‖
  have hReq : (riemannZeta s).re = 1 + Tt.re := by
    rw [hsplit, hf0, Complex.add_re, Complex.one_re]
  have hReT : -‖Tt‖ ≤ Tt.re := neg_le_of_abs_le (Complex.abs_re_le_norm Tt)
  -- ‖Tt‖ ≤ π²/6 − 1 (identical tail bound to zeta_norm_ge_two_sub)
  have hnorm_term : ∀ n : ℕ, ‖f (n + 1)‖ = 1 / (((n : ℝ) + 2)) ^ s.re := by
    intro n
    have hpos : 0 < ((n : ℕ) + 2) := by positivity
    rw [hf]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [norm_div, norm_one]
    have hc : ((n : ℂ) + 1 + 1) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [hc, norm_natCast_cpow_of_pos hpos]
    push_cast; ring_nf
  have hsummf1 : Summable (fun n : ℕ => ‖f (n + 1)‖) :=
    (hsumf.comp_injective (add_left_injective 1)).norm
  have hTle : ‖Tt‖ ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re := by
    calc ‖Tt‖ = ‖∑' n : ℕ, f (n + 1)‖ := by rw [hTt]
      _ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsummf1
      _ = ∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re := tsum_congr hnorm_term
  have hbase : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 2 := by
    intro n; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hmono : ∀ n : ℕ, (1 : ℝ) / (((n : ℝ) + 2)) ^ s.re ≤ 1 / (((n : ℝ) + 2)) ^ 2 := by
    intro n
    have hpow : (((n : ℝ) + 2)) ^ (2 : ℝ) ≤ (((n : ℝ) + 2)) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (hbase n) hsre.ge
    rw [Real.rpow_two] at hpow
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hsumσ : Summable (fun n : ℕ => 1 / (((n : ℝ) + 2)) ^ s.re) := by
    simpa only [hnorm_term] using hsummf1
  have hsum2 : Summable (fun n : ℕ => 1 / (((n : ℝ) + 2)) ^ 2) := by
    have hz := hasSum_zeta_two.summable
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 2).mpr hz
    refine h2.congr (fun n => ?_); push_cast; ring_nf
  have htail : (∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re) ≤ Real.pi ^ 2 / 6 - 1 := by
    calc (∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re)
        ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ 2 := Summable.tsum_le_tsum hmono hsumσ hsum2
      _ = Real.pi ^ 2 / 6 - 1 := ZeroFreeBridge.basel_tail
  rw [hReq]; linarith [hReT, le_trans hTle htail]

/-- **The Jensen centre lower bound.**  `2 − π²/6 ≤ ‖F_T(2)‖`, since `F_T(2) = Re ζ(2+iT) ≥ 2 − π²/6 > 0`. -/
theorem backlundAux_two_norm_ge (T : ℝ) :
    2 - Real.pi ^ 2 / 6 ≤ ‖backlundAux T ((2 : ℝ) : ℂ)‖ := by
  have hre := re_zeta_two_ge T
  have hpi : Real.pi ^ 2 / 6 < 2 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  rw [backlundAux_ofReal T 2, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  exact hre

end Backlund
