import CF_EData
import Crux3_BandDHData

/-!
# CF_LemmaO: each counterfeit has a periodic orbit of non-prime-power length (log 6)

Counterfeit-ladder lane (CF), 2026-09-24, `rvm_bridge` island.

`conjecture1_proved = False`.  Bookkeeping witnesses; nothing here bears on RH.

"Lemma O" (textbook): for `F = sum a(n) n^{-s}` with `a(1) = 1` and `-F'/F = sum c(n) n^{-s}`, the weights `c`
are supported on prime powers iff `a` is multiplicative (iff `F` has an Euler product).  This file does NOT
formalize Lemma O itself (remaining obligation, see LANE_NOTES_CF.md).  It proves the finite witnesses that
pin each counterfeit's failure to one orbit, at length `log 6`:

* Davenport-Heilbronn `D` (`Crux3.aD`, `Crux3.cD`):
  `cD 6 = (1 + kappa^2) log 6 != 0` (`cD_six`, `cD_six_ne_zero`), and for ANY `w` with D's defining
  identity on `[1, 56]`, `w 6 = (1 + kappa^2) log 6 != 0` (`dh_orbit_six`); `aD 6 != aD 2 * aD 3`.
* the Epstein counterfeit `E`: `cE 6 = 2 log 6 != 0` (`CF_EData.cE_six`), `aE 6 = 2 != 0 = aE 2 * aE 3`.
* zeta and zeta_K: `Lambda(6) = 0`, `6` is not a prime power, and `cK n != 0 -> IsPrimePow n` for all `n`
  (`cK_support`); `aK` is multiplicative at `6 = 2 * 3`.
No `sorry`.
-/

open Crux3

noncomputable section

namespace CF

/-- **`c_D(6) = (1 + kappa^2) log 6`** (the synthesis' claim, verified from Crux3's closed form `dtab 6`). -/
theorem cD_six : cD 6 = (1 + kapD ^ 2) * Real.log 6 := by
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  simp only [cD, cDexpr, dtab, polyEval, List.map, List.sum_cons, List.sum_nil]
  rw [h6]
  push_cast
  ring

theorem cD_six_ne_zero : cD 6 ≠ 0 := by
  rw [cD_six]
  have h1 : 0 < 1 + kapD ^ 2 := by positivity
  have h2 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  positivity

/-- For ANY weights with D's defining identity on `[1, 56]`: `w 6 = (1 + kappa^2) log 6 != 0`, while
`Lambda(6) = 0`. -/
theorem dh_orbit_six (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) :
    w 6 = (1 + kapD ^ 2) * Real.log 6 ∧ w 6 ≠ 0 ∧ ArithmeticFunction.vonMangoldt 6 = 0 := by
  have hw1 : w 1 = 0 := by
    have h := hw 1 le_rfl (by norm_num)
    rw [Nat.divisors_one, Finset.sum_singleton, Nat.div_self (by norm_num), aD_one, Nat.cast_one, Real.log_one,
      mul_zero, mul_one] at h
    exact h.symm
  have h := eq_cD_of_conv w hw1 hw 6 (by norm_num) (by norm_num)
  exact ⟨by rw [h, cD_six], by rw [h]; exact cD_six_ne_zero, vonMangoldt_six⟩

/-- `6` is not a prime power (so an orbit of length `log 6` is forbidden for an Euler product). -/
theorem not_isPrimePow_six : ¬ IsPrimePow 6 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mp vonMangoldt_six

/-- zeta_K's weights are supported on prime powers. -/
theorem cK_support (n : ℕ) (h : cK n ≠ 0) : IsPrimePow n := by
  apply ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
  intro h0
  apply h
  rw [cK, h0, zero_mul]

/-- The Epstein weights are NOT supported on prime powers: `cE 6 != 0`, `6` not a prime power. -/
theorem cE_not_primePow_supported : cE 6 ≠ 0 ∧ ¬ IsPrimePow 6 := ⟨cE_six_ne_zero, not_isPrimePow_six⟩

/-- Non-multiplicativity witnesses (the other side of Lemma O). -/
theorem aE_not_mult : aE 6 ≠ aE 2 * aE 3 := by
  rw [aE_6, aE_2, aE_3]; norm_num

theorem aD_not_mult : aD 6 ≠ aD 2 * aD 3 := by
  simp only [aD]
  norm_num
  intro h
  nlinarith [sq_nonneg kapD]

theorem aK_mult_six : aKint 6 = aKint 2 * aKint 3 := by decide

end CF
