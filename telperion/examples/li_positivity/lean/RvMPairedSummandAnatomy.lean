/-
RvMPairedSummandAnatomy — Route P extended: the unconditional structure of the paired Li summand.

`RvMOnLinePositivity` showed the paired Li summand of an ON-LINE zero is a perfect square.  This
isolates the UNCONDITIONAL structural fact underneath it: because `pairedZero ρ = 1 - ρ` sends
`w := 1 - 1/ρ` to `w⁻¹`, for EVERY nontrivial zero and every `n`,

  * `liPairedSummand_eq_two_sub_v_sub_inv` — with `v := (1 - 1/ρ)^(n+1)`,
        `liPairedSummand n ρ = 2 - v - v⁻¹`.
  * `liPairedSummand_re_nonneg_iff` — hence `0 ≤ (liPairedSummand n ρ).re ↔ (v + v⁻¹).re ≤ 2`.

So per-zero positivity is EXACTLY the condition `Re(v + v⁻¹) ≤ 2`.  On the critical line `|v| = 1`, so
`v⁻¹ = conj v` and `(v + v⁻¹).re = 2·(v.re) ≤ 2` automatically (`onLine_re_v_add_inv_le_two`) — recovering
`RvMOnLinePositivity`.  Off the line `|v| ≠ 1` and `Re(v + v⁻¹) = (r^k + r^{-k})·cos` can exceed `2`
(`r^k + r^{-k} > 2` when `r ≠ 1`): this is EXACTLY where the arithmetic obstruction lives, per zero.

Unconditional and kernel-clean.  It does NOT prove RH — it pinpoints the per-zero positivity condition.
conjecture1_proved = False.
-/
import Mathlib
import Lc.LiCriterion.Basic

open Complex

namespace RvMWeierstrass

/-- **Unconditional anatomy of the paired Li summand.**  For every nontrivial zero `ρ` and every `n`,
    with `v := (1 - 1/ρ)^(n+1)`, `liPairedSummand n ρ = 2 - v - v⁻¹`.  (No critical-line hypothesis:
    `pairedZero ρ = 1 - ρ` sends `w := 1 - 1/ρ` to `w⁻¹`, so the two summands are reciprocal powers.) -/
theorem liPairedSummand_eq_two_sub_v_sub_inv (n : ℕ) (ρ : LiCriterion.NontrivialZero) :
    LiCriterion.liPairedSummand n ρ
      = 2 - (1 - 1 / ρ.val) ^ (n + 1) - ((1 - 1 / ρ.val) ^ (n + 1))⁻¹ := by
  have hρ0 : ρ.val ≠ 0 := LiCriterion.NontrivialZero.ne_zero ρ
  have hρ1 : ρ.val ≠ 1 := LiCriterion.NontrivialZero.ne_one ρ
  have hρ1' : ρ.val - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have h1ρ : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  set w : ℂ := 1 - 1 / ρ.val with hw
  have hwe : w = (ρ.val - 1) / ρ.val := by rw [hw, sub_div, div_self hρ0]
  have hpair : (1 : ℂ) - 1 / (1 - ρ.val) = w⁻¹ := by rw [hwe, inv_div]; field_simp; ring
  have hzp : ∀ x : ℂ, x ^ (-(n + 1 : ℤ)) = (x ^ (n + 1))⁻¹ := by
    intro x; rw [zpow_neg]; congr 1
  have hpair_pow : (w⁻¹) ^ (-(n + 1 : ℤ)) = w ^ (n + 1) := by rw [hzp w⁻¹, inv_pow, inv_inv]
  simp only [LiCriterion.liPairedSummand, LiCriterion.liSummand, LiCriterion.pairedZero_val]
  rw [← hw, hpair, hzp w, hpair_pow]
  ring

/-- **Per-zero positivity condition, exactly.**  `0 ≤ (liPairedSummand n ρ).re ↔ (v + v⁻¹).re ≤ 2`,
    with `v := (1 - 1/ρ)^(n+1)`.  All the arithmetic content of Li positivity sits in this condition. -/
theorem liPairedSummand_re_nonneg_iff (n : ℕ) (ρ : LiCriterion.NontrivialZero) :
    0 ≤ (LiCriterion.liPairedSummand n ρ).re
      ↔ ((1 - 1 / ρ.val) ^ (n + 1) + ((1 - 1 / ρ.val) ^ (n + 1))⁻¹).re ≤ 2 := by
  rw [liPairedSummand_eq_two_sub_v_sub_inv, Complex.sub_re, Complex.sub_re, Complex.add_re]
  have h2 : ((2 : ℂ)).re = 2 := by norm_num
  rw [h2]
  constructor <;> intro h <;> linarith

/-- On the critical line the per-zero condition holds automatically: `|v| = 1` gives
    `v⁻¹ = conj v`, so `(v + v⁻¹).re = 2·(v.re) ≤ 2`.  (Recovers `RvMOnLinePositivity`.) -/
theorem onLine_re_v_add_inv_le_two (n : ℕ) (ρ : LiCriterion.NontrivialZero)
    (hρ : ρ.val.re = 1 / 2) :
    ((1 - 1 / ρ.val) ^ (n + 1) + ((1 - 1 / ρ.val) ^ (n + 1))⁻¹).re ≤ 2 := by
  have hρ0 : ρ.val ≠ 0 := LiCriterion.NontrivialZero.ne_zero ρ
  have hρ1 : ρ.val ≠ 1 := LiCriterion.NontrivialZero.ne_one ρ
  have hnρ0 : Complex.normSq ρ.val ≠ 0 := by rw [ne_eq, Complex.normSq_eq_zero]; exact hρ0
  set w : ℂ := 1 - 1 / ρ.val with hw
  have hwe : w = (ρ.val - 1) / ρ.val := by rw [hw, sub_div, div_self hρ0]
  have hnum : Complex.normSq (ρ.val - 1) = Complex.normSq ρ.val := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [hρ]; ring
  have hnorm : Complex.normSq w = 1 := by
    rw [hwe, Complex.normSq_div, hnum, div_self hnρ0]
  set v : ℂ := w ^ (n + 1) with hv
  have hv1 : Complex.normSq v = 1 := by rw [hv, map_pow, hnorm, one_pow]
  have huc : v * (starRingEnd ℂ) v = 1 := by rw [Complex.mul_conj, hv1, Complex.ofReal_one]
  have hinv : v⁻¹ = (starRingEnd ℂ) v := inv_eq_of_mul_eq_one_right huc
  rw [hinv, Complex.add_re, Complex.conj_re]
  -- (v + conj v).re = 2·(v.re); and v.re ≤ 1 since v.re² ≤ v.re² + v.im² = normSq v = 1
  have hsq : v.re * v.re + v.im * v.im = 1 := by
    have h := hv1; rwa [Complex.normSq_apply] at h
  have hvre : v.re ≤ 1 := by
    nlinarith [hsq, mul_self_nonneg v.im, mul_self_nonneg (v.re - 1)]
  linarith
