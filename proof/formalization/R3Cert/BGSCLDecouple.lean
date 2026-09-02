/-
  SCL per-hub decouple residual — the `nlinarith` core of `FlowedHubStep` (the d≤6 tangent decouple).
  This discharges the Telperion `PerHubDecoupleResidualCertificate` in Lean.  The d=2 residual `R(S) ≤ 0`
  is PROVEN here (sorry-free, axiom-clean); d=3..6 follow by the SAME template (`log((4d-1)/(3d))` combined via
  `×11` into `log(rational)`, bounded by a clean `exp` power, then `μ/(d+S)` cleared and `nlinarith` on the
  upward parabola in `S`).  Verified against the Telperion cert (20 endpoint atoms, margin ≥ +0.007).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep

namespace R3Cert
namespace BGSCL

/-- The keystone log bound for the d=2 decouple: `g := log(7/6) − F* ≤ −1/22`.  Via `11·g =
    log((7/6)^11 · 64/621)` and the clean half-integer bound `exp(1/2) = √(exp 1) < 1.6489`. -/
theorem log76_gap : Real.log (7/6) - FSTAR ≤ -(1/22) := by
  have hF : FSTAR = Real.log (621 / 64) / 11 := rfl
  rw [hF]
  have hcomb : (11:ℝ) * (Real.log (7/6) - Real.log (621/64)/11)
      = Real.log ((7/6)^11 * (64/621)) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
      show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]; ring
  have hval : Real.log ((7/6)^11 * (64/621)) ≤ -(1/2) := by
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_neg]
    have hehalf : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hexp12 : Real.exp (1/2) < 1.6489 := by nlinarith [hehalf, h1, Real.exp_pos (1/2 : ℝ)]
    have hpos : (0:ℝ) < Real.exp (1/2) := Real.exp_pos _
    have hinvcancel : (Real.exp (1/2))⁻¹ * Real.exp (1/2) = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    have hinvpos : (0:ℝ) < (Real.exp (1/2))⁻¹ := inv_pos.mpr hpos
    nlinarith [hexp12, hpos, hinvcancel, hinvpos]
  nlinarith [hcomb, hval]

/-- d=2 decouple residual `R(S) ≤ 0` on `S ∈ [0, 1/2]`, `μ ∈ I`.  `μ'' = muPP 2 μ = 3(7−3μ)/49`;
    `R(S) = μ''/3 − μ/3 − 1/7 + log(7/6) − F* + 9μS/49 + μ/(2+S)`.  The log part `≤ −1/22` (`log76_gap`);
    the rational part `≤ 1/22` after clearing `(2+S) > 0` (upward parabola, margin `+0.0002`). -/
theorem decouple_d2 (μ S : ℝ) (hμ : inI μ) (hS0 : 0 ≤ S) (hSmax : S ≤ 1/2) :
    (muPP 2 μ)/3 - μ/3 - 1/7 + Real.log (7/6) - FSTAR + 9*μ*S/49 + μ/(2+S) ≤ 0 := by
  obtain ⟨hμlo, hμhi⟩ := hμ
  have hmuPP : muPP 2 μ = 3*(7 - 3*μ)/49 := by rw [muPP]; norm_num
  have hg := log76_gap
  have h2S : (0:ℝ) < 2 + S := by linarith
  have hμpos : 0 ≤ μ := by linarith
  rw [hmuPP, div_eq_mul_inv μ (2+S)]
  have hinv : (2+S)⁻¹ * (2+S) = 1 := inv_mul_cancel₀ (ne_of_gt h2S)
  have hinvpos : 0 < (2+S)⁻¹ := inv_pos.mpr h2S
  nlinarith [hg, hμlo, hμhi, hS0, hSmax, h2S, hinv, hinvpos, mul_nonneg hμpos (le_of_lt hinvpos),
    mul_nonneg hμpos hS0, mul_nonneg (mul_nonneg hμpos hS0) (le_of_lt hinvpos),
    mul_nonneg (mul_nonneg hμpos (le_of_lt hinvpos)) hS0]

/-- d=3 log gap: `log(3/2) + log(11/9) - 3 F* ≤ 0` (the combined `log(X_3)` with `X_3 = (3/2)^11·(11/9)^11·(64/621)^3 < 1`). -/
theorem log_gap_d3 : Real.log (3/2) + Real.log (11/9) - 3*FSTAR ≤ 0 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(Real.log (3/2) + Real.log (11/9) - 3*(Real.log (621/64)/11))
      = Real.log ((3/2)^11 * (11/9)^11 * (64/621)^3) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^11 * (11/9)^11 * (64/621)^3) ≤ 0 :=
    Real.log_nonpos (by positivity) (by norm_num)
  nlinarith [hcomb, hX]

/-- d=3 decouple residual `R(S) ≤ 0` on `S ∈ [0,2]`, `μ ∈ I`.  `μ'' = muPP 3 μ = 3(11−3μ)/121`. -/
theorem decouple_d3 (μ S : ℝ) (hμ : inI μ) (hS0 : 0 ≤ S) (hSmax : S ≤ 2) :
    2*(muPP 3 μ)/3 - μ/3 + 9*μ*S/121 - 2/11 + (Real.log (3/2) + Real.log (11/9) - 3*FSTAR) + μ/(3+S) ≤ 0 := by
  obtain ⟨hμlo, hμhi⟩ := hμ
  have hmuPP : muPP 3 μ = 3*(11 - 3*μ)/121 := by rw [muPP]; norm_num
  have hg := log_gap_d3
  have h3S : (0:ℝ) < 3 + S := by linarith
  have hμpos : 0 ≤ μ := by linarith
  rw [hmuPP, div_eq_mul_inv μ (3+S)]
  have hinv : (3+S)⁻¹ * (3+S) = 1 := inv_mul_cancel₀ (ne_of_gt h3S)
  have hinvpos : 0 < (3+S)⁻¹ := inv_pos.mpr h3S
  nlinarith [hg, hμlo, hμhi, hS0, hSmax, h3S, hinv, hinvpos, mul_nonneg hμpos (le_of_lt hinvpos),
    mul_nonneg hμpos hS0, mul_nonneg (mul_nonneg hμpos hS0) (le_of_lt hinvpos),
    mul_nonneg (mul_nonneg hμpos (le_of_lt hinvpos)) hS0]

/-- d=4 log gap: `2·log(3/2) + log(5/4) - 5 F* ≤ 1334065663/1159983480832`. -/
theorem log_gap_d4 : 2*Real.log (3/2) + Real.log (5/4) - 5*FSTAR ≤ 1334065663/1159983480832 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(2*Real.log (3/2) + Real.log (5/4) - 5*(Real.log (621/64)/11))
      = Real.log ((3/2)^22 * (5/4)^11 * (64/621)^5) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^22 * (5/4)^11 * (64/621)^5)
      ≤ (3/2)^22 * (5/4)^11 * (64/621)^5 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hXval : (3/2)^22 * (5/4)^11 * (64/621)^5 - 1 = 1334065663/105453043712 := by norm_num
  nlinarith [hcomb, hX, hXval]

/-- d=4 decouple residual `R(S) ≤ 0` on `S ∈ [0,3]`, `μ ∈ I`.  `μ'' = muPP 4 μ = 3(15−3μ)/225`. -/
theorem decouple_d4 (μ S : ℝ) (hμ : inI μ) (hS0 : 0 ≤ S) (hSmax : S ≤ 3) :
    (1*(muPP 4 μ)/1) - μ/3 + 1*μ*S/16 - (1/4) + (2*Real.log (3/2) + Real.log (5/4) - 5*FSTAR) + μ/(4+S) ≤ 0 := by
  obtain ⟨hμlo, hμhi⟩ := hμ
  have hmuPP : muPP 4 μ = 3*(15 - 3*μ)/225 := by rw [muPP]; norm_num
  have hg := log_gap_d4
  have hdS : (0:ℝ) < 4 + S := by linarith
  have hμpos : 0 ≤ μ := by linarith
  rw [hmuPP, div_eq_mul_inv μ (4+S)]
  have hinv : (4+S)⁻¹ * (4+S) = 1 := inv_mul_cancel₀ (ne_of_gt hdS)
  have hinvpos : 0 < (4+S)⁻¹ := inv_pos.mpr hdS
  nlinarith [hg, hμlo, hμhi, hS0, hSmax, hdS, hinv, hinvpos, mul_nonneg hμpos (le_of_lt hinvpos),
    mul_nonneg hμpos hS0, mul_nonneg (mul_nonneg hμpos hS0) (le_of_lt hinvpos),
    mul_nonneg (mul_nonneg hμpos (le_of_lt hinvpos)) hS0]


/-- d=5 log gap: `3·log(3/2) + log(19/15) - 7 F* ≤ 12677795138367509/1828763667822265625`. -/
theorem log_gap_d5 : 3*Real.log (3/2) + Real.log (19/15) - 7*FSTAR ≤ 12677795138367509/1828763667822265625 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(3*Real.log (3/2) + Real.log (19/15) - 7*(Real.log (621/64)/11))
      = Real.log ((3/2)^33 * (19/15)^11 * (64/621)^7) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^33 * (19/15)^11 * (64/621)^7)
      ≤ (3/2)^33 * (19/15)^11 * (64/621)^7 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hXval : (3/2)^33 * (19/15)^11 * (64/621)^7 - 1 = 12677795138367509/166251242529296875 := by norm_num
  nlinarith [hcomb, hX, hXval]

/-- d=5 decouple residual `R(S) ≤ 0` on `S ∈ [0,4]`, `μ ∈ I`.  `μ'' = muPP 5 μ = 3(19−3μ)/361`. -/
theorem decouple_d5 (μ S : ℝ) (hμ : inI μ) (hS0 : 0 ≤ S) (hSmax : S ≤ 4) :
    (4*(muPP 5 μ)/3) - μ/3 + 9*μ*S/361 - (4/19) + (3*Real.log (3/2) + Real.log (19/15) - 7*FSTAR) + μ/(5+S) ≤ 0 := by
  obtain ⟨hμlo, hμhi⟩ := hμ
  have hmuPP : muPP 5 μ = 3*(19 - 3*μ)/361 := by rw [muPP]; norm_num
  have hg := log_gap_d5
  have hdS : (0:ℝ) < 5 + S := by linarith
  have hμpos : 0 ≤ μ := by linarith
  rw [hmuPP, div_eq_mul_inv μ (5+S)]
  have hinv : (5+S)⁻¹ * (5+S) = 1 := inv_mul_cancel₀ (ne_of_gt hdS)
  have hinvpos : 0 < (5+S)⁻¹ := inv_pos.mpr hdS
  nlinarith [hg, hμlo, hμhi, hS0, hSmax, hdS, hinv, hinvpos, mul_nonneg hμpos (le_of_lt hinvpos),
    mul_nonneg hμpos hS0, mul_nonneg (mul_nonneg hμpos hS0) (le_of_lt hinvpos),
    mul_nonneg (mul_nonneg hμpos (le_of_lt hinvpos)) hS0]


/-- d=6 log gap: `4·log(3/2) + log(23/18) - 9 F* ≤ 43/5346`. -/
theorem log_gap_d6 : 4*Real.log (3/2) + Real.log (23/18) - 9*FSTAR ≤ 43/5346 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(4*Real.log (3/2) + Real.log (23/18) - 9*(Real.log (621/64)/11))
      = Real.log ((3/2)^44 * (23/18)^11 * (64/621)^9) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^44 * (23/18)^11 * (64/621)^9)
      ≤ (3/2)^44 * (23/18)^11 * (64/621)^9 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hXval : (3/2)^44 * (23/18)^11 * (64/621)^9 - 1 = 43/486 := by norm_num
  nlinarith [hcomb, hX, hXval]

/-- d=6 decouple residual `R(S) ≤ 0` on `S ∈ [0,5]`, `μ ∈ I`.  `μ'' = muPP 6 μ = 3(23−3μ)/529`. -/
theorem decouple_d6 (μ S : ℝ) (hμ : inI μ) (hS0 : 0 ≤ S) (hSmax : S ≤ 5) :
    (5*(muPP 6 μ)/3) - μ/3 + 9*μ*S/529 - (5/23) + (4*Real.log (3/2) + Real.log (23/18) - 9*FSTAR) + μ/(6+S) ≤ 0 := by
  obtain ⟨hμlo, hμhi⟩ := hμ
  have hmuPP : muPP 6 μ = 3*(23 - 3*μ)/529 := by rw [muPP]; norm_num
  have hg := log_gap_d6
  have hdS : (0:ℝ) < 6 + S := by linarith
  have hμpos : 0 ≤ μ := by linarith
  rw [hmuPP, div_eq_mul_inv μ (6+S)]
  have hinv : (6+S)⁻¹ * (6+S) = 1 := inv_mul_cancel₀ (ne_of_gt hdS)
  have hinvpos : 0 < (6+S)⁻¹ := inv_pos.mpr hdS
  nlinarith [hg, hμlo, hμhi, hS0, hSmax, hdS, hinv, hinvpos, mul_nonneg hμpos (le_of_lt hinvpos),
    mul_nonneg hμpos hS0, mul_nonneg (mul_nonneg hμpos hS0) (le_of_lt hinvpos),
    mul_nonneg (mul_nonneg hμpos (le_of_lt hinvpos)) hS0]

end BGSCL
end R3Cert
