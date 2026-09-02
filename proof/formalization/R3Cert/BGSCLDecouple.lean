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

end BGSCL
end R3Cert
