import Mathlib

/-!
  # g-step analytic cores (capped-joint-induction candidate, 2026-08-19)

  Formalizes the load-bearing rational inequalities behind the PROVEN g-step pieces of
  the capped joint induction (`docs/CANDIDATE_CAPPED_JOINT_INDUCTION.md`):

  - **j=1 (binding case):** with `μ_B=1/(2+μ)`, `a_B=(2+μ)/2`, the step collapses to
    `g_1(μ) = ((7+3μ)/10)^11 · Bcap(μ)/W`; on `μ ∈ (0,½]`, `Bcap ≤ glemma` gives
    `g_1 ≤ W·((7+3μ)/(2(3+μ)))^11`, and `(7+3μ)/(2(3+μ)) ≤ 17/14` (monotone cap), so
    `g_1 ≤ W·(17/14)^11 ≤ 1`.
  - **q=2:** `Bcap ≤ glemma` gives `L2 = W³(5/3)^11·f^11`, `f(a,b)=(10+3a+3b)/((3+a)(3+b))`
    decreasing in each variable so `f ≤ f(0,0)=10/9`, hence `L2 ≤ W³(50/27)^11 < 1` —
    the arm certificate `64³·50^11 < 621³·27^11`.

  This file kernel-checks the two rational cores + their certificates. The full induction
  assembly (Bcap/glemma definitions, the message recursion, Case-1 and Case-2) is separate.
  Entirely in `ℚ`.  `conjecture1_proved = False`.
-/

namespace R3Cert.GStepCore

/-- Base constant `W = 64/621`. -/
def W : ℚ := 64 / 621

/-- **j=1 monotone cap.** The single-child arm factor is `≤ 17/14` on `μ ∈ [0, ½]`
    (cross-multiplied: `14(7+3μ) ≤ 34(3+μ) ⟺ 8μ ≤ 4`). -/
theorem frac_j1 {μ : ℚ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1 / 2) :
    (7 + 3 * μ) / (2 * (3 + μ)) ≤ 17 / 14 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- **j=1 certificate.** `W·(17/14)^11 ≤ 1` (⟺ `64·17^11 ≤ 621·14^11`); this closes the
    binding case of the g-step, tight at the arm. -/
theorem cert_j1 : W * (17 / 14) ^ 11 ≤ 1 := by
  norm_num [W]

/-- **q=2 factor bound.** `f(a,b) = (10+3a+3b)/((3+a)(3+b)) ≤ 10/9` for `a,b ≥ 0`
    (cross-multiplied: `10·(3+a)(3+b) − 9(10+3a+3b) = 3a+3b+10ab ≥ 0`). -/
theorem frac_q2 {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (10 + 3 * a + 3 * b) / ((3 + a) * (3 + b)) ≤ 10 / 9 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_nonneg ha hb, ha, hb]

/-- **q=2 certificate (the arm certificate).** `W³·(50/27)^11 < 1`
    (⟺ `64³·50^11 < 621³·27^11`); identical to `arm_maximal`'s final rational certificate. -/
theorem cert_q2 : W ^ 3 * (50 / 27) ^ 11 < 1 := by
  norm_num [W]

/-- **Case-1 core (rigorous, all j).** The g-step normalized factor is
    `Φ = base^11 · P / (W·(5/3)^11)` with `P = ∏ Bcap ≤ 1` (each `Bcap ≤ 1` is `phi_le_one`).
    In the regime `base^11 ≤ W·(5/3)^11`, `Φ ≤ 1` — no suppression needed. This is the
    fully-rigorous half of the 2-case g-step split; abstract in `(base, P)`. -/
theorem case1_bound {base P : ℚ} (hb : 0 ≤ base)
    (hbase : base ^ 11 ≤ W * (5 / 3) ^ 11) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    base ^ 11 * P / (W * (5 / 3) ^ 11) ≤ 1 := by
  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  have hb11 : (0 : ℚ) ≤ base ^ 11 := by positivity
  rw [div_le_one hden]
  calc base ^ 11 * P ≤ base ^ 11 * 1 := by
        exact mul_le_mul_of_nonneg_left hP1 hb11
    _ = base ^ 11 := by ring
    _ ≤ W * (5 / 3) ^ 11 := hbase

end R3Cert.GStepCore
