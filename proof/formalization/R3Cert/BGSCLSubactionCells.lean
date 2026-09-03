/-
  Corrected compact-core SUBACTION cells for the VALIDATED 5-case witness (2026-09-03).

  Companion to `BGSCLSubaction`.  The POC cells there (`subaction_cell_broom_d4`,
  `subaction_cell_d4_d3`) used ρ coefficients from the (tail-failing) witness.  The
  witness that verifies on all branches n≤15 + tail + 120k mixed high-degree trees is

      ρ(1,μ)=F* ; ρ(2,μ)=2F*−log(3/2)+(1/4)(μ−1/3) ; ρ(3,μ)=μ/32 ; ρ(4,μ)=μ/384 ; ρ(d≥5)=0.

  This file re-derives the two representative deg-4 cells at the CORRECTED slopes.
  The two analytic cores are Telperion-generated (`emit_log_combination`, F*-folding):
  `log54_sub_fstar_le_40` (tighter 1/40, the old 1/20 is too loose once ρ(4)≠0) and
  `log74_le_4fstar_broom` (negative threshold −1/2688, from the ρ(4) term tightening
  the broom).  Both use the SAME fold as the dogfooded BG lemmas.  Kernel-checked, no
  `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction

namespace R3Cert
namespace BGSCL

open Real

/-- Corrected degree-3 line of the validated witness: `ρ₃(μ) = μ/32` (through the origin). -/
noncomputable def rho3c (μ : ℝ) : ℝ := μ / 32

/-- Corrected degree-4 line of the validated witness: `ρ₄(μ) = μ/384` (the tail fix). -/
noncomputable def rho4c (μ : ℝ) : ℝ := μ / 384

/-! ### Analytic cores — Telperion `emit_log_combination` output (F*-folding, tangent route). -/

-- ===== F*-folding, TANGENT route: 1·log(5/4) − 1·FSTAR ≤ 1/40 (FSTAR = log(621/64)/11) =====
-- Fold: 11·(log 5/4 − FSTAR) = log((5/4)^11·(621/64)⁻¹) ≤ (5/4)^11·(621/64)⁻¹ − 1
-- ≤ 11/40 (norm_num).  Tighter than the shipped `log54_sub_fstar_le` (1/20); needed
-- once ρ(4)≠0 tightens the deg-4/deg-3 cell.  TIGHT AT THE TIE (no F* lower bound).
theorem log54_sub_fstar_le_40 : Real.log (5/4 : ℝ) - (FSTAR : ℝ) ≤ (1/40 : ℝ) := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (5/4 : ℝ) ^ (11 : ℕ) * (64/621) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((5/4 : ℝ) ^ (11 : ℕ) * (64/621))
      = 11 * Real.log (5/4 : ℝ) - Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621 : ℝ) = (621/64 : ℝ)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (5/4 : ℝ) ^ (11 : ℕ) * (64/621) - 1 ≤ 11/40 := by norm_num
  linarith

-- ===== F*-folding, TANGENT route (general k=4): 1·log(7/4) − 4·FSTAR ≤ -1/2688 =====
-- Fold: 11·(log 7/4 − 4·FSTAR) = log((7/4)^11·((621/64)^4)⁻¹) ≤ (7/4)^11·((621/64)^4)⁻¹ − 1
-- ≤ -11/2688 (norm_num).  Negative threshold from the ρ(4) term tightening the broom.
theorem log74_le_4fstar_broom : Real.log (7/4 : ℝ) - (4 * FSTAR : ℝ) ≤ (-1/2688 : ℝ) := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (7/4 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (4 : ℕ))⁻¹) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((7/4 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (4 : ℕ))⁻¹))
      = 11 * Real.log (7/4 : ℝ) - 4 * Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_inv, Real.log_pow]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (7/4 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (4 : ℕ))⁻¹) - 1 ≤ -11/2688 := by norm_num
  linarith

/-! ### The two corrected compact-core cells. -/

/-- **Corrected broom cell (deg-4 hub, 3 leaf children).**  SUB at the deg-4 all-leaf
    corner with the validated witness: the hub's own `ρ₄(bY hub) = (1/7)/384 = 1/2688`
    (bY(broom)=1/7) now appears on the LHS (it vanished under the old ρ(4)=0).  Discharged
    by the Telperion `log74_le_4fstar_broom` at the corrected negative threshold. -/
theorem subaction_cell_broom_d4_corrected :
    (Real.log (1 + 3 / ((3 : ℝ) + 1)) - FSTAR) + (1/2688 : ℝ) ≤ 3 * FSTAR := by
  have h74 : (1 + 3 / ((3 : ℝ) + 1)) = 7 / 4 := by norm_num
  rw [h74]
  have := log74_le_4fstar_broom
  linarith

/-- **Corrected tight cell (deg-4 hub, three deg-3 children, y ∈ [1/5,1/3]).**  SUB at the
    binding class with the validated witness `ρ₃(μ)=μ/32`.  The hub's own `ρ₄(bY hub) =
    1/(384(4+S)) ≤ 5/8832` (since `S = Σy ≥ 3/5`) is over-bounded by the constant `5/8832`,
    so this cell IMPLIES the exact SUB inequality.  Proof: concave-log tangent at the
    aggregate endpoint `S=1` (`log_tangent`), plus the corrected log-enclosure
    `log54_sub_fstar_le_40`.  Kernel-checked. -/
theorem subaction_cell_d4_d3_corrected (y1 y2 y3 : ℝ)
    (h1 : 1 / 5 ≤ y1) (h1' : y1 ≤ 1 / 3) (h2 : 1 / 5 ≤ y2) (h2' : y2 ≤ 1 / 3)
    (h3 : 1 / 5 ≤ y3) (h3' : y3 ≤ 1 / 3) :
    (Real.log (1 + (y1 + y2 + y3) / 4) - FSTAR) + (5/8832 : ℝ)
      ≤ rho3c y1 + rho3c y2 + rho3c y3 := by
  have hS0 : (0 : ℝ) ≤ y1 + y2 + y3 := by linarith
  have htan := log_tangent (d := (4 : ℝ)) (s := y1 + y2 + y3) (s0 := (1 : ℝ))
    (by norm_num) hS0 (by norm_num)
  rw [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num, show (4 : ℝ) + 1 = 5 by norm_num] at htan
  have henc := log54_sub_fstar_le_40
  simp only [rho3c]
  linarith

end BGSCL
end R3Cert
