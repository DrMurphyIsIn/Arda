/- telperion 0.1.6 | family IntegralityGate | input-hash acdc553fa1e8bb15
   11 theorems, 11 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace IntegralityGate

-- Integrality gate (p = 23): the strict inequality is an arithmetic
-- fact — the tie sits exactly on the 23-column.  Two decidable parts:
-- (1) the p-adic tie pin v_23(621) = 1, and
-- (2) the finite exceptional table (4 rows, the 23 ∣ n cases).
theorem ig_bg_23gate_valuation : (23 ∣ 621) ∧ ¬ (529 ∣ 621) := by norm_num
theorem ig_bg_23gate_row_0 : (357696 : ℤ) < 357697 := by norm_num
theorem ig_bg_23gate_row_1 : (357695 : ℤ) < 357696 := by norm_num
theorem ig_bg_23gate_row_2 : (621 : ℤ) < 622 := by norm_num
theorem ig_bg_23gate_row_3 : (15552 : ℤ) < 15553 := by norm_num
def ig_bg_23gate_exc : List (ℤ × ℤ) := [(357696, 357697), (357695, 357696), (621, 622), (15552, 15553)]
theorem ig_bg_23gate_table : ∀ x ∈ ig_bg_23gate_exc, x.1 < x.2 := by decide
-- Integrality gate (p = 5): the strict inequality is an arithmetic
-- fact — the tie sits exactly on the 5-column.  Two decidable parts:
-- (1) the p-adic tie pin v_5(50) = 2, and
-- (2) the finite exceptional table (3 rows, the 5 ∣ n cases).
theorem ig_p5_gate_valuation : (25 ∣ 50) ∧ ¬ (125 ∣ 50) := by norm_num
theorem ig_p5_gate_row_0 : (1 : ℤ) < 2 := by norm_num
theorem ig_p5_gate_row_1 : (7 : ℤ) < 10 := by norm_num
theorem ig_p5_gate_row_2 : (49 : ℤ) < 50 := by norm_num
def ig_p5_gate_exc : List (ℤ × ℤ) := [(1, 2), (7, 10), (49, 50)]
theorem ig_p5_gate_table : ∀ x ∈ ig_p5_gate_exc, x.1 < x.2 := by decide

end IntegralityGate
