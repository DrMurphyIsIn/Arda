/- telperion 0.1.6 | family BraggDefectSIE | input-hash 034a024e17005445
   36 theorems, 21 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import ScaledInterval

namespace BraggDefectSIE

open ScaledInterval

-- sie_defect_offline: scaled_interval_eval at scale S = 10000000000000000000000000000000000000000 (9 nodes).  Every box is recomputed by the kernel (decide +kernel); the mem_* lemmas lift it to ℝ.  conjecture1_proved = False.
def sie_defect_offline_S : ℤ := 10000000000000000000000000000000000000000
theorem sie_defect_offline_hS : (0 : ℤ) < sie_defect_offline_S := by decide +kernel
def sie_defect_offline_b0 : RI := ⟨(-20000000000000000000000000000000000000000), (-19999999999999999999999999999999999999999)⟩
noncomputable def sie_defect_offline_v0 : ℝ := (-2 : ℝ)
theorem sie_defect_offline_b0_calc : RI.subset (RI.ofFrac sie_defect_offline_S (-2) 1) sie_defect_offline_b0 = true := by decide +kernel
theorem sie_defect_offline_b0_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b0 sie_defect_offline_v0 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_defect_offline_hS (by norm_num) (by norm_num [sie_defect_offline_v0])) sie_defect_offline_b0_calc
def sie_defect_offline_b1 : RI := ⟨(-1000000000000000000000000000000000000000), (-999999999999999999999999999999999999999)⟩
noncomputable def sie_defect_offline_v1 : ℝ := ((-1 : ℝ) / 10)
theorem sie_defect_offline_b1_calc : RI.subset (RI.ofFrac sie_defect_offline_S (-1) 10) sie_defect_offline_b1 = true := by decide +kernel
theorem sie_defect_offline_b1_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b1 sie_defect_offline_v1 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_defect_offline_hS (by norm_num) (by norm_num [sie_defect_offline_v1])) sie_defect_offline_b1_calc
def sie_defect_offline_b2 : RI := ⟨9048374180359595731642490594464366211924, 9048374180359595731642490594464366211977⟩
theorem sie_defect_offline_b2_small : RI.expSmallOK sie_defect_offline_S sie_defect_offline_b1 0 = true := by decide +kernel
theorem sie_defect_offline_b2_rem : RI.expRemOK sie_defect_offline_S 34 1 = true := by decide +kernel
noncomputable def sie_defect_offline_v2 : ℝ := Real.exp sie_defect_offline_v1
theorem sie_defect_offline_b2_calc : RI.subset (RI.expR sie_defect_offline_S sie_defect_offline_b1 0 34 1) sie_defect_offline_b2 = true := by decide +kernel
theorem sie_defect_offline_b2_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b2 sie_defect_offline_v2 :=
  RI.mem_of_subset (RI.mem_expR sie_defect_offline_hS sie_defect_offline_b1_mem sie_defect_offline_b2_small sie_defect_offline_b2_rem) sie_defect_offline_b2_calc
def sie_defect_offline_b3 : RI := ⟨(-10951625819640404268357509405535633788076), (-10951625819640404268357509405535633788022)⟩
noncomputable def sie_defect_offline_v3 : ℝ := sie_defect_offline_v0 + sie_defect_offline_v2
theorem sie_defect_offline_b3_calc : RI.subset (RI.add sie_defect_offline_b0 sie_defect_offline_b2) sie_defect_offline_b3 = true := by decide +kernel
theorem sie_defect_offline_b3_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b3 sie_defect_offline_v3 :=
  RI.mem_of_subset (RI.mem_add sie_defect_offline_b0_mem sie_defect_offline_b2_mem) sie_defect_offline_b3_calc
def sie_defect_offline_b4 : RI := ⟨1000000000000000000000000000000000000000, 1000000000000000000000000000000000000001⟩
noncomputable def sie_defect_offline_v4 : ℝ := ((1 : ℝ) / 10)
theorem sie_defect_offline_b4_calc : RI.subset (RI.ofFrac sie_defect_offline_S 1 10) sie_defect_offline_b4 = true := by decide +kernel
theorem sie_defect_offline_b4_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b4 sie_defect_offline_v4 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_defect_offline_hS (by norm_num) (by norm_num [sie_defect_offline_v4])) sie_defect_offline_b4_calc
def sie_defect_offline_b5 : RI := ⟨11051709180756476248117078264902466682235, 11051709180756476248117078264902466682277⟩
theorem sie_defect_offline_b5_small : RI.expSmallOK sie_defect_offline_S sie_defect_offline_b4 0 = true := by decide +kernel
theorem sie_defect_offline_b5_rem : RI.expRemOK sie_defect_offline_S 34 1 = true := by decide +kernel
noncomputable def sie_defect_offline_v5 : ℝ := Real.exp sie_defect_offline_v4
theorem sie_defect_offline_b5_calc : RI.subset (RI.expR sie_defect_offline_S sie_defect_offline_b4 0 34 1) sie_defect_offline_b5 = true := by decide +kernel
theorem sie_defect_offline_b5_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b5 sie_defect_offline_v5 :=
  RI.mem_of_subset (RI.mem_expR sie_defect_offline_hS sie_defect_offline_b4_mem sie_defect_offline_b5_small sie_defect_offline_b5_rem) sie_defect_offline_b5_calc
def sie_defect_offline_b6 : RI := ⟨100083361116071979759568859366832894159, 100083361116071979759568859366832894255⟩
noncomputable def sie_defect_offline_v6 : ℝ := sie_defect_offline_v3 + sie_defect_offline_v5
theorem sie_defect_offline_b6_calc : RI.subset (RI.add sie_defect_offline_b3 sie_defect_offline_b5) sie_defect_offline_b6 = true := by decide +kernel
theorem sie_defect_offline_b6_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b6 sie_defect_offline_v6 :=
  RI.mem_of_subset (RI.mem_add sie_defect_offline_b3_mem sie_defect_offline_b5_mem) sie_defect_offline_b6_calc
def sie_defect_offline_b7 : RI := ⟨1001667917229006871799595119804369890, 1001667917229006871799595119804369893⟩
noncomputable def sie_defect_offline_v7 : ℝ := sie_defect_offline_v6 * sie_defect_offline_v6
theorem sie_defect_offline_b7_calc : RI.subset (RI.mul sie_defect_offline_S sie_defect_offline_b6 sie_defect_offline_b6) sie_defect_offline_b7 = true := by decide +kernel
theorem sie_defect_offline_b7_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b7 sie_defect_offline_v7 :=
  RI.mem_of_subset (RI.mem_mul sie_defect_offline_hS sie_defect_offline_b6_mem sie_defect_offline_b6_mem) sie_defect_offline_b7_calc
def sie_defect_offline_b8 : RI := ⟨(-1001667917229006871799595119804369893), (-1001667917229006871799595119804369890)⟩
noncomputable def sie_defect_offline_v8 : ℝ := -sie_defect_offline_v7
theorem sie_defect_offline_b8_calc : RI.subset (RI.neg sie_defect_offline_b7) sie_defect_offline_b8 = true := by decide +kernel
theorem sie_defect_offline_b8_mem : RI.Mem sie_defect_offline_S sie_defect_offline_b8 sie_defect_offline_v8 :=
  RI.mem_of_subset (RI.mem_neg sie_defect_offline_b7_mem) sie_defect_offline_b8_calc
theorem sie_defect_offline_lo_calc : RI.lowerOK sie_defect_offline_S sie_defect_offline_b8 (-1957503930982498711627558116252003079150110082803036995985602456729126067929069837779873677055641334915004924707647824293913235373458273903210508792181881) 19542444130562717342736579894714125276139669165907166175656490622972757664768900000000000000000000000000000000000000000000000000000000000000000000000000000000 = true := by decide +kernel
theorem sie_defect_offline_hi_calc : RI.upperOK sie_defect_offline_S sie_defect_offline_b8 (-1957503930982498711614926803795741251867682177931660778058090203284392257792384397626586656512971699612677910422316624293913235373458273903210508792181881) 19542444130562717342737210934295300643770643047158621178046789521488913388427220640000000000000000000000000000000000000000000000000000000000000000000000000000 = true := by decide +kernel
/-- `sie_defect_offline`: the kernel-checked enclosure (exact-evaluated pre-emission). -/
theorem sie_defect_offline : ((-1957503930982498711627558116252003079150110082803036995985602456729126067929069837779873677055641334915004924707647824293913235373458273903210508792181881 : ℝ) / 19542444130562717342736579894714125276139669165907166175656490622972757664768900000000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ (-((((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))) * (((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))))) ∧ (-((((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))) * (((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))))) ≤ ((-1957503930982498711614926803795741251867682177931660778058090203284392257792384397626586656512971699612677910422316624293913235373458273903210508792181881 : ℝ) / 19542444130562717342737210934295300643770643047158621178046789521488913388427220640000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  have h : RI.Mem sie_defect_offline_S sie_defect_offline_b8 (-((((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))) * (((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))))) := sie_defect_offline_b8_mem
  exact ⟨RI.le_of_mem sie_defect_offline_hS h (by norm_num) (by norm_num) sie_defect_offline_lo_calc,
    RI.ge_of_mem sie_defect_offline_hS h (by norm_num) (by norm_num) sie_defect_offline_hi_calc⟩
example : ((-1957503930982498711627558116252003079150110082803036995985602456729126067929069837779873677055641334915004924707647824293913235373458273903210508792181881 : ℝ) / 19542444130562717342736579894714125276139669165907166175656490622972757664768900000000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ (-((((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))) * (((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))))) ∧ (-((((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))) * (((-2 : ℝ) + (Real.exp ((-1 : ℝ) / 10))) + (Real.exp ((1 : ℝ) / 10))))) ≤ ((-1957503930982498711614926803795741251867682177931660778058090203284392257792384397626586656512971699612677910422316624293913235373458273903210508792181881 : ℝ) / 19542444130562717342737210934295300643770643047158621178046789521488913388427220640000000000000000000000000000000000000000000000000000000000000000000000000000) := sie_defect_offline

-- sie_exp_tenth: scaled_interval_eval at scale S = 10000000000000000000000000000000000000000 (2 nodes).  Every box is recomputed by the kernel (decide +kernel); the mem_* lemmas lift it to ℝ.  conjecture1_proved = False.
def sie_exp_tenth_S : ℤ := 10000000000000000000000000000000000000000
theorem sie_exp_tenth_hS : (0 : ℤ) < sie_exp_tenth_S := by decide +kernel
def sie_exp_tenth_b0 : RI := ⟨1000000000000000000000000000000000000000, 1000000000000000000000000000000000000001⟩
noncomputable def sie_exp_tenth_v0 : ℝ := ((1 : ℝ) / 10)
theorem sie_exp_tenth_b0_calc : RI.subset (RI.ofFrac sie_exp_tenth_S 1 10) sie_exp_tenth_b0 = true := by decide +kernel
theorem sie_exp_tenth_b0_mem : RI.Mem sie_exp_tenth_S sie_exp_tenth_b0 sie_exp_tenth_v0 :=
  RI.mem_of_subset (RI.mem_ofFrac sie_exp_tenth_hS (by norm_num) (by norm_num [sie_exp_tenth_v0])) sie_exp_tenth_b0_calc
def sie_exp_tenth_b1 : RI := ⟨11051709180756476248117078264902466682235, 11051709180756476248117078264902466682277⟩
theorem sie_exp_tenth_b1_small : RI.expSmallOK sie_exp_tenth_S sie_exp_tenth_b0 0 = true := by decide +kernel
theorem sie_exp_tenth_b1_rem : RI.expRemOK sie_exp_tenth_S 34 1 = true := by decide +kernel
noncomputable def sie_exp_tenth_v1 : ℝ := Real.exp sie_exp_tenth_v0
theorem sie_exp_tenth_b1_calc : RI.subset (RI.expR sie_exp_tenth_S sie_exp_tenth_b0 0 34 1) sie_exp_tenth_b1 = true := by decide +kernel
theorem sie_exp_tenth_b1_mem : RI.Mem sie_exp_tenth_S sie_exp_tenth_b1 sie_exp_tenth_v1 :=
  RI.mem_of_subset (RI.mem_expR sie_exp_tenth_hS sie_exp_tenth_b0_mem sie_exp_tenth_b1_small sie_exp_tenth_b1_rem) sie_exp_tenth_b1_calc
theorem sie_exp_tenth_lo_calc : RI.lowerOK sie_exp_tenth_S sie_exp_tenth_b1 442068367230259049924676660787771898883 400000000000000000000000000000000000000 = true := by decide +kernel
theorem sie_exp_tenth_hi_calc : RI.upperOK sie_exp_tenth_S sie_exp_tenth_b1 11051709180756476248117094953514706601127 10000000000000000000000000000000000000000 = true := by decide +kernel
/-- `sie_exp_tenth`: the kernel-checked enclosure (exact-evaluated pre-emission). -/
theorem sie_exp_tenth : ((442068367230259049924676660787771898883 : ℝ) / 400000000000000000000000000000000000000) ≤ (Real.exp ((1 : ℝ) / 10)) ∧ (Real.exp ((1 : ℝ) / 10)) ≤ ((11051709180756476248117094953514706601127 : ℝ) / 10000000000000000000000000000000000000000) := by
  have h : RI.Mem sie_exp_tenth_S sie_exp_tenth_b1 (Real.exp ((1 : ℝ) / 10)) := sie_exp_tenth_b1_mem
  exact ⟨RI.le_of_mem sie_exp_tenth_hS h (by norm_num) (by norm_num) sie_exp_tenth_lo_calc,
    RI.ge_of_mem sie_exp_tenth_hS h (by norm_num) (by norm_num) sie_exp_tenth_hi_calc⟩
example : ((442068367230259049924676660787771898883 : ℝ) / 400000000000000000000000000000000000000) ≤ (Real.exp ((1 : ℝ) / 10)) ∧ (Real.exp ((1 : ℝ) / 10)) ≤ ((11051709180756476248117094953514706601127 : ℝ) / 10000000000000000000000000000000000000000) := sie_exp_tenth

end BraggDefectSIE
