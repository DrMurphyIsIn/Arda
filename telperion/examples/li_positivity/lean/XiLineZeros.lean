/- telperion 0.1.6 | family XiLineZeros | input-hash 8bf933124b3cae44
   3 theorems, 11 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import LambdaLineReal

open Complex

namespace XiLineZeros

/-!
# On-line zero localization of the completed Riemann zeta function (Stage 1 core)

Each theorem below states: given certified real enclosures of `Lambda(1/2 + i*t)`
(the documented Arb-certified NON-KERNEL input, as hypotheses) with alternating
signs, there exist strictly increasing reals in `[a, b]` at which
`completedRiemannZeta (1/2 + t*I) = 0`, i.e. `>= N` zeros of `Lambda` on the
critical line.  The proof lifts to the real part `gLine` (real on the line by the
Task-2 prelude `ZetaZeroLocalization.completedZeta_im_eq_zero`), uses its
continuity, and applies the intermediate value theorem on each sign-change
subinterval.

Note: `conjecture1_proved = False`.  This localizes individual nontrivial zeros ON
the critical line from certified enclosures; it does NOT prove RH.
-/

-- Real part of Lambda on the critical line.
noncomputable def gLine (t : ℝ) : ℝ := (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re

-- The lifting point `1/2 + t*I` is never 0 nor 1 (its real part is 1/2).
theorem line_ne_zero (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (0 : ℂ).re := by rw [h]
  simp at hre

theorem line_ne_one (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (1 : ℂ).re := by rw [h]
  simp at hre

-- `gLine` is continuous on all of ℝ.  `completedRiemannZeta` is differentiable
-- (hence continuous) at each line point `1/2 + t*I`, which is never 0 nor 1.
theorem gLine_continuous : Continuous gLine := by
  have hline : Continuous (fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hZeta : Continuous (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hd : DifferentiableAt ℂ completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) :=
      differentiableAt_completedZeta (line_ne_zero t) (line_ne_one t)
    exact ContinuousAt.comp (g := completedRiemannZeta)
      (f := fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) hd.continuousAt
      (hline.continuousAt (x := t))
  exact Complex.continuous_re.comp hZeta

-- On the line, Lambda equals its real part promoted to ℂ.
theorem lambda_eq_gLine (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = (gLine t : ℂ) := by
  have him : (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).im = 0 :=
    ZetaZeroLocalization.completedZeta_im_eq_zero t
  apply Complex.ext
  · rfl
  · rw [him]; simp [gLine]

theorem lambda_zero_first_14_15 (henc0 : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552))) (henc1 : (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15) : ∃ x1 : ℝ, (14 ≤ x1 ∧ x1 ≤ 15) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0) := by
  -- sign-change subinterval [14, 15]: root r1
  have hle0 : (14 : ℝ) ≤ 15 := by norm_num
  have hcont0 : ContinuousOn gLine (Set.Icc (14 : ℝ) 15) :=
    gLine_continuous.continuousOn
  have he_neg0 : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552)) := henc0
  have hneg0 : gLine 14 < 0 := by linarith [he_neg0]
  have he_pos0 : (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15 := henc1
  have hpos0 : (0 : ℝ) < gLine 15 := by linarith [he_pos0]
  have hmem0 : (0 : ℝ) ∈ gLine '' Set.Icc (14 : ℝ) 15 :=
    intermediate_value_Icc hle0 hcont0 ⟨le_of_lt hneg0, le_of_lt hpos0⟩
  obtain ⟨r1, hIcc0, hz0⟩ := hmem0
  have hri_lo0 : (14 : ℝ) < r1 := by
    rcases lt_or_eq_of_le hIcc0.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz0; rw [hz0] at hneg0; exact lt_irrefl 0 hneg0
  have hri_hi0 : r1 < (15 : ℝ) := by
    rcases lt_or_eq_of_le hIcc0.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz0; rw [hz0] at hpos0; exact lt_irrefl 0 hpos0
  have hLam0 : completedRiemannZeta (1 / 2 + (r1 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz0]; simp
  exact ⟨r1, ⟨by linarith [hri_lo0], by linarith [hri_hi0]⟩, hLam0⟩
example : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552)) → (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15 → ∃ x1 : ℝ, (14 ≤ x1 ∧ x1 ≤ 15) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0) := lambda_zero_first_14_15

theorem lambda_two_zeros_14_22 (henc0 : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552))) (henc1 : (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15) (henc2 : gLine 22 ≤ (-(1801852518142851124113227678086075933521062890040095480779984646131 / 56539106072908298546665520023773392506479484700019806659891398441363832832))) : ∃ x1 x2 : ℝ, (14 ≤ x1 ∧ x1 < x2 ∧ x2 ≤ 22) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0) := by
  -- sign-change subinterval [14, 15]: root r1
  have hle0 : (14 : ℝ) ≤ 15 := by norm_num
  have hcont0 : ContinuousOn gLine (Set.Icc (14 : ℝ) 15) :=
    gLine_continuous.continuousOn
  have he_neg0 : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552)) := henc0
  have hneg0 : gLine 14 < 0 := by linarith [he_neg0]
  have he_pos0 : (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15 := henc1
  have hpos0 : (0 : ℝ) < gLine 15 := by linarith [he_pos0]
  have hmem0 : (0 : ℝ) ∈ gLine '' Set.Icc (14 : ℝ) 15 :=
    intermediate_value_Icc hle0 hcont0 ⟨le_of_lt hneg0, le_of_lt hpos0⟩
  obtain ⟨r1, hIcc0, hz0⟩ := hmem0
  have hri_lo0 : (14 : ℝ) < r1 := by
    rcases lt_or_eq_of_le hIcc0.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz0; rw [hz0] at hneg0; exact lt_irrefl 0 hneg0
  have hri_hi0 : r1 < (15 : ℝ) := by
    rcases lt_or_eq_of_le hIcc0.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz0; rw [hz0] at hpos0; exact lt_irrefl 0 hpos0
  have hLam0 : completedRiemannZeta (1 / 2 + (r1 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz0]; simp
  -- sign-change subinterval [15, 22]: root r2
  have hle1 : (15 : ℝ) ≤ 22 := by norm_num
  have hcont1 : ContinuousOn gLine (Set.Icc (15 : ℝ) 22) :=
    gLine_continuous.continuousOn
  have he_neg1 : gLine 22 ≤ (-(1801852518142851124113227678086075933521062890040095480779984646131 / 56539106072908298546665520023773392506479484700019806659891398441363832832)) := henc2
  have hneg1 : gLine 22 < 0 := by linarith [he_neg1]
  have he_pos1 : (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15 := henc1
  have hpos1 : (0 : ℝ) < gLine 15 := by linarith [he_pos1]
  have hmem1 : (0 : ℝ) ∈ gLine '' Set.Icc (15 : ℝ) 22 :=
    intermediate_value_Icc' hle1 hcont1 ⟨le_of_lt hneg1, le_of_lt hpos1⟩
  obtain ⟨r2, hIcc1, hz1⟩ := hmem1
  have hri_lo1 : (15 : ℝ) < r2 := by
    rcases lt_or_eq_of_le hIcc1.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz1; rw [hz1] at hpos1; exact lt_irrefl 0 hpos1
  have hri_hi1 : r2 < (22 : ℝ) := by
    rcases lt_or_eq_of_le hIcc1.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz1; rw [hz1] at hneg1; exact lt_irrefl 0 hneg1
  have hLam1 : completedRiemannZeta (1 / 2 + (r2 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz1]; simp
  exact ⟨r1, r2, ⟨by linarith [hri_lo0], by linarith [hri_hi0, hri_lo1], by linarith [hri_hi1]⟩, ⟨hLam0, hLam1⟩⟩
example : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552)) → (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15 → gLine 22 ≤ (-(1801852518142851124113227678086075933521062890040095480779984646131 / 56539106072908298546665520023773392506479484700019806659891398441363832832)) → ∃ x1 x2 : ℝ, (14 ≤ x1 ∧ x1 < x2 ∧ x2 ≤ 22) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0) := lambda_two_zeros_14_22

theorem lambda_five_zeros_10_35 (henc8 : gLine 14 ≤ (-(73514097015932122112492589522271229502816984469312927938540724795094269239212512177602688194782951 / 35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416))) (henc9 : (2164343974256490366469119739937955650606711627583237028976624988105895516706199125783653140285231 / 559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944) ≤ gLine (29 / 2)) (henc22 : (8269572685861737265745636426276617573078736670612006593514409701930429424083354072348482068599609 / 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248) ≤ gLine 21) (henc23 : gLine (43 / 2) ≤ (-(14423352346132175721092019155338722797520943329041583503878160878595501167387150060661720462584489 / 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656))) (henc30 : gLine 25 ≤ (-(12981845829014324267080217854140594645728590894119209328480022621435772592901655587876085410796295 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872))) (henc31 : (6426463925131225995131591435275196951708251545367651003606072414446537691714308122961887169144729 / 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248) ≤ gLine (51 / 2)) (henc40 : (2448429418443069137831064390533583129598947878053442658519996320245205028633451654805415303761583 / 73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968) ≤ gLine 30) (henc41 : gLine (61 / 2) ≤ (-(1063185649582606514786425224501146226770241288656632341722042262646404797195790747549871321110301 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872))) (henc45 : gLine (65 / 2) ≤ (-(18803692014841497986507197754909735206420974618350328439671339541039560960699763220806714339397681 / 4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952))) (henc46 : (4441230828274178839190258324823673937214981662201877851657117694506058186701334669614029524082949 / 9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904) ≤ gLine 33) : ∃ x1 x2 x3 x4 x5 : ℝ, (10 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 ≤ 35) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0) := by
  -- sign-change subinterval [14, (29 / 2)]: root r1
  have hle0 : (14 : ℝ) ≤ (29 / 2) := by norm_num
  have hcont0 : ContinuousOn gLine (Set.Icc (14 : ℝ) (29 / 2)) :=
    gLine_continuous.continuousOn
  have he_neg0 : gLine 14 ≤ (-(73514097015932122112492589522271229502816984469312927938540724795094269239212512177602688194782951 / 35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416)) := henc8
  have hneg0 : gLine 14 < 0 := by linarith [he_neg0]
  have he_pos0 : (2164343974256490366469119739937955650606711627583237028976624988105895516706199125783653140285231 / 559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944) ≤ gLine (29 / 2) := henc9
  have hpos0 : (0 : ℝ) < gLine (29 / 2) := by linarith [he_pos0]
  have hmem0 : (0 : ℝ) ∈ gLine '' Set.Icc (14 : ℝ) (29 / 2) :=
    intermediate_value_Icc hle0 hcont0 ⟨le_of_lt hneg0, le_of_lt hpos0⟩
  obtain ⟨r1, hIcc0, hz0⟩ := hmem0
  have hri_lo0 : (14 : ℝ) < r1 := by
    rcases lt_or_eq_of_le hIcc0.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz0; rw [hz0] at hneg0; exact lt_irrefl 0 hneg0
  have hri_hi0 : r1 < ((29 / 2) : ℝ) := by
    rcases lt_or_eq_of_le hIcc0.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz0; rw [hz0] at hpos0; exact lt_irrefl 0 hpos0
  have hLam0 : completedRiemannZeta (1 / 2 + (r1 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz0]; simp
  -- sign-change subinterval [21, (43 / 2)]: root r2
  have hle1 : (21 : ℝ) ≤ (43 / 2) := by norm_num
  have hcont1 : ContinuousOn gLine (Set.Icc (21 : ℝ) (43 / 2)) :=
    gLine_continuous.continuousOn
  have he_neg1 : gLine (43 / 2) ≤ (-(14423352346132175721092019155338722797520943329041583503878160878595501167387150060661720462584489 / 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656)) := henc23
  have hneg1 : gLine (43 / 2) < 0 := by linarith [he_neg1]
  have he_pos1 : (8269572685861737265745636426276617573078736670612006593514409701930429424083354072348482068599609 / 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248) ≤ gLine 21 := henc22
  have hpos1 : (0 : ℝ) < gLine 21 := by linarith [he_pos1]
  have hmem1 : (0 : ℝ) ∈ gLine '' Set.Icc (21 : ℝ) (43 / 2) :=
    intermediate_value_Icc' hle1 hcont1 ⟨le_of_lt hneg1, le_of_lt hpos1⟩
  obtain ⟨r2, hIcc1, hz1⟩ := hmem1
  have hri_lo1 : (21 : ℝ) < r2 := by
    rcases lt_or_eq_of_le hIcc1.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz1; rw [hz1] at hpos1; exact lt_irrefl 0 hpos1
  have hri_hi1 : r2 < ((43 / 2) : ℝ) := by
    rcases lt_or_eq_of_le hIcc1.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz1; rw [hz1] at hneg1; exact lt_irrefl 0 hneg1
  have hLam1 : completedRiemannZeta (1 / 2 + (r2 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz1]; simp
  -- sign-change subinterval [25, (51 / 2)]: root r3
  have hle2 : (25 : ℝ) ≤ (51 / 2) := by norm_num
  have hcont2 : ContinuousOn gLine (Set.Icc (25 : ℝ) (51 / 2)) :=
    gLine_continuous.continuousOn
  have he_neg2 : gLine 25 ≤ (-(12981845829014324267080217854140594645728590894119209328480022621435772592901655587876085410796295 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872)) := henc30
  have hneg2 : gLine 25 < 0 := by linarith [he_neg2]
  have he_pos2 : (6426463925131225995131591435275196951708251545367651003606072414446537691714308122961887169144729 / 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248) ≤ gLine (51 / 2) := henc31
  have hpos2 : (0 : ℝ) < gLine (51 / 2) := by linarith [he_pos2]
  have hmem2 : (0 : ℝ) ∈ gLine '' Set.Icc (25 : ℝ) (51 / 2) :=
    intermediate_value_Icc hle2 hcont2 ⟨le_of_lt hneg2, le_of_lt hpos2⟩
  obtain ⟨r3, hIcc2, hz2⟩ := hmem2
  have hri_lo2 : (25 : ℝ) < r3 := by
    rcases lt_or_eq_of_le hIcc2.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz2; rw [hz2] at hneg2; exact lt_irrefl 0 hneg2
  have hri_hi2 : r3 < ((51 / 2) : ℝ) := by
    rcases lt_or_eq_of_le hIcc2.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz2; rw [hz2] at hpos2; exact lt_irrefl 0 hpos2
  have hLam2 : completedRiemannZeta (1 / 2 + (r3 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz2]; simp
  -- sign-change subinterval [30, (61 / 2)]: root r4
  have hle3 : (30 : ℝ) ≤ (61 / 2) := by norm_num
  have hcont3 : ContinuousOn gLine (Set.Icc (30 : ℝ) (61 / 2)) :=
    gLine_continuous.continuousOn
  have he_neg3 : gLine (61 / 2) ≤ (-(1063185649582606514786425224501146226770241288656632341722042262646404797195790747549871321110301 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872)) := henc41
  have hneg3 : gLine (61 / 2) < 0 := by linarith [he_neg3]
  have he_pos3 : (2448429418443069137831064390533583129598947878053442658519996320245205028633451654805415303761583 / 73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968) ≤ gLine 30 := henc40
  have hpos3 : (0 : ℝ) < gLine 30 := by linarith [he_pos3]
  have hmem3 : (0 : ℝ) ∈ gLine '' Set.Icc (30 : ℝ) (61 / 2) :=
    intermediate_value_Icc' hle3 hcont3 ⟨le_of_lt hneg3, le_of_lt hpos3⟩
  obtain ⟨r4, hIcc3, hz3⟩ := hmem3
  have hri_lo3 : (30 : ℝ) < r4 := by
    rcases lt_or_eq_of_le hIcc3.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz3; rw [hz3] at hpos3; exact lt_irrefl 0 hpos3
  have hri_hi3 : r4 < ((61 / 2) : ℝ) := by
    rcases lt_or_eq_of_le hIcc3.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz3; rw [hz3] at hneg3; exact lt_irrefl 0 hneg3
  have hLam3 : completedRiemannZeta (1 / 2 + (r4 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz3]; simp
  -- sign-change subinterval [(65 / 2), 33]: root r5
  have hle4 : ((65 / 2) : ℝ) ≤ 33 := by norm_num
  have hcont4 : ContinuousOn gLine (Set.Icc ((65 / 2) : ℝ) 33) :=
    gLine_continuous.continuousOn
  have he_neg4 : gLine (65 / 2) ≤ (-(18803692014841497986507197754909735206420974618350328439671339541039560960699763220806714339397681 / 4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952)) := henc45
  have hneg4 : gLine (65 / 2) < 0 := by linarith [he_neg4]
  have he_pos4 : (4441230828274178839190258324823673937214981662201877851657117694506058186701334669614029524082949 / 9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904) ≤ gLine 33 := henc46
  have hpos4 : (0 : ℝ) < gLine 33 := by linarith [he_pos4]
  have hmem4 : (0 : ℝ) ∈ gLine '' Set.Icc ((65 / 2) : ℝ) 33 :=
    intermediate_value_Icc hle4 hcont4 ⟨le_of_lt hneg4, le_of_lt hpos4⟩
  obtain ⟨r5, hIcc4, hz4⟩ := hmem4
  have hri_lo4 : ((65 / 2) : ℝ) < r5 := by
    rcases lt_or_eq_of_le hIcc4.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz4; rw [hz4] at hneg4; exact lt_irrefl 0 hneg4
  have hri_hi4 : r5 < (33 : ℝ) := by
    rcases lt_or_eq_of_le hIcc4.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz4; rw [hz4] at hpos4; exact lt_irrefl 0 hpos4
  have hLam4 : completedRiemannZeta (1 / 2 + (r5 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz4]; simp
  have hgap0 : ((29 / 2) : ℝ) ≤ 21 := by norm_num
  have hgap1 : ((43 / 2) : ℝ) ≤ 25 := by norm_num
  have hgap2 : ((51 / 2) : ℝ) ≤ 30 := by norm_num
  have hgap3 : ((61 / 2) : ℝ) ≤ (65 / 2) := by norm_num
  exact ⟨r1, r2, r3, r4, r5, ⟨by linarith [hri_lo0], by linarith [hri_hi0, hgap0, hri_lo1], by linarith [hri_hi1, hgap1, hri_lo2], by linarith [hri_hi2, hgap2, hri_lo3], by linarith [hri_hi3, hgap3, hri_lo4], by linarith [hri_hi4]⟩, ⟨hLam0, hLam1, hLam2, hLam3, hLam4⟩⟩
example : gLine 14 ≤ (-(73514097015932122112492589522271229502816984469312927938540724795094269239212512177602688194782951 / 35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416)) → (2164343974256490366469119739937955650606711627583237028976624988105895516706199125783653140285231 / 559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944) ≤ gLine (29 / 2) → (8269572685861737265745636426276617573078736670612006593514409701930429424083354072348482068599609 / 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248) ≤ gLine 21 → gLine (43 / 2) ≤ (-(14423352346132175721092019155338722797520943329041583503878160878595501167387150060661720462584489 / 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656)) → gLine 25 ≤ (-(12981845829014324267080217854140594645728590894119209328480022621435772592901655587876085410796295 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872)) → (6426463925131225995131591435275196951708251545367651003606072414446537691714308122961887169144729 / 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248) ≤ gLine (51 / 2) → (2448429418443069137831064390533583129598947878053442658519996320245205028633451654805415303761583 / 73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968) ≤ gLine 30 → gLine (61 / 2) ≤ (-(1063185649582606514786425224501146226770241288656632341722042262646404797195790747549871321110301 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872)) → gLine (65 / 2) ≤ (-(18803692014841497986507197754909735206420974618350328439671339541039560960699763220806714339397681 / 4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952)) → (4441230828274178839190258324823673937214981662201877851657117694506058186701334669614029524082949 / 9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904) ≤ gLine 33 → ∃ x1 x2 x3 x4 x5 : ℝ, (10 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 ≤ 35) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧ completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0) := lambda_five_zeros_10_35

end XiLineZeros
