import ArctanTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
open Real
namespace ForgePhi15Terms
set_option maxHeartbeats 4000000

theorem pterm_0 :
    (Real.pi/2 - 2701/81000 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(0:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(0:ℝ))) ≤ (Real.pi/2 - 2699/81000 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (1/30) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (1/30) 1 = (1/30 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (1/30) = Real.pi/2 - Real.arctan (30/1) := by
    have := Real.arctan_inv_of_pos (x := (30/1:ℝ)) (by norm_num)
    rwa [show ((30/1:ℝ))⁻¹ = 1/30 by norm_num] at this
  rw [hrefl] at h
  rw [show ((15/2)/(1/4+(0:ℝ))) = 30/1 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_1 :
    (Real.pi/2 - 6421/38880 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(1:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(1:ℝ))) ≤ (Real.pi/2 - 6419/38880 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (1/6) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (1/6) 2 = (107/648 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (1/6) = Real.pi/2 - Real.arctan (6/1) := by
    have := Real.arctan_inv_of_pos (x := (6/1:ℝ)) (by norm_num)
    rwa [show ((6/1:ℝ))⁻¹ = 1/6 by norm_num] at this
  rw [hrefl] at h
  rw [show ((15/2)/(1/4+(1:ℝ))) = 6/1 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_2 :
    (Real.pi/2 - 20406207/70000000 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(2:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(2:ℝ))) ≤ (Real.pi/2 - 20401833/70000000 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (3/10) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (3/10) 3 = (145743/500000 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (3/10) = Real.pi/2 - Real.arctan (10/3) := by
    have := Real.arctan_inv_of_pos (x := (10/3:ℝ)) (by norm_num)
    rwa [show ((10/3:ℝ))⁻¹ = 3/10 by norm_num] at this
  rw [hrefl] at h
  rw [show ((15/2)/(1/4+(2:ℝ))) = 10/3 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_3 :
    (Real.pi/2 - 507067411865911/1240029000000000 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(3:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(3:ℝ))) ≤ (Real.pi/2 - 506918948874689/1240029000000000 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (13/30) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (13/30) 4 = (62591750663/153090000000 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (13/30) = Real.pi/2 - Real.arctan (30/13) := by
    have := Real.arctan_inv_of_pos (x := (30/13:ℝ)) (by norm_num)
    rwa [show ((30/13:ℝ))⁻¹ = 13/30 by norm_num] at this
  rw [hrefl] at h
  rw [show ((15/2)/(1/4+(3:ℝ))) = 30/13 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_4 :
    (Real.pi/2 - 8227901420735862344449/15959173230000000000000 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(4:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(4:ℝ))) ≤ (Real.pi/2 - 8226376115718794830151/15959173230000000000000 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (17/30) (by norm_num) 6
  have hps : ArctanTaylor.atanPS (17/30) 6 = (703174253694643469/1364031900000000000 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (17/30) = Real.pi/2 - Real.arctan (30/17) := by
    have := Real.arctan_inv_of_pos (x := (30/17:ℝ)) (by norm_num)
    rwa [show ((30/17:ℝ))⁻¹ = 17/30 by norm_num] at this
  rw [hrefl] at h
  rw [show ((15/2)/(1/4+(4:ℝ))) = 30/17 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_5 :
    (Real.pi/2 - 2539216286231660491910797/4157010000000000000000000 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(5:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(5:ℝ))) ≤ (Real.pi/2 - 2538717493376138933919403/4157010000000000000000000 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (7/10) (by norm_num) 9
  have hps : ArctanTaylor.atanPS (7/10) 9 = (1336298363054684059429/2187900000000000000000 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (7/10) = Real.pi/2 - Real.arctan (10/7) := by
    have := Real.arctan_inv_of_pos (x := (10/7:ℝ)) (by norm_num)
    rwa [show ((10/7:ℝ))⁻¹ = 7/10 by norm_num] at this
  rw [hrefl] at h
  rw [show ((15/2)/(1/4+(5:ℝ))) = 10/7 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_6 :
    (Real.pi/2 - 665389785449606502022893944166791965/957715783793651987641867290707755008 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(6:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(6:ℝ))) ≤ (Real.pi/2 - 665248280516247400608213463209760715/957715783793651987641867290707755008 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (5/6) (by norm_num) 16
  have hps : ArctanTaylor.atanPS (5/6) 16 = (6160361416508582882551423182298855/8867738738830110996683956395442176 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (5/6) = Real.pi/2 - Real.arctan (6/5) := by
    have := Real.arctan_inv_of_pos (x := (6/5:ℝ)) (by norm_num)
    rwa [show ((6/5:ℝ))⁻¹ = 5/6 by norm_num] at this
  rw [hrefl] at h
  rw [show ((15/2)/(1/4+(6:ℝ))) = 6/5 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_7 :
    (Real.pi/4 + 10442/616137 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(7:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(7:ℝ))) ≤ (Real.pi/4 + 10444/616137 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (1/59) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (1/59) 1 = (1/59 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hadd : Real.arctan 1 + Real.arctan (1/59) = Real.arctan (30/29) := by
    rw [Real.arctan_add (by norm_num)]; norm_num
  have hval : Real.arctan (30/29) = Real.pi/4 + Real.arctan (1/59) := by
    rw [← hadd, Real.arctan_one]
  rw [show ((15/2)/(1/4+(7:ℝ))) = 30/29 by norm_num, hval]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_8 :
    (Real.pi/4 - 1324/27783 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(8:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(8:ℝ))) ≤ (Real.pi/4 - 1322/27783 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (1/21) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (1/21) 1 = (1/21 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hadd : Real.arctan 1 + Real.arctan (-1/21) = Real.arctan (10/11) := by
    rw [Real.arctan_add (by norm_num)]; norm_num
  have hval : Real.arctan (10/11) = Real.pi/4 - Real.arctan (1/21) := by
    rw [← hadd, Real.arctan_one, show (-1/21:ℝ) = -(1/21) by norm_num, Real.arctan_neg]; ring
  rw [show ((15/2)/(1/4+(8:ℝ))) = 10/11 by norm_num, hval]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_9 :
    (441436638709251483113578019849450155480388691207637830/648055844510834701572981187605645931221217899401108557 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(9:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(9:ℝ))) ≤ (441538711694954915018139419849450155480388691207637830/648055844510834701572981187605645931221217899401108557 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/37) (by norm_num) 14
  have hps : ArctanTaylor.atanPS (30/37) 14 = (11120316243976302840378295757019978224235880486830/16323413629652520127275917170994330904038132525657 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(9:ℝ))) = 30/37 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_10 :
    (215489670110627230858647948737597720670/341192558805939178825433267955370828949 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(10:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(10:ℝ))) ≤ (1508749792943786194010535641163184044690/2388347911641574251778032875687595802643 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/41) (by norm_num) 10
  have hps : ArctanTaylor.atanPS (30/41) 10 = (897435301522360740636844521810341490/1420789953385826443651417534614869603 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(10:ℝ))) = 30/41 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_11 :
    (6459782550946/10987890768855 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(11:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(11:ℝ))) ≤ (6461094581666/10987890768855 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/3) (by norm_num) 8
  have hps : ArctanTaylor.atanPS (2/3) 8 = (126675266006/215448838605 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(11:ℝ))) = 2/3 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_12 :
    (1770669094250935849081369290/3223125661568992906564444607 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(12:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(12:ℝ))) ≤ (1770942680077735849081369290/3223125661568992906564444607 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/49) (by norm_num) 7
  have hps : ArctanTaylor.atanPS (30/49) 7 = (737528482783979945473290/1342409688283628865707807 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(12:ℝ))) = 30/49 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_13 :
    (13422029202982394149888230/26062758647532092682168973 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(13:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(13:ℝ))) ≤ (13424484460402394149888230/26062758647532092682168973 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/53) (by norm_num) 6
  have hps : ArctanTaylor.atanPS (30/53) 6 = (367589255187786350190/713715766561658752969 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(13:ℝ))) = 30/53 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_14 :
    (39109621224749930/80727749416465767 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(14:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(14:ℝ))) ≤ (39122221224749930/80727749416465767 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/19) (by norm_num) 5
  have hps : ArctanTaylor.atanPS (10/19) 5 = (9850395674830/20329324960077 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(14:ℝ))) = 10/19 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_15 :
    (1531420628337146495310/3350571656080559576897 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(15:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(15:ℝ))) ≤ (1531668634137146495310/3350571656080559576897 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/61) (by norm_num) 5
  have hps : ArctanTaylor.atanPS (30/61) 5 = (37417718385506010/81859022649838987 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(15:ℝ))) = 30/61 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_16 :
    (298351541508558/689981751704245 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(16:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(16:ℝ))) ≤ (298376937302478/689981751704245 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/13) (by norm_num) 5
  have hps : ArctanTaylor.atanPS (6/13) 5 = (160497170202/371157478055 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(16:ℝ))) = 6/13 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_17 :
    (46525156718030/113472617672169 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(17:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(17:ℝ))) ≤ (46539156718030/113472617672169 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/23) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (10/23) 4 = (29320829690/71501334387 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(17:ℝ))) = 10/23 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_18 :
    (160656816970370010/412101106957875391 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(18:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(18:ℝ))) ≤ (160687434970370010/412101106957875391 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/73) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (30/73) 4 = (30150520917690/77331789633679 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(18:ℝ))) = 30/73 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_19 :
    (35346420214889430/95151694449171437 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(19:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(19:ℝ))) ≤ (35350794214889430/95151694449171437 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/77) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (30/77) 4 = (41733892815690/112339662867971 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(19:ℝ))) = 30/77 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_20 :
    (170391783374030/480412641554181 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(20:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(20:ℝ))) ≤ (170405783374030/480412641554181 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/27) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (10/27) 4 = (25971465230/73222472421 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(20:ℝ))) = 10/27 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_21 :
    (4872747738/14361853555 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(21:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(21:ℝ))) ≤ (4875547098/14361853555 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/17) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (6/17) 3 = (2409366/7099285 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(21:ℝ))) = 6/17 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_22 :
    (100660912338810/309619344268703 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(22:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(22:ℝ))) ≤ (100704652338810/309619344268703 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/89) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/89) 3 = (1815838230/5584059449 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(22:ℝ))) = 30/89 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_23 :
    (180284746010/577764896331 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(23:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(23:ℝ))) ≤ (180344746010/577764896331 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/31) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (10/31) 3 = (26804630/85887453 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(23:ℝ))) = 10/31 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_24 :
    (169645000512090/565587991346791 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(24:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(24:ℝ))) ≤ (169688740512090/565587991346791 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/97) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/97) 3 = (2576057430/8587340257 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(24:ℝ))) = 30/97 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_25 :
    (216688594383210/750494746474907 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(25:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(25:ℝ))) ≤ (216732334383210/750494746474907 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/101) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/101) 3 = (3034863030/10510100501 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(25:ℝ))) = 30/101 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_26 :
    (24065018/86472015 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(26:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(26:ℝ))) ≤ (24068858/86472015 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/7) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (2/7) 3 = (70166/252105 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(26:ℝ))) = 2/7 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_27 :
    (343680380753610/1279627384571683 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(27:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(27:ℝ))) ≤ (343724120753610/1279627384571683 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/109) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/109) 3 = (4132675830/15386239549 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(27:ℝ))) = 30/109 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_28 :
    (427350415684890/1646823836313719 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(28:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(28:ℝ))) ≤ (427394155684890/1646823836313719 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/113) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/113) 3 = (4781359830/18424351793 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(28:ℝ))) = 30/113 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_29 :
    (241116974270/960617046753 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(29:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(29:ℝ))) ≤ (241136974270/960617046753 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/39) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (10/39) 3 = (22647410/90224199 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(29:ℝ))) = 10/39 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_30 :
    (646041566428410/2658248835082687 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(30:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(30:ℝ))) ≤ (646085306428410/2658248835082687 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/121) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/121) 3 = (6303857430/25937424601 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(30:ℝ))) = 30/121 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_31 :
    (10063555314/42724609375 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(31:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(31:ℝ))) ≤ (10064115186/42724609375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/25) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (6/25) 3 = (11501526/48828125 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(31:ℝ))) = 6/25 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_32 :
    (1304301213290/5708190833247 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(32:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(32:ℝ))) ≤ (1304361213290/5708190833247 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/43) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (10/43) 3 = (100775030/441025329 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(32:ℝ))) = 10/43 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_33 :
    (1143196343648490/5152992694858939 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(33:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(33:ℝ))) ≤ (1143240083648490/5152992694858939 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/133) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/133) 3 = (9232680630/41615795893 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(33:ℝ))) = 30/133 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_34 :
    (1366913116264890/6340770144334031 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(34:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(34:ℝ))) ≤ (1366956856264890/6340770144334031 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/137) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (30/137) 3 = (10404199830/48261724457 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(34:ℝ))) = 30/137 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_35 :
    (144121430/688035021 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(35:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(35:ℝ))) ≤ (144241430/688035021 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/47) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/47) 2 = (65270/311469 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(35:ℝ))) = 10/47 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_36 :
    (20907894/102555745 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(36:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(36:ℝ))) ≤ (20923446/102555745 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/29) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/29) 2 = (4974/24389 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(36:ℝ))) = 6/29 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_37 :
    (14581863030/73439775749 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(37:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(37:ℝ))) ≤ (14591583030/73439775749 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/149) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/149) 2 = (657030/3307949 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(37:ℝ))) = 30/149 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_38 :
    (66765010/345025251 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(38:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(38:ℝ))) ≤ (66805010/345025251 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/51) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/51) 2 = (77030/397953 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(38:ℝ))) = 10/51 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_39 :
    (18000495030/95388992557 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(39:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(39:ℝ))) ≤ (18010215030/95388992557 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/157) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/157) 2 = (730470/3869893 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(39:ℝ))) = 30/157 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_40 :
    (19918798230/108175616801 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(40:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(40:ℝ))) ≤ (19928518230/108175616801 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/161) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/161) 2 = (768630/4173281 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(40:ℝ))) = 30/161 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_41 :
    (434294/2415765 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(41:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(41:ℝ))) ≤ (434486/2415765 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/11) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (2/11) 2 = (718/3993 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(41:ℝ))) = 2/11 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_42 :
    (24210012630/137858491849 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(42:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(42:ℝ))) ≤ (24219732630/137858491849 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/169) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/169) 2 = (847830/4826809 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(42:ℝ))) = 30/169 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_43 :
    (26598130230/154963892093 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(43:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(43:ℝ))) ≤ (26607850230/154963892093 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/173) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/173) 2 = (888870/5177717 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(43:ℝ))) = 30/173 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_44 :
    (359979830/2144772897 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(44:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(44:ℝ))) ≤ (360099830/2144772897 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/59) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/59) 2 = (103430/616137 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(44:ℝ))) = 10/59 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_45 :
    (31898784630/194264244901 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(45:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(45:ℝ))) ≤ (31908504630/194264244901 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/181) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/181) 2 = (973830/5929741 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(45:ℝ))) = 30/181 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_46 :
    (55724214/346719785 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(46:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(46:ℝ))) ≤ (55739766/346719785 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/37) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/37) 2 = (8142/50653 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(46:ℝ))) = 6/37 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_47 :
    (156186610/992436543 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(47:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(47:ℝ))) ≤ (156226610/992436543 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/63) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/63) 2 = (118070/750141 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(47:ℝ))) = 10/63 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_48 :
    (41284539030/267785184193 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(48:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(48:ℝ))) ≤ (41294259030/267785184193 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/193) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/193) 2 = (1108470/7189057 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(48:ℝ))) = 30/193 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_49 :
    (44830013430/296709280757 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(49:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(49:ℝ))) ≤ (44839733430/296709280757 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/197) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/197) 2 = (1155270/7645373 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(49:ℝ))) = 30/197 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_50 :
    (599984630/4050375321 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(50:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(50:ℝ))) ≤ (600104630/4050375321 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/67) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/67) 2 = (133670/902289 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(50:ℝ))) = 10/67 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_51 :
    (84159894/579281005 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(51:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(51:ℝ))) ≤ (84175446/579281005 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/41) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/41) 2 = (10014/68921 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(51:ℝ))) = 6/41 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_52 :
    (56842903830/398778220049 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(52:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(52:ℝ))) ≤ (56852623830/398778220049 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/209) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/209) 2 = (1301430/9129329 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(52:ℝ))) = 30/209 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_53 :
    (757249430/5412688053 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(53:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(53:ℝ))) ≤ (757369430/5412688053 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/71) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/71) 2 = (150230/1073733 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(53:ℝ))) = 10/71 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_54 :
    (66092556630/481170140857 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(54:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(54:ℝ))) ≤ (66102276630/481170140857 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/217) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/217) 2 = (1403670/10218313 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(54:ℝ))) = 30/217 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_55 :
    (71118869430/527182965101 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(55:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(55:ℝ))) ≤ (71128589430/527182965101 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/221) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/221) 2 = (1456230/10793861 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(55:ℝ))) = 30/221 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_56 :
    (503218/3796875 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(56:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(56:ℝ))) ≤ (503282/3796875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/15) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (2/15) 2 = (1342/10125 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(56:ℝ))) = 2/15 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_57 :
    (82024925430/629763392149 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(57:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(57:ℝ))) ≤ (82034645430/629763392149 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/229) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/229) 2 = (1564230/12008989 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(57:ℝ))) = 30/229 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_58 :
    (87925404630/686719856393 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(58:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(58:ℝ))) ≤ (87935124630/686719856393 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/233) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/233) 2 = (1619670/12649337 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(58:ℝ))) = 30/233 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_59 :
    (1162201430/9231169197 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(59:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(59:ℝ))) ≤ (1162321430/9231169197 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/79) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/79) 2 = (186230/1479117 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(59:ℝ))) = 10/79 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_60 :
    (100674487830/812990017201 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(60:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(60:ℝ))) ≤ (100684207830/812990017201 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/241) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/241) 2 = (1733430/13997521 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(60:ℝ))) = 30/241 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_61 :
    (172071894/1412376245 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(61:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(61:ℝ))) ≤ (172087446/1412376245 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/49) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/49) 2 = (14334/117649 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(61:ℝ))) = 6/49 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_62 :
    (1416800630/11817121929 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(62:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(62:ℝ))) ≤ (1416920630/11817121929 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/83) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/83) 2 = (205670/1715361 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(62:ℝ))) = 10/83 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_63 :
    (122333621430/1036579476493 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(63:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(63:ℝ))) ≤ (122343341430/1036579476493 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/253) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/253) 2 = (1911270/16194277 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(63:ℝ))) = 30/253 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_64 :
    (130274811030/1121154893057 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(64:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(64:ℝ))) ≤ (130284531030/1121154893057 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/257) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/257) 2 = (1972470/16974593 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(64:ℝ))) = 30/257 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_65 :
    (570354610/4984209207 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(65:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(65:ℝ))) ≤ (570394610/4984209207 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/87) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/87) 2 = (226070/1975509 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(65:ℝ))) = 10/87 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_66 :
    (235695414/2090977465 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(66:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(66:ℝ))) ≤ (235710966/2090977465 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/53) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/53) 2 = (16782/148877 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(66:ℝ))) = 6/53 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_67 :
    (156427320630/1408514752349 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(67:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(67:ℝ))) ≤ (156437040630/1408514752349 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/269) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/269) 2 = (2161830/19465109 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(67:ℝ))) = 30/269 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_68 :
    (2048907830/18720964353 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(68:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(68:ℝ))) ≤ (2049027830/18720964353 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/91) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/91) 2 = (247430/2260713 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(68:ℝ))) = 10/91 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_69 :
    (175924762230/1630793025157 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(69:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(69:ℝ))) ≤ (175934482230/1630793025157 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/277) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/277) 2 = (2292870/21253933 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(69:ℝ))) = 30/277 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_70 :
    (186329676630/1751989905401 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(70:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(70:ℝ))) ≤ (186339396630/1751989905401 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/281) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/281) 2 = (2359830/22188041 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(70:ℝ))) = 30/281 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_71 :
    (3895094/37141485 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(71:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(71:ℝ))) ≤ (3895286/37141485 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/19) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (2/19) 2 = (2158/20577 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(71:ℝ))) = 2/19 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_72 :
    (208516174230/2015993900449 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(72:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(72:ℝ))) ≤ (208525894230/2015993900449 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/289) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/289) 2 = (2496630/24137569 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(72:ℝ))) = 30/289 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_73 :
    (220324023030/2159424884693 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(73:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(73:ℝ))) ≤ (220333743030/2159424884693 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/293) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/293) 2 = (2566470/25153757 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(73:ℝ))) = 30/293 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_74 :
    (957309010/9509900499 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(74:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(74:ℝ))) ≤ (957349010/9509900499 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/99) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/99) 2 = (293030/2910897 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(74:ℝ))) = 10/99 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_75 :
    (245435967030/2470770901501 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(75:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(75:ℝ))) ≤ (245445687030/2470770901501 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/301) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/301) 2 = (2709030/27270901 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(75:ℝ))) = 30/301 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_76 :
    (414027894/4222981505 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(76:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(76:ℝ))) ≤ (414043446/4222981505 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/61) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/61) 2 = (22254/226981 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(76:ℝ))) = 6/61 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_77 :
    (3365857430/34778222229 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(77:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(77:ℝ))) ≤ (3365977430/34778222229 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/103) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/103) 2 = (317270/3278181 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(77:ℝ))) = 10/103 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_78 :
    (287051167830/3004150512793 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(78:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(78:ℝ))) ≤ (287060887830/3004150512793 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/313) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/313) 2 = (2930070/30664297 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(78:ℝ))) = 30/313 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_79 :
    (302031912630/3201078401357 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(79:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(79:ℝ))) ≤ (302041632630/3201078401357 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/317) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/317) 2 = (3005670/31855013 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(79:ℝ))) = 30/317 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_80 :
    (3920879030/42076551921 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(80:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(80:ℝ))) ≤ (3920999030/42076551921 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/107) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/107) 2 = (342470/3675129 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(80:ℝ))) = 10/107 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_81 :
    (533989974/5801453125 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(81:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(81:ℝ))) ≤ (534005526/5801453125 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/65) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/65) 2 = (25278/274625 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(81:ℝ))) = 6/65 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_82 :
    (350504393430/3854601532649 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(82:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(82:ℝ))) ≤ (350514113430/3854601532649 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/329) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/329) 2 = (3238230/35611289 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(82:ℝ))) = 30/329 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_83 :
    (1513943410/16850581551 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(83:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(83:ℝ))) ≤ (1513983410/16850581551 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/111) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/111) 2 = (368630/4102893 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(83:ℝ))) = 10/111 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_84 :
    (385910551830/4346598285457 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(84:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(84:ℝ))) ≤ (385920271830/4346598285457 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/337) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/337) 2 = (3398070/38272753 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(84:ℝ))) = 30/337 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_85 :
    (404586739830/4610753397701 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(85:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(85:ℝ))) ≤ (404596459830/4610753397701 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/341) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/341) 2 = (3479430/39651821 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(85:ℝ))) = 30/341 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_86 :
    (8373974/96545145 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(86:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(86:ℝ))) ≤ (8374166/96545145 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/23) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (2/23) 2 = (3166/36501 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(86:ℝ))) = 2/23 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_87 :
    (443963439030/5177583776749 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(87:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(87:ℝ))) ≤ (443973159030/5177583776749 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/349) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/349) 2 = (3645030/42508549 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(87:ℝ))) = 30/349 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_88 :
    (464695745430/5481173216993 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(88:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(88:ℝ))) ≤ (464705465430/5481173216993 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/353) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/353) 2 = (3729270/43986977 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(88:ℝ))) = 30/353 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_89 :
    (6001796630/71590609797 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(89:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(89:ℝ))) ≤ (6001916630/71590609797 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/119) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/119) 2 = (423830/5055477 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(89:ℝ))) = 10/119 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_90 :
    (508329142230/6131066257801 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(90:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(90:ℝ))) ≤ (508338862230/6131066257801 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/361) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/361) 2 = (3900630/47045881 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(90:ℝ))) = 30/361 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_91 :
    (850021014/10365357965 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(91:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(91:ℝ))) ≤ (850036566/10365357965 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/73) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/73) 2 = (31902/389017 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(91:ℝ))) = 6/73 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_92 :
    (2283803410/28153056843 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(92:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(92:ℝ))) ≤ (2283843410/28153056843 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/123) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/123) 2 = (452870/5582601 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(92:ℝ))) = 10/123 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_93 :
    (579449338230/7220115733093 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(93:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(93:ℝ))) ≤ (579459058230/7220115733093 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/373) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/373) 2 = (4164870/51895117 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(93:ℝ))) = 30/373 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_94 :
    (604735558230/7615646045657 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(94:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(94:ℝ))) ≤ (604745278230/7615646045657 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/377) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/377) 2 = (4254870/53582633 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(94:ℝ))) = 30/377 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_95 :
    (7788150230/99115108221 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(95:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(95:ℝ))) ≤ (7788270230/99115108221 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/127) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/127) 2 = (482870/6145149 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(95:ℝ))) = 10/127 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_96 :
    (1052449014/13533920785 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(96:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(96:ℝ))) ≤ (1052464566/13533920785 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/77) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/77) 2 = (35502/456533 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(96:ℝ))) = 6/77 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_97 :
    (685574602230/8907339520949 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(97:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(97:ℝ))) ≤ (685584322230/8907339520949 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/389) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/389) 2 = (4530630/58863869 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(97:ℝ))) = 30/389 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_98 :
    (8817776630/115738468953 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(98:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(98:ℝ))) ≤ (8817896630/115738468953 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/131) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/131) 2 = (513830/6744273 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(98:ℝ))) = 10/131 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_99 :
    (743794565430/9861716961757 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(99:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(99:ℝ))) ≤ (743804285430/9861716961757 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/397) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/397) 2 = (4719270/62570773 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(99:ℝ))) = 30/397 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_100 :
    (774256779030/10368641602001 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(100:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(100:ℝ))) ≤ (774266499030/10368641602001 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/401) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/401) 2 = (4815030/64481201 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(100:ℝ))) = 30/401 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_101 :
    (5304658/71744535 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(101:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(101:ℝ))) ≤ (5304722/71744535 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/27) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (2/27) 2 = (4366/59049 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(101:ℝ))) = 2/27 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_102 :
    (837977599830/11445019581049 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(102:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(102:ℝ))) ≤ (837987319830/11445019581049 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/409) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/409) 2 = (5009430/68417929 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(102:ℝ))) = 30/409 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_103 :
    (871273531830/12015732693293 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(103:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(103:ℝ))) ≤ (871283251830/12015732693293 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/413) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/413) 2 = (5108070/70444997 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(103:ℝ))) = 30/413 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_104 :
    (11179650230/155666534097 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(104:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(104:ℝ))) ≤ (11179770230/155666534097 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/139) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/139) 2 = (578630/8056857 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(104:ℝ))) = 10/139 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_105 :
    (940831133430/13225450646101 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(105:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(105:ℝ))) ≤ (940840853430/13225450646101 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/421) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/421) 2 = (5308230/74618461 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(105:ℝ))) = 30/421 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_106 :
    (1563409974/22185265625 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(106:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(106:ℝ))) ≤ (1563425526/22185265625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/85) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/85) 2 = (43278/614125 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(106:ℝ))) = 6/85 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_107 :
    (12524339030/179391326829 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(107:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(107:ℝ))) ≤ (12524459030/179391326829 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/143) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/143) 2 = (612470/8772621 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(107:ℝ))) = 10/143 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_108 :
    (1052871492630/15220870177393 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(108:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(108:ℝ))) ≤ (1052881212630/15220870177393 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/433) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/433) 2 = (5615670/81182737 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(108:ℝ))) = 30/433 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_109 :
    (1092351187830/15937022465957 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(109:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(109:ℝ))) ≤ (1092360907830/15937022465957 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/437) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (30/437) 2 = (5720070/83453453 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(109:ℝ))) = 30/437 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_110 :
    (4662265810/68641485507 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(110:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(110:ℝ))) ≤ (4662305810/68641485507 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/147) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (10/147) 2 = (647270/9529569 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(110:ℝ))) = 10/147 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_111 :
    (1879407894/27920297245 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(111:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(111:ℝ))) ≤ (1879423446/27920297245 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/89) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (6/89) 2 = (47454/704969 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(111:ℝ))) = 6/89 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_112 :
    (6039030/90518849 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(112:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(112:ℝ))) ≤ (6057030/90518849 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/449) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/449) 1 = (30/449 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(112:ℝ))) = 30/449 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_113 :
    (683030/10328853 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(113:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(113:ℝ))) ≤ (685030/10328853 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/151) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/151) 1 = (10/151 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(113:ℝ))) = 10/151 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_114 :
    (6256470/95443993 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(114:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(114:ℝ))) ≤ (6274470/95443993 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/457) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/457) 1 = (30/457 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(114:ℝ))) = 30/457 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_115 :
    (6366630/97972181 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(115:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(115:ℝ))) ≤ (6384630/97972181 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/461) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/461) 1 = (30/461 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(115:ℝ))) = 30/461 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_116 :
    (5758/89373 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(116:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(116:ℝ))) ≤ (5774/89373 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/31) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (2/31) 1 = (2/31 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(116:ℝ))) = 2/31 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_117 :
    (6589830/103161709 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(117:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(117:ℝ))) ≤ (6607830/103161709 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/469) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/469) 1 = (30/469 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(117:ℝ))) = 30/469 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_118 :
    (6702870/105823817 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(118:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(118:ℝ))) ≤ (6720870/105823817 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/473) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/473) 1 = (30/473 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(118:ℝ))) = 30/473 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_119 :
    (757430/12059037 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(119:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(119:ℝ))) ≤ (759430/12059037 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/159) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/159) 1 = (10/159 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(119:ℝ))) = 10/159 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_120 :
    (6931830/111284641 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(120:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(120:ℝ))) ≤ (6949830/111284641 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/481) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/481) 1 = (30/481 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(120:ℝ))) = 30/481 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_121 :
    (56382/912673 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(121:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(121:ℝ))) ≤ (56526/912673 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/97) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/97) 1 = (6/97 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(121:ℝ))) = 6/97 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_122 :
    (796070/12992241 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(122:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(122:ℝ))) ≤ (798070/12992241 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/163) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/163) 1 = (10/163 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(122:ℝ))) = 10/163 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_123 :
    (7282470/119823157 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(123:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(123:ℝ))) ≤ (7300470/119823157 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/493) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/493) 1 = (30/493 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(123:ℝ))) = 30/493 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_124 :
    (7401270/122763473 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(124:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(124:ℝ))) ≤ (7419270/122763473 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/497) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/497) 1 = (30/497 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(124:ℝ))) = 30/497 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_125 :
    (835670/13972389 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(125:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(125:ℝ))) ≤ (837670/13972389 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/167) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/167) 1 = (10/167 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(125:ℝ))) = 10/167 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_126 :
    (61134/1030301 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(126:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(126:ℝ))) ≤ (61278/1030301 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/101) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/101) 1 = (6/101 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(126:ℝ))) = 6/101 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_127 :
    (7763430/131872229 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(127:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(127:ℝ))) ≤ (7781430/131872229 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/509) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/509) 1 = (30/509 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(127:ℝ))) = 30/509 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_128 :
    (876230/15000633 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(128:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(128:ℝ))) ≤ (878230/15000633 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/171) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/171) 1 = (10/171 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(128:ℝ))) = 10/171 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_129 :
    (8009670/138188413 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(129:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(129:ℝ))) ≤ (8027670/138188413 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/517) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/517) 1 = (30/517 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(129:ℝ))) = 30/517 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_130 :
    (8134230/141420761 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(130:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(130:ℝ))) ≤ (8152230/141420761 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/521) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/521) 1 = (30/521 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(130:ℝ))) = 30/521 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_131 :
    (7342/128625 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(131:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(131:ℝ))) ≤ (7358/128625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/35) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (2/35) 1 = (2/35 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(131:ℝ))) = 2/35 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_132 :
    (8386230/148035889 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(132:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(132:ℝ))) ≤ (8404230/148035889 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/529) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/529) 1 = (30/529 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(132:ℝ))) = 30/529 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_133 :
    (8513670/151419437 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(133:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(133:ℝ))) ≤ (8531670/151419437 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/533) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/533) 1 = (30/533 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(133:ℝ))) = 30/533 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_134 :
    (960230/17206017 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(134:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(134:ℝ))) ≤ (962230/17206017 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/179) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/179) 1 = (10/179 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(134:ℝ))) = 10/179 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_135 :
    (8771430/158340421 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(135:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(135:ℝ))) ≤ (8789430/158340421 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/541) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/541) 1 = (30/541 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(135:ℝ))) = 30/541 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_136 :
    (71214/1295029 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(136:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(136:ℝ))) ≤ (71358/1295029 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/109) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/109) 1 = (6/109 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(136:ℝ))) = 6/109 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_137 :
    (1003670/18385461 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(137:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(137:ℝ))) ≤ (1005670/18385461 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/183) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/183) 1 = (10/183 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(137:ℝ))) = 10/183 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_138 :
    (9165270/169112377 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(138:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(138:ℝ))) ≤ (9183270/169112377 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/553) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/553) 1 = (30/553 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(138:ℝ))) = 30/553 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_139 :
    (9298470/172808693 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(139:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(139:ℝ))) ≤ (9316470/172808693 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/557) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/557) 1 = (30/557 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(139:ℝ))) = 30/557 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_140 :
    (1048070/19617609 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(140:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(140:ℝ))) ≤ (1050070/19617609 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/187) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/187) 1 = (10/187 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(140:ℝ))) = 10/187 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_141 :
    (76542/1442897 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(141:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(141:ℝ))) ≤ (76686/1442897 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/113) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/113) 1 = (6/113 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(141:ℝ))) = 6/113 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_142 :
    (9703830/184220009 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(142:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(142:ℝ))) ≤ (9721830/184220009 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/569) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/569) 1 = (30/569 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(142:ℝ))) = 30/569 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_143 :
    (1093430/20903613 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(143:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(143:ℝ))) ≤ (1095430/20903613 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/191) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/191) 1 = (10/191 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(143:ℝ))) = 10/191 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_144 :
    (9978870/192100033 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(144:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(144:ℝ))) ≤ (9996870/192100033 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/577) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/577) 1 = (30/577 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(144:ℝ))) = 30/577 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_145 :
    (10117830/196122941 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(145:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(145:ℝ))) ≤ (10135830/196122941 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/581) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/581) 1 = (30/581 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(145:ℝ))) = 30/581 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_146 :
    (9118/177957 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(146:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(146:ℝ))) ≤ (9134/177957 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/39) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (2/39) 1 = (2/39 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(146:ℝ))) = 2/39 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_147 :
    (10398630/204336469 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(147:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(147:ℝ))) ≤ (10416630/204336469 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/589) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/589) 1 = (30/589 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(147:ℝ))) = 30/589 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_148 :
    (10540470/208527857 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(148:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(148:ℝ))) ≤ (10558470/208527857 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/593) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/593) 1 = (30/593 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(148:ℝ))) = 30/593 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_149 :
    (1187030/23641797 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(149:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(149:ℝ))) ≤ (1189030/23641797 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/199) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/199) 1 = (10/199 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(149:ℝ))) = 10/199 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_150 :
    (10827030/217081801 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(150:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(150:ℝ))) ≤ (10845030/217081801 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/601) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/601) 1 = (30/601 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(150:ℝ))) = 30/601 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_151 :
    (87774/1771561 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(151:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(151:ℝ))) ≤ (87918/1771561 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/121) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/121) 1 = (6/121 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(151:ℝ))) = 6/121 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_152 :
    (1235270/25096281 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(152:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(152:ℝ))) ≤ (1237270/25096281 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/203) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/203) 1 = (10/203 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(152:ℝ))) = 10/203 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_153 :
    (11264070/230346397 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(153:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(153:ℝ))) ≤ (11282070/230346397 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/613) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/613) 1 = (30/613 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(153:ℝ))) = 30/613 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_154 :
    (11411670/234885113 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(154:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(154:ℝ))) ≤ (11429670/234885113 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/617) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/617) 1 = (30/617 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(154:ℝ))) = 30/617 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_155 :
    (1284470/26609229 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(155:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(155:ℝ))) ≤ (1286470/26609229 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/207) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/207) 1 = (10/207 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(155:ℝ))) = 10/207 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_156 :
    (93678/1953125 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(156:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(156:ℝ))) ≤ (93822/1953125 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/125) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/125) 1 = (6/125 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(156:ℝ))) = 6/125 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_157 :
    (11860230/248858189 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(157:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(157:ℝ))) ≤ (11878230/248858189 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/629) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/629) 1 = (30/629 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(157:ℝ))) = 30/629 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_158 :
    (1334630/28181793 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(158:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(158:ℝ))) ≤ (1336630/28181793 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/211) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/211) 1 = (10/211 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(158:ℝ))) = 10/211 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_159 :
    (12164070/258474853 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(159:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(159:ℝ))) ≤ (12182070/258474853 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/637) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/637) 1 = (30/637 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(159:ℝ))) = 30/637 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_160 :
    (12317430/263374721 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(160:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(160:ℝ))) ≤ (12335430/263374721 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/641) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/641) 1 = (30/641 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(160:ℝ))) = 30/641 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_161 :
    (11086/238521 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(161:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(161:ℝ))) ≤ (11102/238521 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/43) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (2/43) 1 = (2/43 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(161:ℝ))) = 2/43 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_162 :
    (12627030/273359449 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(162:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(162:ℝ))) ≤ (12645030/273359449 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/649) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/649) 1 = (30/649 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(162:ℝ))) = 30/649 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_163 :
    (12783270/278445077 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(163:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(163:ℝ))) ≤ (12801270/278445077 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/653) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/653) 1 = (30/653 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(163:ℝ))) = 30/653 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_164 :
    (1437830/31510377 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(164:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(164:ℝ))) ≤ (1439830/31510377 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/219) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/219) 1 = (10/219 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(164:ℝ))) = 10/219 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_165 :
    (13098630/288804781 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(165:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(165:ℝ))) ≤ (13116630/288804781 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/661) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/661) 1 = (30/661 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(165:ℝ))) = 30/661 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_166 :
    (106062/2352637 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(166:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(166:ℝ))) ≤ (106206/2352637 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/133) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/133) 1 = (6/133 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(166:ℝ))) = 6/133 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_167 :
    (1490870/33268701 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(167:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(167:ℝ))) ≤ (1492870/33268701 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/223) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/223) 1 = (10/223 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(167:ℝ))) = 10/223 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_168 :
    (13578870/304821217 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(168:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(168:ℝ))) ≤ (13596870/304821217 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/673) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/673) 1 = (30/673 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(168:ℝ))) = 30/673 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_169 :
    (13740870/310288733 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(169:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(169:ℝ))) ≤ (13758870/310288733 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/677) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/677) 1 = (30/677 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(169:ℝ))) = 30/677 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_170 :
    (1544870/35091249 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(170:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(170:ℝ))) ≤ (1546870/35091249 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/227) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/227) 1 = (10/227 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(170:ℝ))) = 10/227 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_171 :
    (112542/2571353 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(171:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(171:ℝ))) ≤ (112686/2571353 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/137) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/137) 1 = (6/137 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(171:ℝ))) = 6/137 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_172 :
    (14232630/327082769 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(172:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(172:ℝ))) ≤ (14250630/327082769 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/689) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/689) 1 = (30/689 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(172:ℝ))) = 30/689 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_173 :
    (1599830/36979173 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(173:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(173:ℝ))) ≤ (1601830/36979173 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/231) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/231) 1 = (10/231 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(173:ℝ))) = 10/231 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_174 :
    (14565270/338608873 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(174:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(174:ℝ))) ≤ (14583270/338608873 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/697) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/697) 1 = (30/697 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(174:ℝ))) = 30/697 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_175 :
    (14733030/344472101 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(175:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(175:ℝ))) ≤ (14751030/344472101 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/701) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/701) 1 = (30/701 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(175:ℝ))) = 30/701 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_176 :
    (13246/311469 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(176:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(176:ℝ))) ≤ (13262/311469 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/47) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (2/47) 1 = (2/47 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(176:ℝ))) = 2/47 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_177 :
    (15071430/356400829 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(177:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(177:ℝ))) ≤ (15089430/356400829 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/709) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/709) 1 = (30/709 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(177:ℝ))) = 30/709 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_178 :
    (15242070/362467097 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(178:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(178:ℝ))) ≤ (15260070/362467097 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/713) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/713) 1 = (30/713 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(178:ℝ))) = 30/713 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_179 :
    (1712630/40955757 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(179:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(179:ℝ))) ≤ (1714630/40955757 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/239) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/239) 1 = (10/239 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(179:ℝ))) = 10/239 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_180 :
    (15586230/374805361 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(180:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(180:ℝ))) ≤ (15604230/374805361 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/721) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/721) 1 = (30/721 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(180:ℝ))) = 30/721 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_181 :
    (126078/3048625 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(181:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(181:ℝ))) ≤ (126222/3048625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/145) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/145) 1 = (6/145 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(181:ℝ))) = 6/145 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_182 :
    (1770470/43046721 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(182:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(182:ℝ))) ≤ (1772470/43046721 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/243) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/243) 1 = (10/243 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(182:ℝ))) = 10/243 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_183 :
    (16109670/393832837 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(183:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(183:ℝ))) ≤ (16127670/393832837 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/733) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/733) 1 = (30/733 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(183:ℝ))) = 30/733 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_184 :
    (16286070/400315553 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(184:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(184:ℝ))) ≤ (16304070/400315553 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/737) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/737) 1 = (30/737 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(184:ℝ))) = 30/737 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_185 :
    (1829270/45207669 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(185:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(185:ℝ))) ≤ (1831270/45207669 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/247) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/247) 1 = (10/247 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(185:ℝ))) = 10/247 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_186 :
    (133134/3307949 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(186:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(186:ℝ))) ≤ (133278/3307949 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/149) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/149) 1 = (6/149 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(186:ℝ))) = 6/149 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_187 :
    (16821030/420189749 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(187:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(187:ℝ))) ≤ (16839030/420189749 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/749) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/749) 1 = (30/749 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(187:ℝ))) = 30/749 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_188 :
    (1889030/47439753 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(188:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(188:ℝ))) ≤ (1891030/47439753 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/251) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/251) 1 = (10/251 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(188:ℝ))) = 10/251 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_189 :
    (17182470/433798093 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(189:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(189:ℝ))) ≤ (17200470/433798093 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/757) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/757) 1 = (30/757 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(189:ℝ))) = 30/757 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_190 :
    (17364630/440711081 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(190:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(190:ℝ))) ≤ (17382630/440711081 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/761) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/761) 1 = (30/761 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(190:ℝ))) = 30/761 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_191 :
    (15598/397953 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(191:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(191:ℝ))) ≤ (15614/397953 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (2/51) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (2/51) 1 = (2/51 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(191:ℝ))) = 2/51 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_192 :
    (17731830/454756609 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(192:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(192:ℝ))) ≤ (17749830/454756609 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/769) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/769) 1 = (30/769 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(192:ℝ))) = 30/769 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_193 :
    (17916870/461889917 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(193:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(193:ℝ))) ≤ (17934870/461889917 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/773) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/773) 1 = (30/773 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(193:ℝ))) = 30/773 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_194 :
    (2011430/52121937 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(194:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(194:ℝ))) ≤ (2013430/52121937 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/259) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/259) 1 = (10/259 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(194:ℝ))) = 10/259 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_195 :
    (18289830/476379541 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(195:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(195:ℝ))) ≤ (18307830/476379541 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/781) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/781) 1 = (30/781 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(195:ℝ))) = 30/781 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_196 :
    (147822/3869893 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(196:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(196:ℝ))) ≤ (147966/3869893 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (6/157) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (6/157) 1 = (6/157 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(196:ℝ))) = 6/157 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_197 :
    (2074070/54574341 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(197:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(197:ℝ))) ≤ (2076070/54574341 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/263) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/263) 1 = (10/263 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(197:ℝ))) = 10/263 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_198 :
    (18856470/498677257 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(198:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(198:ℝ))) ≤ (18874470/498677257 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/793) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/793) 1 = (30/793 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(198:ℝ))) = 30/793 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_199 :
    (19047270/506261573 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(199:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(199:ℝ))) ≤ (19065270/506261573 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (30/797) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (30/797) 1 = (30/797 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(199:ℝ))) = 30/797 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_200 :
    (2137670/57102489 : ℝ) ≤ Real.arctan ((15/2)/(1/4+(200:ℝ)))
    ∧ Real.arctan ((15/2)/(1/4+(200:ℝ))) ≤ (2139670/57102489 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (10/267) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (10/267) 1 = (10/267 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show ((15/2)/(1/4+(200:ℝ))) = 10/267 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

end ForgePhi15Terms
