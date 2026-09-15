import ArctanTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
open Real
namespace ForgePhi14Terms
set_option maxHeartbeats 4000000

theorem pterm_0 :
    (Real.pi/2 - 2353/65856 : ℝ) ≤ Real.arctan (7/(1/4+(0:ℝ)))
    ∧ Real.arctan (7/(1/4+(0:ℝ))) ≤ (Real.pi/2 - 2351/65856 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (1/28) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (1/28) 1 = (1/28 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (1/28) = Real.pi/2 - Real.arctan (28/1) := by
    have := Real.arctan_inv_of_pos (x := (28/1:ℝ)) (by norm_num)
    rwa [show ((28/1:ℝ))⁻¹ = 1/28 by norm_num] at this
  rw [hrefl] at h
  rw [show (7/(1/4+(0:ℝ))) = 28/1 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_1 :
    (Real.pi/2 - 9123715/51631104 : ℝ) ≤ Real.arctan (7/(1/4+(1:ℝ)))
    ∧ Real.arctan (7/(1/4+(1:ℝ))) ≤ (Real.pi/2 - 9119965/51631104 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (5/28) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (5/28) 2 = (11635/65856 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (5/28) = Real.pi/2 - Real.arctan (28/5) := by
    have := Real.arctan_inv_of_pos (x := (28/5:ℝ)) (by norm_num)
    rwa [show ((28/5:ℝ))⁻¹ = 5/28 by norm_num] at this
  rw [hrefl] at h
  rw [show (7/(1/4+(1:ℝ))) = 28/5 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_2 :
    (Real.pi/2 - 146915772237/472252497920 : ℝ) ≤ Real.arctan (7/(1/4+(2:ℝ)))
    ∧ Real.arctan (7/(1/4+(2:ℝ))) ≤ (Real.pi/2 - 146867942547/472252497920 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (9/28) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (9/28) 3 = (26766009/86051840 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (9/28) = Real.pi/2 - Real.arctan (28/9) := by
    have := Real.arctan_inv_of_pos (x := (28/9:ℝ)) (by norm_num)
    rwa [show ((28/9:ℝ))⁻¹ = 9/28 by norm_num] at this
  rw [hrefl] at h
  rw [show (7/(1/4+(2:ℝ))) = 28/9 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_3 :
    (Real.pi/2 - 1784594958895156993/4105287186398576640 : ℝ) ≤ Real.arctan (7/(1/4+(3:ℝ)))
    ∧ Real.arctan (7/(1/4+(3:ℝ))) ≤ (Real.pi/2 - 1784433664459693663/4105287186398576640 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (13/28) (by norm_num) 5
  have hps : ArctanTaylor.atanPS (13/28) 5 = (206924201261297/476030517903360 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (13/28) = Real.pi/2 - Real.arctan (28/13) := by
    have := Real.arctan_inv_of_pos (x := (28/13:ℝ)) (by norm_num)
    rwa [show ((28/13:ℝ))⁻¹ = 13/28 by norm_num] at this
  rw [hrefl] at h
  rw [show (7/(1/4+(3:ℝ))) = 28/13 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_4 :
    (Real.pi/2 - 17901503075549160015974093/32803412210959045802065920 : ℝ) ≤ Real.arctan (7/(1/4+(4:ℝ)))
    ∧ Real.arctan (7/(1/4+(4:ℝ))) ≤ (Real.pi/2 - 17899047116570964594023699/32803412210959045802065920 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (17/28) (by norm_num) 7
  have hps : ArctanTaylor.atanPS (17/28) 7 = (22831983540892936613519/41841087003774293114880 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (17/28) = Real.pi/2 - Real.arctan (28/17) := by
    have := Real.arctan_inv_of_pos (x := (28/17:ℝ)) (by norm_num)
    rwa [show ((28/17:ℝ))⁻¹ = 17/28 by norm_num] at this
  rw [hrefl] at h
  rw [show (7/(1/4+(4:ℝ))) = 28/17 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_5 :
    (Real.pi/2 - 1683948021873249947421/2616460849481808609280 : ℝ) ≤ Real.arctan (7/(1/4+(5:ℝ)))
    ∧ Real.arctan (7/(1/4+(5:ℝ))) ≤ (Real.pi/2 - 1683643635323171126211/2616460849481808609280 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (3/4) (by norm_num) 11
  have hps : ArctanTaylor.atanPS (3/4) 11 = (4575532142929919937/7109947960548392960 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (3/4) = Real.pi/2 - Real.arctan (4/3) := by
    have := Real.arctan_inv_of_pos (x := (4/3:ℝ)) (by norm_num)
    rwa [show ((4/3:ℝ))⁻¹ = 3/4 by norm_num] at this
  rw [hrefl] at h
  rw [show (7/(1/4+(5:ℝ))) = 4/3 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_6 :
    (Real.pi/2 - 20900182701941194915059177882029408521692846105554694111492604675298707559579120865040825/28674026128649993792384129293169662039749679745141116858360750167033807170849847298228224 : ℝ) ≤ Real.arctan (7/(1/4+(6:ℝ)))
    ∧ Real.arctan (7/(1/4+(6:ℝ))) ≤ (Real.pi/2 - 20895647052492327199427689150423497154728345187343382547271626931909622624390827408009575/28674026128649993792384129293169662039749679745141116858360750167033807170849847298228224 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (25/28) (by norm_num) 24
  have hps : ArctanTaylor.atanPS (25/28) 24 = (543989870814680369045278881617723158012562360642675924858968029040091761036676752825/746408426922375931705126231080009944808144516481182758703684666988593481123746545664 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hrefl : Real.arctan (25/28) = Real.pi/2 - Real.arctan (28/25) := by
    have := Real.arctan_inv_of_pos (x := (28/25:ℝ)) (by norm_num)
    rwa [show ((28/25:ℝ))⁻¹ = 25/28 by norm_num] at this
  rw [hrefl] at h
  rw [show (7/(1/4+(6:ℝ))) = 28/25 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_7 :
    (Real.pi/4 - 9748/555579 : ℝ) ≤ Real.arctan (7/(1/4+(7:ℝ)))
    ∧ Real.arctan (7/(1/4+(7:ℝ))) ≤ (Real.pi/4 - 9746/555579 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (1/57) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (1/57) 1 = (1/57 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  have hadd : Real.arctan 1 + Real.arctan (-1/57) = Real.arctan (28/29) := by
    rw [Real.arctan_add (by norm_num)]; norm_num
  have hval : Real.arctan (28/29) = Real.pi/4 - Real.arctan (1/57) := by
    rw [← hadd, Real.arctan_one, show (-1/57:ℝ) = -(1/57) by norm_num, Real.arctan_neg]; ring
  rw [show (7/(1/4+(7:ℝ))) = 28/29 by norm_num, hval]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_8 :
    (214720216165239242260307876165541221856477974322122285078092916/305183680851169606645806027794691195400586746430810521370575275 : ℝ) ≤ Real.arctan (7/(1/4+(8:ℝ)))
    ∧ Real.arctan (7/(1/4+(8:ℝ))) ≤ (214775687224528222465231740640388227664273556022593062372449396/305183680851169606645806027794691195400586746430810521370575275 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/33) (by norm_num) 17
  have hps : ArctanTaylor.atanPS (28/33) 17 = (6507513687723749465538479042514082568496235308253262840159732/9247990328823321413509273569536096830320810497903349132441675 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(8:ℝ))) = 28/33 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_9 :
    (36270258740306532366237318476752372925761924/55991043713073545650363493904338672129762595 : ℝ) ≤ Real.arctan (7/(1/4+(9:ℝ)))
    ∧ Real.arctan (7/(1/4+(9:ℝ))) ≤ (36278264744073391123228305738446981617453444/55991043713073545650363493904338672129762595 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/37) (by norm_num) 11
  have hps : ArctanTaylor.atanPS (28/37) 11 = (1152039309625876131252034557360170142332/1778227322802221413610807441303988062685 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(9:ℝ))) = 28/37 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_10 :
    (171303295580970686291464219381076/285971686663247306089347949249995 : ℝ) ≤ Real.arctan (7/(1/4+(10:ℝ)))
    ∧ Real.arctan (7/(1/4+(10:ℝ))) ≤ (171354731331317470075281858743636/285971686663247306089347949249995 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/41) (by norm_num) 8
  have hps : ArctanTaylor.atanPS (28/41) 8 = (5995346378421250592552508628/10007057656970546456568147435 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(10:ℝ))) = 28/41 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_11 :
    (7501480022918649540761212924/13477675730683047637939453125 : ℝ) ≤ Real.arctan (7/(1/4+(11:ℝ)))
    ∧ Real.arctan (7/(1/4+(11:ℝ))) ≤ (7502937952350247720574638076/13477675730683047637939453125 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/45) (by norm_num) 7
  have hps : ArctanTaylor.atanPS (28/45) 7 = (246986304119652629816228/443709489075985107421875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(11:ℝ))) = 28/45 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_12 :
    (323618490867148/623480781969045 : ℝ) ≤ Real.arctan (7/(1/4+(12:ℝ)))
    ∧ Real.arctan (7/(1/4+(12:ℝ))) ≤ (323684928642508/623480781969045 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/7) (by norm_num) 6
  have hps : ArctanTaylor.atanPS (4/7) 6 = (508087456444/978776737785 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(12:ℝ))) = 4/7 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_13 :
    (2229927449137460981188/4588172785039234840515 : ℝ) ≤ Real.arctan (7/(1/4+(13:ℝ)))
    ∧ Real.arctan (7/(1/4+(13:ℝ))) ≤ (2230673864989533449668/4588172785039234840515 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/53) (by norm_num) 5
  have hps : ArctanTaylor.atanPS (28/53) 5 = (72180350725379372/148489361631095985 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(13:ℝ))) = 28/53 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_14 :
    (518228558092907077892/1134974494117354065615 : ℝ) ≤ Real.arctan (7/(1/4+(14:ℝ)))
    ∧ Real.arctan (7/(1/4+(14:ℝ))) ≤ (172770497729193932204/378324831372451355205 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/57) (by norm_num) 5
  have hps : ArctanTaylor.atanPS (28/57) 5 = (130513730959517612/285815787992282565 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(14:ℝ))) = 28/57 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_15 :
    (9268916123459597860612/21539389217660740137195 : ℝ) ≤ Real.arctan (7/(1/4+(15:ℝ)))
    ∧ Real.arctan (7/(1/4+(15:ℝ))) ≤ (9269662539311670329092/21539389217660740137195 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/61) (by norm_num) 5
  have hps : ArctanTaylor.atanPS (28/61) 5 = (226461345468853292/526236574177536345 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(15:ℝ))) = 28/61 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_16 :
    (75800820901749692/186407215541015625 : ℝ) ≤ Real.arctan (7/(1/4+(16:ℝ)))
    ∧ Real.arctan (7/(1/4+(16:ℝ))) ≤ (75821977813656508/186407215541015625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/65) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (28/65) 4 = (5981175491732/14706683671875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(16:ℝ))) = 28/65 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_17 :
    (614895781853481772/1595343952600930305 : ℝ) ≤ Real.arctan (7/(1/4+(17:ℝ)))
    ∧ Real.arctan (7/(1/4+(17:ℝ))) ≤ (615001566413015852/1595343952600930305 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/69) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (28/69) 4 = (14351529186988/37231766262945 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(17:ℝ))) = 28/69 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_18 :
    (970191948260394412/2649221401872056085 : ℝ) ≤ Real.arctan (7/(1/4+(18:ℝ)))
    ∧ Real.arctan (7/(1/4+(18:ℝ))) ≤ (970297732819928492/2649221401872056085 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/73) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (28/73) 4 = (60689612844196/165710977786455 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(18:ℝ))) = 28/73 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_19 :
    (259033434412/742753522665 : ℝ) ≤ Real.arctan (7/(1/4+(19:ℝ)))
    ∧ Real.arctan (7/(1/4+(19:ℝ))) ≤ (259051784492/742753522665 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/11) (by norm_num) 4
  have hps : ArctanTaylor.atanPS (4/11) 4 = (713616004/2046152955 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(19:ℝ))) = 4/11 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_20 :
    (38068478493388/114383962274805 : ℝ) ≤ Real.arctan (7/(1/4+(20:ℝ)))
    ∧ Real.arctan (7/(1/4+(20:ℝ))) ≤ (38087754105548/114383962274805 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/81) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/81) 3 = (5803706188/17433922005 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(20:ℝ))) = 28/81 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_21 :
    (30603475454132/96173126484375 : ℝ) ≤ Real.arctan (7/(1/4+(21:ℝ)))
    ∧ Real.arctan (7/(1/4+(21:ℝ))) ≤ (30615040821428/96173126484375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/85) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/85) 3 = (21182877604/66555796875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(21:ℝ))) = 28/85 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_22 :
    (202225610388004/663470023432935 : ℝ) ≤ Real.arctan (7/(1/4+(22:ℝ)))
    ∧ Real.arctan (7/(1/4+(22:ℝ))) ≤ (202283437224484/663470023432935 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/89) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/89) 3 = (25533963364/83760891735 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(22:ℝ))) = 28/89 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_23 :
    (87980967395692/300850435303785 : ℝ) ≤ Real.arctan (7/(1/4+(23:ℝ)))
    ∧ Real.arctan (7/(1/4+(23:ℝ))) ≤ (88000243007852/300850435303785 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/93) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/93) 3 = (10173500428/34784418465 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(23:ℝ))) = 28/93 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_24 :
    (340588151826916/1211974267171695 : ℝ) ≤ Real.arctan (7/(1/4+(24:ℝ)))
    ∧ Real.arctan (7/(1/4+(24:ℝ))) ≤ (340645978663396/1211974267171695 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/97) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/97) 3 = (36201197284/128810103855 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(24:ℝ))) = 28/97 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_25 :
    (434914569112324/1608203028160515 : ℝ) ≤ Real.arctan (7/(1/4+(25:ℝ)))
    ∧ Real.arctan (7/(1/4+(25:ℝ))) ≤ (434972395948804/1608203028160515 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/101) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/101) 3 = (42637337764/157651507515 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(25:ℝ))) = 28/101 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_26 :
    (311683676/1196015625 : ℝ) ≤ Real.arctan (7/(1/4+(26:ℝ)))
    ∧ Real.arctan (7/(1/4+(26:ℝ))) ≤ (311716444/1196015625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/15) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (4/15) 3 = (989524/3796875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(26:ℝ))) = 4/15 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_27 :
    (689473042530244/2742058681225035 : ℝ) ≤ Real.arctan (7/(1/4+(27:ℝ)))
    ∧ Real.arctan (7/(1/4+(27:ℝ))) ≤ (689530869366724/2742058681225035 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/109) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/109) 3 = (58034000164/230793593235 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(27:ℝ))) = 28/109 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_28 :
    (857154021901156/3528908220672255 : ℝ) ≤ Real.arctan (7/(1/4+(28:ℝ)))
    ∧ Real.arctan (7/(1/4+(28:ℝ))) ≤ (857211848737636/3528908220672255 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/113) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/113) 3 = (67129997284/276365276895 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(28:ℝ))) = 28/113 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_29 :
    (352493014496812/1500621058034865 : ℝ) ≤ Real.arctan (7/(1/4+(29:ℝ)))
    ∧ Real.arctan (7/(1/4+(29:ℝ))) ≤ (352512290108972/1500621058034865 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/117) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/117) 3 = (25750796428/109622401785 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(29:ℝ))) = 28/117 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_30 :
    (1295338905019684/5696247503748615 : ℝ) ≤ Real.arctan (7/(1/4+(30:ℝ)))
    ∧ Real.arctan (7/(1/4+(30:ℝ))) ≤ (1295396731856164/5696247503748615 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/121) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/121) 3 = (88475364964/389061369015 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(30:ℝ))) = 28/121 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_31 :
    (315230759828852/1430511474609375 : ℝ) ≤ Real.arctan (7/(1/4+(31:ℝ)))
    ∧ Real.arctan (7/(1/4+(31:ℝ))) ≤ (315242325196148/1430511474609375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/125) (by norm_num) 3
  have hps : ArctanTaylor.atanPS (28/125) 3 = (100875693604/457763671875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(31:ℝ))) = 28/125 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_32 :
    (38143154252/178615258245 : ℝ) ≤ Real.arctan (7/(1/4+(32:ℝ)))
    ∧ Real.arctan (7/(1/4+(32:ℝ))) ≤ (38177574988/178615258245 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/129) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/129) 2 = (1375892/6440067 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(32:ℝ))) = 28/129 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_33 :
    (7700668/37141485 : ℝ) ≤ Real.arctan (7/(1/4+(33:ℝ)))
    ∧ Real.arctan (7/(1/4+(33:ℝ))) ≤ (7706812/37141485 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/19) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/19) 2 = (4268/20577 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(33:ℝ))) = 4/19 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_34 :
    (145843935076/723925866855 : ℝ) ≤ Real.arctan (7/(1/4+(34:ℝ)))
    ∧ Real.arctan (7/(1/4+(34:ℝ))) ≤ (145947197284/723925866855 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/137) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/137) 2 = (1554644/7714059 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(34:ℝ))) = 28/137 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_35 :
    (54590992652/278654183505 : ℝ) ≤ Real.arctan (7/(1/4+(35:ℝ)))
    ∧ Real.arctan (7/(1/4+(35:ℝ))) ≤ (54625413388/278654183505 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/141) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/141) 2 = (1648052/8409663 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(35:ℝ))) = 28/141 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_36 :
    (183301927396/961460109375 : ℝ) ≤ Real.arctan (7/(1/4+(36:ℝ)))
    ∧ Real.arctan (7/(1/4+(36:ℝ))) ≤ (183405189604/961460109375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/145) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/145) 2 = (1744148/9145875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(36:ℝ))) = 28/145 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_37 :
    (204523035556/1101596636235 : ℝ) ≤ Real.arctan (7/(1/4+(37:ℝ)))
    ∧ Real.arctan (7/(1/4+(37:ℝ))) ≤ (204626297764/1101596636235 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/149) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/149) 2 = (1842932/9923847 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(37:ℝ))) = 28/149 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_38 :
    (75843711692/419205679965 : ℝ) ≤ Real.arctan (7/(1/4+(38:ℝ)))
    ∧ Real.arctan (7/(1/4+(38:ℝ))) ≤ (75878132428/419205679965 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/153) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/153) 2 = (1944404/10744731 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(38:ℝ))) = 28/153 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_39 :
    (252423639076/1430834888355 : ℝ) ≤ Real.arctan (7/(1/4+(39:ℝ)))
    ∧ Real.arctan (7/(1/4+(39:ℝ))) ≤ (252526901284/1430834888355 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/157) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/157) 2 = (2048564/11609679 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(39:ℝ))) = 28/157 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_40 :
    (16618108/96545145 : ℝ) ≤ Real.arctan (7/(1/4+(40:ℝ)))
    ∧ Real.arctan (7/(1/4+(40:ℝ))) ≤ (16624252/96545145 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/23) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/23) 2 = (6284/36501 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(40:ℝ))) = 4/23 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_41 :
    (102754805132/611490515625 : ℝ) ≤ Real.arctan (7/(1/4+(41:ℝ)))
    ∧ Real.arctan (7/(1/4+(41:ℝ))) ≤ (102789225868/611490515625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/165) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/165) 2 = (2264948/13476375 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(41:ℝ))) = 28/165 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_42 :
    (339420416356/2067877377735 : ℝ) ≤ Real.arctan (7/(1/4+(42:ℝ)))
    ∧ Real.arctan (7/(1/4+(42:ℝ))) ≤ (339523678564/2067877377735 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/169) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/169) 2 = (2377172/14480427 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(42:ℝ))) = 28/169 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_43 :
    (372876279076/2324458381395 : ℝ) ≤ Real.arctan (7/(1/4+(43:ℝ)))
    ∧ Real.arctan (7/(1/4+(43:ℝ))) ≤ (372979541284/2324458381395 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/173) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/173) 2 = (2492084/15533151 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(43:ℝ))) = 28/173 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_44 :
    (136247439692/868633023285 : ℝ) ≤ Real.arctan (7/(1/4+(44:ℝ)))
    ∧ Real.arctan (7/(1/4+(44:ℝ))) ≤ (136281860428/868633023285 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/177) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/177) 2 = (2609684/16635699 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(44:ℝ))) = 28/177 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_45 :
    (447131432356/2913963673515 : ℝ) ≤ Real.arctan (7/(1/4+(45:ℝ)))
    ∧ Real.arctan (7/(1/4+(45:ℝ))) ≤ (447234694564/2913963673515 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/181) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/181) 2 = (2729972/17789223 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(45:ℝ))) = 28/181 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_46 :
    (488159095396/3250497984375 : ℝ) ≤ Real.arctan (7/(1/4+(46:ℝ)))
    ∧ Real.arctan (7/(1/4+(46:ℝ))) ≤ (488262357604/3250497984375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/185) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/185) 2 = (2852948/18994875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(46:ℝ))) = 28/185 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_47 :
    (10550036/71744535 : ℝ) ≤ Real.arctan (7/(1/4+(47:ℝ)))
    ∧ Real.arctan (7/(1/4+(47:ℝ))) ≤ (10552084/71744535 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/27) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/27) 2 = (8684/59049 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(47:ℝ))) = 4/27 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_48 :
    (578604879076/4016777762895 : ℝ) ≤ Real.arctan (7/(1/4+(48:ℝ)))
    ∧ Real.arctan (7/(1/4+(48:ℝ))) ≤ (578708141284/4016777762895 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/193) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/193) 2 = (3106964/21567171 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(48:ℝ))) = 28/193 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_49 :
    (628266855076/4450639211355 : ℝ) ≤ Real.arctan (7/(1/4+(49:ℝ)))
    ∧ Real.arctan (7/(1/4+(49:ℝ))) ≤ (628370117284/4450639211355 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/197) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/197) 2 = (3238004/22936119 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(49:ℝ))) = 28/197 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_50 :
    (227018363852/1640402005005 : ℝ) ≤ Real.arctan (7/(1/4+(50:ℝ)))
    ∧ Real.arctan (7/(1/4+(50:ℝ))) ≤ (227052784588/1640402005005 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/201) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/201) 2 = (3371732/24361803 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(50:ℝ))) = 28/201 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_51 :
    (737097967396/5430759421875 : ℝ) ≤ Real.arctan (7/(1/4+(51:ℝ)))
    ∧ Real.arctan (7/(1/4+(51:ℝ))) ≤ (737201229604/5430759421875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/205) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/205) 2 = (3508148/25845375 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(51:ℝ))) = 28/205 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_52 :
    (796526441956/5981673300735 : ℝ) ≤ Real.arctan (7/(1/4+(52:ℝ)))
    ∧ Real.arctan (7/(1/4+(52:ℝ))) ≤ (796629704164/5981673300735 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/209) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/209) 2 = (3647252/27387987 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(52:ℝ))) = 28/209 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_53 :
    (286491351692/2192138661465 : ℝ) ≤ Real.arctan (7/(1/4+(53:ℝ)))
    ∧ Real.arctan (7/(1/4+(53:ℝ))) ≤ (286525772428/2192138661465 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/213) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/213) 2 = (3789044/28990791 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(53:ℝ))) = 28/213 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_54 :
    (55100668/429437265 : ℝ) ≤ Real.arctan (7/(1/4+(54:ℝ)))
    ∧ Real.arctan (7/(1/4+(54:ℝ))) ≤ (55106812/429437265 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/31) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/31) 2 = (11468/89373 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(54:ℝ))) = 4/31 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_55 :
    (996473758756/7907744476515 : ℝ) ≤ Real.arctan (7/(1/4+(55:ℝ)))
    ∧ Real.arctan (7/(1/4+(55:ℝ))) ≤ (996577020964/7907744476515 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/221) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/221) 2 = (4080692/32381583 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(55:ℝ))) = 28/221 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_56 :
    (356935277132/2883251953125 : ℝ) ≤ Real.arctan (7/(1/4+(56:ℝ)))
    ∧ Real.arctan (7/(1/4+(56:ℝ))) ≤ (356969697868/2883251953125 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/225) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/225) 2 = (4230548/34171875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(56:ℝ))) = 28/225 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_57 :
    (1149217006756/9446450882235 : ℝ) ≤ Real.arctan (7/(1/4+(57:ℝ)))
    ∧ Real.arctan (7/(1/4+(57:ℝ))) ≤ (1149320268964/9446450882235 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/229) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/229) 2 = (4383092/36026967 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(57:ℝ))) = 28/229 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_58 :
    (1231853727076/10300797845895 : ℝ) ≤ Real.arctan (7/(1/4+(58:ℝ)))
    ∧ Real.arctan (7/(1/4+(58:ℝ))) ≤ (1231956989284/10300797845895 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/233) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/233) 2 = (4538324/37948011 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(58:ℝ))) = 28/233 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_59 :
    (439621671692/3738623524785 : ℝ) ≤ Real.arctan (7/(1/4+(59:ℝ)))
    ∧ Real.arctan (7/(1/4+(59:ℝ))) ≤ (439656092428/3738623524785 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/237) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/237) 2 = (4696244/39936159 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(59:ℝ))) = 28/237 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_60 :
    (1410402473956/12194850258015 : ℝ) ≤ Real.arctan (7/(1/4+(60:ℝ)))
    ∧ Real.arctan (7/(1/4+(60:ℝ))) ≤ (1410505736164/12194850258015 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/241) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/241) 2 = (4856852/41992563 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(60:ℝ))) = 28/241 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_61 :
    (89642428/787828125 : ℝ) ≤ Real.arctan (7/(1/4+(61:ℝ)))
    ∧ Real.arctan (7/(1/4+(61:ℝ))) ≤ (89648572/787828125 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/35) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/35) 2 = (14636/128625 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(61:ℝ))) = 4/35 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_62 :
    (535891739852/4785934381245 : ℝ) ≤ Real.arctan (7/(1/4+(62:ℝ)))
    ∧ Real.arctan (7/(1/4+(62:ℝ))) ≤ (535926160588/4785934381245 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/249) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/249) 2 = (5186132/46314747 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(62:ℝ))) = 28/249 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_63 :
    (1713726615076/15548692147395 : ℝ) ≤ Real.arctan (7/(1/4+(63:ℝ)))
    ∧ Real.arctan (7/(1/4+(63:ℝ))) ≤ (1713829877284/15548692147395 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/253) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/253) 2 = (5354804/48582831 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(63:ℝ))) = 28/253 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_64 :
    (1824936399076/16817323395855 : ℝ) ≤ Real.arctan (7/(1/4+(64:ℝ)))
    ∧ Real.arctan (7/(1/4+(64:ℝ))) ≤ (1825039661284/16817323395855 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/257) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/257) 2 = (5526164/50923779 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(64:ℝ))) = 28/257 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_65 :
    (647156359052/6055814186505 : ℝ) ≤ Real.arctan (7/(1/4+(65:ℝ)))
    ∧ Real.arctan (7/(1/4+(65:ℝ))) ≤ (647190779788/6055814186505 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/261) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/261) 2 = (5700212/53338743 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(65:ℝ))) = 28/261 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_66 :
    (2063491735396/19602913734375 : ℝ) ≤ Real.arctan (7/(1/4+(66:ℝ)))
    ∧ Real.arctan (7/(1/4+(66:ℝ))) ≤ (2063594997604/19602913734375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/265) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/265) 2 = (5876948/55828875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(66:ℝ))) = 28/265 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_67 :
    (2191174040356/21127721285235 : ℝ) ≤ Real.arctan (7/(1/4+(67:ℝ)))
    ∧ Real.arctan (7/(1/4+(67:ℝ))) ≤ (2191277302564/21127721285235 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/269) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/269) 2 = (6056372/58395327 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(67:ℝ))) = 28/269 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_68 :
    (46105556/451120995 : ℝ) ≤ Real.arctan (7/(1/4+(68:ℝ)))
    ∧ Real.arctan (7/(1/4+(68:ℝ))) ≤ (46107604/451120995 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/39) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/39) 2 = (18188/177957 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(68:ℝ))) = 4/39 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_69 :
    (2464209159076/24461895377355 : ℝ) ≤ Real.arctan (7/(1/4+(69:ℝ)))
    ∧ Real.arctan (7/(1/4+(69:ℝ))) ≤ (2464312421284/24461895377355 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/277) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/277) 2 = (6423284/63761799 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(69:ℝ))) = 28/277 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_70 :
    (2609914208356/26279848581015 : ℝ) ≤ Real.arctan (7/(1/4+(70:ℝ)))
    ∧ Real.arctan (7/(1/4+(70:ℝ))) ≤ (2610017470564/26279848581015 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/281) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/281) 2 = (6610772/66564123 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(70:ℝ))) = 28/281 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_71 :
    (920661125132/9401438390625 : ℝ) ≤ Real.arctan (7/(1/4+(71:ℝ)))
    ∧ Real.arctan (7/(1/4+(71:ℝ))) ≤ (920695545868/9401438390625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/285) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/285) 2 = (6800948/69447375 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(71:ℝ))) = 28/285 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_72 :
    (2920599229156/30239908506735 : ℝ) ≤ Real.arctan (7/(1/4+(72:ℝ)))
    ∧ Real.arctan (7/(1/4+(72:ℝ))) ≤ (2920702491364/30239908506735 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/289) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/289) 2 = (6993812/72412707 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(72:ℝ))) = 28/289 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_73 :
    (3085946919076/32391373270395 : ℝ) ≤ Real.arctan (7/(1/4+(73:ℝ)))
    ∧ Real.arctan (7/(1/4+(73:ℝ))) ≤ (3086050181284/32391373270395 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/293) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/293) 2 = (7189364/75461271 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(73:ℝ))) = 28/293 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_74 :
    (1086071391692/11554529106285 : ℝ) ≤ Real.arctan (7/(1/4+(74:ℝ)))
    ∧ Real.arctan (7/(1/4+(74:ℝ))) ≤ (1086105812428/11554529106285 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/297) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/297) 2 = (7387604/78594219 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(74:ℝ))) = 28/297 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_75 :
    (204533308/2205126645 : ℝ) ≤ Real.arctan (7/(1/4+(75:ℝ)))
    ∧ Real.arctan (7/(1/4+(75:ℝ))) ≤ (204539452/2205126645 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/43) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/43) 2 = (22124/238521 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(75:ℝ))) = 4/43 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_76 :
    (3624271207396/39590451609375 : ℝ) ≤ Real.arctan (7/(1/4+(76:ℝ)))
    ∧ Real.arctan (7/(1/4+(76:ℝ))) ≤ (3624374469604/39590451609375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/305) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/305) 2 = (7792148/85117875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(76:ℝ))) = 28/305 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_77 :
    (1272816448652/14085180002745 : ℝ) ≤ Real.arctan (7/(1/4+(77:ℝ)))
    ∧ Real.arctan (7/(1/4+(77:ℝ))) ≤ (1272850869388/14085180002745 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/309) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/309) 2 = (7998452/88510887 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(77:ℝ))) = 28/309 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_78 :
    (4020323775076/45062257691895 : ℝ) ≤ Real.arctan (7/(1/4+(78:ℝ)))
    ∧ Real.arctan (7/(1/4+(78:ℝ))) ≤ (4020427037284/45062257691895 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/313) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/313) 2 = (8207444/91992891 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(78:ℝ))) = 28/313 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_79 :
    (4230095127076/48016176020355 : ℝ) ≤ Real.arctan (7/(1/4+(79:ℝ)))
    ∧ Real.arctan (7/(1/4+(79:ℝ))) ≤ (4230198389284/48016176020355 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/317) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/317) 2 = (8419124/95565039 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(79:ℝ))) = 28/317 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_80 :
    (1482655538252/17041003528005 : ℝ) ≤ Real.arctan (7/(1/4+(80:ℝ)))
    ∧ Real.arctan (7/(1/4+(80:ℝ))) ≤ (1482689958988/17041003528005 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/321) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/321) 2 = (8633492/99228483 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(80:ℝ))) = 28/321 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_81 :
    (4674144031396/54388623046875 : ℝ) ≤ Real.arctan (7/(1/4+(81:ℝ)))
    ∧ Real.arctan (7/(1/4+(81:ℝ))) ≤ (4674247293604/54388623046875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/325) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/325) 2 = (8850548/102984375 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(81:ℝ))) = 28/325 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_82 :
    (292070908/3440175105 : ℝ) ≤ Real.arctan (7/(1/4+(82:ℝ)))
    ∧ Real.arctan (7/(1/4+(82:ℝ))) ≤ (292077052/3440175105 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/47) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/47) 2 = (26444/311469 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(82:ℝ))) = 4/47 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_83 :
    (1717417575692/20473456584465 : ℝ) ≤ Real.arctan (7/(1/4+(83:ℝ)))
    ∧ Real.arctan (7/(1/4+(83:ℝ))) ≤ (1717451996428/20473456584465 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/333) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/333) 2 = (9292724/110778111 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(83:ℝ))) = 28/333 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_84 :
    (5404608495076/65198974281855 : ℝ) ≤ Real.arctan (7/(1/4+(84:ℝ)))
    ∧ Real.arctan (7/(1/4+(84:ℝ))) ≤ (5404711757284/65198974281855 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/337) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/337) 2 = (9517844/114818259 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(84:ℝ))) = 28/337 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_85 :
    (5666119169956/69161300965515 : ℝ) ≤ Real.arctan (7/(1/4+(85:ℝ)))
    ∧ Real.arctan (7/(1/4+(85:ℝ))) ≤ (5666222432164/69161300965515 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/341) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/341) 2 = (9745652/118955463 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(85:ℝ))) = 28/341 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_86 :
    (1979001149132/24437989828125 : ℝ) ≤ Real.arctan (7/(1/4+(86:ℝ)))
    ∧ Real.arctan (7/(1/4+(86:ℝ))) ≤ (1979035569868/24437989828125 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/345) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/345) 2 = (9976148/123190875 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(86:ℝ))) = 28/345 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_87 :
    (6217482603556/77663756651235 : ℝ) ≤ Real.arctan (7/(1/4+(87:ℝ)))
    ∧ Real.arctan (7/(1/4+(87:ℝ))) ≤ (6217585865764/77663756651235 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/349) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/349) 2 = (10209332/127525647 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(87:ℝ))) = 28/349 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_88 :
    (6507780495076/82217598254895 : ℝ) ≤ Real.arctan (7/(1/4+(88:ℝ)))
    ∧ Real.arctan (7/(1/4+(88:ℝ))) ≤ (6507883757284/82217598254895 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/353) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/353) 2 = (10445204/131960931 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(88:ℝ))) = 28/353 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_89 :
    (135025556/1725126255 : ℝ) ≤ Real.arctan (7/(1/4+(89:ℝ)))
    ∧ Real.arctan (7/(1/4+(89:ℝ))) ≤ (135027604/1725126255 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/51) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/51) 2 = (31148/397953 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(89:ℝ))) = 4/51 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_90 :
    (7118740813156/91965993867015 : ℝ) ≤ Real.arctan (7/(1/4+(90:ℝ)))
    ∧ Real.arctan (7/(1/4+(90:ℝ))) ≤ (7118844075364/91965993867015 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/361) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/361) 2 = (10925012/141137643 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(90:ℝ))) = 28/361 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_91 :
    (7439863855396/97175230921875 : ℝ) ≤ Real.arctan (7/(1/4+(91:ℝ)))
    ∧ Real.arctan (7/(1/4+(91:ℝ))) ≤ (7439967117604/97175230921875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/365) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/365) 2 = (11168948/145881375 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(91:ℝ))) = 28/365 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_92 :
    (2590575621452/34205964064245 : ℝ) ≤ Real.arctan (7/(1/4+(92:ℝ)))
    ∧ Real.arctan (7/(1/4+(92:ℝ))) ≤ (2590610042188/34205964064245 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/369) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/369) 2 = (11415572/150730227 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(92:ℝ))) = 28/369 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_93 :
    (8114566599076/108301735996395 : ℝ) ≤ Real.arctan (7/(1/4+(93:ℝ)))
    ∧ Real.arctan (7/(1/4+(93:ℝ))) ≤ (8114669861284/108301735996395 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/373) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/373) 2 = (11664884/155685351 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(93:ℝ))) = 28/373 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_94 :
    (8468622399076/114234690684855 : ℝ) ≤ Real.arctan (7/(1/4+(94:ℝ)))
    ∧ Real.arctan (7/(1/4+(94:ℝ))) ≤ (8468725661284/114234690684855 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/377) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/377) 2 = (11916884/160747899 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(94:ℝ))) = 28/377 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_95 :
    (2944712061452/40141618829505 : ℝ) ≤ Real.arctan (7/(1/4+(95:ℝ)))
    ∧ Real.arctan (7/(1/4+(95:ℝ))) ≤ (2944746482188/40141618829505 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/381) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/381) 2 = (12171572/165919023 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(95:ℝ))) = 28/381 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_96 :
    (548066428/7549265625 : ℝ) ≤ Real.arctan (7/(1/4+(96:ℝ)))
    ∧ Real.arctan (7/(1/4+(96:ℝ))) ≤ (548072572/7549265625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/55) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/55) 2 = (36236/499125 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(96:ℝ))) = 4/55 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_97 :
    (9600518293156/133610092814235 : ℝ) ≤ Real.arctan (7/(1/4+(97:ℝ)))
    ∧ Real.arctan (7/(1/4+(97:ℝ))) ≤ (9600621555364/133610092814235 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/389) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/389) 2 = (12689012/176591607 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(97:ℝ))) = 28/389 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_98 :
    (3333961119692/46874079925965 : ℝ) ≤ Real.arctan (7/(1/4+(98:ℝ)))
    ∧ Real.arctan (7/(1/4+(98:ℝ))) ≤ (3333995540428/46874079925965 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/393) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/393) 2 = (12951764/182095371 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(98:ℝ))) = 28/393 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_99 :
    (10415699895076/147925754426355 : ℝ) ≤ Real.arctan (7/(1/4+(99:ℝ)))
    ∧ Real.arctan (7/(1/4+(99:ℝ))) ≤ (10415803157284/147925754426355 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/397) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/397) 2 = (13217204/187712319 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(99:ℝ))) = 28/397 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_100 :
    (10842222723556/155529624030015 : ℝ) ≤ Real.arctan (7/(1/4+(100:ℝ)))
    ∧ Real.arctan (7/(1/4+(100:ℝ))) ≤ (10842325985764/155529624030015 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/401) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/401) 2 = (13485332/193443603 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(100:ℝ))) = 28/401 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_101 :
    (3760569749132/54481006265625 : ℝ) ≤ Real.arctan (7/(1/4+(101:ℝ)))
    ∧ Real.arctan (7/(1/4+(101:ℝ))) ≤ (3760604169868/54481006265625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/405) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/405) 2 = (13756148/199290375 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(101:ℝ))) = 28/405 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_102 :
    (11734419449956/171675293715735 : ℝ) ≤ Real.arctan (7/(1/4+(102:ℝ)))
    ∧ Real.arctan (7/(1/4+(102:ℝ))) ≤ (11734522712164/171675293715735 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/409) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/409) 2 = (14029652/205253787 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(102:ℝ))) = 28/409 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_103 :
    (725924668/10723864485 : ℝ) ≤ Real.arctan (7/(1/4+(103:ℝ)))
    ∧ Real.arctan (7/(1/4+(103:ℝ))) ≤ (725930812/10723864485 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/59) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (4/59) 2 = (41708/616137 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(103:ℝ))) = 4/59 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_104 :
    (4226854575692/63044946309285 : ℝ) ≤ Real.arctan (7/(1/4+(104:ℝ)))
    ∧ Real.arctan (7/(1/4+(104:ℝ))) ≤ (4226888996428/63044946309285 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/417) (by norm_num) 2
  have hps : ArctanTaylor.atanPS (28/417) 2 = (14584724/217535139 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(104:ℝ))) = 28/417 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_105 :
    (14866292/223855383 : ℝ) ≤ Real.arctan (7/(1/4+(105:ℝ)))
    ∧ Real.arctan (7/(1/4+(105:ℝ))) ≤ (14910196/223855383 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/421) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/421) 1 = (28/421 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(105:ℝ))) = 28/421 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_106 :
    (15150548/230296875 : ℝ) ≤ Real.arctan (7/(1/4+(106:ℝ)))
    ∧ Real.arctan (7/(1/4+(106:ℝ))) ≤ (15194452/230296875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/425) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/425) 1 = (28/425 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(106:ℝ))) = 28/425 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_107 :
    (15437492/236860767 : ℝ) ≤ Real.arctan (7/(1/4+(107:ℝ)))
    ∧ Real.arctan (7/(1/4+(107:ℝ))) ≤ (15481396/236860767 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/429) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/429) 1 = (28/429 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(107:ℝ))) = 28/429 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_108 :
    (15727124/243548211 : ℝ) ≤ Real.arctan (7/(1/4+(108:ℝ)))
    ∧ Real.arctan (7/(1/4+(108:ℝ))) ≤ (15771028/243548211 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/433) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/433) 1 = (28/433 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(108:ℝ))) = 28/433 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_109 :
    (16019444/250360359 : ℝ) ≤ Real.arctan (7/(1/4+(109:ℝ)))
    ∧ Real.arctan (7/(1/4+(109:ℝ))) ≤ (16063348/250360359 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/437) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/437) 1 = (28/437 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(109:ℝ))) = 28/437 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_110 :
    (47564/750141 : ℝ) ≤ Real.arctan (7/(1/4+(110:ℝ)))
    ∧ Real.arctan (7/(1/4+(110:ℝ))) ≤ (47692/750141 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/63) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/63) 1 = (4/63 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(110:ℝ))) = 4/63 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_111 :
    (16612148/264363375 : ℝ) ≤ Real.arctan (7/(1/4+(111:ℝ)))
    ∧ Real.arctan (7/(1/4+(111:ℝ))) ≤ (16656052/264363375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/445) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/445) 1 = (28/445 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(111:ℝ))) = 28/445 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_112 :
    (16912532/271556547 : ℝ) ≤ Real.arctan (7/(1/4+(112:ℝ)))
    ∧ Real.arctan (7/(1/4+(112:ℝ))) ≤ (16956436/271556547 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/449) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/449) 1 = (28/449 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(112:ℝ))) = 28/449 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_113 :
    (17215604/278879031 : ℝ) ≤ Real.arctan (7/(1/4+(113:ℝ)))
    ∧ Real.arctan (7/(1/4+(113:ℝ))) ≤ (17259508/278879031 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/453) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/453) 1 = (28/453 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(113:ℝ))) = 28/453 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_114 :
    (17521364/286331979 : ℝ) ≤ Real.arctan (7/(1/4+(114:ℝ)))
    ∧ Real.arctan (7/(1/4+(114:ℝ))) ≤ (17565268/286331979 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/457) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/457) 1 = (28/457 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(114:ℝ))) = 28/457 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_115 :
    (17829812/293916543 : ℝ) ≤ Real.arctan (7/(1/4+(115:ℝ)))
    ∧ Real.arctan (7/(1/4+(115:ℝ))) ≤ (17873716/293916543 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/461) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/461) 1 = (28/461 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(115:ℝ))) = 28/461 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_116 :
    (18140948/301633875 : ℝ) ≤ Real.arctan (7/(1/4+(116:ℝ)))
    ∧ Real.arctan (7/(1/4+(116:ℝ))) ≤ (18184852/301633875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/465) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/465) 1 = (28/465 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(116:ℝ))) = 28/465 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_117 :
    (53804/902289 : ℝ) ≤ Real.arctan (7/(1/4+(117:ℝ)))
    ∧ Real.arctan (7/(1/4+(117:ℝ))) ≤ (53932/902289 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/67) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/67) 1 = (4/67 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(117:ℝ))) = 4/67 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_118 :
    (18771284/317471451 : ℝ) ≤ Real.arctan (7/(1/4+(118:ℝ)))
    ∧ Real.arctan (7/(1/4+(118:ℝ))) ≤ (18815188/317471451 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/473) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/473) 1 = (28/473 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(118:ℝ))) = 28/473 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_119 :
    (19090484/325593999 : ℝ) ≤ Real.arctan (7/(1/4+(119:ℝ)))
    ∧ Real.arctan (7/(1/4+(119:ℝ))) ≤ (19134388/325593999 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/477) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/477) 1 = (28/477 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(119:ℝ))) = 28/477 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_120 :
    (19412372/333853923 : ℝ) ≤ Real.arctan (7/(1/4+(120:ℝ)))
    ∧ Real.arctan (7/(1/4+(120:ℝ))) ≤ (19456276/333853923 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/481) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/481) 1 = (28/481 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(120:ℝ))) = 28/481 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_121 :
    (19736948/342252375 : ℝ) ≤ Real.arctan (7/(1/4+(121:ℝ)))
    ∧ Real.arctan (7/(1/4+(121:ℝ))) ≤ (19780852/342252375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/485) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/485) 1 = (28/485 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(121:ℝ))) = 28/485 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_122 :
    (20064212/350790507 : ℝ) ≤ Real.arctan (7/(1/4+(122:ℝ)))
    ∧ Real.arctan (7/(1/4+(122:ℝ))) ≤ (20108116/350790507 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/489) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/489) 1 = (28/489 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(122:ℝ))) = 28/489 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_123 :
    (20394164/359469471 : ℝ) ≤ Real.arctan (7/(1/4+(123:ℝ)))
    ∧ Real.arctan (7/(1/4+(123:ℝ))) ≤ (20438068/359469471 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/493) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/493) 1 = (28/493 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(123:ℝ))) = 28/493 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_124 :
    (60428/1073733 : ℝ) ≤ Real.arctan (7/(1/4+(124:ℝ)))
    ∧ Real.arctan (7/(1/4+(124:ℝ))) ≤ (60556/1073733 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/71) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/71) 1 = (4/71 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(124:ℝ))) = 4/71 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_125 :
    (21062132/377254503 : ℝ) ≤ Real.arctan (7/(1/4+(125:ℝ)))
    ∧ Real.arctan (7/(1/4+(125:ℝ))) ≤ (21106036/377254503 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/501) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/501) 1 = (28/501 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(125:ℝ))) = 28/501 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_126 :
    (21400148/386362875 : ℝ) ≤ Real.arctan (7/(1/4+(126:ℝ)))
    ∧ Real.arctan (7/(1/4+(126:ℝ))) ≤ (21444052/386362875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/505) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/505) 1 = (28/505 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(126:ℝ))) = 28/505 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_127 :
    (21740852/395616687 : ℝ) ≤ Real.arctan (7/(1/4+(127:ℝ)))
    ∧ Real.arctan (7/(1/4+(127:ℝ))) ≤ (21784756/395616687 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/509) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/509) 1 = (28/509 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(127:ℝ))) = 28/509 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_128 :
    (22084244/405017091 : ℝ) ≤ Real.arctan (7/(1/4+(128:ℝ)))
    ∧ Real.arctan (7/(1/4+(128:ℝ))) ≤ (22128148/405017091 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/513) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/513) 1 = (28/513 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(128:ℝ))) = 28/513 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_129 :
    (22430324/414565239 : ℝ) ≤ Real.arctan (7/(1/4+(129:ℝ)))
    ∧ Real.arctan (7/(1/4+(129:ℝ))) ≤ (22474228/414565239 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/517) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/517) 1 = (28/517 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(129:ℝ))) = 28/517 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_130 :
    (22779092/424262283 : ℝ) ≤ Real.arctan (7/(1/4+(130:ℝ)))
    ∧ Real.arctan (7/(1/4+(130:ℝ))) ≤ (22822996/424262283 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/521) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/521) 1 = (28/521 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(130:ℝ))) = 28/521 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_131 :
    (67436/1265625 : ℝ) ≤ Real.arctan (7/(1/4+(131:ℝ)))
    ∧ Real.arctan (7/(1/4+(131:ℝ))) ≤ (67564/1265625 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/75) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/75) 1 = (4/75 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(131:ℝ))) = 4/75 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_132 :
    (23484692/444107667 : ℝ) ≤ Real.arctan (7/(1/4+(132:ℝ)))
    ∧ Real.arctan (7/(1/4+(132:ℝ))) ≤ (23528596/444107667 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/529) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/529) 1 = (28/529 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(132:ℝ))) = 28/529 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_133 :
    (23841524/454258311 : ℝ) ≤ Real.arctan (7/(1/4+(133:ℝ)))
    ∧ Real.arctan (7/(1/4+(133:ℝ))) ≤ (23885428/454258311 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/533) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/533) 1 = (28/533 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(133:ℝ))) = 28/533 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_134 :
    (24201044/464562459 : ℝ) ≤ Real.arctan (7/(1/4+(134:ℝ)))
    ∧ Real.arctan (7/(1/4+(134:ℝ))) ≤ (24244948/464562459 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/537) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/537) 1 = (28/537 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(134:ℝ))) = 28/537 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_135 :
    (24563252/475021263 : ℝ) ≤ Real.arctan (7/(1/4+(135:ℝ)))
    ∧ Real.arctan (7/(1/4+(135:ℝ))) ≤ (24607156/475021263 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/541) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/541) 1 = (28/541 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(135:ℝ))) = 28/541 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_136 :
    (24928148/485635875 : ℝ) ≤ Real.arctan (7/(1/4+(136:ℝ)))
    ∧ Real.arctan (7/(1/4+(136:ℝ))) ≤ (24972052/485635875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/545) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/545) 1 = (28/545 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(136:ℝ))) = 28/545 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_137 :
    (25295732/496407447 : ℝ) ≤ Real.arctan (7/(1/4+(137:ℝ)))
    ∧ Real.arctan (7/(1/4+(137:ℝ))) ≤ (25339636/496407447 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/549) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/549) 1 = (28/549 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(137:ℝ))) = 28/549 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_138 :
    (74828/1479117 : ℝ) ≤ Real.arctan (7/(1/4+(138:ℝ)))
    ∧ Real.arctan (7/(1/4+(138:ℝ))) ≤ (74956/1479117 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/79) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/79) 1 = (4/79 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(138:ℝ))) = 4/79 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_139 :
    (26038964/518426079 : ℝ) ≤ Real.arctan (7/(1/4+(139:ℝ)))
    ∧ Real.arctan (7/(1/4+(139:ℝ))) ≤ (26082868/518426079 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/557) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/557) 1 = (28/557 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(139:ℝ))) = 28/557 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_140 :
    (26414612/529675443 : ℝ) ≤ Real.arctan (7/(1/4+(140:ℝ)))
    ∧ Real.arctan (7/(1/4+(140:ℝ))) ≤ (26458516/529675443 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/561) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/561) 1 = (28/561 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(140:ℝ))) = 28/561 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_141 :
    (26792948/541086375 : ℝ) ≤ Real.arctan (7/(1/4+(141:ℝ)))
    ∧ Real.arctan (7/(1/4+(141:ℝ))) ≤ (26836852/541086375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/565) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/565) 1 = (28/565 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(141:ℝ))) = 28/565 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_142 :
    (27173972/552660027 : ℝ) ≤ Real.arctan (7/(1/4+(142:ℝ)))
    ∧ Real.arctan (7/(1/4+(142:ℝ))) ≤ (27217876/552660027 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/569) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/569) 1 = (28/569 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(142:ℝ))) = 28/569 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_143 :
    (27557684/564397551 : ℝ) ≤ Real.arctan (7/(1/4+(143:ℝ)))
    ∧ Real.arctan (7/(1/4+(143:ℝ))) ≤ (27601588/564397551 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/573) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/573) 1 = (28/573 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(143:ℝ))) = 28/573 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_144 :
    (27944084/576300099 : ℝ) ≤ Real.arctan (7/(1/4+(144:ℝ)))
    ∧ Real.arctan (7/(1/4+(144:ℝ))) ≤ (27987988/576300099 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/577) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/577) 1 = (28/577 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(144:ℝ))) = 28/577 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_145 :
    (82604/1715361 : ℝ) ≤ Real.arctan (7/(1/4+(145:ℝ)))
    ∧ Real.arctan (7/(1/4+(145:ℝ))) ≤ (82732/1715361 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/83) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/83) 1 = (4/83 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(145:ℝ))) = 4/83 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_146 :
    (28724948/600604875 : ℝ) ≤ Real.arctan (7/(1/4+(146:ℝ)))
    ∧ Real.arctan (7/(1/4+(146:ℝ))) ≤ (28768852/600604875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/585) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/585) 1 = (28/585 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(146:ℝ))) = 28/585 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_147 :
    (29119412/613009407 : ℝ) ≤ Real.arctan (7/(1/4+(147:ℝ)))
    ∧ Real.arctan (7/(1/4+(147:ℝ))) ≤ (29163316/613009407 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/589) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/589) 1 = (28/589 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(147:ℝ))) = 28/589 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_148 :
    (29516564/625583571 : ℝ) ≤ Real.arctan (7/(1/4+(148:ℝ)))
    ∧ Real.arctan (7/(1/4+(148:ℝ))) ≤ (29560468/625583571 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/593) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/593) 1 = (28/593 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(148:ℝ))) = 28/593 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_149 :
    (29916404/638328519 : ℝ) ≤ Real.arctan (7/(1/4+(149:ℝ)))
    ∧ Real.arctan (7/(1/4+(149:ℝ))) ≤ (29960308/638328519 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/597) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/597) 1 = (28/597 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(149:ℝ))) = 28/597 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_150 :
    (30318932/651245403 : ℝ) ≤ Real.arctan (7/(1/4+(150:ℝ)))
    ∧ Real.arctan (7/(1/4+(150:ℝ))) ≤ (30362836/651245403 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/601) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/601) 1 = (28/601 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(150:ℝ))) = 28/601 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_151 :
    (30724148/664335375 : ℝ) ≤ Real.arctan (7/(1/4+(151:ℝ)))
    ∧ Real.arctan (7/(1/4+(151:ℝ))) ≤ (30768052/664335375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/605) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/605) 1 = (28/605 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(151:ℝ))) = 28/605 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_152 :
    (90764/1975509 : ℝ) ≤ Real.arctan (7/(1/4+(152:ℝ)))
    ∧ Real.arctan (7/(1/4+(152:ℝ))) ≤ (90892/1975509 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/87) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/87) 1 = (4/87 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(152:ℝ))) = 4/87 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_153 :
    (31542644/691039191 : ℝ) ≤ Real.arctan (7/(1/4+(153:ℝ)))
    ∧ Real.arctan (7/(1/4+(153:ℝ))) ≤ (31586548/691039191 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/613) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/613) 1 = (28/613 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(153:ℝ))) = 28/613 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_154 :
    (31955924/704655339 : ℝ) ≤ Real.arctan (7/(1/4+(154:ℝ)))
    ∧ Real.arctan (7/(1/4+(154:ℝ))) ≤ (31999828/704655339 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/617) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/617) 1 = (28/617 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(154:ℝ))) = 28/617 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_155 :
    (32371892/718449183 : ℝ) ≤ Real.arctan (7/(1/4+(155:ℝ)))
    ∧ Real.arctan (7/(1/4+(155:ℝ))) ≤ (32415796/718449183 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/621) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/621) 1 = (28/621 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(155:ℝ))) = 28/621 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_156 :
    (32790548/732421875 : ℝ) ≤ Real.arctan (7/(1/4+(156:ℝ)))
    ∧ Real.arctan (7/(1/4+(156:ℝ))) ≤ (32834452/732421875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/625) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/625) 1 = (28/625 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(156:ℝ))) = 28/625 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_157 :
    (33211892/746574567 : ℝ) ≤ Real.arctan (7/(1/4+(157:ℝ)))
    ∧ Real.arctan (7/(1/4+(157:ℝ))) ≤ (33255796/746574567 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/629) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/629) 1 = (28/629 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(157:ℝ))) = 28/629 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_158 :
    (33635924/760908411 : ℝ) ≤ Real.arctan (7/(1/4+(158:ℝ)))
    ∧ Real.arctan (7/(1/4+(158:ℝ))) ≤ (33679828/760908411 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/633) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/633) 1 = (28/633 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(158:ℝ))) = 28/633 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_159 :
    (99308/2260713 : ℝ) ≤ Real.arctan (7/(1/4+(159:ℝ)))
    ∧ Real.arctan (7/(1/4+(159:ℝ))) ≤ (99436/2260713 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/91) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/91) 1 = (4/91 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(159:ℝ))) = 4/91 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_160 :
    (34492052/790124163 : ℝ) ≤ Real.arctan (7/(1/4+(160:ℝ)))
    ∧ Real.arctan (7/(1/4+(160:ℝ))) ≤ (34535956/790124163 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/641) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/641) 1 = (28/641 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(160:ℝ))) = 28/641 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_161 :
    (34924148/805008375 : ℝ) ≤ Real.arctan (7/(1/4+(161:ℝ)))
    ∧ Real.arctan (7/(1/4+(161:ℝ))) ≤ (34968052/805008375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/645) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/645) 1 = (28/645 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(161:ℝ))) = 28/645 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_162 :
    (35358932/820078347 : ℝ) ≤ Real.arctan (7/(1/4+(162:ℝ)))
    ∧ Real.arctan (7/(1/4+(162:ℝ))) ≤ (35402836/820078347 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/649) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/649) 1 = (28/649 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(162:ℝ))) = 28/649 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_163 :
    (35796404/835335231 : ℝ) ≤ Real.arctan (7/(1/4+(163:ℝ)))
    ∧ Real.arctan (7/(1/4+(163:ℝ))) ≤ (35840308/835335231 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/653) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/653) 1 = (28/653 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(163:ℝ))) = 28/653 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_164 :
    (36236564/850780179 : ℝ) ≤ Real.arctan (7/(1/4+(164:ℝ)))
    ∧ Real.arctan (7/(1/4+(164:ℝ))) ≤ (36280468/850780179 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/657) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/657) 1 = (28/657 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(164:ℝ))) = 28/657 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_165 :
    (36679412/866414343 : ℝ) ≤ Real.arctan (7/(1/4+(165:ℝ)))
    ∧ Real.arctan (7/(1/4+(165:ℝ))) ≤ (36723316/866414343 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/661) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/661) 1 = (28/661 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(165:ℝ))) = 28/661 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_166 :
    (108236/2572125 : ℝ) ≤ Real.arctan (7/(1/4+(166:ℝ)))
    ∧ Real.arctan (7/(1/4+(166:ℝ))) ≤ (108364/2572125 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/95) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/95) 1 = (4/95 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(166:ℝ))) = 4/95 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_167 :
    (37573172/898254927 : ℝ) ≤ Real.arctan (7/(1/4+(167:ℝ)))
    ∧ Real.arctan (7/(1/4+(167:ℝ))) ≤ (37617076/898254927 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/669) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/669) 1 = (28/669 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(167:ℝ))) = 28/669 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_168 :
    (38024084/914463651 : ℝ) ≤ Real.arctan (7/(1/4+(168:ℝ)))
    ∧ Real.arctan (7/(1/4+(168:ℝ))) ≤ (38067988/914463651 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/673) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/673) 1 = (28/673 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(168:ℝ))) = 28/673 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_169 :
    (38477684/930866199 : ℝ) ≤ Real.arctan (7/(1/4+(169:ℝ)))
    ∧ Real.arctan (7/(1/4+(169:ℝ))) ≤ (38521588/930866199 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/677) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/677) 1 = (28/677 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(169:ℝ))) = 28/677 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_170 :
    (38933972/947463723 : ℝ) ≤ Real.arctan (7/(1/4+(170:ℝ)))
    ∧ Real.arctan (7/(1/4+(170:ℝ))) ≤ (38977876/947463723 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/681) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/681) 1 = (28/681 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(170:ℝ))) = 28/681 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_171 :
    (39392948/964257375 : ℝ) ≤ Real.arctan (7/(1/4+(171:ℝ)))
    ∧ Real.arctan (7/(1/4+(171:ℝ))) ≤ (39436852/964257375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/685) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/685) 1 = (28/685 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(171:ℝ))) = 28/685 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_172 :
    (39854612/981248307 : ℝ) ≤ Real.arctan (7/(1/4+(172:ℝ)))
    ∧ Real.arctan (7/(1/4+(172:ℝ))) ≤ (39898516/981248307 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/689) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/689) 1 = (28/689 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(172:ℝ))) = 28/689 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_173 :
    (117548/2910897 : ℝ) ≤ Real.arctan (7/(1/4+(173:ℝ)))
    ∧ Real.arctan (7/(1/4+(173:ℝ))) ≤ (117676/2910897 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/99) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/99) 1 = (4/99 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(173:ℝ))) = 4/99 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_174 :
    (40786004/1015826619 : ℝ) ≤ Real.arctan (7/(1/4+(174:ℝ)))
    ∧ Real.arctan (7/(1/4+(174:ℝ))) ≤ (40829908/1015826619 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/697) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/697) 1 = (28/697 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(174:ℝ))) = 28/697 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_175 :
    (41255732/1033416303 : ℝ) ≤ Real.arctan (7/(1/4+(175:ℝ)))
    ∧ Real.arctan (7/(1/4+(175:ℝ))) ≤ (41299636/1033416303 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/701) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/701) 1 = (28/701 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(175:ℝ))) = 28/701 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_176 :
    (41728148/1051207875 : ℝ) ≤ Real.arctan (7/(1/4+(176:ℝ)))
    ∧ Real.arctan (7/(1/4+(176:ℝ))) ≤ (41772052/1051207875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/705) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/705) 1 = (28/705 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(176:ℝ))) = 28/705 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_177 :
    (42203252/1069202487 : ℝ) ≤ Real.arctan (7/(1/4+(177:ℝ)))
    ∧ Real.arctan (7/(1/4+(177:ℝ))) ≤ (42247156/1069202487 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/709) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/709) 1 = (28/709 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(177:ℝ))) = 28/709 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_178 :
    (42681044/1087401291 : ℝ) ≤ Real.arctan (7/(1/4+(178:ℝ)))
    ∧ Real.arctan (7/(1/4+(178:ℝ))) ≤ (42724948/1087401291 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/713) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/713) 1 = (28/713 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(178:ℝ))) = 28/713 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_179 :
    (43161524/1105805439 : ℝ) ≤ Real.arctan (7/(1/4+(179:ℝ)))
    ∧ Real.arctan (7/(1/4+(179:ℝ))) ≤ (43205428/1105805439 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/717) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/717) 1 = (28/717 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(179:ℝ))) = 28/717 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_180 :
    (127244/3278181 : ℝ) ≤ Real.arctan (7/(1/4+(180:ℝ)))
    ∧ Real.arctan (7/(1/4+(180:ℝ))) ≤ (127372/3278181 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/103) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/103) 1 = (4/103 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(180:ℝ))) = 4/103 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_181 :
    (44130548/1143234375 : ℝ) ≤ Real.arctan (7/(1/4+(181:ℝ)))
    ∧ Real.arctan (7/(1/4+(181:ℝ))) ≤ (44174452/1143234375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/725) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/725) 1 = (28/725 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(181:ℝ))) = 28/725 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_182 :
    (44619092/1162261467 : ℝ) ≤ Real.arctan (7/(1/4+(182:ℝ)))
    ∧ Real.arctan (7/(1/4+(182:ℝ))) ≤ (44662996/1162261467 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/729) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/729) 1 = (28/729 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(182:ℝ))) = 28/729 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_183 :
    (45110324/1181498511 : ℝ) ≤ Real.arctan (7/(1/4+(183:ℝ)))
    ∧ Real.arctan (7/(1/4+(183:ℝ))) ≤ (45154228/1181498511 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/733) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/733) 1 = (28/733 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(183:ℝ))) = 28/733 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_184 :
    (45604244/1200946659 : ℝ) ≤ Real.arctan (7/(1/4+(184:ℝ)))
    ∧ Real.arctan (7/(1/4+(184:ℝ))) ≤ (45648148/1200946659 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/737) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/737) 1 = (28/737 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(184:ℝ))) = 28/737 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_185 :
    (46100852/1220607063 : ℝ) ≤ Real.arctan (7/(1/4+(185:ℝ)))
    ∧ Real.arctan (7/(1/4+(185:ℝ))) ≤ (46144756/1220607063 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/741) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/741) 1 = (28/741 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(185:ℝ))) = 28/741 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_186 :
    (46600148/1240480875 : ℝ) ≤ Real.arctan (7/(1/4+(186:ℝ)))
    ∧ Real.arctan (7/(1/4+(186:ℝ))) ≤ (46644052/1240480875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/745) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/745) 1 = (28/745 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(186:ℝ))) = 28/745 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_187 :
    (137324/3675129 : ℝ) ≤ Real.arctan (7/(1/4+(187:ℝ)))
    ∧ Real.arctan (7/(1/4+(187:ℝ))) ≤ (137452/3675129 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/107) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/107) 1 = (4/107 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(187:ℝ))) = 4/107 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_188 :
    (47606804/1280873331 : ℝ) ≤ Real.arctan (7/(1/4+(188:ℝ)))
    ∧ Real.arctan (7/(1/4+(188:ℝ))) ≤ (47650708/1280873331 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/753) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/753) 1 = (28/753 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(188:ℝ))) = 28/753 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_189 :
    (48114164/1301394279 : ℝ) ≤ Real.arctan (7/(1/4+(189:ℝ)))
    ∧ Real.arctan (7/(1/4+(189:ℝ))) ≤ (48158068/1301394279 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/757) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/757) 1 = (28/757 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(189:ℝ))) = 28/757 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_190 :
    (48624212/1322133243 : ℝ) ≤ Real.arctan (7/(1/4+(190:ℝ)))
    ∧ Real.arctan (7/(1/4+(190:ℝ))) ≤ (48668116/1322133243 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/761) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/761) 1 = (28/761 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(190:ℝ))) = 28/761 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_191 :
    (49136948/1343091375 : ℝ) ≤ Real.arctan (7/(1/4+(191:ℝ)))
    ∧ Real.arctan (7/(1/4+(191:ℝ))) ≤ (49180852/1343091375 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/765) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/765) 1 = (28/765 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(191:ℝ))) = 28/765 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_192 :
    (49652372/1364269827 : ℝ) ≤ Real.arctan (7/(1/4+(192:ℝ)))
    ∧ Real.arctan (7/(1/4+(192:ℝ))) ≤ (49696276/1364269827 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/769) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/769) 1 = (28/769 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(192:ℝ))) = 28/769 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_193 :
    (50170484/1385669751 : ℝ) ≤ Real.arctan (7/(1/4+(193:ℝ)))
    ∧ Real.arctan (7/(1/4+(193:ℝ))) ≤ (50214388/1385669751 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/773) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/773) 1 = (28/773 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(193:ℝ))) = 28/773 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_194 :
    (147788/4102893 : ℝ) ≤ Real.arctan (7/(1/4+(194:ℝ)))
    ∧ Real.arctan (7/(1/4+(194:ℝ))) ≤ (147916/4102893 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (4/111) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (4/111) 1 = (4/111 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(194:ℝ))) = 4/111 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_195 :
    (51214772/1429138623 : ℝ) ≤ Real.arctan (7/(1/4+(195:ℝ)))
    ∧ Real.arctan (7/(1/4+(195:ℝ))) ≤ (51258676/1429138623 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/781) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/781) 1 = (28/781 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(195:ℝ))) = 28/781 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_196 :
    (51740948/1451209875 : ℝ) ≤ Real.arctan (7/(1/4+(196:ℝ)))
    ∧ Real.arctan (7/(1/4+(196:ℝ))) ≤ (51784852/1451209875 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/785) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/785) 1 = (28/785 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(196:ℝ))) = 28/785 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_197 :
    (52269812/1473507207 : ℝ) ≤ Real.arctan (7/(1/4+(197:ℝ)))
    ∧ Real.arctan (7/(1/4+(197:ℝ))) ≤ (52313716/1473507207 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/789) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/789) 1 = (28/789 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(197:ℝ))) = 28/789 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_198 :
    (52801364/1496031771 : ℝ) ≤ Real.arctan (7/(1/4+(198:ℝ)))
    ∧ Real.arctan (7/(1/4+(198:ℝ))) ≤ (52845268/1496031771 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/793) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/793) 1 = (28/793 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(198:ℝ))) = 28/793 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_199 :
    (53335604/1518784719 : ℝ) ≤ Real.arctan (7/(1/4+(199:ℝ)))
    ∧ Real.arctan (7/(1/4+(199:ℝ))) ≤ (53379508/1518784719 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/797) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/797) 1 = (28/797 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(199:ℝ))) = 28/797 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

theorem pterm_200 :
    (53872532/1541767203 : ℝ) ≤ Real.arctan (7/(1/4+(200:ℝ)))
    ∧ Real.arctan (7/(1/4+(200:ℝ))) ≤ (53916436/1541767203 : ℝ) := by
  have h := ArctanTaylor.arctan_bracket (28/801) (by norm_num) 1
  have hps : ArctanTaylor.atanPS (28/801) 1 = (28/801 : ℝ) := by
    rw [ArctanTaylor.atanPS]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hps] at h
  rw [show (7/(1/4+(200:ℝ))) = 28/801 by norm_num]
  rw [abs_le] at h
  constructor <;> [nlinarith [h.1]; nlinarith [h.2]]

end ForgePhi14Terms
