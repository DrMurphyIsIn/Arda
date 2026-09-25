/-  RS4_Demo.lean -- lane B4: two worked heights, kernel-checked, with certified SIGNS of
    Re completedRiemannZeta(1/2+it), plus three tampered certificates the kernel REJECTS.

    Configuration: the island's P = 64 evaluator `ArbEcon.OrderK.cfg64 tn tq`, validated once for
    all heights by `ArbEcon.OrderK.valid64` (EMZetaHighCheck).  Certificates were emitted by an
    UNTRUSTED mpmath script (scratchpad/b4/emit.py); every value is re-verified by `RS4.check`.

      t = 20001/2 = 10000.5 : Zmain in [0.29804, 0.29904] for every phase in the ball
                              => Hardy Z(10000.5) in [0.29604, 0.30105]   (mpmath: 0.2985401511)
                              => Re Lambda(1/2 + 10000.5 i) > 0.
      t = 10000             : Zmain in [-0.34190, -0.34090]
                              => Hardy Z(10000) in [-0.34390, -0.33889]   (mpmath: -0.3413947242)
                              => Re Lambda(1/2 + 10000 i) < 0.

    Negative controls (each `check ... = false` is ALSO decided by the kernel):
      * `bad_flip`   : the sign-flipped output box;
      * `bad_narrow` : an output box of half-width 1e-4 (it contains the true value, but the
                       certified enclosure is wider, ~2.1e-4, so the checker must refuse it);
      * `bad_psi`    : Psi bracket shifted by 0.01 (the quotient check against the two cos balls fails).

    conjecture1_proved = False.  Two heights; nothing about RH.
-/
import RS4_Z
import EMZetaHighCheck

open Complex

namespace RS4.Demo

noncomputable section

/-! ## t = 10000.5 -/

def cfgA : ArbEcon.Cfg := ArbEcon.OrderK.cfg64 20001 1

theorem validA : ArbEcon.Valid cfgA (20001 / 2 : ℝ) 9 :=
  ArbEcon.OrderK.valid64 20001 1 _ (by norm_num)

def zA : Cert := ⟨39, 735937012410128295560, 735937012410128295612, 423435731678353398,
  423435731678353400, 418648967964371565, 418648967964502122, 587782752321680106885197,
  587782756010845780235121, 2920513788782627811, 2920513788782627812, 103760481544834446288,
  103760481544834446630, 18115484132488945967, 18115484132488946882, 12950258999377744492,
  12950258999414637981, 101417857354832736920191035065280393624,
  101758139721753675383654409672712161836⟩

/-- The kernel accepts the certificate at t = 10000.5. -/
theorem okA : check cfgA zA = true := by decide +kernel

theorem zA_lo : (2 / 1000 : ℝ) < (zA.zlo : ℝ) / 2 ^ (2 * cfgA.P) := by
  show (2 / 1000 : ℝ) < ((101417857354832736920191035065280393624 : ℤ) : ℝ) / 2 ^ (2 * 64)
  norm_num

/-- **Certified sign at t = 10000.5**: `Re Lambda(1/2 + 10000.5 i) > 0`. -/
theorem sign_A : 0 < (completedRiemannZeta ((1 / 2 : ℂ) + ((20001 / 2 : ℝ) : ℂ) * I)).re :=
  rs4_sign_pos validA zA okA zA_lo

/-- **Certified enclosure of Hardy's Z at t = 10000.5.** -/
theorem hardyZ_A : ∃ M φ : ℝ, 0 < M ∧
    Gammaℝ ((1 / 2 : ℂ) + ((20001 / 2 : ℝ) : ℂ) * I) = (M : ℂ) * cexp (I * φ) ∧
    |φ - RSInt.rsThetaMain (20001 / 2)| ≤ 1 / (20001 / 2) ∧
    (29604 / 100000 : ℝ) ≤ (completedRiemannZeta ((1 / 2 : ℂ) + ((20001 / 2 : ℝ) : ℂ) * I)).re / M ∧
    (completedRiemannZeta ((1 / 2 : ℂ) + ((20001 / 2 : ℝ) : ℂ) * I)).re / M ≤ (30105 / 100000 : ℝ) := by
  obtain ⟨M, φ, hM, hp, hφ, h1, h2⟩ := rs4_Z_enclosure validA zA okA
  refine ⟨M, φ, hM, hp, hφ, ?_, ?_⟩
  · refine le_trans ?_ h1
    show (29604 / 100000 : ℝ) ≤ ((101417857354832736920191035065280393624 : ℤ) : ℝ) / 2 ^ (2 * 64) - 2 / 1000
    norm_num
  · refine le_trans h2 ?_
    show ((101758139721753675383654409672712161836 : ℤ) : ℝ) / 2 ^ (2 * 64) + 2 / 1000 ≤ (30105 / 100000 : ℝ)
    norm_num

/-! ## t = 10000 -/

def cfgB : ArbEcon.Cfg := ArbEcon.OrderK.cfg64 10000 0

theorem validB : ArbEcon.Valid cfgB (10000 : ℝ) 9 :=
  ArbEcon.OrderK.valid64 10000 0 _ (by norm_num)

def zB : Cert := ⟨39, 735918614674730245206, 735918614674730245257, 422963994873275184,
  422963994873275186, 418187810891360267, 418187810891489521, 587748752720350004166202,
  587748756409700122638114, 2920550294520512138, 2920550294520512139, 103644885164096038523,
  103644885164096038858, 18206742091009507940, 18206742091009508837, 12917014478880176271,
  12917014478917069760, -116341713711492213740936717703079480602,
  -116001431344571275277473343095647712389⟩

/-- The kernel accepts the certificate at t = 10000. -/
theorem okB : check cfgB zB = true := by decide +kernel

theorem zB_hi : (zB.zhi : ℝ) / 2 ^ (2 * cfgB.P) < -(2 / 1000 : ℝ) := by
  show ((-116001431344571275277473343095647712389 : ℤ) : ℝ) / 2 ^ (2 * 64) < -(2 / 1000 : ℝ)
  norm_num

/-- **Certified sign at t = 10000**: `Re Lambda(1/2 + 10000 i) < 0`. -/
theorem sign_B : (completedRiemannZeta ((1 / 2 : ℂ) + ((10000 : ℝ) : ℂ) * I)).re < 0 :=
  rs4_sign_neg validB zB okB zB_hi

/-! ## negative controls (t = 10000.5): the kernel REJECTS tampered certificates -/

/-- The sign-flipped output box. -/
def zA_flip : Cert := { zA with zlo := -101758139721753675383654409672712161836,
                                zhi := -101417857354832736920191035065280393624 }

theorem bad_flip : check cfgA zA_flip = false := by decide +kernel

/-- An output box of half-width 1e-4 around the true value (narrower than what is certified). -/
def zA_narrow : Cert := { zA with zlo := 101553970301601112305576384908253100908,
                                  zhi := 101622026774985299998269059829739454551 }

theorem bad_narrow : check cfgA zA_narrow = false := by decide +kernel

/-- The Psi bracket shifted by 0.01. -/
def zA_psi : Cert := { zA with F0 := 13134726440114840008, F1 := 13134726440151733497 }

theorem bad_psi : check cfgA zA_psi = false := by decide +kernel

end

end RS4.Demo
