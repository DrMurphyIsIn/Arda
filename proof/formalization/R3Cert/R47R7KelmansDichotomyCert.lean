/-
  R47 / R7 -- the TWO-HUB Kelmans-step DICHOTOMY, machine-checked (all p >= q >= 1).

  Completes the kernel-verification of the local Kelmans merge table.  For the adjacent
  hubward step on the two-hub family, with p = 1+s+r arms on the receiver-side donor and
  q = 1+s on the donor (r, s >= 0 <=> p >= q >= 1), the step gain in pi = per(L)/prod(deg),
  Phi2 = num/den (den > 0), has a SIGN-DEFINITE numerator PER LOAD CELL (ca, cb):

    * cb >= 1 (30 cells): num all-nonneg, positive constant  =>  Phi2 > 0  -- the step
      strictly INCREASES pi: a LOADED donor merges profitably.        [monotone, all N]
    * cb = 0, ca >= 2 (4 cells): -num all-nonneg, positive constant  =>  Phi2 < 0 -- the
      step strictly DECREASES pi: a DE-LOADED donor merge is a loss.  [anti-monotone, all N]
    * cb = 0, ca in {0,1} (2 mixed cells): genuinely sign-changing, tiled exactly by the
      shifted decreasing tails (q >= qmin, and the fixed-q p-tails) plus the finitely many
      increasing corners (small (p,q), Phi2 a positive rational).

  This is the ''increases iff the donor is loaded'' dichotomy that MOTIVATES the assisted
  merge (R47R7KelmansAssistedMergeCert): a de-loaded donor loses, so it must first borrow a
  cherry.  Ports certify_two_hub_symbolic (kelmans_mixed_load.py) Python -> kernel.  All
  positivity emitted by telperion emit_nonneg_orthant; the finite corners by norm_num.

  Self-building R3Cert.+ leaf, imported by nothing -- collision-safe.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert.Step3


/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(0,1), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c0_1 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 780*s*s*s*s + 1170*r*s*s*s + 390*r*r*s*s + 12230*s*s*s + 11736*r*s*s + 1690*r*r*s + 47502*s*s + 32786*r*s + 1300*r*r + 57892*s + 22220*r + 21840 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(1,1), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c1_1 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 2340*s*s*s*s + 5850*r*s*s*s + 4680*r*r*s*s + 1170*r*r*r*s + 33858*s*s*s + 63816*r*s*s + 31128*r*r*s + 1170*r*r*r + 131956*s*s + 154504*r*s + 26448*r*r + 171698*s + 96538*r + 71260 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(2,1), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c2_1 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 7020*s*s*s*s + 17550*r*s*s*s + 14040*r*r*s*s + 3510*r*r*r*s + 102438*s*s*s + 204642*r*s*s + 105714*r*r*s + 3510*r*r*r + 465402*s*s + 616044*r*s + 91674*r*r + 732024*s + 428952*r + 362040 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(3,1), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c3_1 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 7020*s*s*s*s + 17550*r*s*s*s + 14040*r*r*s*s + 3510*r*r*r*s + 103302*s*s*s + 217836*r*s*s + 118044*r*r*s + 3510*r*r*r + 520560*s*s + 797256*r*s + 104004*r*r + 1020114*s + 596970*r + 595836 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(4,1), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c4_1 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 63180*s*s*s*s + 157950*r*s*s*s + 126360*r*r*s*s + 31590*r*r*r*s + 937494*s*s*s + 2079270*r*s*s + 1173366*r*r*s + 31590*r*r*r + 5052078*s*s + 9064332*r*s + 1047006*r*r + 12712356*s + 7143012*r + 8534592 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(5,1), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c5_1 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 189540*s*s*s*s + 473850*r*s*s*s + 379080*r*r*s*s + 94770*r*r*r*s + 2835810*s*s*s + 6594048*r*s*s + 3853008*r*r*s + 94770*r*r*r + 15869196*s*s + 33634440*r*s + 3473928*r*r + 52440858*s + 27514242*r + 39217932 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(0,2), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c0_2 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 2964*s*s*s*s + 4446*r*s*s*s + 1482*r*r*s*s + 33866*s*s*s + 37194*r*s*s + 8398*r*r*s + 123288*s*s + 88748*r*s + 6916*r*r + 151774*s + 56000*r + 59388 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(1,2), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c1_2 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 8892*s*s*s*s + 22230*r*s*s*s + 17784*r*r*s*s + 4446*r*r*r*s + 94050*s*s*s + 167898*r*s*s + 78294*r*r*s + 4446*r*r*r + 309530*s*s + 337280*r*s + 60510*r*r + 355412*s + 191612*r + 131040 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(2,2), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c2_2 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 26676*s*s*s*s + 66690*r*s*s*s + 53352*r*r*s*s + 13338*r*r*r*s + 330642*s*s*s + 599040*r*s*s + 281736*r*r*s + 13338*r*r*r + 1294332*s*s + 1460472*r*s + 228384*r*r + 1703442*s + 928122*r + 713076 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(3,2), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c3_2 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 26676*s*s*s*s + 66690*r*s*s*s + 53352*r*r*s*s + 13338*r*r*r*s + 379134*s*s*s + 694386*r*s*s + 328590*r*r*s + 13338*r*r*r + 1726002*s*s + 2018088*r*s + 275238*r*r + 2688336*s + 1390392*r + 1314792 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(4,2), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c4_2 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 240084*s*s*s*s + 600210*r*s*s*s + 480168*r*r*s*s + 120042*r*r*r*s + 3848634*s*s*s + 7107588*r*s*s + 3378996*r*r*s + 120042*r*r*r + 20012400*s*s + 24162192*r*s + 2898828*r*r + 37320966*s + 17654814*r + 20917116 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(5,2), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c5_2 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 720252*s*s*s*s + 1800630*r*s*s*s + 1440504*r*r*s*s + 360126*r*r*r*s + 12855186*s*s*s + 23897106*r*s*s + 11402046*r*r*s + 360126*r*r*r + 75252402*s*s + 93427344*r*s + 9961542*r*r + 167524524*s + 71330868*r + 104407056 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(0,3), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c0_3 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 15444*s*s*s*s + 23166*r*s*s*s + 7722*r*r*s*s + 183978*s*s*s + 214164*r*s*s + 54054*r*r*s + 685422*s*s + 503010*r*s + 46332*r*r + 886896*s + 312012*r + 370008 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(1,3), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c1_3 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 138996*s*s*s*s + 347490*r*s*s*s + 277992*r*r*s*s + 69498*r*r*r*s + 1388178*s*s*s + 2447820*r*s*s + 1129140*r*r*s + 69498*r*r*r + 4359096*s*s + 4655664*r*s + 851148*r*r + 4744494*s + 2555334*r + 1634580 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(2,3), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c2_3 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 416988*s*s*s*s + 1042470*r*s*s*s + 833976*r*r*s*s + 208494*r*r*r*s + 5029614*s*s*s + 8940942*r*s*s + 4119822*r*r*s + 208494*r*r*r + 18826182*s*s + 20460924*r*s + 3285846*r*r + 22469076*s + 12562452*r + 8255520 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(3,3), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c3_3 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 416988*s*s*s*s + 1042470*r*s*s*s + 833976*r*r*s*s + 208494*r*r*r*s + 5894694*s*s*s + 10538424*r*s*s + 4852224*r*r*s + 208494*r*r*r + 25891164*s*s + 28658448*r*s + 4018248*r*r + 35766198*s + 19162494*r + 15352740 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(4,3), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c4_3 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 3752892*s*s*s*s + 9382230*r*s*s*s + 7505784*r*r*s*s + 1876446*r*r*r*s + 60837966*s*s*s + 109223154*r*s*s + 50261634*r*r*s + 1876446*r*r*r + 308450106*s*s + 347036076*r*s + 42755850*r*r + 504829584*s + 247195152*r + 253464552 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(5,3), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c5_3 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 11258676*s*s*s*s + 28146690*r*s*s*s + 22517352*r*r*s*s + 5629338*r*r*r*s + 205871058*s*s*s + 370801476*r*s*s + 170559756*r*r*s + 5629338*r*r*r + 1187173584*s*s + 1354435344*r*s + 148042404*r*r + 2306187126*s + 1011780558*r + 1313625924 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(0,4), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c0_4 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 197964*s*s*s*s + 296946*r*s*s*s + 98982*r*r*s*s + 2554470*s*s*s + 3086586*r*s*s + 824850*r*r*s + 9802620*s*s + 7277904*r*s + 725868*r*r + 13394430*s + 4488264*r + 5948316 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(1,4), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c1_4 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 593892*s*s*s*s + 1484730*r*s*s*s + 1187784*r*r*s*s + 296946*r*r*r*s + 5789718*s*s*s + 10153674*r*s*s + 4660902*r*r*s + 296946*r*r*r + 17722746*s*s + 18752904*r*s + 3473118*r*r + 18547920*s + 10083960*r + 6021000 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(2,4), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c2_4 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 1781676*s*s*s*s + 4454190*r*s*s*s + 3563352*r*r*s*s + 890838*r*r*r*s + 21250350*s*s*s + 37471572*r*s*s + 17112060*r*r*s + 890838*r*r*r + 77160600*s*s + 82483272*r*s + 13548708*r*r + 84007530*s + 49465890*r + 26315604 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(3,4), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c3_4 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 1781676*s*s*s*s + 4454190*r*s*s*s + 3563352*r*r*s*s + 890838*r*r*r*s + 25131546*s*s*s + 44482122*r*s*s + 20241414*r*r*s + 890838*r*r*r + 107269434*s*s + 115986816*r*s + 16678062*r*r + 131683644*s + 75958884*r + 47764080 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(4,4), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c4_4 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 16035084*s*s*s*s + 40087710*r*s*s*s + 32070168*r*r*s*s + 8017542*r*r*r*s + 261114678*s*s*s + 463434048*r*s*s + 210336912*r*r*s + 8017542*r*r*r + 1291452660*s*s + 1410924096*r*s + 178266744*r*r + 1863701622*s + 987577758*r + 817328556 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(5,4), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c5_4 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 48105252*s*s*s*s + 120263130*r*s*s*s + 96210504*r*r*s*s + 24052626*r*r*r*s + 888136326*s*s*s + 1579586994*r*s*s + 715503294*r*r*s + 24052626*r*r*r + 5017585986*s*s + 5530433112*r*s + 619292790*r*r + 8602100856*s + 4071109248*r + 4424545944 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(0,5), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c0_5 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 256932*s*s*s*s + 385398*r*s*s*s + 128466*r*r*s*s + 3610386*s*s*s + 4481568*r*s*s + 1241838*r*r*s + 14230242*s*s + 10648638*r*s + 1113372*r*r + 20513844*s + 6552468*r + 9637056 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(1,5), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c1_5 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 770796*s*s*s*s + 1926990*r*s*s*s + 1541592*r*r*s*s + 385398*r*r*r*s + 7414902*s*s*s + 12963888*r*s*s + 5934384*r*r*s + 385398*r*r*r + 22293684*s*s + 23464296*r*s + 4392792*r*r + 22539438*s + 12427398*r + 6889860 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(2,5), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c2_5 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 2312388*s*s*s*s + 5780970*r*s*s*s + 4624776*r*r*s*s + 1156194*r*r*r*s + 27411858*s*s*s + 48120318*r*s*s + 21864654*r*r*s + 1156194*r*r*r + 96993126*s*s + 102734244*r*s + 17239878*r*r + 95793840*s + 60394896*r + 23900184 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(3,5), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c3_5 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 2312388*s*s*s*s + 5780970*r*s*s*s + 4624776*r*r*s*s + 1156194*r*r*r*s + 32579010*s*s*s + 57348972*r*s*s + 25926156*r*r*s + 1156194*r*r*r + 135389880*s*s + 144522792*r*s + 21301380*r*r + 145740222*s + 92954790*r + 40616964 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(4,5), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c4_5 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 20811492*s*s*s*s + 52028730*r*s*s*s + 41622984*r*r*s*s + 10405746*r*r*r*s + 339715458*s*s*s + 599198634*r*s*s + 269888922*r*r*s + 10405746*r*r*r + 1638641826*s*s + 1761826788*r*s + 228265938*r*r + 2055304692*s + 1214656884*r + 735566832 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Loaded donor: step gain Phi2>0 (num>=0), cell (ca,cb)=(5,5), all p>=q>=1 (p=1+s+r,q=1+s). -/
theorem dich_inc_c5_5 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 62434476*s*s*s*s + 156086190*r*s*s*s + 124868952*r*r*s*s + 31217238*r*r*r*s + 1158659478*s*s*s + 2046769560*r*s*s + 919327320*r*r*s + 31217238*r*r*r + 6400010556*s*s + 6923919528*r*s + 794458368*r*r + 9573780582*s + 5033236158*r + 4269995028 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- De-loaded donor: step gain Phi2<0 (-num>=0), cell (ca,cb)=(2,0), all p>=q>=1. -/
theorem dich_dec_c2_0 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 4212*s*s*s*s + 10530*r*s*s*s + 8424*r*r*s*s + 2106*r*r*r*s + 41922*s*s*s + 63252*r*s*s + 23436*r*r*s + 2106*r*r*r + 131664*s*s + 86616*r*s + 15012*r*r + 139230*s + 33894*r + 45276 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- De-loaded donor: step gain Phi2<0 (-num>=0), cell (ca,cb)=(3,0), all p>=q>=1. -/
theorem dich_dec_c3_0 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 4212*s*s*s*s + 10530*r*s*s*s + 8424*r*r*s*s + 2106*r*r*r*s + 57510*s*s*s + 86238*r*s*s + 30834*r*r*s + 2106*r*r*r + 246510*s*s + 159408*r*s + 22410*r*r + 343548*s + 83700*r + 150336 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- De-loaded donor: step gain Phi2<0 (-num>=0), cell (ca,cb)=(4,0), all p>=q>=1. -/
theorem dich_dec_c4_0 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 37908*s*s*s*s + 94770*r*s*s*s + 75816*r*r*s*s + 18954*r*r*r*s + 657882*s*s*s + 983016*r*s*s + 344088*r*r*s + 18954*r*r*r + 3536244*s*s + 2244672*r*s + 268272*r*r + 5911218*s + 1356426*r + 2994948 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- De-loaded donor: step gain Phi2<0 (-num>=0), cell (ca,cb)=(5,0), all p>=q>=1. -/
theorem dich_dec_c5_0 (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 113724*s*s*s*s + 284310*r*s*s*s + 227448*r*r*s*s + 56862*r*r*r*s + 2394522*s*s*s + 3569670*r*s*s + 1232010*r*r*s + 56862*r*r*r + 15413814*s*s + 9628632*r*s + 1004562*r*r + 29669328*s + 6343272*r + 16536312 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Mixed cell (ca,cb)=(0,0), decreasing tail q>=3: Phi2<0 (-num>=0). -/
theorem dich_mix_c0_0_qtail (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 156*s*s*s + 234*r*s*s + 78*r*r*s + 1022*s*s + 1022*r*s + 234*r*r + 1920*s + 960*r + 774 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs]

/-- Mixed cell (ca,cb)=(1,0), decreasing tail q>=2: Phi2<0 (-num>=0). -/
theorem dich_mix_c1_0_qtail (r : ℝ) (s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (0:ℝ) < 1404*s*s*s*s + 3510*r*s*s*s + 2808*r*r*s*s + 702*r*r*r*s + 14394*s*s*s + 23952*r*s*s + 10962*r*r*s + 1404*r*r*r + 50884*s*s + 47718*r*s + 10692*r*r + 72194*s + 27708*r + 33540 := by
  nlinarith [hr, hs, mul_nonneg hs hs, mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg (mul_nonneg hs hs) hs, mul_nonneg (mul_nonneg hr hs) hs, mul_nonneg (mul_nonneg hr hr) hs, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hs) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hs) hs, mul_nonneg (mul_nonneg (mul_nonneg hr hr) hr) hs]

/-- Mixed cell (0,0), q=1, p>=4: Phi2<0 (-num>=0). -/
theorem dich_mix_c0_0_q1 (r : ℝ) (hr : 0 ≤ r) :
    (0:ℝ) < 78*r*r + 320*r + 32 := by
  nlinarith [hr, mul_nonneg hr hr]

/-- Mixed cell (0,0), q=2, p>=3: Phi2<0 (-num>=0). -/
theorem dich_mix_c0_0_q2 (r : ℝ) (hr : 0 ≤ r) :
    (0:ℝ) < 156*r*r + 484*r + 48 := by
  nlinarith [hr, mul_nonneg hr hr]

/-- Mixed cell (1,0), q=1, p>=2: Phi2<0 (-num>=0). -/
theorem dich_mix_c1_0_q1 (r : ℝ) (hr : 0 ≤ r) :
    (0:ℝ) < 702*r*r*r + 4644*r*r + 7614*r + 2912 := by
  nlinarith [hr, mul_nonneg hr hr, mul_nonneg (mul_nonneg hr hr) hr]

/-- Mixed cell (0,0), increasing corner (p,q)=(1,1): Phi2 = 113/3174 > 0 (step INCREASES). -/
theorem dich_mix_c0_0_exc_p1_q1 : (0:ℝ) < (113/3174 : ℝ) := by norm_num

/-- Mixed cell (0,0), increasing corner (p,q)=(2,1): Phi2 = 37/1587 > 0 (step INCREASES). -/
theorem dich_mix_c0_0_exc_p2_q1 : (0:ℝ) < (37/1587 : ℝ) := by norm_num

/-- Mixed cell (0,0), increasing corner (p,q)=(2,2): Phi2 = 56/4761 > 0 (step INCREASES). -/
theorem dich_mix_c0_0_exc_p2_q2 : (0:ℝ) < (56/4761 : ℝ) := by norm_num

/-- Mixed cell (0,0), increasing corner (p,q)=(3,1): Phi2 = 21/2116 > 0 (step INCREASES). -/
theorem dich_mix_c0_0_exc_p3_q1 : (0:ℝ) < (21/2116 : ℝ) := by norm_num

/-- Mixed cell (1,0), increasing corner (p,q)=(1,1): Phi2 = 19/6348 > 0 (step INCREASES). -/
theorem dich_mix_c1_0_exc_p1_q1 : (0:ℝ) < (19/6348 : ℝ) := by norm_num


end R3Cert.Step3
