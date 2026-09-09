/-
  A3(2): the PairCollapse6 POLYNOMIAL layer -- auto-generated, do not edit by hand.

  For every cell (d = cA + cb, candidate (x,y,c'), cA) of the frozen selection table, the three
  cleared clause numerators (W1, W2' at weight 1/6, ROOT) as integer-coefficient polynomial
  inequalities over the Capped region.  Every cell was numerically self-checked on a dense
  exact grid before emission (proof/verification/gen_pc6_cells.py); nlinarith discharges with a
  uniform product-hint battery.  The bridge layer (rational cavity forms -> these polynomials)
  and the assembly into `PairCollapse6` are separate, upcoming files.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3
namespace PC6

set_option maxHeartbeats 1000000

theorem pc6_d0p_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a4 + b4) :
    (0:ℝ) ≤ 23218*a5^2*b5 + 11362*a5^2*b4 + 79534*a5^2 + 47000*a5*a4*b5 + 23000*a5*a4*b4 + 161000*a5*a4 + 23218*a5*b5^2 + 47000*a5*b5*b4 + 742127*a5*b5 + 23782*a5*b4^2 + 674291*a5*b4 + 661871*a5 + 23782*a4^2*b5 + 11638*a4^2*b4 + 81466*a4^2 + 11362*a4*b5^2 + 23000*a4*b5*b4 + 697199*a4*b5 + 11638*a4*b4^2 + 627923*a4*b4 + 634271*a4 + 159068*b5^2 + 322000*b5*b4 + 1446976*b5 + 162932*b4^2 + 1366936*b4 + 158700 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d0p_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a4 + b4) :
    (0:ℝ) ≤ 139308*a5^2*b5 + 68172*a5^2*b4 + 477204*a5^2 + 282000*a5*a4*b5 + 138000*a5*a4*b4 + 966000*a5*a4 + 139308*a5*b5^2 + 282000*a5*b5*b4 + 4473301*a5*b5 + 142692*a5*b4^2 + 4055797*a5*b4 + 4041583*a5 + 142692*a4^2*b5 + 69828*a4^2*b4 + 488796*a4^2 + 68172*a4*b5^2 + 138000*a4*b5*b4 + 4203733*a4*b5 + 69828*a4*b4^2 + 3777589*a4*b4 + 3875983*a4 + 522652*b5^2 + 1058000*b5*b4 + 7045728*b5 + 535348*b4^2 + 6513048*b4 + (-52900) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ a4 + b4 - 1),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a4 + b4 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d0p_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a4 + b4) :
    (0:ℝ) ≤ 11609*a5^2*b5 + 5681*a5^2*b4 + 39767*a5^2 + 23500*a5*a4*b5 + 11500*a5*a4*b4 + 80500*a5*a4 + 11609*a5*b5^2 + 23500*a5*b5*b4 + 349185*a5*b5 + 11891*a5*b4^2 + 326439*a5*b4 + 255990*a5 + 11891*a4^2*b5 + 5819*a4^2*b4 + 40733*a4^2 + 5681*a4*b5^2 + 11500*a4*b5*b4 + 326439*a4*b5 + 5819*a4*b4^2 + 303117*a4*b4 + 241224*a4 + 39767*b5^2 + 80500*b5*b4 + 255990*b5 + 40733*b4^2 + 241224*b4 + (-281957) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ a4 + b4 - 1),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a4 + b4 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d0f_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 0) :
    (0:ℝ) ≤ 7768525320146708*a5^2*b5 + 4787693968271708*a5^2*b4 + 21927474241552958*a5^2 + 15725759757382000*a5*a4*b5 + 9691688194882000*a5*a4*b4 + 44387599679257000*a5*a4 + 7768525320146708*a5*b5^2 + 15725759757382000*a5*b5*b4 + 150826754768431178*a5*b5 + 7957234437235292*a5*b4^2 + 136799191284269762*a5*b4 + 114558806619300095*a5 + 7957234437235292*a4^2*b5 + 4903994226610292*a4^2*b4 + 22460125437704042*a4^2 + 4787693968271708*a4*b5^2 + 9691688194882000*a4*b5*b4 + 142605621026045846*a4*b5 + 4903994226610292*a4*b4^2 + 128288422106884430*a4*b4 + 110350330465977263*a4 + 43854948483105916*b5^2 + 88775199358514000*b5*b4 + 256238934348697399*b5 + 44920250875408084*b4^2 + 241482901104124567*b4 + (-544822914017892) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ -(a4 + b4)),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ -(a4 + b4))]

set_option maxHeartbeats 4000000 in
theorem pc6_d0f_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 0) :
    (0:ℝ) ≤ 46611151920880248*a5^2*b5 + 28726163809630248*a5^2*b4 + 131564845449317748*a5^2 + 94354558544292000*a5*a4*b5 + 58150129169292000*a5*a4*b4 + 266325598075542000*a5*a4 + 46611151920880248*a5*b5^2 + 94354558544292000*a5*b5*b4 + 911832685624563002*a5*b5 + 47743406623411752*a5*b4^2 + 825030415446782006*a5*b4 + 706750220775635879*a5 + 47743406623411752*a4^2*b5 + 29423965359661752*a4^2*b4 + 134760752626224252*a4^2 + 28726163809630248*a4*b5^2 + 58150129169292000*a4*b5*b4 + 862505883170251010*a4*b5 + 29423965359661752*a4*b4^2 + 773965800382470014*a4*b4 + 681499363855698887*a4 + 154577749167854246*b5^2 + 312910423416709000*b5*b4 + 1238047318973651887*b5 + 158332674248854754*b4^2 + 1138963562414964895*b4 + (-156527610734280484) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ -(a4 + b4)),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ -(a4 + b4))]

set_option maxHeartbeats 4000000 in
theorem pc6_d0f_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 0) :
    (0:ℝ) ≤ 3884262660073354*a5^2*b5 + 2393846984135854*a5^2*b4 + 10963737120776479*a5^2 + 7862879878691000*a5*a4*b5 + 4845844097441000*a5*a4*b4 + 22193799839628500*a5*a4 + 3884262660073354*a5*b5^2 + 7862879878691000*a5*b5*b4 + 68093036217154268*a5*b5 + 3978617218617646*a5*b4^2 + 63888114787417310*a5*b4 + 36616975658955914*a5 + 3978617218617646*a4^2*b5 + 2451997113305146*a4^2*b4 + 11230062718852021*a4^2 + 2393846984135854*a4*b5^2 + 4845844097441000*a4*b5*b4 + 63888114787417310*a4*b5 + 2451997113305146*a4*b4^2 + 59574580069555352*a4*b4 + 34246411984218956*a4 + 10963737120776479*b5^2 + 22193799839628500*b5*b4 + 36616975658955914*b5 + 11230062718852021*b4^2 + 34246411984218956*b4 + (-57848255100883065) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ -(a4 + b4)),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ -(a4 + b4))]

theorem pc6_d1p_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a4 + b4) :
    (0:ℝ) ≤ 3158142*a5^2*b5 + 1806558*a5^2*b4 + 2749604*a5^2 + 6393000*a5*a4*b5 + 3657000*a5*a4*b4 + 5566000*a5*a4 + 3158142*a5*b5^2 + 6393000*a5*b5*b4 + 80823371*a5*b5 + 3234858*a5*b4^2 + 74530787*a5*b4 + 88462922*a5 + 3234858*a4^2*b5 + 1850442*a4^2*b4 + 2816396*a4^2 + 1806558*a4*b5^2 + 3657000*a4*b5*b4 + 74132243*a4*b5 + 1850442*a4*b4^2 + 67675499*a4*b4 + 80227082*a4 + 19156332*b5^2 + 38778000*b5*b4 + 170496562*b5 + 19621668*b4^2 + 164253442*b4 + 114814160 := by
  positivity

theorem pc6_d1p_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a4 + b4) :
    (0:ℝ) ≤ 18948852*a5^2*b5 + 10839348*a5^2*b4 + 16497624*a5^2 + 38358000*a5*a4*b5 + 21942000*a5*a4*b4 + 33396000*a5*a4 + 18948852*a5*b5^2 + 38358000*a5*b5*b4 + 487733967*a5*b5 + 19409148*a5*b4^2 + 448782831*a5*b4 + 533209874*a5 + 19409148*a4^2*b5 + 11102652*a4^2*b4 + 16898376*a4^2 + 10839348*a4*b5^2 + 21942000*a4*b5*b4 + 447587199*a4*b5 + 11102652*a4*b4^2 + 407651103*a4*b4 + 483794834*a4 + 65717808*b5^2 + 133032000*b5*b4 + 779310794*b5 + 67314192*b4^2 + 735873914*b4 + 388963120 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d1p_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a4 + b4) :
    (0:ℝ) ≤ 1579071*a5^2*b5 + 903279*a5^2*b4 + 1374802*a5^2 + 3196500*a5*a4*b5 + 1828500*a5*a4*b4 + 2783000*a5*a4 + 1579071*a5*b5^2 + 3196500*a5*b5*b4 + 37435744*a5*b5 + 1617429*a5*b4^2 + 35563060*a5*b4 + 41640488*a5 + 1617429*a4^2*b5 + 925221*a4^2*b4 + 1408198*a4^2 + 903279*a4*b5^2 + 1828500*a4*b5*b4 + 34051822*a4*b5 + 925221*a4*b4^2 + 32113474*a4*b4 + 37489172*a4 + 4789083*b5^2 + 9694500*b5*b4 + 30342037*b5 + 4905417*b4^2 + 29379073*b4 + (-5168330) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ a4 + b4 - 2),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a4 + b4 - 2)]

theorem pc6_d1p_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a4 + b4) :
    (0:ℝ) ≤ 3158142*a5^2*b5 + 1806558*a5^2*b4 + 9578166*a5^2 + 6393000*a5*a4*b5 + 3657000*a5*a4*b4 + 19389000*a5*a4 + 3158142*a5*b5^2 + 6393000*a5*b5*b4 + 80823371*a5*b5 + 3234858*a5*b4^2 + 71508311*a5*b4 + 78735233*a5 + 3234858*a4^2*b5 + 1850442*a4^2*b4 + 9810834*a4^2 + 1806558*a4*b5^2 + 3657000*a4*b5*b4 + 77154719*a4*b5 + 1850442*a4*b4^2 + 67675499*a4*b4 + 77041973*a4 + 12327770*b5^2 + 24955000*b5*b4 + 178736703*b5 + 12627230*b4^2 + 163094403*b4 + 67968565 := by
  positivity

theorem pc6_d1p_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a4 + b4) :
    (0:ℝ) ≤ 2105428*a5^2*b5 + 1204372*a5^2*b4 + 6385444*a5^2 + 4262000*a5*a4*b5 + 2438000*a5*a4*b4 + 12926000*a5*a4 + 2105428*a5*b5^2 + 4262000*a5*b5*b4 + 54192663*a5*b5 + 2156572*a5*b4^2 + 47849775*a5*b4 + 53431599*a5 + 2156572*a4^2*b5 + 1233628*a4^2*b4 + 6540556*a4^2 + 1204372*a4*b5^2 + 2438000*a4*b5*b4 + 51746895*a4*b5 + 1233628*a4*b4^2 + 45294567*a4*b4 + 52302759*a4 + 2749604*b5^2 + 5566000*b5*b4 + 104313349*b5 + 2816396*b4^2 + 93220909*b4 + 38460945 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d1p_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a4 + b4) :
    (0:ℝ) ≤ 1579071*a5^2*b5 + 903279*a5^2*b4 + 4789083*a5^2 + 3196500*a5*a4*b5 + 1828500*a5*a4*b4 + 9694500*a5*a4 + 1579071*a5*b5^2 + 3196500*a5*b5*b4 + 37435744*a5*b5 + 1617429*a5*b4^2 + 34051822*a5*b4 + 30342037*a5 + 1617429*a4^2*b5 + 925221*a4^2*b4 + 4905417*a4^2 + 903279*a4*b5^2 + 1828500*a4*b5*b4 + 35563060*a4*b5 + 925221*a4*b4^2 + 32113474*a4*b4 + 29379073*a4 + 1374802*b5^2 + 2783000*b5*b4 + 41640488*b5 + 1408198*b4^2 + 37489172*b4 + (-5168330) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ a4 + b4 - 2),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a4 + b4 - 2)]

theorem pc6_d1f_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 1) :
    (0:ℝ) ≤ 23305575960440124*a5^2*b5 + 14363081904815124*a5^2*b4 + 23012903718536498*a5^2 + 47177279272146000*a5*a4*b5 + 29075064584646000*a5*a4*b4 + 46584825341167000*a5*a4 + 23305575960440124*a5*b5^2 + 47177279272146000*a5*b5*b4 + 503274468321637394*a5*b5 + 23871703311705876*a5*b4^2 + 461757905220418898*a5*b4 + 512700988320186167*a5 + 23871703311705876*a4^2*b5 + 14711982679830876*a4^2*b4 + 23571921622630502*a4^2 + 14363081904815124*a4*b5^2 + 29075064584646000*a4*b5*b4 + 459121015947606398*a4*b5 + 14711982679830876*a4*b4^2 + 416518319965137902*a4*b4 + 458444349399311675*a4 + 131564845449317748*b5^2 + 266325598075542000*b5*b4 + 1055460696974092417*b5 + 134760752626224252*b4^2 + 1014388504417280425*b4 + 595169312528023217 := by
  positivity

theorem pc6_d1f_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 1) :
    (0:ℝ) ≤ 139833455762640744*a5^2*b5 + 86178491428890744*a5^2*b4 + 138077422311218988*a5^2 + 283063675632876000*a5*a4*b5 + 174450387507876000*a5*a4*b4 + 279508952047002000*a5*a4 + 139833455762640744*a5*b5^2 + 283063675632876000*a5*b5*b4 + 3040263280971752166*a5*b5 + 143230219870235256*a5*b4^2 + 2783253234546003690*a5*b4 + 3096563498595206981*a5 + 143230219870235256*a4^2*b5 + 88271896078985256*a4^2*b4 + 141431529735783012*a4^2 + 86178491428890744*a4*b5^2 + 174450387507876000*a4*b5*b4 + 2775342566727566190*a4*b5 + 88271896078985256*a4*b4^2 + 2511815723014317714*a4*b4 + 2771023665069960029*a4 + 463733247503562738*b5^2 + 938731270250127000*b5*b4 + 4724842624556925731*b5 + 474998022746564262*b4^2 + 4438856130123866279*b4 + 1595169941132959885 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d1f_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 1) :
    (0:ℝ) ≤ 11652787980220062*a5^2*b5 + 7181540952407562*a5^2*b4 + 11506451859268249*a5^2 + 23588639636073000*a5*a4*b5 + 14537532292323000*a5*a4*b4 + 23292412670583500*a5*a4 + 11652787980220062*a5*b5^2 + 23588639636073000*a5*b5*b4 + 229676210659634734*a5*b5 + 11935851655852938*a5*b4^2 + 217344510046056736*a5*b4 + 234665257963779845*a5 + 11935851655852938*a4^2*b5 + 7355991339915438*a4^2*b4 + 11785960811315251*a4^2 + 7181540952407562*a4*b5^2 + 14537532292323000*a4*b5*b4 + 207316420796986360*a4*b5 + 7355991339915438*a4*b4^2 + 194550267030908362*a4*b4 + 207257429551295597*a4 + 32891211362329437*b5^2 + 66581399518885500*b5*b4 + 181536900458867797*b5 + 33690188156556063*b4^2 + 175224186228883549*b4 + (-77446570996113404) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ 1 - (a4 + b4)),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ 1 - (a4 + b4))]

theorem pc6_d1f_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 1) :
    (0:ℝ) ≤ 23305575960440124*a5^2*b5 + 14363081904815124*a5^2*b4 + 65782422724658874*a5^2 + 47177279272146000*a5*a4*b5 + 29075064584646000*a5*a4*b4 + 133162799037771000*a5*a4 + 23305575960440124*a5*b5^2 + 47177279272146000*a5*b5*b4 + 503274468321637394*a5*b5 + 23871703311705876*a5*b4^2 + 441701726722278146*a5*b4 + 487048366821900395*a5 + 23871703311705876*a4^2*b5 + 14711982679830876*a4^2*b4 + 67380376313112126*a4^2 + 14363081904815124*a4*b5^2 + 29075064584646000*a4*b5*b4 + 479177194445747150*a4*b5 + 14711982679830876*a4*b4^2 + 416518319965137902*a4*b4 + 476020891950385151*a4 + 88795326443195372*b5^2 + 179747624378938000*b5*b4 + 1066450564117747941*b5 + 90952297935742628*b4^2 + 963131964697795197*b4 + 326343587289865069 := by
  positivity

theorem pc6_d1f_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 1) :
    (0:ℝ) ≤ 15537050640293416*a5^2*b5 + 9575387936543416*a5^2*b4 + 43854948483105916*a5^2 + 31451519514764000*a5*a4*b5 + 19383376389764000*a5*a4*b4 + 88775199358514000*a5*a4 + 15537050640293416*a5*b5^2 + 31451519514764000*a5*b5*b4 + 337807031219083574*a5*b5 + 15914468874470584*a5*b4^2 + 295879573728573242*a5*b4 + 331164704901212033*a5 + 15914468874470584*a4^2*b5 + 9807988453220584*a4^2*b4 + 44920250875408084*a4^2 + 9575387936543416*a4*b5^2 + 19383376389764000*a4*b5*b4 + 321742181968490078*a4*b5 + 9807988453220584*a4*b4^2 + 279090635890479746*a4*b4 + 323813054986868537*a4 + 23012903718536498*b5^2 + 46584825341167000*b5*b4 + 613462332710313103*b5 + 23571921622630502*b4^2 + 540188450975657107*b4 + 172941960796464105 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d1f_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a4 + b4 ≤ 1) :
    (0:ℝ) ≤ 11652787980220062*a5^2*b5 + 7181540952407562*a5^2*b4 + 32891211362329437*a5^2 + 23588639636073000*a5*a4*b5 + 14537532292323000*a5*a4*b4 + 66581399518885500*a5*a4 + 11652787980220062*a5*b5^2 + 23588639636073000*a5*b5*b4 + 229676210659634734*a5*b5 + 11935851655852938*a5*b4^2 + 207316420796986360*a5*b4 + 181536900458867797*a5 + 11935851655852938*a4^2*b5 + 7355991339915438*a4^2*b4 + 33690188156556063*a4^2 + 7181540952407562*a4*b5^2 + 14537532292323000*a4*b5*b4 + 217344510046056736*a4*b5 + 7355991339915438*a4*b4^2 + 194550267030908362*a4*b4 + 175224186228883549*a4 + 11506451859268249*b5^2 + 23292412670583500*b5*b4 + 234665257963779845*b5 + 11785960811315251*b4^2 + 207257429551295597*b4 + (-77446570996113404) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h5 (by linarith : (0:ℝ) ≤ 1 - (a4 + b4)),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ 1 - (a4 + b4))]

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 212818164*a5^2*b5 + 161689164*a5^2*b4 + 125744242*a5^2 + 430806000*a5*a4*b5 + 327306000*a5*a4*b4 + 254543000*a5*a4 + 212818164*a5*b5^2 + 430806000*a5*b5*b4 + 1364219722*a5*b5 + 217987836*a5*b4^2 + 1340398738*a5*b4 + 135795565*a5 + 217987836*a4^2*b5 + 165616836*a4^2*b4 + 128798758*a4^2 + 161689164*a4*b5^2 + 327306000*a4*b5*b4 + 1208717566*a4*b5 + 165616836*a4*b4^2 + 1182412582*a4*b4 + 141904597*a4 + 911361828*b5^2 + 1844862000*b5*b4 + 1805553413*b5 + 933500172*b4^2 + 1962427445*b4 + (-231385838) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 1276908984*a5^2*b5 + 970134984*a5^2*b4 + 754465452*a5^2 + 2584836000*a5*a4*b5 + 1963836000*a5*a4*b4 + 1527258000*a5*a4 + 1276908984*a5*b5^2 + 2584836000*a5*b5*b4 + 8373580554*a5*b5 + 1307927016*a5*b4^2 + 8185425150*a5*b4 + 926008681*a5 + 1307927016*a4^2*b5 + 993701016*a4^2*b4 + 772792548*a4^2 + 970134984*a4*b5^2 + 1963836000*a4*b5*b4 + 7440567618*a4*b5 + 993701016*a4*b4^2 + 7237508214*a4*b4 + 962662873*a4 + 3606223218*b5^2 + 7300047000*b5*b4 + 5170450297*b5 + 3693823782*b4^2 + 6021235489*b4 + (-1165844446) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 106409082*a5^2*b5 + 80844582*a5^2*b4 + 62872121*a5^2 + 215403000*a5*a4*b5 + 163653000*a5*a4*b4 + 127271500*a5*a4 + 106409082*a5*b5^2 + 215403000*a5*b5*b4 + 481569668*a5*b5 + 108993918*a5*b4^2 + 517838426*a5*b4 + (-50591984)*a5 + 108993918*a4^2*b5 + 82808418*a4^2*b4 + 64399379*a4^2 + 80844582*a4*b5^2 + 163653000*a4*b5*b4 + 401233754*a4*b5 + 82808418*a4*b4^2 + 436881512*a4*b4 + (-49064726)*a4 + 227840457*b5^2 + 461215500*b5*b4 + (-54519664)*b5 + 233375043*b4^2 + 7313594*b4 + (-113464105) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 638454492*a5^2*b5 + 485067492*a5^2*b4 + 872137734*a5^2 + 1292418000*a5*a4*b5 + 981918000*a5*a4*b4 + 1765461000*a5*a4 + 638454492*a5*b5^2 + 1292418000*a5*b5*b4 + 4092659166*a5*b5 + 653963508*a5*b4^2 + 3671382198*a5*b4 + (-503378761)*a5 + 653963508*a4^2*b5 + 496850508*a4^2*b4 + 893323266*a4^2 + 485067492*a4*b5^2 + 981918000*a4*b5*b4 + 3975966714*a4*b5 + 496850508*a4*b4^2 + 3547237746*a4*b4 + (-123215665)*a4 + 2239180476*b5^2 + 4532754000*b5*b4 + 1935138695*b5 + 2293573524*b4^2 + 2043924791*b4 + (-5086444514) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 425636328*a5^2*b5 + 323378328*a5^2*b4 + 581425156*a5^2 + 861612000*a5*a4*b5 + 654612000*a5*a4*b4 + 1176974000*a5*a4 + 425636328*a5*b5^2 + 861612000*a5*b5*b4 + 2791193518*a5*b5 + 435975672*a5*b4^2 + 2495265706*a5*b4 + (-249862901)*a5 + 435975672*a4^2*b5 + 331233672*a4^2*b4 + 595548844*a4^2 + 323378328*a4*b5^2 + 654612000*a4*b5*b4 + 2713398550*a4*b5 + 331233672*a4*b4^2 + 2412502738*a4*b4 + 3579163*a4 + 872137734*b5^2 + 1765461000*b5*b4 + 817920227*b5 + 893323266*b4^2 + 860291291*b4 + (-1852710482) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 319227246*a5^2*b5 + 242533746*a5^2*b4 + 436068867*a5^2 + 646209000*a5*a4*b5 + 490959000*a5*a4*b4 + 882730500*a5*a4 + 319227246*a5*b5^2 + 646209000*a5*b5*b4 + 1444709004*a5*b5 + 326981754*a5*b4^2 + 1378608270*a5*b4 + (-1073511476)*a5 + 326981754*a4^2*b5 + 248425254*a4^2*b4 + 446661633*a4^2 + 242533746*a4*b5^2 + 490959000*a4*b5*b4 + 1378608270*a4*b5 + 248425254*a4*b4^2 + 1310644536*a4*b4 + (-894022694)*a4 + 436068867*b5^2 + 882730500*b5*b4 + (-1073511476)*b5 + 446661633*b4^2 + (-894022694)*b4 + (-1002892295) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 212818164*a5^2*b5 + 161689164*a5^2*b4 + 455680914*a5^2 + 430806000*a5*a4*b5 + 327306000*a5*a4*b4 + 922431000*a5*a4 + 212818164*a5*b5^2 + 430806000*a5*b5*b4 + 1364219722*a5*b5 + 217987836*a5*b4^2 + 1107189394*a5*b4 + 749743933*a5 + 217987836*a4^2*b5 + 165616836*a4^2*b4 + 466750086*a4^2 + 161689164*a4*b5^2 + 327306000*a4*b5*b4 + 1441926910*a4*b5 + 165616836*a4*b4^2 + 1182412582*a4*b4 + 884479621*a4 + 581425156*b5^2 + 1176974000*b5*b4 + 705664389*b5 + 595548844*b4^2 + 508717077*b4 + (-520281142) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

theorem pc6_d2p_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 425636328*a5^2*b5 + 323378328*a5^2*b4 + 911361828*a5^2 + 861612000*a5*a4*b5 + 654612000*a5*a4*b4 + 1844862000*a5*a4 + 425636328*a5*b5^2 + 861612000*a5*b5*b4 + 2791193518*a5*b5 + 435975672*a5*b4^2 + 2262056362*a5*b4 + 1633855315*a5 + 435975672*a4^2*b5 + 331233672*a4^2*b4 + 933500172*a4^2 + 323378328*a4*b5^2 + 654612000*a4*b5*b4 + 2946607894*a4*b5 + 331233672*a4*b4^2 + 2412502738*a4*b4 + 1903326691*a4 + 542201062*b5^2 + 1097573000*b5*b4 + 2354607699*b5 + 555371938*b4^2 + 1930560075*b4 + 594979262 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d2p_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 2 ≤ a5 + b5) :
    (0:ℝ) ≤ 106409082*a5^2*b5 + 80844582*a5^2*b4 + 227840457*a5^2 + 215403000*a5*a4*b5 + 163653000*a5*a4*b4 + 461215500*a5*a4 + 106409082*a5*b5^2 + 215403000*a5*b5*b4 + 481569668*a5*b5 + 108993918*a5*b4^2 + 401233754*a5*b4 + (-54519664)*a5 + 108993918*a4^2*b5 + 82808418*a4^2*b4 + 233375043*a4^2 + 80844582*a4*b5^2 + 163653000*a4*b5*b4 + 517838426*a4*b5 + 82808418*a4*b4^2 + 436881512*a4*b4 + 7313594*a4 + 62872121*b5^2 + 127271500*b5*b4 + (-50591984)*b5 + 64399379*b4^2 + (-49064726)*b4 + (-113464105) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)]

set_option maxHeartbeats 4000000 in
theorem pc6_d2f_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 139608846*a5^2*b5 + 88248654*a5^2*b4 + (-96202054)*a5^2 + 282609000*a5*a4*b5 + 178641000*a5*a4*b4 + (-194741000)*a5*a4 + 139608846*a5*b5^2 + 282609000*a5*b5*b4 + 2967421317*a5*b5 + 143000154*a5*b4^2 + 2784006825*a5*b4 + 4049967305*a5 + 143000154*a4^2*b5 + 90392346*a4^2*b4 + (-98538946)*a4^2 + 88248654*a4*b5^2 + 178641000*a4*b5*b4 + 2653531965*a4*b5 + 90392346*a4*b4^2 + 2463879393*a4*b4 + 3545519345*a4 + 767139516*b5^2 + 1552914000*b5*b4 + 6768235530*b5 + 785774484*b4^2 + 6642404370*b4 + 8268931250 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d2f_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 837653076*a5^2*b5 + 529491924*a5^2*b4 + (-577212324)*a5^2 + 1695654000*a5*a4*b5 + 1071846000*a5*a4*b4 + (-1168446000)*a5*a4 + 837653076*a5*b5^2 + 1695654000*a5*b5*b4 + 17928028035*a5*b5 + 858000924*a5*b4^2 + 16782107067*a5*b4 + 24214702013*a5 + 858000924*a4^2*b5 + 542354076*a4^2*b4 + (-591233676)*a4^2 + 529491924*a4*b5^2 + 1071846000*a4*b5*b4 + 16044691923*a4*b5 + 542354076*a4*b4^2 + 14861342475*a4*b4 + 21188014253*a4 + 2732470104*b5^2 + 5531316000*b5*b4 + 29178609278*b5 + 2798845896*b4^2 + 28196452238*b4 + 31243274290 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d2f_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 69804423*a5^2*b5 + 44124327*a5^2*b4 + (-48101027)*a5^2 + 141304500*a5*a4*b5 + 89320500*a5*a4*b4 + (-97370500)*a5*a4 + 69804423*a5*b5^2 + 141304500*a5*b5*b4 + 1352156169*a5*b5 + 71500077*a5*b4^2 + 1308846027*a5*b4 + 2115635588*a5 + 71500077*a4^2*b5 + 45196173*a4^2*b4 + (-49269473)*a4^2 + 44124327*a4*b5^2 + 89320500*a4*b5*b4 + 1193515839*a4*b5 + 45196173*a4*b4^2 + 1147710465*a4*b4 + 1864580054*a4 + 191784879*b5^2 + 388228500*b5*b4 + 1216669962*b5 + 196443621*b4^2 + 1207929180*b4 + 868867159 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5))]

theorem pc6_d2f_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 418826538*a5^2*b5 + 264745962*a5^2*b4 + 431051556*a5^2 + 847827000*a5*a4*b5 + 535923000*a5*a4*b4 + 872574000*a5*a4 + 418826538*a5*b5^2 + 847827000*a5*b5*b4 + 8902263951*a5*b5 + 429000462*a5*b4^2 + 8006029911*a5*b4 + 8746797742*a5 + 429000462*a4^2*b5 + 271177038*a4^2*b4 + 441522444*a4^2 + 264745962*a4*b5^2 + 535923000*a4*b5*b4 + 8306586459*a4*b5 + 271177038*a4*b4^2 + 7391638179*a4*b4 + 8142134182*a4 + 1581760830*b5^2 + 3201945000*b5*b4 + 19295662987*b5 + 1620184170*b4^2 + 18009489187*b4 + 13776424310 := by
  positivity

theorem pc6_d2f_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 279217692*a5^2*b5 + 176497308*a5^2*b4 + 287367704*a5^2 + 565218000*a5*a4*b5 + 357282000*a5*a4*b4 + 581716000*a5*a4 + 279217692*a5*b5^2 + 565218000*a5*b5*b4 + 5976009345*a5*b5 + 286000308*a5*b4^2 + 5363375313*a5*b4 + 5873566810*a5 + 286000308*a4^2*b5 + 180784692*a4^2*b4 + 294348296*a4^2 + 176497308*a4*b5^2 + 357282000*a4*b5*b4 + 5578891017*a4*b5 + 180784692*a4*b4^2 + 4953780825*a4*b4 + 5470457770*a4 + 431051556*b5^2 + 872574000*b5*b4 + 10453487695*b5 + 441522444*b4^2 + 9520315135*b4 + 6737634950 := by
  positivity

theorem pc6_d2f_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 209413269*a5^2*b5 + 132372981*a5^2*b4 + 215525778*a5^2 + 423913500*a5*a4*b5 + 267961500*a5*a4*b4 + 436287000*a5*a4 + 209413269*a5*b5^2 + 423913500*a5*b5*b4 + 4056468507*a5*b5 + 214500231*a5*b4^2 + 3753542799*a5*b4 + 3967215674*a5 + 214500231*a4^2*b5 + 135588519*a4^2*b4 + 220761222*a4^2 + 132372981*a4*b5^2 + 267961500*a4*b5*b4 + 3753542799*a4*b5 + 135588519*a4*b4^2 + 3443131395*a4*b4 + 3659648450*a4 + 215525778*b5^2 + 436287000*b5*b4 + 3967215674*b5 + 220761222*b4^2 + 3659648450*b4 + 1269394748 := by
  positivity

theorem pc6_d2f_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 139608846*a5^2*b5 + 88248654*a5^2*b4 + 383569758*a5^2 + 282609000*a5*a4*b5 + 178641000*a5*a4*b4 + 776457000*a5*a4 + 139608846*a5*b5^2 + 282609000*a5*b5*b4 + 2967421317*a5*b5 + 143000154*a5*b4^2 + 2553346449*a5*b4 + 3156221391*a5 + 143000154*a4^2*b5 + 90392346*a4^2*b4 + 392887242*a4^2 + 88248654*a4*b5^2 + 178641000*a4*b5*b4 + 2884192341*a4*b5 + 90392346*a4*b4^2 + 2463879393*a4*b4 + 3148057311*a4 + 287367704*b5^2 + 581716000*b5*b4 + 7470529996*b5 + 294348296*b4^2 + 6629408956*b4 + 4593423380 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d2f_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 279217692*a5^2*b5 + 176497308*a5^2*b4 + 767139516*a5^2 + 565218000*a5*a4*b5 + 357282000*a5*a4*b4 + 1552914000*a5*a4 + 279217692*a5*b5^2 + 565218000*a5*b5*b4 + 5976009345*a5*b5 + 286000308*a5*b4^2 + 5132714937*a5*b4 + 6425546685*a5 + 286000308*a4^2*b5 + 180784692*a4^2*b4 + 785774484*a4^2 + 176497308*a4*b5^2 + 357282000*a4*b5*b4 + 5809551393*a4*b5 + 180784692*a4*b4^2 + 4953780825*a4*b4 + 6409218525*a4 + (-48720256)*b5^2 + (-98624000)*b5*b4 + 13930752700*b5 + (-49903744)*b4^2 + 12172787260*b4 + 9087743900 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d2f_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 1) :
    (0:ℝ) ≤ 69804423*a5^2*b5 + 44124327*a5^2*b4 + 191784879*a5^2 + 141304500*a5*a4*b5 + 89320500*a5*a4*b4 + 388228500*a5*a4 + 69804423*a5*b5^2 + 141304500*a5*b5*b4 + 1352156169*a5*b5 + 71500077*a5*b4^2 + 1193515839*a5*b4 + 1216669962*a5 + 71500077*a4^2*b5 + 45196173*a4^2*b4 + 196443621*a4^2 + 44124327*a4*b5^2 + 89320500*a4*b5*b4 + 1308846027*a4*b5 + 45196173*a4*b4^2 + 1147710465*a4*b4 + 1207929180*a4 + (-48101027)*b5^2 + (-97370500)*b5*b4 + 2115635588*b5 + (-49269473)*b4^2 + 1864580054*b4 + 868867159 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 675792*a5^2*b5 + 527592*a5^2*b4 + 122018*a5^2 + 1368000*a5*a4*b5 + 1068000*a5*a4*b4 + 247000*a5*a4 + 675792*a5*b5^2 + 1368000*a5*b5*b4 + 3780392*a5*b5 + 692208*a5*b4^2 + 3880256*a5*b4 + 130321*a5 + 692208*a4^2*b5 + 540408*a4^2*b4 + 124982*a4^2 + 527592*a4*b5^2 + 1068000*a4*b5*b4 + 3157724*a4*b5 + 540408*a4*b4^2 + 3250388*a4*b4 + 136249*a4 + 2759484*b5^2 + 5586000*b5*b4 + 6310641*b5 + 2826516*b4^2 + 7103169*b4 + (-227430) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 4054752*a5^2*b5 + 3165552*a5^2*b4 + 732108*a5^2 + 8208000*a5*a4*b5 + 6408000*a5*a4*b4 + 1482000*a5*a4 + 4054752*a5*b5^2 + 8208000*a5*b5*b4 + 23280168*a5*b5 + 4153248*a5*b4^2 + 23748252*a5*b4 + 889865*a5 + 4153248*a4^2*b5 + 3242448*a4^2*b4 + 749892*a4^2 + 3165552*a4*b5^2 + 6408000*a4*b5*b4 + 19544160*a4*b5 + 3242448*a4*b4^2 + 19969044*a4*b4 + 925433*a4 + 11159954*b5^2 + 22591000*b5*b4 + 15188353*b5 + 11431046*b4^2 + 19681321*b4 + (-1148702) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 337896*a5^2*b5 + 263796*a5^2*b4 + 61009*a5^2 + 684000*a5*a4*b5 + 534000*a5*a4*b4 + 123500*a5*a4 + 337896*a5*b5^2 + 684000*a5*b5*b4 + 1253392*a5*b5 + 346104*a5*b4^2 + 1442974*a5*b4 + (-49818)*a5 + 346104*a4^2*b5 + 270204*a4^2*b4 + 62491*a4^2 + 263796*a4*b5^2 + 534000*a4*b5*b4 + 933850*a4*b5 + 270204*a4*b4^2 + 1121632*a4*b4 + (-48336)*a4 + 689871*b5^2 + 1396500*b5*b4 + 85196*b5 + 706629*b4^2 + 348878*b4 + (-110827) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 6082128*a5^2*b5 + 4748328*a5^2*b4 + 4871334*a5^2 + 12312000*a5*a4*b5 + 9612000*a5*a4*b4 + 9861000*a5*a4 + 6082128*a5*b5^2 + 12312000*a5*b5*b4 + 34023528*a5*b5 + 6229872*a5*b4^2 + 31867560*a5*b4 + (-21700793)*a5 + 6229872*a4^2*b5 + 4863672*a4^2*b4 + 4989666*a4^2 + 4748328*a4*b5^2 + 9612000*a4*b5*b4 + 31474260*a4*b5 + 4863672*a4*b4^2 + 29253492*a4*b4 + (-17019497)*a4 + 21062184*b5^2 + 42636000*b5*b4 + 10680907*b5 + 21573816*b4^2 + 16148803*b4 + (-75109660) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 4054752*a5^2*b5 + 3165552*a5^2*b4 + 3247556*a5^2 + 8208000*a5*a4*b5 + 6408000*a5*a4*b4 + 6574000*a5*a4 + 4054752*a5*b5^2 + 8208000*a5*b5*b4 + 23280168*a5*b5 + 4153248*a5*b4^2 + 21711756*a5*b4 + (-13988389)*a5 + 4153248*a4^2*b5 + 3242448*a4^2*b4 + 3326444*a4^2 + 3165552*a4*b5^2 + 6408000*a4*b5*b4 + 21580656*a4*b5 + 3242448*a4*b4^2 + 19969044*a4*b4 + (-10867525)*a4 + 8644506*b5^2 + 17499000*b5*b4 + (-3194489)*b5 + 8854494*b4^2 + 188575*b4 + (-31131196) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 3041064*a5^2*b5 + 2374164*a5^2*b4 + 2435667*a5^2 + 6156000*a5*a4*b5 + 4806000*a5*a4*b4 + 4930500*a5*a4 + 3041064*a5*b5^2 + 6156000*a5*b5*b4 + 11280528*a5*b5 + 3114936*a5*b4^2 + 11459394*a5*b4 + (-15440692)*a5 + 3114936*a4^2*b5 + 2431836*a4^2*b4 + 2494833*a4^2 + 2374164*a4*b5^2 + 4806000*a4*b5*b4 + 9932022*a4*b5 + 2431836*a4*b4^2 + 10094688*a4*b4 + (-13159210)*a4 + 4322253*b5^2 + 8749500*b5*b4 + (-15035650)*b5 + 4427247*b4^2 + (-11967568)*b4 + (-13431727) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 6082128*a5^2*b5 + 4748328*a5^2*b4 + 8644506*a5^2 + 12312000*a5*a4*b5 + 9612000*a5*a4*b4 + 17499000*a5*a4 + 6082128*a5*b5^2 + 12312000*a5*b5*b4 + 34023528*a5*b5 + 6229872*a5*b4^2 + 28812816*a5*b4 + (-13779731)*a5 + 6229872*a4^2*b5 + 4863672*a4^2*b4 + 8854494*a4^2 + 4748328*a4*b5^2 + 9612000*a4*b5*b4 + 34529004*a4*b5 + 4863672*a4*b4^2 + 29253492*a4*b4 + (-7433579)*a4 + 17289012*b5^2 + 34998000*b5*b4 + (-4639211)*b5 + 17708988*b4^2 + (-3799259)*b4 + (-78434470) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 12164256*a5^2*b5 + 9496656*a5^2*b4 + 17289012*a5^2 + 24624000*a5*a4*b5 + 19224000*a5*a4*b4 + 34998000*a5*a4 + 12164256*a5*b5^2 + 24624000*a5*b5*b4 + 69840504*a5*b5 + 12459744*a5*b4^2 + 59025780*a5*b4 + (-25010441)*a5 + 12459744*a4^2*b5 + 9727344*a4^2*b4 + 17708988*a4^2 + 9496656*a4*b5^2 + 19224000*a4*b5*b4 + 70851456*a4*b5 + 9727344*a4*b4^2 + 59907132*a4*b4 + (-12318137)*a4 + 18387174*b5^2 + 37221000*b5*b4 + (-3142505)*b5 + 18833826*b4^2 + (-2249201)*b4 + (-79833706) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 3041064*a5^2*b5 + 2374164*a5^2*b4 + 4322253*a5^2 + 6156000*a5*a4*b5 + 4806000*a5*a4*b4 + 8749500*a5*a4 + 3041064*a5*b5^2 + 6156000*a5*b5*b4 + 11280528*a5*b5 + 3114936*a5*b4^2 + 9932022*a5*b4 + (-15035650)*a5 + 3114936*a4^2*b5 + 2431836*a4^2*b4 + 4427247*a4^2 + 2374164*a4*b5^2 + 4806000*a4*b5*b4 + 11459394*a4*b5 + 2431836*a4*b4^2 + 10094688*a4*b4 + (-11967568)*a4 + 2435667*b5^2 + 4930500*b5*b4 + (-15440692)*b5 + 2494833*b4^2 + (-13159210)*b4 + (-13431727) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c3_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 675792*a5^2*b5 + 527592*a5^2*b4 + 1379742*a5^2 + 1368000*a5*a4*b5 + 1068000*a5*a4*b4 + 2793000*a5*a4 + 675792*a5*b5^2 + 1368000*a5*b5*b4 + 3780392*a5*b5 + 692208*a5*b4^2 + 2862008*a5*b4 + 2770675*a5 + 692208*a4^2*b5 + 540408*a4^2*b4 + 1413258*a4^2 + 527592*a4*b5^2 + 1068000*a4*b5*b4 + 4175972*a4*b5 + 540408*a4*b4^2 + 3250388*a4*b4 + 3331555*a4 + 1501760*b5^2 + 3040000*b5*b4 + 1203935*b5 + 1538240*b4^2 + 453815*b4 + (-1335700) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

theorem pc6_d3p_c3_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 4054752*a5^2*b5 + 3165552*a5^2*b4 + 8278452*a5^2 + 8208000*a5*a4*b5 + 6408000*a5*a4*b4 + 16758000*a5*a4 + 4054752*a5*b5^2 + 8208000*a5*b5*b4 + 23280168*a5*b5 + 4153248*a5*b4^2 + 17638764*a5*b4 + 17844591*a5 + 4153248*a4^2*b5 + 3242448*a4^2*b4 + 8479548*a4^2 + 3165552*a4*b5^2 + 6408000*a4*b5*b4 + 25653648*a4*b5 + 3242448*a4*b4^2 + 19969044*a4*b4 + 21209871*a4 + 3613610*b5^2 + 7315000*b5*b4 + 21629315*b5 + 3701390*b4^2 + 16866395*b4 + 12411180 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d3p_c3_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : 1 ≤ a5 + b5) :
    (0:ℝ) ≤ 337896*a5^2*b5 + 263796*a5^2*b4 + 689871*a5^2 + 684000*a5*a4*b5 + 534000*a5*a4*b4 + 1396500*a5*a4 + 337896*a5*b5^2 + 684000*a5*b5*b4 + 1253392*a5*b5 + 346104*a5*b4^2 + 933850*a5*b4 + 85196*a5 + 346104*a4^2*b5 + 270204*a4^2*b4 + 706629*a4^2 + 263796*a4*b5^2 + 534000*a4*b5*b4 + 1442974*a4*b5 + 270204*a4*b4^2 + 1121632*a4*b4 + 348878*a4 + 61009*b5^2 + 123500*b5*b4 + (-49818)*b5 + 62491*b4^2 + (-48336)*b4 + (-110827) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)]

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 18169345194*a5^2*b5 + 12314283306*a5^2*b4 + (-29298280440)*a5^2 + 36780051000*a5*a4*b5 + 24927699000*a5*a4*b4 + (-59308260000)*a5*a4 + 18169345194*a5*b5^2 + 36780051000*a5*b5*b4 + 331034358229*a5*b5 + 18610705806*a5*b4^2 + 316585783141*a5*b4 + 562414453636*a5 + 18610705806*a4^2*b5 + 12613415694*a4^2*b4 + (-30009979560)*a4^2 + 12314283306*a4*b5^2 + 24927699000*a4*b5*b4 + 288454504669*a4*b5 + 12613415694*a4*b4^2 + 273294788461*a4*b4 + 483298888036*a4 + 91961778324*b5^2 + 186157446000*b5*b4 + 813666478706*b5 + 94195667676*b4^2 + 812243080466*b4 + 1414239666680 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 36338690388*a5^2*b5 + 24628566612*a5^2*b4 + (-58596560880)*a5^2 + 73560102000*a5*a4*b5 + 49855398000*a5*a4*b4 + (-118616520000)*a5*a4 + 36338690388*a5*b5^2 + 73560102000*a5*b5*b4 + 667426343887*a5*b5 + 37221411612*a5*b4^2 + 636802701103*a5*b4 + 1116189670732*a5 + 37221411612*a4^2*b5 + 25226831388*a4^2*b4 + (-60019959120)*a4^2 + 24628566612*a4*b5^2 + 49855398000*a4*b5*b4 + 582266636767*a4*b5 + 25226831388*a4*b4^2 + 550220711743*a4*b4 + 957958539532*a4 + 112849610952*b5^2 + 228440508000*b5*b4 + 1110460846142*b5 + 115590897048*b4^2 + 1098981586622*b4 + 1868104273160 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 9084672597*a5^2*b5 + 6157141653*a5^2*b4 + (-14649140220)*a5^2 + 18390025500*a5*a4*b5 + 12463849500*a5*a4*b4 + (-29654130000)*a5*a4 + 9084672597*a5*b5^2 + 18390025500*a5*b5*b4 + 148396065374*a5*b5 + 9305352903*a5*b4^2 + 146689047686*a5*b4 + 308815221848*a5 + 9305352903*a4^2*b5 + 6306707847*a4^2*b4 + (-15004989780)*a4^2 + 6157141653*a4*b5^2 + 12463849500*a4*b5*b4 + 126885458288*a4*b5 + 6306707847*a4*b4^2 + 124893984152*a4*b4 + 269613288608*a4 + 22990444581*b5^2 + 46539361500*b5*b4 + 148225349177*b5 + 23548916919*b4^2 + 150459238529*b4 + 225054283412 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 18169345194*a5^2*b5 + 12314283306*a5^2*b4 + (-4205223906)*a5^2 + 36780051000*a5*a4*b5 + 24927699000*a5*a4*b4 + (-8512599000)*a5*a4 + 18169345194*a5*b5^2 + 36780051000*a5*b5*b4 + 331034358229*a5*b5 + 18610705806*a5*b4^2 + 303383390209*a5*b4 + 350404289461*a5 + 18610705806*a4^2*b5 + 12613415694*a4^2*b4 + (-4307375094)*a4^2 + 12314283306*a4*b5^2 + 24927699000*a4*b5*b4 + 301656897601*a4*b5 + 12613415694*a4*b4^2 + 273294788461*a4*b4 + 312114998521*a4 + 66868721790*b5^2 + 135361785000*b5*b4 + 705774017941*b5 + 68493063210*b4^2 + 676117190041*b4 + 792007238705 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 36338690388*a5^2*b5 + 24628566612*a5^2*b4 + (-8410447812)*a5^2 + 73560102000*a5*a4*b5 + 49855398000*a5*a4*b4 + (-17025198000)*a5*a4 + 36338690388*a5*b5^2 + 73560102000*a5*b5*b4 + 667426343887*a5*b5 + 37221411612*a5*b4^2 + 610397915239*a5*b4 + 699568577001*a5 + 37221411612*a4^2*b5 + 25226831388*a4^2*b4 + (-8614750188)*a4^2 + 24628566612*a4*b5^2 + 49855398000*a4*b5*b4 + 608671422631*a4*b5 + 25226831388*a4*b4^2 + 550220711743*a4*b4 + 622989995121*a4 + 62663497884*b5^2 + 126849186000*b5*b4 + 1054938305481*b5 + 64185688116*b4^2 + 986992186641*b4 + 1119225029055 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 9084672597*a5^2*b5 + 6157141653*a5^2*b4 + (-2102611953)*a5^2 + 18390025500*a5*a4*b5 + 12463849500*a5*a4*b4 + (-4256299500)*a5*a4 + 9084672597*a5*b5^2 + 18390025500*a5*b5*b4 + 148396065374*a5*b5 + 9305352903*a5*b4^2 + 140087851220*a5*b4 + 179164759565*a5 + 9305352903*a4^2*b5 + 6306707847*a4^2*b4 + (-2153687547)*a4^2 + 6157141653*a4*b5^2 + 12463849500*a4*b5*b4 + 133486654754*a4*b5 + 6306707847*a4*b4^2 + 124893984152*a4*b4 + 160071189689*a4 + 10443916314*b5^2 + 21141531000*b5*b4 + 125634802008*b5 + 10697614686*b4^2 + 120353172996*b4 + 128004405758 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

theorem pc6_d3f_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 18169345194*a5^2*b5 + 12314283306*a5^2*b4 + 20887832628*a5^2 + 36780051000*a5*a4*b5 + 24927699000*a5*a4*b4 + 42283062000*a5*a4 + 18169345194*a5*b5^2 + 36780051000*a5*b5*b4 + 331034358229*a5*b5 + 18610705806*a5*b4^2 + 290180997277*a5*b4 + 290635134738*a5 + 18610705806*a4^2*b5 + 12613415694*a4^2*b4 + 21395229372*a4^2 + 12314283306*a4*b5^2 + 24927699000*a4*b5*b4 + 314859290533*a4*b5 + 12613415694*a4*b4^2 + 273294788461*a4*b4 + 280579273458*a4 + 41775665256*b5^2 + 84566124000*b5*b4 + 750122566628*b5 + 42790458744*b4^2 + 679639464068*b4 + 575931589240 := by
  positivity

theorem pc6_d3f_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 36338690388*a5^2*b5 + 24628566612*a5^2*b4 + 41775665256*a5^2 + 73560102000*a5*a4*b5 + 49855398000*a5*a4*b4 + 84566124000*a5*a4 + 36338690388*a5*b5^2 + 73560102000*a5*b5*b4 + 667426343887*a5*b5 + 37221411612*a5*b4^2 + 583993129375*a5*b4 + 587429502174*a5 + 37221411612*a4^2*b5 + 25226831388*a4^2*b4 + 42790458744*a4^2 + 24628566612*a4*b5^2 + 49855398000*a4*b5*b4 + 635076208495*a4*b5 + 25226831388*a4*b4^2 + 550220711743*a4*b4 + 567317779614*a4 + 12477384816*b5^2 + 25257864000*b5*b4 + 1303897783724*b5 + 12780479184*b4^2 + 1154299115564*b4 + 1029796195720 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 9084672597*a5^2*b5 + 6157141653*a5^2*b4 + 10443916314*a5^2 + 18390025500*a5*a4*b5 + 12463849500*a5*a4*b4 + 21141531000*a5*a4 + 9084672597*a5*b5^2 + 18390025500*a5*b5*b4 + 148396065374*a5*b5 + 9305352903*a5*b4^2 + 133486654754*a5*b4 + 125634802008*a5 + 9305352903*a4^2*b5 + 6306707847*a4^2*b4 + 10697614686*a4^2 + 6157141653*a4*b5^2 + 12463849500*a4*b5*b4 + 140087851220*a4*b5 + 6306707847*a4*b4^2 + 124893984152*a4*b4 + 120353172996*a4 + (-2102611953)*b5^2 + (-4256299500)*b5*b4 + 179164759565*b5 + (-2153687547)*b4^2 + 160071189689*b4 + 128004405758 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

theorem pc6_d3f_c3_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 18169345194*a5^2*b5 + 12314283306*a5^2*b4 + 45980889162*a5^2 + 36780051000*a5*a4*b5 + 24927699000*a5*a4*b4 + 93078723000*a5*a4 + 18169345194*a5*b5^2 + 36780051000*a5*b5*b4 + 331034358229*a5*b5 + 18610705806*a5*b4^2 + 276978604345*a5*b4 + 383106989467*a5 + 18610705806*a4^2*b5 + 12613415694*a4^2*b4 + 47097833838*a4^2 + 12314283306*a4*b5^2 + 24927699000*a4*b5*b4 + 328061683465*a4*b5 + 12613415694*a4*b4^2 + 273294788461*a4*b4 + 388691712847*a4 + 16682608722*b5^2 + 33770463000*b5*b4 + 946712124767*b5 + 17087854278*b4^2 + 822809902547*b4 + 766012718285 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c3_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 36338690388*a5^2*b5 + 24628566612*a5^2*b4 + 91961778324*a5^2 + 73560102000*a5*a4*b5 + 49855398000*a5*a4*b4 + 186157446000*a5*a4 + 36338690388*a5*b5^2 + 73560102000*a5*b5*b4 + 667426343887*a5*b5 + 37221411612*a5*b4^2 + 557588343511*a5*b4 + 779772446251*a5 + 37221411612*a4^2*b5 + 25226831388*a4^2*b4 + 94195667676*a4^2 + 24628566612*a4*b5^2 + 49855398000*a4*b5*b4 + 661480994359*a4*b5 + 25226831388*a4*b4^2 + 550220711743*a4*b4 + 790941893011*a4 + (-37708728252)*b5^2 + (-76333458000)*b5*b4 + 1857339280871*b5 + (-38624729748)*b4^2 + 1600902373391*b4 + 1599817773155 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

set_option maxHeartbeats 4000000 in
theorem pc6_d3f_c3_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4)
    (hsel : a5 + b5 ≤ 0) :
    (0:ℝ) ≤ 9084672597*a5^2*b5 + 6157141653*a5^2*b4 + 22990444581*a5^2 + 18390025500*a5*a4*b5 + 12463849500*a5*a4*b4 + 46539361500*a5*a4 + 9084672597*a5*b5^2 + 18390025500*a5*b5*b4 + 148396065374*a5*b5 + 9305352903*a5*b4^2 + 126885458288*a5*b4 + 148225349177*a5 + 9305352903*a4^2*b5 + 6306707847*a4^2*b4 + 23548916919*a4^2 + 6157141653*a4*b5^2 + 12463849500*a4*b5*b4 + 146689047686*a4*b5 + 6306707847*a4*b4^2 + 124893984152*a4*b4 + 150459238529*a4 + (-14649140220)*b5^2 + (-29654130000)*b5*b4 + 308815221848*b5 + (-15004989780)*b4^2 + 269613288608*b4 + 225054283412 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4), mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))]

theorem pc6_d4p_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 441142*a5^2*b5 + 352222*a5^2*b4 + 893000*a5*a4*b5 + 713000*a5*a4*b4 + 441142*a5*b5^2 + 893000*a5*b5*b4 + 2235673*a5*b5 + 451858*a5*b4^2 + 2398693*a5*b4 + 451858*a4^2*b5 + 360778*a4^2*b4 + 352222*a4*b5^2 + 713000*a4*b5*b4 + 1758925*a4*b5 + 360778*a4*b4^2 + 1917625*a4*b4 + 1727024*b5^2 + 3496000*b5*b4 + 4574953*b5 + 1768976*b4^2 + 5256673*b4 := by
  positivity

theorem pc6_d4p_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 13804279*a5*b5 + 2711148*a5*b4^2 + 14703739*a5*b4 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 10943791*a4*b5 + 2164668*a4*b4^2 + 11817331*a4*b4 + 7123974*b5^2 + 14421000*b5*b4 + 10088145*b5 + 7297026*b4^2 + 14021145*b4 := by
  positivity

theorem pc6_d4p_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 220571*a5^2*b5 + 176111*a5^2*b4 + 446500*a5*a4*b5 + 356500*a5*a4*b4 + 220571*a5*b5^2 + 446500*a5*b5*b4 + 702145*a5*b5 + 225929*a5*b4^2 + 867445*a5*b4 + 225929*a4^2*b5 + 180389*a4^2*b4 + 176111*a4*b5^2 + 356500*a4*b5*b4 + 458413*a4*b5 + 180389*a4*b4^2 + 622633*a4*b4 + 431756*b5^2 + 874000*b5*b4 + 232484*b5 + 442244*b4^2 + 442244*b4 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 441142*a5^2*b5 + 352222*a5^2*b4 + 215878*a5^2 + 893000*a5*a4*b5 + 713000*a5*a4*b4 + 437000*a5*a4 + 441142*a5*b5^2 + 893000*a5*b5*b4 + 2235673*a5*b5 + 451858*a5*b4^2 + 2194177*a5*b4 + (-2449385)*a5 + 451858*a4^2*b5 + 360778*a4^2*b4 + 221122*a4^2 + 352222*a4*b5^2 + 713000*a4*b5*b4 + 1963441*a4*b5 + 360778*a4*b4^2 + 1917625*a4*b4 + (-2040353)*a4 + 1511146*b5^2 + 3059000*b5*b4 + 514786*b5 + 1547854*b4^2 + 1186018*b4 + (-7256822) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 1295268*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 2622000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 13804279*a5*b5 + 2711148*a5*b4^2 + 13476643*a5*b4 + (-14505341)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 1326732*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 12170887*a4*b5 + 2164668*a4*b4^2 + 11817331*a4*b4 + (-12051149)*a4 + 5828706*b5^2 + 11799000*b5*b4 + (-6825066)*b5 + 5970294*b4^2 + (-2954994)*b4 + (-28645350) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 220571*a5^2*b5 + 176111*a5^2*b4 + 107939*a5^2 + 446500*a5*a4*b5 + 356500*a5*a4*b4 + 218500*a5*a4 + 220571*a5*b5^2 + 446500*a5*b5*b4 + 702145*a5*b5 + 225929*a5*b4^2 + 765187*a5*b4 + (-1428116)*a5 + 225929*a4^2*b5 + 180389*a4^2*b4 + 110561*a4^2 + 176111*a4*b5^2 + 356500*a4*b5*b4 + 560671*a4*b5 + 180389*a4*b4^2 + 622633*a4*b4 + (-1226222)*a4 + 323817*b5^2 + 655500*b5*b4 + (-1311874)*b5 + 331683*b4^2 + (-1005100)*b4 + (-1336783) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 1295268*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 2622000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 6707019*a5*b5 + 1355574*a5*b4^2 + 5968983*a5*b4 + (-8751362)*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1326732*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 6503871*a4*b5 + 1082334*a4*b4^2 + 5752875*a4*b4 + (-6894986)*a4 + 3885804*b5^2 + 7866000*b5*b4 + (-4691195)*b5 + 3980196*b4^2 + (-3306779)*b4 + (-29409226) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 2590536*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 5244000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 13804279*a5*b5 + 2711148*a5*b4^2 + 12249547*a5*b4 + (-17120786)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2653464*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 13397983*a4*b5 + 2164668*a4*b4^2 + 11817331*a4*b4 + (-13408034)*a4 + 4533438*b5^2 + 9177000*b5*b4 + (-11848381)*b5 + 4643562*b4^2 + (-9236869)*b4 + (-36284110) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 647634*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 1311000*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 2106435*a5*b5 + 677787*a5*b4^2 + 1988787*a5*b4 + (-5596222)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 663366*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 1988787*a4*b5 + 541167*a4*b4^2 + 1867899*a4*b4 + (-4683766)*a4 + 647634*b5^2 + 1311000*b5*b4 + (-5596222)*b5 + 663366*b4^2 + (-4683766)*b4 + (-5347132) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c3_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 441142*a5^2*b5 + 352222*a5^2*b4 + 647634*a5^2 + 893000*a5*a4*b5 + 713000*a5*a4*b4 + 1311000*a5*a4 + 441142*a5*b5^2 + 893000*a5*b5*b4 + 2235673*a5*b5 + 451858*a5*b4^2 + 1785145*a5*b4 + (-1403207)*a5 + 451858*a4^2*b5 + 360778*a4^2*b4 + 663366*a4^2 + 352222*a4*b5^2 + 713000*a4*b5*b4 + 2372473*a4*b5 + 360778*a4*b4^2 + 1917625*a4*b4 + (-773927)*a4 + 1079390*b5^2 + 2185000*b5*b4 + (-1660600)*b5 + 1105610*b4^2 + (-1608160)*b4 + (-7638760) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c3_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 3885804*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 7866000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 13804279*a5*b5 + 2711148*a5*b4^2 + 11022451*a5*b4 + (-7846335)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 3980196*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 14625079*a4*b5 + 2164668*a4*b4^2 + 11817331*a4*b4 + (-4070655)*a4 + 3238170*b5^2 + 6555000*b5*b4 + (-4981800)*b5 + 3316830*b4^2 + (-4824480)*b4 + (-22916280) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c3_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 220571*a5^2*b5 + 176111*a5^2*b4 + 323817*a5^2 + 446500*a5*a4*b5 + 356500*a5*a4*b4 + 655500*a5*a4 + 220571*a5*b5^2 + 446500*a5*b5*b4 + 702145*a5*b5 + 225929*a5*b4^2 + 560671*a5*b4 + (-1311874)*a5 + 225929*a4^2*b5 + 180389*a4^2*b4 + 331683*a4^2 + 176111*a4*b5^2 + 356500*a4*b5*b4 + 765187*a4*b5 + 180389*a4*b4^2 + 622633*a4*b4 + (-1005100)*a4 + 107939*b5^2 + 218500*b5*b4 + (-1428116)*b5 + 110561*b4^2 + (-1226222)*b4 + (-1336783) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d4p_c4_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 441142*a5^2*b5 + 352222*a5^2*b4 + 863512*a5^2 + 893000*a5*a4*b5 + 713000*a5*a4*b4 + 1748000*a5*a4 + 441142*a5*b5^2 + 893000*a5*b5*b4 + 2235673*a5*b5 + 451858*a5*b4^2 + 1580629*a5*b4 + 2092356*a5 + 451858*a4^2*b5 + 360778*a4^2*b4 + 884488*a4^2 + 352222*a4*b5^2 + 713000*a4*b5*b4 + 2576989*a4*b5 + 360778*a4*b4^2 + 1917625*a4*b4 + 2532852*a4 + 863512*b5^2 + 1748000*b5*b4 + 224181*b5 + 884488*b4^2 + (-331683)*b4 + (-763876) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d4p_c4_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 5181072*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 10488000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 13804279*a5*b5 + 2711148*a5*b4^2 + 9795355*a5*b4 + 13318012*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 5306928*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 15852175*a4*b5 + 2164668*a4*b4^2 + 11817331*a4*b4 + 15960988*a4 + 1942902*b5^2 + 3933000*b5*b4 + 13774677*b5 + 1990098*b4^2 + 10282173*b4 + 11458140 := by
  positivity

theorem pc6_d4p_c4_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 220571*a5^2*b5 + 176111*a5^2*b4 + 431756*a5^2 + 446500*a5*a4*b5 + 356500*a5*a4*b4 + 874000*a5*a4 + 220571*a5*b5^2 + 446500*a5*b5*b4 + 702145*a5*b5 + 225929*a5*b4^2 + 458413*a5*b4 + 232484*a5 + 225929*a4^2*b5 + 180389*a4^2*b4 + 442244*a4^2 + 176111*a4*b5^2 + 356500*a4*b5*b4 + 867445*a4*b5 + 180389*a4*b4^2 + 622633*a4*b4 + 442244*a4 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c0_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + (-647634)*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + (-1311000)*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 9591409*a5*b5 + 1355574*a5*b4^2 + 10112617*a5*b4 + 11881593*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + (-663366)*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 7579765*a4*b5 + 1082334*a4*b4^2 + 8081533*a4*b4 + 10040949*a4 + 5181072*b5^2 + 10488000*b5*b4 + 25016939*b5 + 5306928*b4^2 + 27187955*b4 + 34947327 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c0_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + (-1295268)*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + (-2622000)*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 19573059*a5*b5 + 2711148*a5*b4^2 + 20536815*a5*b4 + 23572217*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + (-1326732)*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 15549771*a4*b5 + 2164668*a4*b4^2 + 16474647*a4*b4 + 19890929*a4 + 7123974*b5^2 + 14421000*b5*b4 + 25614755*b5 + 7297026*b4^2 + 29720807*b4 + 47551281 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c0_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + (-323817)*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + (-655500)*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 3548630*a5*b5 + 677787*a5*b4^2 + 4060604*a5*b4 + 6551067*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + (-331683)*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 2526734*a4*b5 + 541167*a4*b4^2 + 3032228*a4*b4 + 5638611*a4 + 1295268*b5^2 + 2622000*b5*b4 + 3520472*b5 + 1326732*b4^2 + 4181216*b4 + 6874884 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d5p_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 9591409*a5*b5 + 1355574*a5*b4^2 + 9499069*a5*b4 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 8193313*a4*b5 + 1082334*a4*b4^2 + 8081533*a4*b4 + 4533438*b5^2 + 9177000*b5*b4 + 11424928*b5 + 4643562*b4^2 + 13548748*b4 := by
  positivity

theorem pc6_d5p_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 882284*a5^2*b5 + 704444*a5^2*b4 + 1786000*a5*a4*b5 + 1426000*a5*a4*b4 + 882284*a5*b5^2 + 1786000*a5*b5*b4 + 6524353*a5*b5 + 903716*a5*b4^2 + 6436573*a5*b4 + 903716*a4^2*b5 + 721556*a4^2*b4 + 704444*a4*b5^2 + 1426000*a4*b5*b4 + 5592289*a4*b5 + 721556*a4*b4^2 + 5491549*a4*b4 + 1942902*b5^2 + 3933000*b5*b4 + 1959508*b5 + 1990098*b4^2 + 3296728*b4 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 3548630*a5*b5 + 677787*a5*b4^2 + 3753830*a5*b4 + 677787*a4^2*b5 + 541167*a4^2*b4 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 2833508*a4*b5 + 541167*a4*b4^2 + 3032228*a4*b4 + 971451*b5^2 + 1966500*b5*b4 + (-1818357)*b5 + 995049*b4^2 + (-874437)*b4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 647634*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 1311000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 9591409*a5*b5 + 1355574*a5*b4^2 + 8885521*a5*b4 + (-5936645)*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 663366*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 8806861*a4*b5 + 1082334*a4*b4^2 + 8081533*a4*b4 + (-4693817)*a4 + 3885804*b5^2 + 7866000*b5*b4 + 3777865*b5 + 3980196*b4^2 + 5256673*b4 + (-19287869) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 882284*a5^2*b5 + 704444*a5^2*b4 + 431756*a5^2 + 1786000*a5*a4*b5 + 1426000*a5*a4*b4 + 874000*a5*a4 + 882284*a5*b5^2 + 1786000*a5*b5*b4 + 6524353*a5*b5 + 903716*a5*b4^2 + 6027541*a5*b4 + (-3894107)*a5 + 903716*a4^2*b5 + 721556*a4^2*b4 + 442244*a4^2 + 704444*a4*b5^2 + 1426000*a4*b5*b4 + 6001321*a4*b5 + 721556*a4*b4^2 + 5491549*a4*b4 + (-3065555)*a4 + 1511146*b5^2 + 3059000*b5*b4 + (-655937)*b5 + 1547854*b4^2 + 251275*b4 + (-7829729) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 323817*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 655500*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 3548630*a5*b5 + 677787*a5*b4^2 + 3447056*a5*b4 + (-3578593)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 331683*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 3140282*a4*b5 + 541167*a4*b4^2 + 3032228*a4*b4 + (-2965045)*a4 + 647634*b5^2 + 1311000*b5*b4 + (-4184712)*b5 + 663366*b4^2 + (-3256524)*b4 + (-3437442) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c3_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 1295268*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 2622000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 9591409*a5*b5 + 1355574*a5*b4^2 + 8271973*a5*b4 + (-5928342)*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1326732*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 9420409*a4*b5 + 1082334*a4*b4^2 + 8081533*a4*b4 + (-4040502)*a4 + 3238170*b5^2 + 6555000*b5*b4 + 2075750*b5 + 3316830*b4^2 + 2311730*b4 + (-22916280) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c3_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 2590536*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 5244000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 19573059*a5*b5 + 2711148*a5*b4^2 + 16855527*a5*b4 + (-11474746)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2653464*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 19231059*a4*b5 + 2164668*a4*b4^2 + 16474647*a4*b4 + (-7699066)*a4 + 3238170*b5^2 + 6555000*b5*b4 + 2075750*b5 + 3316830*b4^2 + 2311730*b4 + (-22916280) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c3_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 647634*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 1311000*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 3548630*a5*b5 + 677787*a5*b4^2 + 3140282*a5*b4 + (-4184712)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 663366*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 3447056*a4*b5 + 541167*a4*b4^2 + 3032228*a4*b4 + (-3256524)*a4 + 323817*b5^2 + 655500*b5*b4 + (-3578593)*b5 + 331683*b4^2 + (-2965045)*b4 + (-3437442) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c4_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 1942902*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 3933000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 9591409*a5*b5 + 1355574*a5*b4^2 + 7658425*a5*b4 + 24909*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1990098*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 10033957*a4*b5 + 1082334*a4*b4^2 + 8081533*a4*b4 + 1959945*a4 + 2590536*b5^2 + 5244000*b5*b4 + 6318583*b5 + 2653464*b4^2 + 4713919*b4 + (-10885233) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d5p_c4_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 882284*a5^2*b5 + 704444*a5^2*b4 + 1295268*a5^2 + 1786000*a5*a4*b5 + 1426000*a5*a4*b4 + 2622000*a5*a4 + 882284*a5*b5^2 + 1786000*a5*b5*b4 + 6524353*a5*b5 + 903716*a5*b4^2 + 5209477*a5*b4 + 207575*a5 + 903716*a4^2*b5 + 721556*a4^2*b4 + 1326732*a4^2 + 704444*a4*b5^2 + 1426000*a4*b5*b4 + 6819385*a4*b5 + 721556*a4*b4^2 + 5491549*a4*b4 + 1497599*a4 + 647634*b5^2 + 1311000*b5*b4 + 6003069*b5 + 663366*b4^2 + 4854633*b4 + 572907 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c4_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 971451*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 1966500*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 3548630*a5*b5 + 677787*a5*b4^2 + 2833508*a5*b4 + (-1818357)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 995049*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 3753830*a4*b5 + 541167*a4*b4^2 + 3032228*a4*b4 + (-874437)*a4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d5p_c5_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 2590536*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 5244000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 9591409*a5*b5 + 1355574*a5*b4^2 + 7044877*a5*b4 + 11923108*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 2653464*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 10647505*a4*b5 + 1082334*a4*b4^2 + 8081533*a4*b4 + 13307524*a4 + 1942902*b5^2 + 3933000*b5*b4 + 16506364*b5 + 1990098*b4^2 + 12463240*b4 + 16805272 := by
  positivity

theorem pc6_d5p_c5_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 882284*a5^2*b5 + 704444*a5^2*b4 + 1727024*a5^2 + 1786000*a5*a4*b5 + 1426000*a5*a4*b4 + 3496000*a5*a4 + 882284*a5*b5^2 + 1786000*a5*b5*b4 + 6524353*a5*b5 + 903716*a5*b4^2 + 4800445*a5*b4 + 8203364*a5 + 903716*a4^2*b5 + 721556*a4^2*b4 + 1768976*a4^2 + 704444*a4*b5^2 + 1426000*a4*b5*b4 + 7228417*a4*b5 + 721556*a4*b4^2 + 5491549*a4*b4 + 9126308*a4 + 215878*b5^2 + 437000*b5*b4 + 15277520*b5 + 221122*b4^2 + 12503444*b4 + 16805272 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d5p_c5_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 1295268*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 2622000*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 3548630*a5*b5 + 677787*a5*b4^2 + 2526734*a5*b4 + 3520472*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 1326732*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 4060604*a4*b5 + 541167*a4*b4^2 + 3032228*a4*b4 + 4181216*a4 + (-323817)*b5^2 + (-655500)*b5*b4 + 6551067*b5 + (-331683)*b4^2 + 5638611*b4 + 6874884 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c1_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + (-647634)*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + (-1311000)*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 12475799*a5*b5 + 1355574*a5*b4^2 + 12415607*a5*b4 + 10470083*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + (-663366)*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 10496303*a4*b5 + 1082334*a4*b4^2 + 10410191*a4*b4 + 8613707*a4 + 4533438*b5^2 + 9177000*b5*b4 + 21305498*b5 + 4643562*b4^2 + 23539442*b4 + 32464730 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c1_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + (-1295268)*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + (-2622000)*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 25341839*a5*b5 + 2711148*a5*b4^2 + 25142795*a5*b4 + 20749197*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + (-1326732)*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 21382847*a4*b5 + 2164668*a4*b4^2 + 21131963*a4*b4 + 17036445*a4 + 5828706*b5^2 + 11799000*b5*b4 + 18582114*b5 + 5970294*b4^2 + 22735362*b4 + 42395118 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c1_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + (-323817)*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + (-655500)*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 4990825*a5*b5 + 677787*a5*b4^2 + 5212099*a5*b4 + 5845312*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + (-331683)*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 3985003*a4*b5 + 541167*a4*b4^2 + 4196557*a4*b4 + 4924990*a4 + 971451*b5^2 + 1966500*b5*b4 + 298908*b5 + 995049*b4^2 + 1266426*b4 + 6301977 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d6p_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 12475799*a5*b5 + 1355574*a5*b4^2 + 11802059*a5*b4 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 11109851*a4*b5 + 1082334*a4*b4^2 + 10410191*a4*b4 + 3885804*b5^2 + 7866000*b5*b4 + 12246925*b5 + 3980196*b4^2 + 13820125*b4 := by
  positivity

theorem pc6_d6p_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 25341839*a5*b5 + 2711148*a5*b4^2 + 23915699*a5*b4 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 22609943*a4*b5 + 2164668*a4*b4^2 + 21131963*a4*b4 + 4533438*b5^2 + 9177000*b5*b4 + 7912759*b5 + 4643562*b4^2 + 10744519*b4 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 4990825*a5*b5 + 677787*a5*b4^2 + 4905325*a5*b4 + 677787*a4^2*b5 + 541167*a4^2*b4 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 4291777*a4*b5 + 541167*a4*b4^2 + 4196557*a4*b4 + 647634*b5^2 + 1311000*b5*b4 + (-2773202)*b5 + 663366*b4^2 + (-1829282)*b4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c3_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 647634*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 1311000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 12475799*a5*b5 + 1355574*a5*b4^2 + 11188511*a5*b4 + (-4525135)*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 663366*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 11723399*a4*b5 + 1082334*a4*b4^2 + 10410191*a4*b4 + (-3266575)*a4 + 3238170*b5^2 + 6555000*b5*b4 + 9133300*b5 + 3316830*b4^2 + 9447940*b4 + (-15277520) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c3_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 1295268*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 2622000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 25341839*a5*b5 + 2711148*a5*b4^2 + 22688603*a5*b4 + (-8859301)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 1326732*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 23837039*a4*b5 + 2164668*a4*b4^2 + 21131963*a4*b4 + (-6342181)*a4 + 3238170*b5^2 + 6555000*b5*b4 + 9133300*b5 + 3316830*b4^2 + 9447940*b4 + (-15277520) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c3_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 323817*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 655500*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 4990825*a5*b5 + 677787*a5*b4^2 + 4598551*a5*b4 + (-2872838)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 331683*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 4598551*a4*b5 + 541167*a4*b4^2 + 4196557*a4*b4 + (-2251424)*a4 + 323817*b5^2 + 655500*b5*b4 + (-2872838)*b5 + 331683*b4^2 + (-2251424)*b4 + (-2100659) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c4_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 1295268*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 2622000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 12475799*a5*b5 + 1355574*a5*b4^2 + 10574963*a5*b4 + (-3105322)*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1326732*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 12336947*a4*b5 + 1082334*a4*b4^2 + 10410191*a4*b4 + (-1186018)*a4 + 2590536*b5^2 + 5244000*b5*b4 + 11964623*b5 + 2653464*b4^2 + 10422887*b4 + (-13367830) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c4_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 2590536*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 5244000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 25341839*a5*b5 + 2711148*a5*b4^2 + 21461507*a5*b4 + (-5828706)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2653464*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 25064135*a4*b5 + 2164668*a4*b4^2 + 21131963*a4*b4 + (-1990098)*a4 + 1942902*b5^2 + 3933000*b5*b4 + 22243737*b5 + 1990098*b4^2 + 18845625*b4 + (-3437442) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c4_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 647634*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 1311000*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 4990825*a5*b5 + 677787*a5*b4^2 + 4291777*a5*b4 + (-2773202)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 663366*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 4905325*a4*b5 + 541167*a4*b4^2 + 4196557*a4*b4 + (-1829282)*a4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d6p_c5_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 1942902*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 3933000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 12475799*a5*b5 + 1355574*a5*b4^2 + 9961415*a5*b4 + 4259439*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1990098*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 12950495*a4*b5 + 1082334*a4*b4^2 + 10410191*a4*b4 + 6241671*a4 + 1942902*b5^2 + 3933000*b5*b4 + 20740894*b5 + 1990098*b4^2 + 16744966*b4 + 5729070 := by
  positivity

theorem pc6_d6p_c5_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 3885804*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 7866000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 25341839*a5*b5 + 2711148*a5*b4^2 + 20234411*a5*b4 + 9091785*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 3980196*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 26291231*a4*b5 + 2164668*a4*b4^2 + 21131963*a4*b4 + 13056249*a4 + 647634*b5^2 + 1311000*b5*b4 + 47244070*b5 + 663366*b4^2 + 38937574*b4 + 35520234 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d6p_c5_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 971451*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 1966500*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 4990825*a5*b5 + 677787*a5*b4^2 + 3985003*a5*b4 + 298908*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 995049*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 5212099*a4*b5 + 541167*a4*b4^2 + 4196557*a4*b4 + 1266426*a4 + (-323817)*b5^2 + (-655500)*b5*b4 + 5845312*b5 + (-331683)*b4^2 + 4924990*b4 + 6301977 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c2_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + (-647634)*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + (-1311000)*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 15360189*a5*b5 + 1355574*a5*b4^2 + 14718597*a5*b4 + 9058573*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + (-663366)*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 13412841*a4*b5 + 1082334*a4*b4^2 + 12738849*a4*b4 + 7186465*a4 + 3885804*b5^2 + 7866000*b5*b4 + 20715985*b5 + 3980196*b4^2 + 22383577*b4 + 28454381 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c2_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + (-1295268)*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + (-2622000)*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 31110619*a5*b5 + 2711148*a5*b4^2 + 29748775*a5*b4 + 17926177*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + (-1326732)*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 27215923*a4*b5 + 2164668*a4*b4^2 + 25789279*a4*b4 + 14181961*a4 + 4533438*b5^2 + 9177000*b5*b4 + 17793329*b5 + 4643562*b4^2 + 20735213*b4 + 34183451 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c2_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + (-323817)*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + (-655500)*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 6433020*a5*b5 + 677787*a5*b4^2 + 6363594*a5*b4 + 5139557*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + (-331683)*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 5443272*a4*b5 + 541167*a4*b4^2 + 5360886*a4*b4 + 4211369*a4 + 647634*b5^2 + 1311000*b5*b4 + (-1361692)*b5 + 663366*b4^2 + (-402040)*b4 + 4965194 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d7p_c3_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 441142*a5^2*b5 + 352222*a5^2*b4 + 893000*a5*a4*b5 + 713000*a5*a4*b4 + 441142*a5*b5^2 + 893000*a5*b5*b4 + 5120063*a5*b5 + 451858*a5*b4^2 + 4701683*a5*b4 + 451858*a4^2*b5 + 360778*a4^2*b4 + 352222*a4*b5^2 + 713000*a4*b5*b4 + 4675463*a4*b5 + 360778*a4*b4^2 + 4246283*a4*b4 + 1079390*b5^2 + 2185000*b5*b4 + 5396950*b5 + 1105610*b4^2 + 5528050*b4 := by
  positivity

theorem pc6_d7p_c3_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 31110619*a5*b5 + 2711148*a5*b4^2 + 28521679*a5*b4 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 28443019*a4*b5 + 2164668*a4*b4^2 + 25789279*a4*b4 + 3238170*b5^2 + 6555000*b5*b4 + 16190850*b5 + 3316830*b4^2 + 16584150*b4 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c3_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 220571*a5^2*b5 + 176111*a5^2*b4 + 446500*a5*a4*b5 + 356500*a5*a4*b4 + 220571*a5*b5^2 + 446500*a5*b5*b4 + 2144340*a5*b5 + 225929*a5*b4^2 + 2018940*a5*b4 + 225929*a4^2*b5 + 180389*a4^2*b4 + 176111*a4*b5^2 + 356500*a4*b5*b4 + 1916682*a4*b5 + 180389*a4*b4^2 + 1786962*a4*b4 + 107939*b5^2 + 218500*b5*b4 + (-722361)*b5 + 110561*b4^2 + (-512601)*b4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c4_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 441142*a5^2*b5 + 352222*a5^2*b4 + 215878*a5^2 + 893000*a5*a4*b5 + 713000*a5*a4*b4 + 437000*a5*a4 + 441142*a5*b5^2 + 893000*a5*b5*b4 + 5120063*a5*b5 + 451858*a5*b4^2 + 4497167*a5*b4 + (-1037875)*a5 + 451858*a4^2*b5 + 360778*a4^2*b4 + 221122*a4^2 + 352222*a4*b5^2 + 713000*a4*b5*b4 + 4879979*a4*b5 + 360778*a4*b4^2 + 4246283*a4*b4 + (-613111)*a4 + 863512*b5^2 + 1748000*b5*b4 + 5870221*b5 + 884488*b4^2 + 5377285*b4 + (-3246473) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c4_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 1295268*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 2622000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 31110619*a5*b5 + 2711148*a5*b4^2 + 27294583*a5*b4 + (-6036281)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 1326732*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 29670115*a4*b5 + 2164668*a4*b4^2 + 25789279*a4*b4 + (-3487697)*a4 + 1942902*b5^2 + 3933000*b5*b4 + 26478267*b5 + 1990098*b4^2 + 23127351*b4 + (-4010349) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c4_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 220571*a5^2*b5 + 176111*a5^2*b4 + 107939*a5^2 + 446500*a5*a4*b5 + 356500*a5*a4*b4 + 218500*a5*a4 + 220571*a5*b5^2 + 446500*a5*b5*b4 + 2144340*a5*b5 + 225929*a5*b4^2 + 1916682*a5*b4 + (-722361)*a5 + 225929*a4^2*b5 + 180389*a4^2*b4 + 110561*a4^2 + 176111*a4*b5^2 + 356500*a4*b5*b4 + 2018940*a4*b5 + 180389*a4*b4^2 + 1786962*a4*b4 + (-512601)*a4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c5_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 1295268*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 2622000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 15360189*a5*b5 + 1355574*a5*b4^2 + 12877953*a5*b4 + (-282302)*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1326732*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 15253485*a4*b5 + 1082334*a4*b4^2 + 12738849*a4*b4 + 1668466*a4 + 1942902*b5^2 + 3933000*b5*b4 + 24975424*b5 + 1990098*b4^2 + 21026692*b4 + (-763876) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c5_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 2590536*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 5244000*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 31110619*a5*b5 + 2711148*a5*b4^2 + 26067487*a5*b4 + (-182666)*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2653464*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 30897211*a4*b5 + 2164668*a4*b4^2 + 25789279*a4*b4 + 3718870*a4 + 647634*b5^2 + 1311000*b5*b4 + 48655580*b5 + 663366*b4^2 + 40364816*b4 + 22152404 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d7p_c5_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 647634*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 1311000*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 6433020*a5*b5 + 677787*a5*b4^2 + 5443272*a5*b4 + (-1361692)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 663366*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 6363594*a4*b5 + 541167*a4*b4^2 + 5360886*a4*b4 + (-402040)*a4 + (-323817)*b5^2 + (-655500)*b5*b4 + 5139557*b5 + (-331683)*b4^2 + 4211369*b4 + 4965194 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d8p_c3_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + (-647634)*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + (-1311000)*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 18244579*a5*b5 + 1355574*a5*b4^2 + 17021587*a5*b4 + 7647063*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + (-663366)*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 16329379*a4*b5 + 1082334*a4*b4^2 + 15067507*a4*b4 + 5759223*a4 + 3238170*b5^2 + 6555000*b5*b4 + 23248400*b5 + 3316830*b4^2 + 23720360*b4 + 22916280 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d8p_c3_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + (-1295268)*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + (-2622000)*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 36879399*a5*b5 + 2711148*a5*b4^2 + 34354755*a5*b4 + 15103157*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + (-1326732)*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 33048999*a4*b5 + 2164668*a4*b4^2 + 30446595*a4*b4 + 11327477*a4 + 3238170*b5^2 + 6555000*b5*b4 + 23248400*b5 + 3316830*b4^2 + 23720360*b4 + 22916280 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d8p_c3_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + (-323817)*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + (-655500)*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 7875215*a5*b5 + 677787*a5*b4^2 + 7515089*a5*b4 + 4433802*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + (-331683)*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 6901541*a4*b5 + 541167*a4*b4^2 + 6525215*a4*b4 + 3497748*a4 + 323817*b5^2 + 655500*b5*b4 + (-1461328)*b5 + 331683*b4^2 + (-824182)*b4 + 2864535 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d8p_c4_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 18244579*a5*b5 + 1355574*a5*b4^2 + 16408039*a5*b4 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 16942927*a4*b5 + 1082334*a4*b4^2 + 15067507*a4*b4 + 2590536*b5^2 + 5244000*b5*b4 + 23256703*b5 + 2653464*b4^2 + 21840823*b4 := by
  positivity

theorem pc6_d8p_c4_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 882284*a5^2*b5 + 704444*a5^2*b4 + 1786000*a5*a4*b5 + 1426000*a5*a4*b4 + 882284*a5*b5^2 + 1786000*a5*b5*b4 + 12293133*a5*b5 + 903716*a5*b4^2 + 11042553*a5*b4 + 903716*a4^2*b5 + 721556*a4^2*b4 + 704444*a4*b5^2 + 1426000*a4*b5*b4 + 11425365*a4*b5 + 721556*a4*b4^2 + 10148865*a4*b4 + 647634*b5^2 + 1311000*b5*b4 + 10237599*b5 + 663366*b4^2 + 9136359*b4 := by
  positivity

theorem pc6_d8p_c4_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 7875215*a5*b5 + 677787*a5*b4^2 + 7208315*a5*b4 + 677787*a4^2*b5 + 541167*a4^2*b4 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 7208315*a4*b5 + 541167*a4*b4^2 + 6525215*a4*b4 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d8p_c5_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 647634*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 1311000*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 18244579*a5*b5 + 1355574*a5*b4^2 + 15794491*a5*b4 + (-1702115)*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 663366*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 17556475*a4*b5 + 1082334*a4*b4^2 + 15067507*a4*b4 + (-412091)*a4 + 1942902*b5^2 + 3933000*b5*b4 + 29209954*b5 + 1990098*b4^2 + 25308418*b4 + (-2673566) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d8p_c5_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 882284*a5^2*b5 + 704444*a5^2*b4 + 431756*a5^2 + 1786000*a5*a4*b5 + 1426000*a5*a4*b4 + 874000*a5*a4 + 882284*a5*b5^2 + 1786000*a5*b5*b4 + 12293133*a5*b5 + 903716*a5*b4^2 + 10633521*a5*b4 + (-1071087)*a5 + 903716*a4^2*b5 + 721556*a4^2*b4 + 442244*a4^2 + 704444*a4*b5^2 + 1426000*a4*b5*b4 + 11834397*a4*b5 + 721556*a4*b4^2 + 10148865*a4*b4 + (-211071)*a4 + 215878*b5^2 + 437000*b5*b4 + 16689030*b5 + 221122*b4^2 + 13930686*b4 + 3437442 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d8p_c5_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 323817*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 655500*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 7875215*a5*b5 + 677787*a5*b4^2 + 6901541*a5*b4 + (-1461328)*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + 331683*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 7515089*a4*b5 + 541167*a4*b4^2 + 6525215*a4*b4 + (-824182)*a4 + (-323817)*b5^2 + (-655500)*b5*b4 + 4433802*b5 + (-331683)*b4^2 + 3497748*b4 + 2864535 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d9p_c4_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + (-647634)*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + (-1311000)*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 21128969*a5*b5 + 1355574*a5*b4^2 + 19324577*a5*b4 + 6235553*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + (-663366)*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 19245917*a4*b5 + 1082334*a4*b4^2 + 17396165*a4*b4 + 4331981*a4 + 2590536*b5^2 + 5244000*b5*b4 + 28902743*b5 + 2653464*b4^2 + 27549791*b4 + 15850427 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d9p_c4_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + (-1295268)*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + (-2622000)*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 42648179*a5*b5 + 2711148*a5*b4^2 + 38960735*a5*b4 + 12280137*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + (-1326732)*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 38882075*a4*b5 + 2164668*a4*b4^2 + 35103911*a4*b4 + 8472993*a4 + 1942902*b5^2 + 3933000*b5*b4 + 34947327*b5 + 1990098*b4^2 + 31690803*b4 + 8593605 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d9p_c4_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + (-323817)*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + (-655500)*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 9317410*a5*b5 + 677787*a5*b4^2 + 8666584*a5*b4 + 3728047*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + (-331683)*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 8359810*a4*b5 + 541167*a4*b4^2 + 7689544*a4*b4 + 2784127*a4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

theorem pc6_d9p_c5_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 21128969*a5*b5 + 1355574*a5*b4^2 + 18711029*a5*b4 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 19859465*a4*b5 + 1082334*a4*b4^2 + 17396165*a4*b4 + 1942902*b5^2 + 3933000*b5*b4 + 33444484*b5 + 1990098*b4^2 + 29590144*b4 := by
  positivity

theorem pc6_d9p_c5_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 42648179*a5*b5 + 2711148*a5*b4^2 + 37733639*a5*b4 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 40109171*a4*b5 + 2164668*a4*b4^2 + 35103911*a4*b4 + 647634*b5^2 + 1311000*b5*b4 + 51478600*b5 + 663366*b4^2 + 43219300*b4 := by
  positivity

set_option maxHeartbeats 4000000 in
theorem pc6_d9p_c5_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 9317410*a5*b5 + 677787*a5*b4^2 + 8359810*a5*b4 + 677787*a4^2*b5 + 541167*a4^2*b4 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 8666584*a4*b5 + 541167*a4*b4^2 + 7689544*a4*b4 + (-323817)*b5^2 + (-655500)*b5*b4 + 3728047*b5 + (-331683)*b4^2 + 2784127*b4 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d10p_c5_W1 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 1323426*a5^2*b5 + 1056666*a5^2*b4 + (-647634)*a5^2 + 2679000*a5*a4*b5 + 2139000*a5*a4*b4 + (-1311000)*a5*a4 + 1323426*a5*b5^2 + 2679000*a5*b5*b4 + 24013359*a5*b5 + 1355574*a5*b4^2 + 21627567*a5*b4 + 4824043*a5 + 1355574*a4^2*b5 + 1082334*a4^2*b4 + (-663366)*a4^2 + 1056666*a4*b5^2 + 2139000*a4*b5*b4 + 22162455*a4*b5 + 1082334*a4*b4^2 + 19724823*a4*b4 + 2904739*a4 + 1942902*b5^2 + 3933000*b5*b4 + 37679014*b5 + 1990098*b4^2 + 33871870*b4 + 7256822 := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d10p_c5_W2 (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 2646852*a5^2*b5 + 2113332*a5^2*b4 + (-1295268)*a5^2 + 5358000*a5*a4*b5 + 4278000*a5*a4*b4 + (-2622000)*a5*a4 + 2646852*a5*b5^2 + 5358000*a5*b5*b4 + 48416959*a5*b5 + 2711148*a5*b4^2 + 43566715*a5*b4 + 9457117*a5 + 2711148*a4^2*b5 + 2164668*a4^2*b4 + (-1326732)*a4^2 + 2113332*a4*b5^2 + 4278000*a4*b5*b4 + 44715151*a4*b5 + 2164668*a4*b4^2 + 39761227*a4*b4 + 5618509*a4 + 647634*b5^2 + 1311000*b5*b4 + 52890110*b5 + 663366*b4^2 + 44646542*b4 + (-8784574) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

set_option maxHeartbeats 4000000 in
theorem pc6_d10p_c5_RT (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4) :
    (0:ℝ) ≤ 661713*a5^2*b5 + 528333*a5^2*b4 + (-323817)*a5^2 + 1339500*a5*a4*b5 + 1069500*a5*a4*b4 + (-655500)*a5*a4 + 661713*a5*b5^2 + 1339500*a5*b5*b4 + 10759605*a5*b5 + 677787*a5*b4^2 + 9818079*a5*b4 + 3022292*a5 + 677787*a4^2*b5 + 541167*a4^2*b4 + (-331683)*a4^2 + 528333*a4*b5^2 + 1069500*a4*b5*b4 + 9818079*a4*b5 + 541167*a4*b4^2 + 8853873*a4*b4 + 2070506*a4 + (-323817)*b5^2 + (-655500)*b5*b4 + 3022292*b5 + (-331683)*b4^2 + 2070506*b4 + (-3628411) := by
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)]

-- 138 cell theorems emitted
end PC6
end Step3
end R3Cert
