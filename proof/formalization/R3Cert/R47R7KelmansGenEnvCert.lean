/-
  R47 / R7 -- GENERAL-ENVIRONMENT Kelmans-step monotonicity (box certificate, ALL N, ALL m).

  The adjacent hubward Kelmans merge step (donor degrees da >= db >= 2) on ANY loaded backbone
  whose every environment neighbour x of the two hubs satisfies 3*deg(x)+4*load(x) >= 23
  (z_x <= 3/23; a load-5 arm-leaf hits 23 exactly) is pi = per(L)/prod(deg) NON-DECREASING, for
  every load cell (ca, cb) in the 25-cell certified set.  This is the ENVIRONMENT version of the
  local merge rule -- the m-hub generalization of the two-hub base case (R47R7KelmansTwoHubCert):
  it eliminates multi-hub stuckness for arbitrary m and arbitrary N, not just the 2-hub family.

  PROOF (per cell).  The marginal environment sums lie in boxes sigma_Q in [0,(da-1)*3/23],
  sigma_S in [0,(db-1)*3/23]; Phi is bilinear in (sigma_Q, sigma_S) so its minimum is at a box
  CORNER.  With the shift da = 2+v+u, db = 2+v (u, v >= 0 <=> da >= db >= 2), each of the four
  corners has an all-nonnegative-coefficient numerator over a positive denominator -- a
  Positivstellensatz witness that the step gain is >= 0.  The 4 corners x 25 cells = 100 nonneg
  facts below (emitted by telperion emit_nonneg_orthant) discharge exactly that box positivity.

  HONEST SCOPE.  25 of the 30 load cells; the 5 residual cb-heavy cells {(0,5),(1,4),(1,5),(2,5),
  (3,5)} are NOT box-certifiable (the crude sigma_S=0 corner fails) though the step is strictly
  increasing on them on the exact family -- they need the sharp hub-mover treatment, left as
  follow-up.  Self-building leaf (R3Cert.+ glob), imported by nothing -- collision-safe.
  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert.Step3


/-- Env-step gain >= 0, cell (ca,cb)=(0,1), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_1_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 2*v*v*v + 3*u*v*v + 1*u*u*v + 12*v*v + 11*u*v + 1*u*u + 16*v + 8*u + 6 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,1), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_1_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 31*v*v*v + 57*u*v*v + 26*u*u*v + 192*v*v + 190*u*v + 26*u*u + 245*v + 133*u + 84 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,1), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_1_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 31*v*v*v + 36*u*v*v + 5*u*u*v + 240*v*v + 193*u*v + 5*u*u + 365*v + 157*u + 156 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,1), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_1_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 780*v*v*v*v + 1170*u*v*v*v + 390*u*u*v*v + 12230*v*v*v + 11736*u*v*v + 1690*u*u*v + 47502*v*v + 32786*u*v + 1300*u*u + 57892*v + 22220*u + 21840 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,2), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_2_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 4*v*v*v + 6*u*v*v + 2*u*u*v + 21*v*v + 19*u*v + 2*u*u + 26*v + 13*u + 9 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,2), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_2_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 71*v*v*v + 123*u*v*v + 52*u*u*v + 327*v*v + 314*u*v + 52*u*u + 349*v + 191*u + 93 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,2), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_2_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 71*v*v*v + 90*u*v*v + 19*u*u*v + 471*v*v + 386*u*v + 19*u*u + 709*v + 296*u + 309 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,2), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_2_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 2964*v*v*v*v + 4446*u*v*v*v + 1482*u*u*v*v + 33866*v*v*v + 37194*u*v*v + 8398*u*u*v + 123288*v*v + 88748*u*v + 6916*u*u + 151774*v + 56000*u + 59388 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,3), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_3_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 54*v*v*v + 81*u*v*v + 27*u*u*v + 270*v*v + 243*u*v + 27*u*u + 324*v + 162*u + 108 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,3), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_3_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 999*v*v*v + 1701*u*v*v + 702*u*u*v + 3942*v*v + 3726*u*v + 702*u*u + 3645*v + 2025*u + 702 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,3), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_3_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 999*v*v*v + 1296*u*v*v + 297*u*u*v + 6534*v*v + 5427*u*v + 297*u*u + 10125*v + 4131*u + 4590 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,3), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_3_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 15444*v*v*v*v + 23166*u*v*v*v + 7722*u*u*v*v + 183978*v*v*v + 214164*u*v*v + 54054*u*u*v + 685422*v*v + 503010*u*v + 46332*u*u + 886896*v + 312012*u + 370008 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,4), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_4_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 216*v*v*v + 324*u*v*v + 108*u*u*v + 1053*v*v + 945*u*v + 108*u*u + 1242*v + 621*u + 405 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,4), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_4_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 4077*v*v*v + 6885*u*v*v + 2808*u*u*v + 14175*v*v + 13230*u*v + 2808*u*u + 11151*v + 6345*u + 1053 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,4), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_4_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 4077*v*v*v + 5346*u*v*v + 1269*u*u*v + 27135*v*v + 22788*u*v + 1269*u*u + 43551*v + 17442*u + 20493 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(0,4), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c0_4_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 197964*v*v*v*v + 296946*u*v*v*v + 98982*u*u*v*v + 2554470*v*v*v + 3086586*u*v*v + 824850*u*u*v + 9802620*v*v + 7277904*u*v + 725868*u*u + 13394430*v + 4488264*u + 5948316 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,1), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_1_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 6*v*v*v + 9*u*v*v + 3*u*u*v + 40*v*v + 40*u*v + 3*u*u + 62*v + 31*u + 28 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,1), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_1_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 93*v*v*v + 171*u*v*v + 78*u*u*v + 677*v*v + 740*u*v + 78*u*u + 1075*v + 569*u + 491 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,1), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_1_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 93*v*v*v + 108*u*v*v + 15*u*u*v + 677*v*v + 614*u*v + 15*u*u + 1075*v + 506*u + 491 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,1), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_1_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 2340*v*v*v*v + 5850*u*v*v*v + 4680*u*u*v*v + 1170*u*u*u*v + 33858*v*v*v + 63816*u*v*v + 31128*u*u*v + 1170*u*u*u + 131956*v*v + 154504*u*v + 26448*u*u + 171698*v + 96538*u + 71260 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,2), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_2_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 12*v*v*v + 18*u*v*v + 6*u*u*v + 74*v*v + 71*u*v + 6*u*u + 98*v + 53*u + 36 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,2), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_2_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 213*v*v*v + 369*u*v*v + 156*u*u*v + 1252*v*v + 1282*u*v + 156*u*u + 1543*v + 913*u + 504 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,2), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_2_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 213*v*v*v + 270*u*v*v + 57*u*u*v + 1468*v*v + 1291*u*v + 57*u*u + 2191*v + 1021*u + 936 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,2), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_2_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 8892*v*v*v*v + 22230*u*v*v*v + 17784*u*u*v*v + 4446*u*u*u*v + 94050*v*v*v + 167898*u*v*v + 78294*u*u*v + 4446*u*u*u + 309530*v*v + 337280*u*v + 60510*u*u + 355412*v + 191612*u + 131040 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,3), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_3_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 162*v*v*v + 243*u*v*v + 81*u*u*v + 972*v*v + 918*u*v + 81*u*u + 1134*v + 675*u + 324 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,3), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_3_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 2997*v*v*v + 5103*u*v*v + 2106*u*u*v + 15795*v*v + 15768*u*v + 2106*u*u + 15147*v + 10665*u + 2349 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,3), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_3_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 2997*v*v*v + 3888*u*v*v + 891*u*u*v + 20979*v*v + 18360*u*v + 891*u*u + 30699*v + 14472*u + 12717 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(1,3), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c1_3_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 138996*v*v*v*v + 347490*u*v*v*v + 277992*u*u*v*v + 69498*u*u*u*v + 1388178*v*v*v + 2447820*u*v*v + 1129140*u*u*v + 69498*u*u*u + 4359096*v*v + 4655664*u*v + 851148*u*u + 4744494*v + 2555334*u + 1634580 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,1), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_1_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 18*v*v*v + 27*u*v*v + 9*u*u*v + 132*v*v + 141*u*v + 9*u*u + 252*v + 114*u + 138 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,1), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_1_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 279*v*v*v + 513*u*v*v + 234*u*u*v + 2334*v*v + 2730*u*v + 234*u*u + 4797*v + 2217*u + 2742 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,1), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_1_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 279*v*v*v + 324*u*v*v + 45*u*u*v + 1902*v*v + 1947*u*v + 45*u*u + 3285*v + 1623*u + 1662 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,1), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_1_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 7020*v*v*v*v + 17550*u*v*v*v + 14040*u*u*v*v + 3510*u*u*u*v + 102438*v*v*v + 204642*u*v*v + 105714*u*u*v + 3510*u*u*u + 465402*v*v + 616044*u*v + 91674*u*u + 732024*v + 428952*u + 362040 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,2), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_2_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 36*v*v*v + 54*u*v*v + 18*u*u*v + 255*v*v + 255*u*v + 18*u*u + 402*v + 201*u + 183 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,2), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_2_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 639*v*v*v + 1107*u*v*v + 468*u*u*v + 4569*v*v + 4866*u*v + 468*u*u + 7221*v + 3759*u + 3291 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,2), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_2_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 639*v*v*v + 810*u*v*v + 171*u*u*v + 4569*v*v + 4272*u*v + 171*u*u + 7221*v + 3462*u + 3291 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,2), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_2_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 26676*v*v*v*v + 66690*u*v*v*v + 53352*u*u*v*v + 13338*u*u*u*v + 330642*v*v*v + 599040*u*v*v + 281736*u*u*v + 13338*u*u*u + 1294332*v*v + 1460472*u*v + 228384*u*u + 1703442*v + 928122*u + 713076 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,3), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_3_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 486*v*v*v + 729*u*v*v + 243*u*u*v + 3402*v*v + 3321*u*v + 243*u*u + 4536*v + 2592*u + 1620 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,3), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_3_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 8991*v*v*v + 15309*u*v*v + 6318*u*u*v + 59292*v*v + 61074*u*v + 6318*u*u + 72981*v + 45765*u + 22680 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,3), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_3_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 8991*v*v*v + 11664*u*v*v + 2673*u*u*v + 67068*v*v + 61317*u*v + 2673*u*u + 100197*v + 49653*u + 42120 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,3), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_3_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 416988*v*v*v*v + 1042470*u*v*v*v + 833976*u*u*v*v + 208494*u*u*u*v + 5029614*v*v*v + 8940942*u*v*v + 4119822*u*u*v + 208494*u*u*u + 18826182*v*v + 20460924*u*v + 3285846*u*u + 22469076*v + 12562452*u + 8255520 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,4), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_4_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1944*v*v*v + 2916*u*v*v + 972*u*u*v + 13527*v*v + 13041*u*v + 972*u*u + 15066*v + 10125*u + 3483 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,4), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_4_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 36693*v*v*v + 61965*u*v*v + 25272*u*u*v + 226557*v*v + 229230*u*v + 25272*u*u + 201447*v + 167265*u + 11583 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,4), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_4_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 36693*v*v*v + 48114*u*v*v + 11421*u*u*v + 284877*v*v + 258390*u*v + 11421*u*u + 405567*v + 210276*u + 157383 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(2,4), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c2_4_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1781676*v*v*v*v + 4454190*u*v*v*v + 3563352*u*u*v*v + 890838*u*u*u*v + 21250350*v*v*v + 37471572*u*v*v + 17112060*u*u*v + 890838*u*u*u + 77160600*v*v + 82483272*u*v + 13548708*u*u + 84007530*v + 49465890*u + 26315604 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,1), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_1_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 54*v*v*v + 81*u*v*v + 27*u*u*v + 432*v*v + 486*u*v + 27*u*u + 1026*v + 405*u + 648 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,1), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_1_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 837*v*v*v + 1539*u*v*v + 702*u*u*v + 7911*v*v + 9720*u*v + 702*u*u + 20763*v + 8181*u + 13689 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,1), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_1_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 837*v*v*v + 972*u*v*v + 135*u*u*v + 5319*v*v + 6156*u*v + 135*u*u + 10395*v + 5184*u + 5913 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,1), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_1_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 7020*v*v*v*v + 17550*u*v*v*v + 14040*u*u*v*v + 3510*u*u*u*v + 103302*v*v*v + 217836*u*v*v + 118044*u*u*v + 3510*u*u*u + 520560*v*v + 797256*u*v + 104004*u*u + 1020114*v + 596970*u + 595836 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,2), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_2_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 108*v*v*v + 162*u*v*v + 54*u*u*v + 864*v*v + 891*u*v + 54*u*u + 1674*v + 729*u + 918 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,2), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_2_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1917*v*v*v + 3321*u*v*v + 1404*u*u*v + 16146*v*v + 17658*u*v + 1404*u*u + 32751*v + 14337*u + 18522 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,2), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_2_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1917*v*v*v + 2430*u*v*v + 513*u*u*v + 14202*v*v + 14013*u*v + 513*u*u + 24975*v + 11583*u + 12690 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,2), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_2_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 26676*v*v*v*v + 66690*u*v*v*v + 53352*u*u*v*v + 13338*u*u*u*v + 379134*v*v*v + 694386*u*v*v + 328590*u*u*v + 13338*u*u*u + 1726002*v*v + 2018088*u*v + 275238*u*u + 2688336*v + 1390392*u + 1314792 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,3), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_3_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1458*v*v*v + 2187*u*v*v + 729*u*u*v + 11664*v*v + 11664*u*v + 729*u*u + 18954*v + 9477*u + 8748 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,3), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_3_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 26973*v*v*v + 45927*u*v*v + 18954*u*u*v + 213597*v*v + 224532*u*v + 18954*u*u + 346275*v + 178605*u + 159651 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,3), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_3_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 26973*v*v*v + 34992*u*v*v + 8019*u*u*v + 213597*v*v + 202662*u*v + 8019*u*u + 346275*v + 167670*u + 159651 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,3), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_3_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 416988*v*v*v*v + 1042470*u*v*v*v + 833976*u*u*v*v + 208494*u*u*u*v + 5894694*v*v*v + 10538424*u*v*v + 4852224*u*u*v + 208494*u*u*u + 25891164*v*v + 28658448*u*v + 4018248*u*u + 35766198*v + 19162494*u + 15352740 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,4), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_4_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 5832*v*v*v + 8748*u*v*v + 2916*u*u*v + 46656*v*v + 45927*u*v + 2916*u*u + 62694*v + 37179*u + 21870 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,4), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_4_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 110079*v*v*v + 185895*u*v*v + 75816*u*u*v + 828144*v*v + 852930*u*v + 75816*u*u + 1024245*v + 667035*u + 306180 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,4), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_4_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 110079*v*v*v + 144342*u*v*v + 34263*u*u*v + 915624*v*v + 855117*u*v + 34263*u*u + 1374165*v + 710775*u + 568620 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(3,4), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c3_4_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1781676*v*v*v*v + 4454190*u*v*v*v + 3563352*u*u*v*v + 890838*u*u*u*v + 25131546*v*v*v + 44482122*u*v*v + 20241414*u*u*v + 890838*u*u*u + 107269434*v*v + 115986816*u*v + 16678062*u*u + 131683644*v + 75958884*u + 47764080 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,1), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_1_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 162*v*v*v + 243*u*v*v + 81*u*u*v + 1404*v*v + 1647*u*v + 81*u*u + 4104*v + 1404*u + 2862 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,1), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_1_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 2511*v*v*v + 4617*u*v*v + 2106*u*u*v + 26460*v*v + 33750*u*v + 2106*u*u + 86373*v + 29133*u + 62424 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,1), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_1_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 2511*v*v*v + 2916*u*v*v + 405*u*u*v + 14796*v*v + 19413*u*v + 405*u*u + 33885*v + 16497*u + 21600 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,1), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_1_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 63180*v*v*v*v + 157950*u*v*v*v + 126360*u*u*v*v + 31590*u*u*u*v + 937494*v*v*v + 2079270*u*v*v + 1173366*u*u*v + 31590*u*u*u + 5052078*v*v + 9064332*u*v + 1047006*u*u + 12712356*v + 7143012*u + 8534592 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,2), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_2_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 324*v*v*v + 486*u*v*v + 162*u*u*v + 2889*v*v + 3051*u*v + 162*u*u + 6858*v + 2565*u + 4293 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,2), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_2_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 5751*v*v*v + 9963*u*v*v + 4212*u*u*v + 55755*v*v + 62154*u*v + 4212*u*u + 141453*v + 52191*u + 91449 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,2), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_2_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 5751*v*v*v + 7290*u*v*v + 1539*u*u*v + 44091*v*v + 45630*u*v + 1539*u*u + 88965*v + 38340*u + 50625 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,2), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_2_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 240084*v*v*v*v + 600210*u*v*v*v + 480168*u*u*v*v + 120042*u*u*u*v + 3848634*v*v*v + 7107588*u*v*v + 3378996*u*u*v + 120042*u*u*u + 20012400*v*v + 24162192*u*v + 2898828*u*u + 37320966*v + 17654814*u + 20917116 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,3), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_3_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 4374*v*v*v + 6561*u*v*v + 2187*u*u*v + 39366*v*v + 40095*u*v + 2187*u*u + 78732*v + 33534*u + 43740 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,3), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_3_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 80919*v*v*v + 137781*u*v*v + 56862*u*u*v + 747954*v*v + 797526*u*v + 56862*u*u + 1554957*v + 659745*u + 887922 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,3), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_3_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 80919*v*v*v + 104976*u*v*v + 24057*u*u*v + 677970*v*v + 664119*u*v + 24057*u*u + 1240029*v + 559143*u + 642978 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,3), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_3_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 3752892*v*v*v*v + 9382230*u*v*v*v + 7505784*u*u*v*v + 1876446*u*u*u*v + 60837966*v*v*v + 109223154*u*v*v + 50261634*u*u*v + 1876446*u*u*u + 308450106*v*v + 347036076*u*v + 42755850*u*u + 504829584*v + 247195152*u + 253464552 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,4), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_4_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 17496*v*v*v + 26244*u*v*v + 8748*u*u*v + 158193*v*v + 158193*u*v + 8748*u*u + 263898*v + 131949*u + 123201 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,4), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_4_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 330237*v*v*v + 557685*u*v*v + 227448*u*u*v + 2929851*v*v + 3054510*u*v + 227448*u*u + 4868991*v + 2496825*u + 2269377 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,4), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_4_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 330237*v*v*v + 433026*u*v*v + 102789*u*u*v + 2929851*v*v + 2805192*u*v + 102789*u*u + 4868991*v + 2372166*u + 2269377 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,4), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_4_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 16035084*v*v*v*v + 40087710*u*v*v*v + 32070168*u*u*v*v + 8017542*u*u*u*v + 261114678*v*v*v + 463434048*u*v*v + 210336912*u*u*v + 8017542*u*u*u + 1291452660*v*v + 1410924096*u*v + 178266744*u*u + 1863701622*v + 987577758*u + 817328556 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,5), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_5_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 21870*v*v*v + 32805*u*v*v + 10935*u*u*v + 198288*v*v + 196101*u*v + 10935*u*u + 268272*v + 163296*u + 91854 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,5), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_5_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 417717*v*v*v + 702027*u*v*v + 284310*u*u*v + 3563352*v*v + 3663954*u*v + 284310*u*u + 4431591*v + 2961927*u + 1285956 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,5), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_5_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 417717*v*v*v + 551124*u*v*v + 133407*u*u*v + 3878280*v*v + 3670515*u*v + 133407*u*u + 5848767*v + 3119391*u + 2388204 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(4,5), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c4_5_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 20811492*v*v*v*v + 52028730*u*v*v*v + 41622984*u*u*v*v + 10405746*u*u*u*v + 339715458*v*v*v + 599198634*u*v*v + 269888922*u*u*v + 10405746*u*u*u + 1638641826*v*v + 1761826788*u*v + 228265938*u*u + 2055304692*v + 1214656884*u + 735566832 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,1), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_1_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 486*v*v*v + 729*u*v*v + 243*u*u*v + 4536*v*v + 5508*u*v + 243*u*u + 16038*v + 4779*u + 11988 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,1), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_1_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 7533*v*v*v + 13851*u*v*v + 6318*u*u*v + 87561*v*v + 115020*u*v + 6318*u*u + 346275*v + 101169*u + 266247 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,1), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_1_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 7533*v*v*v + 8748*u*v*v + 1215*u*u*v + 40905*v*v + 61074*u*v + 1215*u*u + 112995*v + 52326*u + 79623 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,1), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_1_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 189540*v*v*v*v + 473850*u*v*v*v + 379080*u*u*v*v + 94770*u*u*u*v + 2835810*v*v*v + 6594048*u*v*v + 3853008*u*u*v + 94770*u*u*u + 15869196*v*v + 33634440*u*v + 3473928*u*u + 52440858*v + 27514242*u + 39217932 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,2), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_2_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 972*v*v*v + 1458*u*v*v + 486*u*u*v + 9558*v*v + 10287*u*v + 486*u*u + 27378*v + 8829*u + 18792 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,2), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_2_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 17253*v*v*v + 29889*u*v*v + 12636*u*u*v + 189216*v*v + 214002*u*v + 12636*u*u + 583767*v + 184113*u + 411804 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,2), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_2_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 17253*v*v*v + 21870*u*v*v + 4617*u*u*v + 136728*v*v + 147663*u*v + 4617*u*u + 321327*v + 125793*u + 201852 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,2), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_2_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 720252*v*v*v*v + 1800630*u*v*v*v + 1440504*u*u*v*v + 360126*u*u*u*v + 12855186*v*v*v + 23897106*u*v*v + 11402046*u*u*v + 360126*u*u*u + 75252402*v*v + 93427344*u*v + 9961542*u*u + 167524524*v + 71330868*u + 104407056 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,3), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_3_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 13122*v*v*v + 19683*u*v*v + 6561*u*u*v + 131220*v*v + 135594*u*v + 6561*u*u + 319302*v + 115911*u + 201204 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,3), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_3_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 242757*v*v*v + 413343*u*v*v + 170586*u*u*v + 2565351*v*v + 2764368*u*v + 170586*u*u + 6615675*v + 2351025*u + 4293081 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,3), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_3_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 242757*v*v*v + 314928*u*v*v + 72171*u*u*v + 2145447*v*v + 2160756*u*v + 72171*u*u + 4516155*v + 1845828*u + 2613465 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,3), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_3_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 11258676*v*v*v*v + 28146690*u*v*v*v + 22517352*u*u*v*v + 5629338*u*u*u*v + 205871058*v*v*v + 370801476*u*v*v + 170559756*u*u*v + 5629338*u*u*u + 1187173584*v*v + 1354435344*u*v + 148042404*u*u + 2306187126*v + 1011780558*u + 1313625924 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,4), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_4_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 52488*v*v*v + 78732*u*v*v + 26244*u*u*v + 529254*v*v + 535815*u*v + 26244*u*u + 1089126*v + 457083*u + 612360 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,4), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_4_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 990711*v*v*v + 1673055*u*v*v + 682344*u*u*v + 10125810*v*v + 10650690*u*v + 682344*u*u + 21605373*v + 8977635*u + 12470274 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,4), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_4_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 990711*v*v*v + 1299078*u*v*v + 308367*u*u*v + 9338490*v*v + 9135099*u*v + 308367*u*u + 17668773*v + 7836021*u + 9320994 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,4), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_4_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 48105252*v*v*v*v + 120263130*u*v*v*v + 96210504*u*u*v*v + 24052626*u*u*u*v + 888136326*v*v*v + 1579586994*u*v*v + 715503294*u*u*v + 24052626*u*u*u + 5017585986*v*v + 5530433112*u*v + 619292790*u*u + 8602100856*v + 4071109248*u + 4424545944 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,5), box corner 0 (sigmaQ=0,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_5_k0_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 65610*v*v*v + 98415*u*v*v + 32805*u*u*v + 664848*v*v + 664848*u*v + 32805*u*u + 1132866*v + 566433*u + 533628 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,5), box corner 1 (sigmaQ=hi,sigmaS=0); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_5_k1_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1253151*v*v*v + 2106081*u*v*v + 852930*u*u*v + 12398103*v*v + 12850812*u*v + 852930*u*u + 21036753*v + 10744731*u + 9891801 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,5), box corner 2 (sigmaQ=0,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_5_k2_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 1253151*v*v*v + 1653372*u*v*v + 400221*u*u*v + 12398103*v*v + 11945394*u*v + 400221*u*u + 21036753*v + 10292022*u + 9891801 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv]

/-- Env-step gain >= 0, cell (ca,cb)=(5,5), box corner 3 (sigmaQ=hi,sigmaS=hi); nonneg-coeff in u,v>=0 (da=2+v+u, db=2+v). -/
theorem genenv_step_c5_5_k3_nonneg (u : ℝ) (v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0:ℝ) < 62434476*v*v*v*v + 156086190*u*v*v*v + 124868952*u*u*v*v + 31217238*u*u*u*v + 1158659478*v*v*v + 2046769560*u*v*v + 919327320*u*u*v + 31217238*u*u*u + 6400010556*v*v + 6923919528*u*v + 794458368*u*u + 9573780582*v + 5033236158*u + 4269995028 := by
  nlinarith [hu, hv, mul_nonneg hv hv, mul_nonneg hu hv, mul_nonneg hu hu, mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hu hv) hv, mul_nonneg (mul_nonneg hu hu) hv, mul_nonneg (mul_nonneg hu hu) hu, mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv, mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv]


end R3Cert.Step3
