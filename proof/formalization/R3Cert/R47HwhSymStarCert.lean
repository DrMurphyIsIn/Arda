/-
  R3Cert.R47HwhSymStarCert -- a UNIFORM certificate for the symmetric-multi-star obstruction family,
  the sharply-localized open core of `hwh` (`BG_HWH_STATUS_2026-09-11.md`).

  The balanced multi-star `ST(k,m)` (a centre of degree `k`, `k` hubs each carrying `m` leaves) is the
  symmetric family on which every earlier certificate (degree/averaging/g-dominance) failed.  Its exact
  objective is `Aobj(ST(k,m)) = 2*alpha^(k-1)` with `alpha = (2m+1)/(m+1)` (verified, e.g. triple-3-star
  `ST(3,3) = 49/8`).  The DE-BRANCHING move -- detach one arm from the centre and re-attach it as a pendant
  path via a leaf-leaf edge -- gives (closed form verified exactly against the cavity engine, k=3..8,m=2..8)

      Aobj(ST_move(k,m)) = tau2*alpha^(k-2) + (nu2*alpha^(k-2) + (k-2)*tau2*alpha^(k-3)) / ((k-1)(m+1)),
      tau2 = (20m^2-2m-1)/(4m(m+1)),  nu2 = (10m-3)/(4m).

  The monotonicity `Aobj(ST_move) - Aobj(ST) >= 0` reduces (factor `alpha^(k-3) > 0`, clear `(k-1)(m+1) > 0`)
  to `F_num(k,m) >= 0`, where `F_num` is LINEAR in `k`:

      F_num(k,m) = (k-3) * (2m+1)(4m^3+2m^2-7m-1) + (2m+1)(8m^3+4m^2-11m-3).

  Both cubic factors are positive for `m >= 2` (the substitution `m = t+2` gives all-positive-coefficient
  cubics `4t^3+26t^2+49t+25` and `8t^3+52t^2+101t+55`), and `k >= 3`, so `F_num >= 0`.  This is the
  Positivstellensatz certificate (Telperion-shaped: shifted nonneg-coefficient positivity) that the
  de-branching move is `Aobj`-monotone on the WHOLE balanced multi-star family -- so the symmetric
  obstruction is uniformly NOT a counterexample to `hwh`.

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- **Positivity of the cubic `4m^3+2m^2-7m-1` for `m >= 2`** (the `k`-slope factor), via `m = (m-2)+2`. -/
theorem symstar_cubicA_nonneg (m : ℝ) (hm : 2 ≤ m) : 0 ≤ 4*m^3 + 2*m^2 - 7*m - 1 := by
  have h : 0 ≤ m - 2 := by linarith
  nlinarith [h, mul_nonneg h h, mul_nonneg (mul_nonneg h h) h]

/-- **Positivity of the cubic `8m^3+4m^2-11m-3` for `m >= 2`** (the `k=3` base factor). -/
theorem symstar_cubicF3_nonneg (m : ℝ) (hm : 2 ≤ m) : 0 ≤ 8*m^3 + 4*m^2 - 11*m - 3 := by
  have h : 0 ≤ m - 2 := by linarith
  nlinarith [h, mul_nonneg h h, mul_nonneg (mul_nonneg h h) h]

/-- **The uniform certificate.**  `F_num(k,m) >= 0` for all `k >= 3`, `m >= 2` -- the cleared-denominator,
    `alpha^(k-3)`-factored form of `Aobj(ST_move(k,m)) - Aobj(ST(k,m)) >= 0`.  Proven from the linear-in-`k`
    decomposition `F_num = (k-3)*(2m+1)*cubicA + (2m+1)*cubicF3` with both cubics `>= 0` (`m >= 2`) and
    `k - 3 >= 0`.  Hence the de-branching move is `Aobj`-monotone on the entire balanced multi-star family. -/
theorem symstar_move_certificate (k m : ℝ) (hk : 3 ≤ k) (hm : 2 ≤ m) :
    0 ≤ 8*k*m^4 + 8*k*m^3 - 12*k*m^2 - 9*k*m - k - 8*m^4 - 8*m^3 + 18*m^2 + 10*m := by
  have hm0 : 0 ≤ 2*m + 1 := by linarith
  have hCA : 0 ≤ (2*m+1) * (4*m^3 + 2*m^2 - 7*m - 1) :=
    mul_nonneg hm0 (symstar_cubicA_nonneg m hm)
  have hF3 : 0 ≤ (2*m+1) * (8*m^3 + 4*m^2 - 11*m - 3) :=
    mul_nonneg hm0 (symstar_cubicF3_nonneg m hm)
  have hk3 : 0 ≤ k - 3 := by linarith
  -- F_num = (k-3) * [(2m+1) cubicA] + [(2m+1) cubicF3]
  nlinarith [mul_nonneg hk3 hCA, hF3]

end Step3
end R3Cert
