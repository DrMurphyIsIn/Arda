import Mathlib

/-!
  # 3-type g-step: the full `{½, leaf}` face (all `a≥1`, all `c`) — 2026-08-21

  Generalises the `a=1` slice (`ThreeTypeA1Slice`) to the whole `{a children at μ=½,
  c leaves}` family.  `GS2 a c = base2(a,c)^11 · Bcap(½)^a · W^c`,
  `base2(a,c) = (9a+12c+8)/(6(a+c+1))`, `Bcap(½) = W²(10/7)^11`, `W=64/621`, `T=W(5/3)^11`.

  Two clean factored monotonicities (both tight at `a=1`, verified exact):
  * **c-antitone** (all `a≥1`): `GS2 a (c+1) ≤ GS2 a c` — `U ≤ (58/51)·V` from `58V−51U =
    6·((a-1)(63a+92) + 147ac + 84c² + 224c) ≥ 0`, constant `64·(58/51)^11 ≤ 621`.
  * **a-antitone** (`c=0`, all `a≥1`): `GS2 (a+1) 0 ≤ GS2 a 0` — `Ua ≤ (52/51)·Va` from
    `6·(a-1)(9a+35) ≥ 0`, constant `Bcap(½)·(52/51)^11 ≤ 1`.

  Every `(a,c)` with `a≥1` reduces (c-antitone → `c=0`, a-antitone → `a=1`) to
  `GS2 1 0 = (17/12)^11·Bcap(½) = 0.872·T ≤ T`.  The `a=0` face is the homogeneous pure-leaf
  (`GS_arm_le`/`homog_master`).  All in `ℚ`, no `rpow`.  conjecture1_proved = False.

  Idioms mirror the CI-green `ThreeTypeA1Slice` (`master_core` cleared-lemma shape).
-/

namespace R3Cert.GStep2TypeFace

def W : ℚ := 64 / 621
def T : ℚ := W * (5 / 3) ^ 11
def Bhalf : ℚ := W ^ 2 * (10 / 7) ^ 11
def base2 (a c : ℕ) : ℚ := (9 * (a : ℚ) + 12 * c + 8) / (6 * ((a : ℚ) + c + 1))
def GS2 (a c : ℕ) : ℚ := (base2 a c) ^ 11 * Bhalf ^ a * W ^ c

lemma Bhalf_nonneg : (0 : ℚ) ≤ Bhalf := by norm_num [Bhalf, W]

/-- c-antitone cleared: `64·U^11 ≤ 621·V^11`, `U=(9a+12c+20)(6(a+c+1))`,
    `V=(9a+12c+8)(6(a+c+2))`, for `a≥1`. -/
lemma cleared_c (a c : ℕ) (ha : 1 ≤ a) :
    (64 : ℚ) * ((9 * (a : ℚ) + 12 * c + 20) * (6 * ((a : ℚ) + c + 1))) ^ 11
      ≤ 621 * ((9 * (a : ℚ) + 12 * c + 8) * (6 * ((a : ℚ) + c + 2))) ^ 11 := by
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hc' : (0 : ℚ) ≤ (c : ℚ) := by positivity
  set U : ℚ := (9 * (a : ℚ) + 12 * c + 20) * (6 * ((a : ℚ) + c + 1)) with hU
  set V : ℚ := (9 * (a : ℚ) + 12 * c + 8) * (6 * ((a : ℚ) + c + 2)) with hV
  have hU0 : (0 : ℚ) ≤ U := by rw [hU]; positivity
  have hV0 : (0 : ℚ) ≤ V := by rw [hV]; positivity
  have hstep : U ≤ (58 / 51) * V := by
    rw [hU, hV]
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ (a:ℚ) - 1) (by positivity : (0:ℚ) ≤ 63*(a:ℚ)+92),
      mul_nonneg (show (0:ℚ) ≤ (a:ℚ) by linarith) hc', sq_nonneg (c:ℚ), hc', ha']
  calc (64 : ℚ) * U ^ 11
      ≤ 64 * ((58 / 51) * V) ^ 11 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU0 hstep 11) (by norm_num)
    _ = (64 * 58 ^ 11) / 51 ^ 11 * V ^ 11 := by ring
    _ ≤ 621 * V ^ 11 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hV0 11)

set_option maxHeartbeats 1600000 in
/-- Per-step c-ratio (explicit fractions, mirrors `gs1_key`): `a≥1`. -/
lemma key_c (a c : ℕ) (ha : 1 ≤ a) :
    ((9 * (a : ℚ) + 12 * c + 20) / (6 * ((a : ℚ) + c + 2))) ^ 11 * (64 / 621)
      ≤ ((9 * (a : ℚ) + 12 * c + 8) / (6 * ((a : ℚ) + c + 1))) ^ 11 := by
  rw [div_pow, div_pow, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have lhs_eq : (9 * (a : ℚ) + 12 * c + 20) ^ 11 * 64 * (6 * ((a : ℚ) + c + 1)) ^ 11
      = 64 * ((9 * (a : ℚ) + 12 * c + 20) * (6 * ((a : ℚ) + c + 1))) ^ 11 := by
    ring
  have rhs_eq : (9 * (a : ℚ) + 12 * c + 8) ^ 11 * ((6 * ((a : ℚ) + c + 2)) ^ 11 * 621)
      = 621 * ((9 * (a : ℚ) + 12 * c + 8) * (6 * ((a : ℚ) + c + 2))) ^ 11 := by
    ring
  rw [lhs_eq, rhs_eq]
  exact cleared_c a c ha

/-- `GS2` is antitone in `c` for `a≥1`. -/
lemma cstep (a c : ℕ) (ha : 1 ≤ a) : GS2 a (c + 1) ≤ GS2 a c := by
  have hbw : (0 : ℚ) ≤ Bhalf ^ a * (64 / 621 : ℚ) ^ c :=
    mul_nonneg (pow_nonneg Bhalf_nonneg a) (by positivity)
  have hfp1 : GS2 a (c + 1)
      = ((9 * (a : ℚ) + 12 * c + 20) / (6 * ((a : ℚ) + c + 2))) ^ 11 * (64 / 621)
          * (Bhalf ^ a * (64 / 621) ^ c) := by
    unfold GS2 base2 W; rw [pow_succ]; push_cast; ring
  rw [hfp1]; unfold GS2 base2 W
  conv_rhs => rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right (key_c a c ha) hbw

/-- `GS2 a c ≤ GS2 a 0` for `a≥1`. -/
lemma c_antitone (a c : ℕ) (ha : 1 ≤ a) : GS2 a c ≤ GS2 a 0 := by
  induction c with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (cstep a n ha) ih

/-- a-antitone cleared: `Bcap(½)·Ua^11 ≤ Va^11`, `Ua=(9a+17)(6(a+1))`, `Va=(9a+8)(6(a+2))`,
    `a≥1`. -/
lemma cleared_a (a : ℕ) (ha : 1 ≤ a) :
    Bhalf * ((9 * (a : ℚ) + 17) * (6 * ((a : ℚ) + 1))) ^ 11
      ≤ ((9 * (a : ℚ) + 8) * (6 * ((a : ℚ) + 2))) ^ 11 := by
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  set Ua : ℚ := (9 * (a : ℚ) + 17) * (6 * ((a : ℚ) + 1)) with hUa
  set Va : ℚ := (9 * (a : ℚ) + 8) * (6 * ((a : ℚ) + 2)) with hVa
  have hUa0 : (0 : ℚ) ≤ Ua := by rw [hUa]; positivity
  have hVa0 : (0 : ℚ) ≤ Va := by rw [hVa]; positivity
  have hstep : Ua ≤ (52 / 51) * Va := by
    rw [hUa, hVa]
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ (a:ℚ) - 1) (by positivity : (0:ℚ) ≤ 9*(a:ℚ)+35), ha']
  calc Bhalf * Ua ^ 11
      ≤ Bhalf * ((52 / 51) * Va) ^ 11 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hUa0 hstep 11) Bhalf_nonneg
    _ = (Bhalf * 52 ^ 11 / 51 ^ 11) * Va ^ 11 := by ring
    _ ≤ 1 * Va ^ 11 := mul_le_mul_of_nonneg_right (by norm_num [Bhalf, W]) (pow_nonneg hVa0 11)
    _ = Va ^ 11 := one_mul _

set_option maxHeartbeats 1600000 in
/-- `GS2` is antitone in `a` at `c=0` for `a≥1`. -/
lemma astep (a : ℕ) (ha : 1 ≤ a) : GS2 (a + 1) 0 ≤ GS2 a 0 := by
  have hb0 : (0 : ℚ) ≤ Bhalf ^ a := pow_nonneg Bhalf_nonneg a
  have hfp1 : GS2 (a + 1) 0
      = ((9 * (a : ℚ) + 17) / (6 * ((a : ℚ) + 2))) ^ 11 * Bhalf * Bhalf ^ a := by
    unfold GS2 base2 W; rw [pow_succ]; push_cast; ring
  have hfp0 : GS2 a 0 = ((9 * (a : ℚ) + 8) / (6 * ((a : ℚ) + 1))) ^ 11 * Bhalf ^ a := by
    unfold GS2 base2 W; push_cast; ring
  rw [hfp1, hfp0]
  have hkey : ((9 * (a : ℚ) + 17) / (6 * ((a : ℚ) + 2))) ^ 11 * Bhalf
      ≤ ((9 * (a : ℚ) + 8) / (6 * ((a : ℚ) + 1))) ^ 11 := by
    rw [div_pow, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have le : (9 * (a : ℚ) + 17) ^ 11 * Bhalf * (6 * ((a : ℚ) + 1)) ^ 11
        = Bhalf * ((9 * (a : ℚ) + 17) * (6 * ((a : ℚ) + 1))) ^ 11 := by ring
    have re : (9 * (a : ℚ) + 8) ^ 11 * (6 * ((a : ℚ) + 2)) ^ 11
        = ((9 * (a : ℚ) + 8) * (6 * ((a : ℚ) + 2))) ^ 11 := by ring
    rw [le, re]
    exact cleared_a a ha
  calc ((9 * (a : ℚ) + 17) / (6 * ((a : ℚ) + 2))) ^ 11 * Bhalf * Bhalf ^ a
      = (((9 * (a : ℚ) + 17) / (6 * ((a : ℚ) + 2))) ^ 11 * Bhalf) * Bhalf ^ a := by ring
    _ ≤ ((9 * (a : ℚ) + 8) / (6 * ((a : ℚ) + 1))) ^ 11 * Bhalf ^ a :=
        mul_le_mul_of_nonneg_right hkey hb0

/-- `GS2 a 0 ≤ GS2 1 0` for `a≥1`. -/
lemma a_antitone (a : ℕ) (ha : 1 ≤ a) : GS2 a 0 ≤ GS2 1 0 := by
  induction a, ha using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (astep n hn) ih

set_option maxHeartbeats 1000000 in
/-- **The `{½, leaf}` 2-type face.** For every `a≥1` and every `c`, `GS2 a c ≤ T`. -/
theorem gs2_le_T (a c : ℕ) (ha : 1 ≤ a) : GS2 a c ≤ T := by
  have h10 : GS2 1 0 ≤ T := by norm_num [GS2, base2, Bhalf, W, T]
  exact le_trans (c_antitone a c ha) (le_trans (a_antitone a ha) h10)

end R3Cert.GStep2TypeFace
