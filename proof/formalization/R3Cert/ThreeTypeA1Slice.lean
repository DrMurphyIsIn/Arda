import Mathlib

/-!
  # 3-type g-step: the `a=1` slice (one half-child + `c` leaves) — 2026-08-21

  The g-step's heterogeneous crux reduces (below-average lemma + sum-preserving bang-bang) to
  the **3-type family** `{a children at μ=½, b at μ=ν*, c leaves at μ=1}` (see
  `docs/GSTEP_STEP1_IS_THE_CRUX.md`).  This file kernel-checks the cleanest genuinely
  *heterogeneous* slice of that family: `a=1, b=0` — one child at `μ=½` plus `c` leaves.

  `GS1 c = base1(c)^11 · Bcap(½) · W^c`, with `base1(c) = (12c+17)/(6(c+2))` the cavity base of
  `{½, 1^c}`, `Bcap(½) = glemma(½) = W²(10/7)^11 = 0.53715…` (at `μ=½`, `glemma` is the binding
  branch of `Bcap = min(master_ub, glemma, 1)`), `W = 64/621`, `T = W(5/3)^11`.

  `GS1` is antitone in `c` (proved via the cleared per-step inequality, `master_core` pattern),
  so `GS1 c ≤ GS1 0 = (17/12)^11·Bcap(½) = 0.872·T ≤ T` — strict below the arm.  This is a real
  heterogeneous case (mixed `½`+leaf), NOT covered by the homogeneous bound `homog_master`.
  All in `ℚ`, no `rpow`.  `conjecture1_proved = False`.
-/

namespace R3Cert.ThreeTypeA1Slice

def W : ℚ := 64 / 621
def T : ℚ := W * (5 / 3) ^ 11
/-- `Bcap(1/2) = glemma(1/2) = W²·(10/7)^11`. -/
def Bhalf : ℚ := W ^ 2 * (10 / 7) ^ 11
/-- Cavity base of `{1 child at 1/2, c leaves}`: `(12c+17)/(6(c+2))`. -/
def base1 (c : ℕ) : ℚ := (12 * (c : ℚ) + 17) / (6 * ((c : ℚ) + 2))
/-- g-step factor of `{1 half-child, c leaves}`. -/
def GS1 (c : ℕ) : ℚ := (base1 c) ^ 11 * Bhalf * W ^ c

/-- Cleared per-step inequality (`master_core` shape): with `A = 72c²+318c+306 ≥ 306`,
    `64·(A+42)^11 ≤ 621·A^11`, from `A+42 ≤ (58/51)·A` (⟺ `A≥306`) and `64·58^11 ≤ 621·51^11`. -/
lemma gs1_cleared (c : ℕ) :
    (64 : ℚ) * (72 * (c : ℚ) ^ 2 + 318 * c + 348) ^ 11
      ≤ 621 * (72 * (c : ℚ) ^ 2 + 318 * c + 306) ^ 11 := by
  have hc : (0 : ℚ) ≤ (c : ℚ) := by positivity
  set A : ℚ := 72 * (c : ℚ) ^ 2 + 318 * c + 306 with hA
  have hA306 : (306 : ℚ) ≤ A := by rw [hA]; nlinarith [sq_nonneg (c : ℚ), hc]
  have h1 : 72 * (c : ℚ) ^ 2 + 318 * c + 348 = A + 42 := by rw [hA]; ring
  rw [h1]
  have hA1 : (0 : ℚ) ≤ A + 42 := by linarith
  have hstep : A + 42 ≤ (58 / 51) * A := by nlinarith
  calc (64 : ℚ) * (A + 42) ^ 11
      ≤ 64 * ((58 / 51) * A) ^ 11 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA1 hstep 11) (by norm_num)
    _ = (64 * 58 ^ 11) / 51 ^ 11 * A ^ 11 := by ring
    _ ≤ 621 * A ^ 11 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- Per-step ratio (denominators cleared via `gs1_cleared`). -/
lemma gs1_key (c : ℕ) :
    ((12 * (c : ℚ) + 29) / (6 * ((c : ℚ) + 3))) ^ 11 * (64 / 621)
      ≤ ((12 * (c : ℚ) + 17) / (6 * ((c : ℚ) + 2))) ^ 11 := by
  rw [div_pow, div_pow, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have lhs_eq : (12 * (c : ℚ) + 29) ^ 11 * 64 * (6 * ((c : ℚ) + 2)) ^ 11
      = 64 * (72 * (c : ℚ) ^ 2 + 318 * c + 348) ^ 11 := by
    rw [show 72 * (c : ℚ) ^ 2 + 318 * c + 348
          = (12 * (c : ℚ) + 29) * (6 * ((c : ℚ) + 2)) from by ring, mul_pow]; ring
  have rhs_eq : (12 * (c : ℚ) + 17) ^ 11 * ((6 * ((c : ℚ) + 3)) ^ 11 * 621)
      = 621 * (72 * (c : ℚ) ^ 2 + 318 * c + 306) ^ 11 := by
    rw [show 72 * (c : ℚ) ^ 2 + 318 * c + 306
          = (12 * (c : ℚ) + 17) * (6 * ((c : ℚ) + 3)) from by ring, mul_pow]; ring
  rw [lhs_eq, rhs_eq]
  exact gs1_cleared c

/-- `GS1` is antitone in `c`. -/
lemma gs1_step (c : ℕ) : GS1 (c + 1) ≤ GS1 c := by
  have hc : (0 : ℚ) ≤ Bhalf * (64 / 621 : ℚ) ^ c := by
    have : (0 : ℚ) ≤ Bhalf := by norm_num [Bhalf, W]
    positivity
  have hfp1 : GS1 (c + 1)
      = ((12 * (c : ℚ) + 29) / (6 * ((c : ℚ) + 3))) ^ 11 * (64 / 621) * (Bhalf * (64 / 621) ^ c) := by
    unfold GS1 base1 W; rw [pow_succ]; push_cast; ring
  rw [hfp1]; unfold GS1 base1 W
  exact mul_le_mul_of_nonneg_right (gs1_key c) hc

set_option maxHeartbeats 1000000 in
/-- **The `a=1` slice.** `{1 child at μ=½} + c leaves` satisfies the g-step `≤ T` for all `c`. -/
theorem gs1_le_T (c : ℕ) : GS1 c ≤ T := by
  have hmono : GS1 c ≤ GS1 0 := by
    induction c with
    | zero => le_refl _
    | succ n ih => exact le_trans (gs1_step n) ih
  have h0 : GS1 0 ≤ T := by norm_num [GS1, base1, Bhalf, W, T]
  linarith

end R3Cert.ThreeTypeA1Slice
