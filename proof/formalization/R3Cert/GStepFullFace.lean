import Mathlib
import R3Cert.GStep2TypeFace
import R3Cert.GStep3TypeFace

/-!
  # g-step full 3-type face: `GS3 b a c ≤ T` for ALL `a` (capstone) — 2026-08-22

  Assembles the `{ν*, ½, leaf}` coverage into a single statement over the whole 3-type support,
  by re-proving the `a=0` pure-leaf face directly in `R3Cert` (the homogeneous `GS_arm_le` lives in
  a *separate* lake project — `telperion/examples/g1_floors/lean` — so it cannot be imported here;
  the pure-leaf face is small, so we re-derive it).

  **Pure-leaf face** (`a=0`): `GS2 0 c = base2(0,c)^11 · W^c`, `base2(0,c)=(12c+8)/(6(c+1))`.
  Unlike the `a≥1` case, `GS_leaf` *rises* `c=0→1` (`23.68 → T`) then falls, so the c-step is
  antitone only for `c≥1`; the cleared step reduces to `84c²+224c−92 = 84(c²−c)+308c−92 ≥ 216 > 0`
  (`c≥1`), same `(58/51)` / `64·58^11 ≤ 621·51^11` constant as the general c-step. Terminal
  `GS2(0,1) = (5/3)^11·W = T`, and `GS2(0,0) = (4/3)^11 ≈ 23.68 < T`.

  **Capstone** (`gs3_full`): for every `b, a, c`, `GS3 b a c ≤ T`. `a≥1` → `gs3_le_T`;
  `a=0` → `base3` b-antitone → `GS3 0 0 c = GS2 0 c ≤ T` (pure-leaf). All in `ℚ`.
  conjecture1_proved = False.

  Idioms mirror the CI-green `GStep2TypeFace`.
-/

namespace R3Cert.GStepFullFace

open R3Cert.GStep2TypeFace R3Cert.GStep3TypeFace

/-- Pure-leaf c-step cleared (`c≥1`): `64·U^11 ≤ 621·V^11`, `U=(12c+20)(6(c+1))`,
    `V=(12c+8)(6(c+2))`.  `58V−51U = 6(84c²+224c−92) ≥ 0` for `c≥1`. -/
lemma leaf_cleared (c : ℕ) (hc : 1 ≤ c) :
    (64 : ℚ) * ((12 * (c : ℚ) + 20) * (6 * ((c : ℚ) + 1))) ^ 11
      ≤ 621 * ((12 * (c : ℚ) + 8) * (6 * ((c : ℚ) + 2))) ^ 11 := by
  have hc' : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc
  set U : ℚ := (12 * (c : ℚ) + 20) * (6 * ((c : ℚ) + 1)) with hU
  set V : ℚ := (12 * (c : ℚ) + 8) * (6 * ((c : ℚ) + 2)) with hV
  have hU0 : (0 : ℚ) ≤ U := by rw [hU]; positivity
  have hV0 : (0 : ℚ) ≤ V := by rw [hV]; positivity
  have hstep : U ≤ (58 / 51) * V := by
    rw [hU, hV]
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ (c:ℚ) - 1) (by positivity : (0:ℚ) ≤ (c:ℚ)), hc']
  calc (64 : ℚ) * U ^ 11
      ≤ 64 * ((58 / 51) * V) ^ 11 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU0 hstep 11) (by norm_num)
    _ = (64 * 58 ^ 11) / 51 ^ 11 * V ^ 11 := by ring
    _ ≤ 621 * V ^ 11 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hV0 11)

/-- Pure-leaf per-step c-ratio (`c≥1`). -/
lemma leaf_key (c : ℕ) (hc : 1 ≤ c) :
    ((12 * (c : ℚ) + 20) / (6 * ((c : ℚ) + 2))) ^ 11 * (64 / 621)
      ≤ ((12 * (c : ℚ) + 8) / (6 * ((c : ℚ) + 1))) ^ 11 := by
  rw [div_pow, div_pow, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have lhs_eq : (12 * (c : ℚ) + 20) ^ 11 * 64 * (6 * ((c : ℚ) + 1)) ^ 11
      = 64 * ((12 * (c : ℚ) + 20) * (6 * ((c : ℚ) + 1))) ^ 11 := by ring
  have rhs_eq : (12 * (c : ℚ) + 8) ^ 11 * ((6 * ((c : ℚ) + 2)) ^ 11 * 621)
      = 621 * ((12 * (c : ℚ) + 8) * (6 * ((c : ℚ) + 2))) ^ 11 := by ring
  rw [lhs_eq, rhs_eq]
  exact leaf_cleared c hc

/-- `GS2 0` is antitone in `c` for `c≥1`. -/
lemma leaf_step (c : ℕ) (hc : 1 ≤ c) : GS2 0 (c + 1) ≤ GS2 0 c := by
  have hbw : (0 : ℚ) ≤ Bhalf ^ 0 * (64 / 621 : ℚ) ^ c :=
    mul_nonneg (pow_nonneg Bhalf_nonneg 0) (by positivity)
  have hfp1 : GS2 0 (c + 1)
      = ((12 * (c : ℚ) + 20) / (6 * ((c : ℚ) + 2))) ^ 11 * (64 / 621)
          * (Bhalf ^ 0 * (64 / 621) ^ c) := by
    unfold GS2 base2 W; rw [pow_succ]; push_cast; ring
  have hfp0 : GS2 0 c
      = ((12 * (c : ℚ) + 8) / (6 * ((c : ℚ) + 1))) ^ 11 * (Bhalf ^ 0 * (64 / 621) ^ c) := by
    unfold GS2 base2 W; push_cast; ring
  rw [hfp1, hfp0]
  exact mul_le_mul_of_nonneg_right (leaf_key c hc) hbw

/-- `GS2 0 c ≤ GS2 0 1` for `c≥1`. -/
lemma leaf_antitone (c : ℕ) (hc : 1 ≤ c) : GS2 0 c ≤ GS2 0 1 := by
  induction c, hc using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (leaf_step n hn) ih

set_option maxHeartbeats 1000000 in
/-- **Pure-leaf face** (`a=0`): `GS2 0 c ≤ T` for all `c` (max `T` at `c=1`). -/
theorem gs2_leaf_le_T (c : ℕ) : GS2 0 c ≤ T := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; norm_num [GS2, base2, Bhalf, W, T]
  · have h1 : GS2 0 1 ≤ T := by norm_num [GS2, base2, Bhalf, W, T]
    exact le_trans (leaf_antitone c hc) h1

/-- **Capstone.** The full `{ν*, ½, leaf}` 3-type face for ALL `a`: `GS3 b a c ≤ T`.
    `a≥1` via `gs3_le_T`; `a=0` via b-antitone to the pure-leaf face. -/
theorem gs3_full (b a c : ℕ) : GS3 b a c ≤ T := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact le_trans (gs3_b_antitone b 0 c) (by rw [GS3_zero]; exact gs2_leaf_le_T c)
  · exact gs3_le_T b a c ha

end R3Cert.GStepFullFace
