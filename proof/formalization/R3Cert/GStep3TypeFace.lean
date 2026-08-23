import Mathlib
import R3Cert.GStep2TypeFace

/-!
  # 3-type g-step: the full `{ν*, ½, leaf}` face via RATIONAL enclosure — 2026-08-21

  Adds the third child-type — the "below-average" cap-region children `μ ≤ ν*` — to the
  `{½, leaf}` face (`GStep2TypeFace`).  The extremal cap menu `ν* ≈ 0.30774` is IRRATIONAL
  (`glemma(ν*)=1`), so instead of formalizing it per-value we use a RATIONAL over-enclosure
  `r = 31/100 ≥ ν*`: a cap child has `Bcap=1` and menu `≤ ν* ≤ r`, and raising its menu to `r`
  only raises `base`, so the enclosure over-estimates `GS`.  Everything stays in `ℚ`.

  `GS3 b a c = base3(b,a,c)^11 · Bcap(½)^a · W^c`  (b cap-children at menu `r`, `Bcap=1`;
  a children at `½`; c leaves), `base3 = (3(q+1)+3S+1)/(3(q+1))`, `q=b+a+c`, `S=b·r+a/2+c`.

  **Reduction.**  `base3` is decreasing in the cap-child count `b` — the cross-multiplied step
  reduces EXACTLY (b cancels) to the b-free `r(a+c+1) ≤ a/2 + c + 1/3`, i.e.
  `a(½−r) + c(1−r) + (⅓−r) ≥ 0`, all coefficients `>0` since `r < ⅓`.  Hence
  `GS3 b a c ≤ GS3 0 a c = GS2 a c ≤ T` for every `b` (`a≥1`).  The `a=0` sub-face (cap+leaf,
  no ½-child) is the homogeneous pure-leaf face, covered by `GS_arm_le`/`homog_master`.

  **Enclosure validity.**  `ν* ≤ r` is the single rational fact `γ ≤ (331/300)^11`
  (`γ = W²(5/3)^11`, margin ≈ 0.022), `nustar_enclosure` below.  conjecture1_proved = False.
-/

namespace R3Cert.GStep3TypeFace

open R3Cert.GStep2TypeFace

/-- Rational over-enclosure of the irrational extremal cap menu `ν* ≈ 0.30774`. -/
def r : ℚ := 31 / 100

def gamma : ℚ := W ^ 2 * (5 / 3) ^ 11

/-- Enclosure validity: `ν* ≤ 31/100` — equivalently `glemma(31/100) ≤ 1`, i.e.
    `γ ≤ (1 + r/3)^11 = (331/300)^11`.  A single `norm_num` rational fact. -/
theorem nustar_enclosure : gamma ≤ (1 + r / 3) ^ 11 := by
  norm_num [gamma, r, W]

def base3 (b a c : ℕ) : ℚ :=
  (3 * ((b : ℚ) + a + c + 1) + 3 * ((b : ℚ) * r + (a : ℚ) / 2 + (c : ℚ)) + 1)
    / (3 * ((b : ℚ) + a + c + 1))

/-- Cap children contribute `Bcap = 1`, so they appear only through `base3`. -/
def GS3 (b a c : ℕ) : ℚ := (base3 b a c) ^ 11 * Bhalf ^ a * W ^ c

/-- `b = 0` collapses `base3` to the 2-type `base2`. -/
lemma base3_zero (a c : ℕ) : base3 0 a c = base2 a c := by
  unfold base3 base2
  rw [div_eq_div_iff (by positivity) (by positivity)]
  push_cast; ring

/-- `b = 0` collapses `GS3` to `GS2`. -/
lemma GS3_zero (a c : ℕ) : GS3 0 a c = GS2 a c := by
  unfold GS3 GS2; rw [base3_zero]

/-- **The cap-child step.** `base3` is decreasing in the cap-child count `b`.  The
    cross-multiplied inequality reduces exactly (b cancels) to `r(a+c+1) ≤ a/2 + c + 1/3`. -/
lemma base3_bstep (b a c : ℕ) : base3 (b + 1) a c ≤ base3 b a c := by
  unfold base3 r
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℚ) a, Nat.cast_nonneg (α := ℚ) c,
    Nat.cast_nonneg (α := ℚ) b, mul_nonneg (Nat.cast_nonneg (α := ℚ) b) (Nat.cast_nonneg (α := ℚ) a),
    mul_nonneg (Nat.cast_nonneg (α := ℚ) b) (Nat.cast_nonneg (α := ℚ) c)]

/-- `GS3` is decreasing in the cap-child count `b`. -/
lemma gs3_bstep (b a c : ℕ) : GS3 (b + 1) a c ≤ GS3 b a c := by
  have h0 : (0 : ℚ) ≤ base3 (b + 1) a c := by unfold base3 r; positivity
  have hpow : (base3 (b + 1) a c) ^ 11 ≤ (base3 b a c) ^ 11 :=
    pow_le_pow_left₀ h0 (base3_bstep b a c) 11
  have hB : (0 : ℚ) ≤ Bhalf ^ a := pow_nonneg Bhalf_nonneg a
  have hW : (0 : ℚ) ≤ W ^ c := pow_nonneg (by norm_num [W]) c
  unfold GS3
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hB) hW

/-- `GS3 b a c ≤ GS3 0 a c` for every cap-child count `b`. -/
lemma gs3_b_antitone (b a c : ℕ) : GS3 b a c ≤ GS3 0 a c := by
  induction b with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (gs3_bstep n a c) ih

/-- **The `{ν*, ½, leaf}` 3-type face** (configs with at least one `½`-child).  For every cap-child
    count `b`, every `c`, and `a ≥ 1`, `GS3 b a c ≤ T`.  Reduces (b-antitone) to `GS2 a c ≤ T`. -/
theorem gs3_le_T (b a c : ℕ) (ha : 1 ≤ a) : GS3 b a c ≤ T :=
  le_trans (gs3_b_antitone b a c) (by rw [GS3_zero]; exact gs2_le_T a c ha)

end R3Cert.GStep3TypeFace
