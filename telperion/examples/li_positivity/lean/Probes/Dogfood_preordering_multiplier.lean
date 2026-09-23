/-
  Dogfood_preordering_multiplier -- the Telperion `preordering_multiplier` kind
  (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 3; SHAPES_AUDIT_D_LI_FACE section 3.1, with the
  `li_box_rung` dogfood family of section 3.3) regenerating the Li box rungs of LiBoxRungs.lean:

    re_Q3/Q4/Q5_nonneg_regen   the three hand certificates (multipliers 1, 14 s, s^2 over the
                               generators d = Re z - |z|^2, B = (Im z)^2, s = |z|^2), transcribed
                               verbatim and re-checked exactly by the certifier;
    re_Q4/Q5_nonneg_lp         the same rungs with the certificate FOUND by the emitter's exact
                               LP (multiplier candidates: the constant, then s, s^2, s^3);
    re_Q1/Q2_nonneg_regen      the two M = 1 rungs (the audit's MISS rows), LP-found;
    re_Q6_disk_claim_false     the N = 6 REFUSAL made kernel-checkable: the exact grid scan of the
                               disk located a point where Re Q_6 < 0 (OBSTRUCTED_AND_LOCATED).

  Each regenerated lemma is a real-variable core `<name>_real` (x = Re z, y = Im z) plus a thin
  complex face `<name>` stating the island's form `0 <= (LowHeightBox.Q<N> z).re`.  The block
  between the telperion provenance header and `end DogfoodPreorderingMultiplier` is the FROZEN
  emitter output (examples/li_positivity/dogfood_preordering_multiplier.py regenerates it; a test
  pins the bytes).  The blocks after it are generator-appended: the Q_6 refutation, then
  cross-checks applying each regenerated lemma to the ORIGINAL's statement, and the island's
  termwise dispatch `liPairedSummand_re_nonneg` re-assembled from the regenerated lemmas alone.
  Nothing in LiBoxRungs is modified.

  Run: cd telperion/examples/li_positivity/lean && lake env lean Probes/Dogfood_preordering_multiplier.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a finite real
  polynomial inequality on the disk (Re z)^2 + (Im z)^2 <= Re z, and N = 6 already fails there.
-/
/- telperion 0.1.6 | family DogfoodPreorderingMultiplier | input-hash ca19f4e515910f98
   14 theorems, 115 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import LiBoxRungs

namespace DogfoodPreorderingMultiplier

/-- `re_Q1_nonneg_regen_real` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE
    MULTIPLIER and a constant-coefficient preordering identity (Telperion `preordering_multiplier`).
    Generators (each `>= 0` on the set): `d = x - x ^ 2 - y ^ 2` [hyp]; `B = y ^ 2` [structural];
    `s = x ^ 2 + y ^ 2` [structural].
    Multiplier `M = 1`; certificate: 2 products of the generators with nonnegative rational
    coefficients; the identity `M * p = sum c_a prod g^a` verified EXACTLY in rational arithmetic
    (residual 0); found by the exact LP, product degree <= 1.
    Multiplier zero locus: none -- the multiplier is a positive constant.
    A FINITE real polynomial inequality on the stated set; nothing here bears on RH.
    conjecture1_proved = False. -/
theorem re_Q1_nonneg_regen_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :
    0 ≤ x := by
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  have key : x = d + s := by
    rw [hde, hse]
    ring
  rw [key]
  positivity

/-- `re_Q1_nonneg_regen` -- the complex real-part face of `re_Q1_nonneg_regen_real`.
    ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` shape, whose unfold list
    is the island's own) rewrites the real part into the base coordinates, then the real core
    applies. conjecture1_proved = False. -/
theorem re_Q1_nonneg_regen {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :
    0 ≤ (LowHeightBox.Q1 z).re := by
  have hre : (LowHeightBox.Q1 z).re = z.re := by
    simp only [LowHeightBox.Q1]
  rw [hre]
  exact re_Q1_nonneg_regen_real z.re z.im hz

/-- `re_Q2_nonneg_regen_real` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE
    MULTIPLIER and a constant-coefficient preordering identity (Telperion `preordering_multiplier`).
    Generators (each `>= 0` on the set): `d = x - x ^ 2 - y ^ 2` [hyp]; `B = y ^ 2` [structural];
    `s = x ^ 2 + y ^ 2` [structural].
    Multiplier `M = 1`; certificate: 3 products of the generators with nonnegative rational
    coefficients; the identity `M * p = sum c_a prod g^a` verified EXACTLY in rational arithmetic
    (residual 0); found by the exact LP, product degree <= 1.
    Multiplier zero locus: none -- the multiplier is a positive constant.
    A FINITE real polynomial inequality on the stated set; nothing here bears on RH.
    conjecture1_proved = False. -/
theorem re_Q2_nonneg_regen_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :
    0 ≤ 4 * x + y ^ 2 - x ^ 2 := by
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  have key : 4 * x + y ^ 2 - x ^ 2 = 4 * d + 2 * B + 3 * s := by
    rw [hde, hBe, hse]
    ring
  rw [key]
  positivity

/-- `re_Q2_nonneg_regen` -- the complex real-part face of `re_Q2_nonneg_regen_real`.
    ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` shape, whose unfold list
    is the island's own) rewrites the real part into the base coordinates, then the real core
    applies. conjecture1_proved = False. -/
theorem re_Q2_nonneg_regen {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :
    0 ≤ (LowHeightBox.Q2 z).re := by
  have hre : (LowHeightBox.Q2 z).re = 4 * z.re + z.im ^ 2 - z.re ^ 2 := by
    simp only [LowHeightBox.Q2, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, Complex.mul_im]
    ring
  rw [hre]
  exact re_Q2_nonneg_regen_real z.re z.im hz

/-- `re_Q3_nonneg_regen_real` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE
    MULTIPLIER and a constant-coefficient preordering identity (Telperion `preordering_multiplier`).
    Generators (each `>= 0` on the set): `d = x - x ^ 2 - y ^ 2` [hyp]; `B = y ^ 2` [structural];
    `s = x ^ 2 + y ^ 2` [structural].
    Multiplier `M = 1`; certificate: 8 products of the generators with nonnegative rational
    coefficients; the identity `M * p = sum c_a prod g^a` verified EXACTLY in rational arithmetic
    (residual 0); supplied by the caller, re-checked by the certifier.
    Multiplier zero locus: none -- the multiplier is a positive constant.
    A FINITE real polynomial inequality on the stated set; nothing here bears on RH.
    conjecture1_proved = False. -/
theorem re_Q3_nonneg_regen_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :
    0 ≤ 9 * x + 6 * y ^ 2 + x ^ 3 - 6 * x ^ 2 - 3 * x * y ^ 2 := by
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  have key : 9 * x + 6 * y ^ 2 + x ^ 3 - 6 * x ^ 2 - 3 * x * y ^ 2 = 9 * d + 15 * B + 3 * d ^ 2
      + 3 * d * s + 4 * d ^ 3 + 12 * d ^ 2 * s + 12 * d * s ^ 2 + 4 * s ^ 3 := by
    rw [hde, hBe, hse]
    ring
  rw [key]
  positivity

/-- `re_Q3_nonneg_regen` -- the complex real-part face of `re_Q3_nonneg_regen_real`.
    ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` shape, whose unfold list
    is the island's own) rewrites the real part into the base coordinates, then the real core
    applies. conjecture1_proved = False. -/
theorem re_Q3_nonneg_regen {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :
    0 ≤ (LowHeightBox.Q3 z).re := by
  have hre : (LowHeightBox.Q3 z).re = 9 * z.re + 6 * z.im ^ 2 + z.re ^ 3 - 6 * z.re ^ 2
      - 3 * z.re * z.im ^ 2 := by
    simp only [LowHeightBox.Q3, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, Complex.mul_im, Complex.add_re]
    ring
  rw [hre]
  exact re_Q3_nonneg_regen_real z.re z.im hz

/-- `re_Q4_nonneg_regen_real` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE
    MULTIPLIER and a constant-coefficient preordering identity (Telperion `preordering_multiplier`).
    Generators (each `>= 0` on the set): `d = x - x ^ 2 - y ^ 2` [hyp]; `B = y ^ 2` [structural];
    `s = x ^ 2 + y ^ 2` [structural].
    Multiplier `M = 14 * s`; certificate: 14 products of the generators with nonnegative rational
    coefficients; the identity `M * p = sum c_a prod g^a` verified EXACTLY in rational arithmetic
    (residual 0); supplied by the caller, re-checked by the certifier.
    Multiplier zero locus: s = 0 forces (x = 0, y = 0), where p = 0 >= 0.
    A FINITE real polynomial inequality on the stated set; nothing here bears on RH.
    conjecture1_proved = False. -/
theorem re_Q4_nonneg_regen_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :
    0 ≤ 16 * x + 20 * y ^ 2 + 8 * x ^ 3 + 6 * x ^ 2 * y ^ 2 - 20 * x ^ 2 - 24 * x * y ^ 2 - x ^ 4
      - y ^ 4 := by
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  generalize hP : 16 * x + 20 * y ^ 2 + 8 * x ^ 3 + 6 * x ^ 2 * y ^ 2 - 20 * x ^ 2 - 24 * x * y ^ 2
      - x ^ 4 - y ^ 4 = P
  have key : 14 * s * P = 44 * d * B + 180 * d * s + 433 * B ^ 2 + 44 * B * s + 27 * s ^ 2
      + 44 * d ^ 3 + 438 * d ^ 2 * B + 408 * d * B * s + 5 * d ^ 4 + 112 * d ^ 2 * B * s
      + 224 * d * B * s ^ 2 + 20 * d * s ^ 3 + 112 * B * s ^ 3 + 15 * s ^ 4 := by
    rw [← hP, hde, hBe, hse]
    ring
  have hcert : 0 ≤ 14 * s * P := by rw [key]; positivity
  rcases eq_or_lt_of_le hs0 with hs' | hs'
  · -- locus: s = 0 forces x = 0, y = 0, where the target is 0
    have hlocx : x = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    have hlocy : y = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    rw [← hP, hlocx, hlocy]
    norm_num
  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 14 * s)).mp hcert

/-- `re_Q4_nonneg_regen` -- the complex real-part face of `re_Q4_nonneg_regen_real`.
    ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` shape, whose unfold list
    is the island's own) rewrites the real part into the base coordinates, then the real core
    applies. conjecture1_proved = False. -/
theorem re_Q4_nonneg_regen {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :
    0 ≤ (LowHeightBox.Q4 z).re := by
  have hre : (LowHeightBox.Q4 z).re = 16 * z.re + 20 * z.im ^ 2 + 8 * z.re ^ 3
      + 6 * z.re ^ 2 * z.im ^ 2 - 20 * z.re ^ 2 - 24 * z.re * z.im ^ 2 - z.re ^ 4 - z.im ^ 4 := by
    simp only [LowHeightBox.Q4, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, Complex.mul_im, Complex.add_re]
    ring
  rw [hre]
  exact re_Q4_nonneg_regen_real z.re z.im hz

/-- `re_Q5_nonneg_regen_real` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE
    MULTIPLIER and a constant-coefficient preordering identity (Telperion `preordering_multiplier`).
    Generators (each `>= 0` on the set): `d = x - x ^ 2 - y ^ 2` [hyp]; `B = y ^ 2` [structural];
    `s = x ^ 2 + y ^ 2` [structural].
    Multiplier `M = s ^ 2`; certificate: 18 products of the generators with nonnegative rational
    coefficients; the identity `M * p = sum c_a prod g^a` verified EXACTLY in rational arithmetic
    (residual 0); supplied by the caller, re-checked by the certifier.
    Multiplier zero locus: s = 0 forces (x = 0, y = 0), where p = 0 >= 0.
    A FINITE real polynomial inequality on the stated set; nothing here bears on RH.
    conjecture1_proved = False. -/
theorem re_Q5_nonneg_regen_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :
    0 ≤ 25 * x + 50 * y ^ 2 + 35 * x ^ 3 + 60 * x ^ 2 * y ^ 2 + x ^ 5 + 5 * x * y ^ 4 - 50 * x ^ 2
      - 105 * x * y ^ 2 - 10 * x ^ 4 - 10 * y ^ 4 - 10 * x ^ 3 * y ^ 2 := by
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  generalize hP : 25 * x + 50 * y ^ 2 + 35 * x ^ 3 + 60 * x ^ 2 * y ^ 2 + x ^ 5 + 5 * x * y ^ 4
      - 50 * x ^ 2 - 105 * x * y ^ 2 - 10 * x ^ 4 - 10 * y ^ 4 - 10 * x ^ 3 * y ^ 2 = P
  have key : s ^ 2 * P = 14 * d * B * s + 11 * d * s ^ 2 + 68 * B ^ 3 + 4 * B ^ 2 * s
      + 3 * B * s ^ 2 + 14 * d ^ 3 * s + 72 * d ^ 2 * B ^ 2 + 70 * d ^ 2 * B * s + d ^ 2 * s ^ 2
      + 128 * d * B ^ 2 * s + 11 * d * B * s ^ 2 + 4 * d ^ 4 * B + 2 * d ^ 4 * s + 3 * d ^ 3 * s ^ 2
      + 16 * d * B ^ 2 * s ^ 2 + 4 * d * B * s ^ 3 + 16 * B ^ 2 * s ^ 3 + s ^ 5 := by
    rw [← hP, hde, hBe, hse]
    ring
  have hcert : 0 ≤ s ^ 2 * P := by rw [key]; positivity
  rcases eq_or_lt_of_le hs0 with hs' | hs'
  · -- locus: s = 0 forces x = 0, y = 0, where the target is 0
    have hlocx : x = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    have hlocy : y = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    rw [← hP, hlocx, hlocy]
    norm_num
  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < s ^ 2)).mp hcert

/-- `re_Q5_nonneg_regen` -- the complex real-part face of `re_Q5_nonneg_regen_real`.
    ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` shape, whose unfold list
    is the island's own) rewrites the real part into the base coordinates, then the real core
    applies. conjecture1_proved = False. -/
theorem re_Q5_nonneg_regen {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :
    0 ≤ (LowHeightBox.Q5 z).re := by
  have hre : (LowHeightBox.Q5 z).re = 25 * z.re + 50 * z.im ^ 2 + 35 * z.re ^ 3
      + 60 * z.re ^ 2 * z.im ^ 2 + z.re ^ 5 + 5 * z.re * z.im ^ 4 - 50 * z.re ^ 2
      - 105 * z.re * z.im ^ 2 - 10 * z.re ^ 4 - 10 * z.im ^ 4 - 10 * z.re ^ 3 * z.im ^ 2 := by
    simp only [LowHeightBox.Q5, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, Complex.mul_im, Complex.add_re]
    ring
  rw [hre]
  exact re_Q5_nonneg_regen_real z.re z.im hz

/-- `re_Q4_nonneg_lp_real` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE
    MULTIPLIER and a constant-coefficient preordering identity (Telperion `preordering_multiplier`).
    Generators (each `>= 0` on the set): `d = x - x ^ 2 - y ^ 2` [hyp]; `B = y ^ 2` [structural];
    `s = x ^ 2 + y ^ 2` [structural].
    Multiplier `M = s`; certificate: 12 products of the generators with nonnegative rational
    coefficients; the identity `M * p = sum c_a prod g^a` verified EXACTLY in rational arithmetic
    (residual 0); found by the exact LP, product degree <= 4.
    Multiplier zero locus: s = 0 forces (x = 0, y = 0), where p = 0 >= 0.
    A FINITE real polynomial inequality on the stated set; nothing here bears on RH.
    conjecture1_proved = False. -/
theorem re_Q4_nonneg_lp_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :
    0 ≤ 16 * x + 20 * y ^ 2 + 8 * x ^ 3 + 6 * x ^ 2 * y ^ 2 - 20 * x ^ 2 - 24 * x * y ^ 2 - x ^ 4
      - y ^ 4 := by
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  generalize hP : 16 * x + 20 * y ^ 2 + 8 * x ^ 3 + 6 * x ^ 2 * y ^ 2 - 20 * x ^ 2 - 24 * x * y ^ 2
      - x ^ 4 - y ^ 4 = P
  have key : s * P = 6 * d * B + 10 * d * s + 32 * B ^ 2 + B * s + 3 * s ^ 2 + 6 * d ^ 3
      + 32 * d ^ 2 * B + 5 * d ^ 2 * s + 32 * d * B * s + 8 * d ^ 2 * B * s + 16 * d * B * s ^ 2
      + 8 * B * s ^ 3 := by
    rw [← hP, hde, hBe, hse]
    ring
  have hcert : 0 ≤ s * P := by rw [key]; positivity
  rcases eq_or_lt_of_le hs0 with hs' | hs'
  · -- locus: s = 0 forces x = 0, y = 0, where the target is 0
    have hlocx : x = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    have hlocy : y = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    rw [← hP, hlocx, hlocy]
    norm_num
  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < s)).mp hcert

/-- `re_Q4_nonneg_lp` -- the complex real-part face of `re_Q4_nonneg_lp_real`.
    ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` shape, whose unfold list
    is the island's own) rewrites the real part into the base coordinates, then the real core
    applies. conjecture1_proved = False. -/
theorem re_Q4_nonneg_lp {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :
    0 ≤ (LowHeightBox.Q4 z).re := by
  have hre : (LowHeightBox.Q4 z).re = 16 * z.re + 20 * z.im ^ 2 + 8 * z.re ^ 3
      + 6 * z.re ^ 2 * z.im ^ 2 - 20 * z.re ^ 2 - 24 * z.re * z.im ^ 2 - z.re ^ 4 - z.im ^ 4 := by
    simp only [LowHeightBox.Q4, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, Complex.mul_im, Complex.add_re]
    ring
  rw [hre]
  exact re_Q4_nonneg_lp_real z.re z.im hz

/-- `re_Q5_nonneg_lp_real` -- polynomial nonnegativity on a semialgebraic set, by a POSITIVE
    MULTIPLIER and a constant-coefficient preordering identity (Telperion `preordering_multiplier`).
    Generators (each `>= 0` on the set): `d = x - x ^ 2 - y ^ 2` [hyp]; `B = y ^ 2` [structural];
    `s = x ^ 2 + y ^ 2` [structural].
    Multiplier `M = s ^ 2`; certificate: 19 products of the generators with nonnegative rational
    coefficients; the identity `M * p = sum c_a prod g^a` verified EXACTLY in rational arithmetic
    (residual 0); found by the exact LP, product degree <= 5.
    Multiplier zero locus: s = 0 forces (x = 0, y = 0), where p = 0 >= 0.
    A FINITE real polynomial inequality on the stated set; nothing here bears on RH.
    conjecture1_proved = False. -/
theorem re_Q5_nonneg_lp_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :
    0 ≤ 25 * x + 50 * y ^ 2 + 35 * x ^ 3 + 60 * x ^ 2 * y ^ 2 + x ^ 5 + 5 * x * y ^ 4 - 50 * x ^ 2
      - 105 * x * y ^ 2 - 10 * x ^ 4 - 10 * y ^ 4 - 10 * x ^ 3 * y ^ 2 := by
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=
    ⟨_, by positivity, rfl⟩
  generalize hP : 25 * x + 50 * y ^ 2 + 35 * x ^ 3 + 60 * x ^ 2 * y ^ 2 + x ^ 5 + 5 * x * y ^ 4
      - 50 * x ^ 2 - 105 * x * y ^ 2 - 10 * x ^ 4 - 10 * y ^ 4 - 10 * x ^ 3 * y ^ 2 = P
  have key : s ^ 2 * P = 18 * d * B * s + 7 * d * s ^ 2 + 68 * B ^ 3 + 6 * B ^ 2 * s + s ^ 3
      + d ^ 3 * B + 17 * d ^ 3 * s + 80 * d ^ 2 * B ^ 2 + 61 * d ^ 2 * B * s + 11 * d ^ 2 * s ^ 2
      + 124 * d * B ^ 2 * s + 21 * d * B * s ^ 2 + B * s ^ 3 + d ^ 5 + 12 * d ^ 4 * B + d ^ 4 * s
      + 12 * d ^ 3 * B * s + 16 * d * B ^ 2 * s ^ 2 + 16 * B ^ 2 * s ^ 3 := by
    rw [← hP, hde, hBe, hse]
    ring
  have hcert : 0 ≤ s ^ 2 * P := by rw [key]; positivity
  rcases eq_or_lt_of_le hs0 with hs' | hs'
  · -- locus: s = 0 forces x = 0, y = 0, where the target is 0
    have hlocx : x = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    have hlocy : y = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
    rw [← hP, hlocx, hlocy]
    norm_num
  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < s ^ 2)).mp hcert

/-- `re_Q5_nonneg_lp` -- the complex real-part face of `re_Q5_nonneg_lp_real`.
    ONE caller-supplied `simp only [...]` step (the `complex_re_im_split` shape, whose unfold list
    is the island's own) rewrites the real part into the base coordinates, then the real core
    applies. conjecture1_proved = False. -/
theorem re_Q5_nonneg_lp {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :
    0 ≤ (LowHeightBox.Q5 z).re := by
  have hre : (LowHeightBox.Q5 z).re = 25 * z.re + 50 * z.im ^ 2 + 35 * z.re ^ 3
      + 60 * z.re ^ 2 * z.im ^ 2 + z.re ^ 5 + 5 * z.re * z.im ^ 4 - 50 * z.re ^ 2
      - 105 * z.re * z.im ^ 2 - 10 * z.re ^ 4 - 10 * z.im ^ 4 - 10 * z.re ^ 3 * z.im ^ 2 := by
    simp only [LowHeightBox.Q5, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, Complex.mul_im, Complex.add_re]
    ring
  rw [hre]
  exact re_Q5_nonneg_lp_real z.re z.im hz

end DogfoodPreorderingMultiplier

/-! ## The N = 6 refusal, kernel-checked (generator-appended).
    `preordering_multiplier` REFUSED `0 <= Re Q_6` on the disk as OBSTRUCTED_AND_LOCATED:
    the exact grid scan (60 steps per axis of [0, 1] x [-1/2, 1/2]) found
    Re Q_6 = -27772/15625 < 0 at (x, y) = (4/5, -2/5), a point of the disk.  No
    certificate was emitted; the theorem below confirms in the kernel that the refused
    claim is FALSE, so the refusal is a located obstruction and not a give-up. -/

namespace DogfoodPreorderingMultiplier

/-- `re_Q6_disk_claim_false` -- the located obstruction behind a `preordering_multiplier` REFUSAL,
    kernel-checked.
    The claim `0 <= p` on the declared set is FALSE at the exact rational point
    `(x = 4/5, y = -2/5)`, where every generator is nonnegative and `p = -27772/15625`. No
    certificate was emitted for it. conjecture1_proved = False. -/
theorem re_Q6_disk_claim_false :
    ¬ ∀ x y : ℝ, x ^ 2 + y ^ 2 ≤ x → 0 ≤ 36 * x + 105 * y ^ 2 + 112 * x ^ 3 + 324 * x ^ 2 * y ^ 2
      + 12 * x ^ 5 + 60 * x * y ^ 4 + 15 * x ^ 4 * y ^ 2 + y ^ 6 - 105 * x ^ 2 - 336 * x * y ^ 2
      - 54 * x ^ 4 - 54 * y ^ 4 - 120 * x ^ 3 * y ^ 2 - x ^ 6 - 15 * x ^ 2 * y ^ 4 := by
  intro h
  have hw := h (4 / 5) (-(2 / 5)) (by norm_num)
  norm_num at hw

end DogfoodPreorderingMultiplier

/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the block
    above the refutation is the frozen emitter output).  Each `example` is closed by applying one
    side to the other's statement, so a drift in either statement fails to elaborate. -/

section CrossChecks
open DogfoodPreorderingMultiplier

/-- The regenerated rungs prove the ORIGINAL `LowHeightBox.re_Q<N>_nonneg` statements ... -/
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q1 z).re :=
  re_Q1_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q2 z).re :=
  re_Q2_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q3 z).re :=
  re_Q3_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q4 z).re :=
  re_Q4_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q5 z).re :=
  re_Q5_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q4 z).re :=
  re_Q4_nonneg_lp hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q5 z).re :=
  re_Q5_nonneg_lp hz

/-- ... and the originals prove the regenerated statements: the two are interchangeable. -/
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q3 z).re :=
  LowHeightBox.re_Q3_nonneg hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q4 z).re :=
  LowHeightBox.re_Q4_nonneg hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q5 z).re :=
  LowHeightBox.re_Q5_nonneg hz

/-- The island's termwise dispatch (`LowHeightBox.liPairedSummand_re_nonneg`) re-assembled from the
    regenerated lemmas alone: they are drop-in replacements for the hand proofs. -/
example (n : ℕ) (hn : n ≤ 4) (ρ : LiCriterion.NontrivialZero) :
    0 ≤ (LiCriterion.liPairedSummand n ρ).re := by
  have hz := LowHeightBox.zOf_mem_disk ρ
  interval_cases n
  · rw [LowHeightBox.liPairedSummand_zero_eq]; exact re_Q1_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_one_eq]; exact re_Q2_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_two_eq]; exact re_Q3_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_three_eq]; exact re_Q4_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_four_eq]; exact re_Q5_nonneg_regen hz

end CrossChecks

#print axioms DogfoodPreorderingMultiplier.re_Q1_nonneg_regen_real
#print axioms DogfoodPreorderingMultiplier.re_Q1_nonneg_regen
#print axioms DogfoodPreorderingMultiplier.re_Q2_nonneg_regen_real
#print axioms DogfoodPreorderingMultiplier.re_Q2_nonneg_regen
#print axioms DogfoodPreorderingMultiplier.re_Q3_nonneg_regen_real
#print axioms DogfoodPreorderingMultiplier.re_Q3_nonneg_regen
#print axioms DogfoodPreorderingMultiplier.re_Q4_nonneg_regen_real
#print axioms DogfoodPreorderingMultiplier.re_Q4_nonneg_regen
#print axioms DogfoodPreorderingMultiplier.re_Q5_nonneg_regen_real
#print axioms DogfoodPreorderingMultiplier.re_Q5_nonneg_regen
#print axioms DogfoodPreorderingMultiplier.re_Q4_nonneg_lp_real
#print axioms DogfoodPreorderingMultiplier.re_Q4_nonneg_lp
#print axioms DogfoodPreorderingMultiplier.re_Q5_nonneg_lp_real
#print axioms DogfoodPreorderingMultiplier.re_Q5_nonneg_lp
#print axioms DogfoodPreorderingMultiplier.re_Q6_disk_claim_false
