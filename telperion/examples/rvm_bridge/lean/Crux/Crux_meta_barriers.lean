/-
  Crux_meta_barriers (rvm_bridge island) -- THE GOLDEN FAKE AGAINST THE GAUSSIAN WALL.

  conjecture1_proved = False.  Nothing here says anything about where the zeros of the Riemann zeta
  function lie.

  WHAT IT PROVES.  Every theorem prints `[propext, Classical.choice, Quot.sound]` under
  `#print axioms` (the list is at the end of the file).  There is no `sorry`, no `admit`, no
  `native_decide`, no new axiom declaration and no opaque constant.
  * Section A: the anti-golden fake's zero set, 1/2 +- x0 + i (2k+1) pi / log 5
    (`XiA_eq_zero_iff`).  The islands are separate Lake projects, so this is a self-contained copy
    of section 4 of the li_positivity file.
  * Sections B-F, `fake_gaussian_nonneg`.  For every centre c and every width 0 < lam <= 1/40, the
    corpus's Gaussian test `RvMBridge6.gaussTest c lam`, summed over ALL fake zeros, has a
    nonnegative real part.  The proof covers the full lattice sum: an explicit bound on the nearest
    pair of ordinates, and a tail majorized by a two-sided geometric series.
  * Section G.  The hybrid zero side is zeta's `zeroSide` plus the fake side.  It satisfies the
    E6Bridge30 conclusion (every c, every lam <= 3/2000;
    `hybrid_gaussian_positivity_small`) and the E6Bridge16 sharp envelope for every lam <= 1/40
    (`hybrid_gaussian_envelope`), exactly as zeta does.
  * Section H, `fake_gaussian_negative`.  At width 1/2 and centre pi / log 5 the fake sum is
    NEGATIVE.  So the full Wall (every width) does detect the fake; only the widths proved so far
    are blind to it.
  * Section I.  `XiHR = xi * XiA`, with the corpus's own `xi` (`RvMBridge18.xi`), is entire and
    symmetric.  Its analytic order at every point is `zeroMult + [fake zero]`
    (`analyticOrderNatAt_XiHR`: orders add, and every fake zero is simple, `deriv_XiA_ne_zero`).
    Its multiplicity-weighted zero side is `zeroSide + fakeSide` (`XiHRZeroSide_eq`).  So the zero
    side of this one explicit entire function, which has an off-line zero, satisfies the E6Bridge30
    and E6Bridge16 conclusions (`XiHR_gaussian_positivity_small`, `XiHR_gaussian_envelope`).
  The single statement `gaussian_layer_barrier` (section J) packages these.

  WHAT IT DOES NOT PROVE.
  * Positivity of the fake sum for 1/40 < lam < lam* = 0.18271...  That is numerical only
    (telperion/research/crux_meta-barriers, check N4).
  * The hybrid envelope beyond lam = 1/40.  The paper argument is that zeta's archimedean side grows
    like log |c| while the fake side stays bounded.  Check N10 shows the crossover centre grows
    fast with lam.
  * The sign of the HYBRID sum at width 1/2.  That needs zeta's zeros near height 1.95, i.e. the
    corpus's Arb-conditional certificates.
-/

import E6Bridge30
import E6Bridge16
import E6Bridge20
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Complex

noncomputable section

namespace CruxMetaBarriersRvM

/-! ## A. The anti-golden fake (self-contained: the islands are separate Lake projects; this
section repeats the li_positivity file's section 4 verbatim in substance) -/

/-- The completed function of a genus-one datum, `Xi s = 2 cosh((s - 1/2) L) - c`
(`L = log q`, `c = m / sqrt q`). -/
noncomputable def Xi (L c : ℝ) (s : ℂ) : ℂ := 2 * Complex.cosh ((s - 1 / 2) * L) - c

/-- Functional equation `Xi (1 - s) = Xi s`. -/
theorem Xi_symm (L c : ℝ) (s : ℂ) : Xi L c (1 - s) = Xi L c s := by
  unfold Xi
  have : ((1 - s) - 1 / 2) * (L : ℂ) = -((s - 1 / 2) * L) := by ring
  rw [this, Complex.cosh_neg]

lemma cosh_decomp (x y : ℝ) :
    Complex.cosh ((x : ℂ) + y * I) =
      (Real.cosh x * Real.cos y : ℝ) + (Real.sinh x * Real.sin y : ℝ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

/-- The golden ratio. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma sqrt5_bounds : 2.236 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2361 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma phi_pos : 0 < phi := by unfold phi; positivity

lemma one_lt_phi : 1 < phi := by
  have := sqrt5_bounds.1; unfold phi; linarith

lemma phi_lt : phi < 1.61805 := by
  have := sqrt5_bounds.2; unfold phi; linarith

lemma phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi; have h := sqrt5_sq; nlinarith [h]

lemma cosh_log_phi : Real.cosh (Real.log phi) = Real.sqrt 5 / 2 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  rw [Real.cosh_log phi_pos]
  unfold phi
  have hne : (1 + Real.sqrt 5) ≠ 0 := by positivity
  field_simp
  nlinarith [h5]

lemma log5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)

lemma log5_bounds : 1.58 < Real.log 5 ∧ Real.log 5 < 1.64 := by
  have h5 : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    have e : (5 : ℝ) = 2 ^ 2 * (5 / 4) := by norm_num
    calc Real.log 5 = Real.log (2 ^ 2 * (5 / 4)) := by rw [← e]
      _ = 2 * Real.log 2 + Real.log (5 / 4) := by
          rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have hu := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  norm_num at hu hl
  constructor <;> linarith

lemma log_phi_pos : 0 < Real.log phi := Real.log_pos one_lt_phi

lemma log_phi_lt : Real.log phi < 0.61805 := by
  have := Real.log_le_sub_one_of_pos phi_pos
  have := phi_lt
  linarith

/-- `2 log phi < log 5` (i.e. `phi^2 < 5`): the fake zeros lie strictly inside the strip. -/
lemma two_log_phi_lt_log5 : 2 * Real.log phi < Real.log 5 := by
  rw [← Real.log_rpow phi_pos, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  apply Real.log_lt_log (by have := phi_pos; positivity)
  rw [phi_sq]; have := phi_lt; linarith

/-- Displacement of the fake zeros from the critical line, `log phi / log 5`. -/
noncomputable def x0 : ℝ := Real.log phi / Real.log 5

lemma x0_pos : 0 < x0 := div_pos log_phi_pos log5_pos

lemma x0_lt_half : x0 < 1 / 2 := by
  unfold x0; rw [div_lt_iff₀ log5_pos]; linarith [two_log_phi_lt_log5]

lemma x0_lt : x0 < 0.4 := by
  unfold x0; rw [div_lt_iff₀ log5_pos]
  have := log5_bounds.1; have := log_phi_lt; linarith

/-- The first fake height `pi / log 5` lies in `(1.9, 2)`. -/
lemma pi_div_log5_bounds : 1.9 < Real.pi / Real.log 5 ∧ Real.pi / Real.log 5 < 2 := by
  have h1 := log5_bounds.1
  have h2 := log5_bounds.2
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  constructor
  · rw [lt_div_iff₀ log5_pos]; nlinarith
  · rw [div_lt_iff₀ log5_pos]; nlinarith

/-- The anti-golden completed function `2 cosh((s - 1/2) log 5) + sqrt 5`. -/
noncomputable def XiA (s : ℂ) : ℂ := Xi (Real.log 5) (-Real.sqrt 5) s

/-- The explicit fake zeros `1/2 + eps x0 + i (2k+1) pi / log 5`. -/
noncomputable def fakeZero (k : ℤ) (ε : ℝ) : ℂ :=
  ((1 / 2 + ε * x0 : ℝ) : ℂ) + (((2 * k + 1) * Real.pi / Real.log 5 : ℝ) : ℂ) * I

@[simp] lemma fakeZero_re (k : ℤ) (ε : ℝ) : (fakeZero k ε).re = 1 / 2 + ε * x0 := by
  simp only [fakeZero, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

@[simp] lemma fakeZero_im (k : ℤ) (ε : ℝ) :
    (fakeZero k ε).im = (2 * k + 1) * Real.pi / Real.log 5 := by
  simp only [fakeZero, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma cosh_w0 :
    Complex.cosh ((Real.log phi : ℂ) + Real.pi * I) = ((-(Real.sqrt 5 / 2) : ℝ) : ℂ) := by
  rw [Complex.cosh_add_pi_mul_I, ← Complex.ofReal_cosh, cosh_log_phi]; push_cast; ring

lemma XiA_eq (s : ℂ) :
    XiA s = 2 * Complex.cosh ((s - 1 / 2) * (Real.log 5 : ℝ)) + (Real.sqrt 5 : ℂ) := by
  unfold XiA Xi; push_cast; ring

lemma w_of_fakeZero (k : ℤ) (ε : ℝ) :
    (fakeZero k ε - 1 / 2) * ((Real.log 5 : ℝ) : ℂ)
      = ((ε * Real.log phi : ℝ) : ℂ) + (((2 * k + 1) * Real.pi : ℝ) : ℂ) * I := by
  have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt log5_pos)
  unfold fakeZero x0
  push_cast
  field_simp
  ring

/-- Every listed point is a zero. -/
theorem XiA_fakeZero (k : ℤ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : XiA (fakeZero k ε) = 0 := by
  rw [XiA_eq, w_of_fakeZero, cosh_decomp]
  have hcos : Real.cos ((2 * k + 1) * Real.pi) = -1 := by
    have := Real.cos_int_mul_two_pi_add_pi k
    rw [← this]; congr 1; ring
  have hsin : Real.sin ((2 * k + 1) * Real.pi) = 0 := by
    have := Real.sin_int_mul_pi (2 * k + 1)
    rw [← this]; push_cast; ring_nf
  have hch : Real.cosh (ε * Real.log phi) = Real.sqrt 5 / 2 := by
    rcases hε with h | h
    · rw [h, one_mul, cosh_log_phi]
    · rw [h, neg_one_mul, Real.cosh_neg, cosh_log_phi]
  rw [hcos, hsin, hch]
  push_cast
  ring

/-- **The complete zero set of the anti-golden completed function.** -/
theorem XiA_eq_zero_iff (s : ℂ) :
    XiA s = 0 ↔ ∃ k : ℤ, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ s = fakeZero k ε := by
  constructor
  · intro hz
    have hL := log5_pos
    have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
    set w : ℂ := (s - 1 / 2) * (Real.log 5 : ℝ) with hw
    have hs : s = 1 / 2 + w / (Real.log 5 : ℝ) := by rw [hw]; field_simp; ring
    have hcosh : Complex.cosh w = Complex.cosh ((Real.log phi : ℂ) + Real.pi * I) := by
      rw [XiA_eq, ← hw] at hz
      rw [cosh_w0]; push_cast; linear_combination hz / 2
    rw [← Complex.cos_mul_I, ← Complex.cos_mul_I, Complex.cos_eq_cos_iff] at hcosh
    obtain ⟨k, hk | hk⟩ := hcosh
    · refine ⟨k, 1, Or.inl rfl, ?_⟩
      have hw' : w = (Real.log phi : ℂ) + (2 * k + 1) * Real.pi * I := by
        linear_combination I * hk + (w - (Real.log phi : ℂ) - Real.pi * I) * I_sq
      rw [hs, hw']
      unfold fakeZero x0
      push_cast
      field_simp
      ring
    · refine ⟨-k - 1, -1, Or.inr rfl, ?_⟩
      have hw' : w = -(Real.log phi : ℂ) - (2 * k + 1) * Real.pi * I := by
        linear_combination (-I) * hk + (w + (Real.log phi : ℂ) + Real.pi * I) * I_sq
      rw [hs, hw']
      unfold fakeZero x0
      push_cast
      field_simp
      ring
  · rintro ⟨k, ε, hε, rfl⟩
    exact XiA_fakeZero k ε hε

/-- The zero set is periodic with period `2 pi i / log 5` (a lattice in the imaginary direction). -/
theorem XiA_periodic (s : ℂ) :
    XiA (s + ((2 * Real.pi / Real.log 5 : ℝ) : ℂ) * I) = XiA s := by
  have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt log5_pos)
  rw [XiA_eq, XiA_eq]
  have : (s + ((2 * Real.pi / Real.log 5 : ℝ) : ℂ) * I - 1 / 2) * ((Real.log 5 : ℝ) : ℂ)
      = (s - 1 / 2) * ((Real.log 5 : ℝ) : ℂ) + (2 * (Real.pi : ℂ)) * I := by
    push_cast; field_simp; ring
  rw [this, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_two_pi,
    Complex.sin_two_pi]
  ring

/-- The fake zeros lie strictly inside the critical strip. -/
lemma fakeZero_re_mem (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    0 < (fakeZero k ε).re ∧ (fakeZero k ε).re < 1 := by
  rw [fakeZero_re]
  have h1 := x0_pos; have h2 := x0_lt_half
  rcases hε with h | h <;> rw [h] <;> constructor <;> linarith

/-- The fake zeros are all OFF the critical line. -/
lemma fakeZero_re_ne_half (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : (fakeZero k ε).re ≠ 1 / 2 := by
  rw [fakeZero_re]
  have h1 := x0_pos
  rcases hε with h | h <;> rw [h] <;> intro hc <;> linarith

lemma fakeZero_abs_re_sub_half (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ((fakeZero k ε).re - 1 / 2) ^ 2 = x0 ^ 2 := by
  rw [fakeZero_re]; rcases hε with h | h <;> rw [h] <;> ring

lemma one_le_abs_two_mul_add_one (k : ℤ) : (1 : ℝ) ≤ |2 * (k : ℝ) + 1| := by
  have : (1 : ℤ) ≤ |2 * k + 1| := by
    rcases le_or_gt 0 k with hk | hk
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_neg (by omega)]; omega
  have h' : ((1 : ℤ) : ℝ) ≤ ((|2 * k + 1| : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h'
  exact h'

/-- No fake zero lies below height `pi / log 5`. -/
lemma fakeZero_abs_im_ge (k : ℤ) (ε : ℝ) : Real.pi / Real.log 5 ≤ |(fakeZero k ε).im| := by
  rw [fakeZero_im, show (2 * (k : ℝ) + 1) * Real.pi / Real.log 5
      = (2 * (k : ℝ) + 1) * (Real.pi / Real.log 5) by ring, abs_mul,
    abs_of_pos (div_pos Real.pi_pos log5_pos)]
  have := one_le_abs_two_mul_add_one k
  have hp : 0 < Real.pi / Real.log 5 := div_pos Real.pi_pos log5_pos
  nlinarith

lemma fakeZero_im_sq_ge (k : ℤ) (ε : ℝ) : 3.61 ≤ (fakeZero k ε).im ^ 2 := by
  have h := fakeZero_abs_im_ge k ε
  have hb := pi_div_log5_bounds.1
  have h' : (1.9 : ℝ) ≤ |(fakeZero k ε).im| := by linarith
  have := sq_abs (fakeZero k ε).im
  nlinarith [abs_nonneg (fakeZero k ε).im]

/-- The golden-anti fake has an explicit zero in the rectangle `[0.001, 0.999] x [0, 55/16]`. -/
lemma fakeZero_in_box :
    1 / 1000 ≤ (fakeZero 0 1).re ∧ (fakeZero 0 1).re ≤ 999 / 1000 ∧
      0 ≤ (fakeZero 0 1).im ∧ (fakeZero 0 1).im ≤ 55 / 16 := by
  have him : (fakeZero 0 1).im = Real.pi / Real.log 5 := by
    rw [fakeZero_im]; push_cast; ring
  rw [fakeZero_re, him]
  have h1 := x0_pos; have h2 := x0_lt
  have hb := pi_div_log5_bounds
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## B. The corpus's Gaussian test at a fake zero

The corpus sums `gaussTest c lam (gammaOf rho) = (z - c)^2 exp(-2 lam (z - c)^2)`,
`z = gammaOf rho = (rho - 1/2)/i`, over the zeros.  At a fake zero `1/2 + eps x0 + i t_k` one has
`gammaOf = t_k - i eps x0`, and with `u = t_k - c` the real part is `Aterm lam u` for both signs of
`eps`. -/

/-- The fake ordinates `t_k = (2k+1) pi / log 5`. -/
def tk (k : ℤ) : ℝ := (2 * k + 1) * Real.pi / Real.log 5

/-- The real part of the Gaussian test at a fake zero, as a function of `u = t_k - c`. -/
def Aterm (lam u : ℝ) : ℝ :=
  Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2)) *
    ((u ^ 2 - x0 ^ 2) * Real.cos (4 * lam * u * x0) + 2 * u * x0 * Real.sin (4 * lam * u * x0))

lemma gammaOf_fakeZero (k : ℤ) (ε : ℝ) :
    Zeta23.gammaOf (fakeZero k ε) = ((tk k : ℝ) : ℂ) + ((-(ε * x0) : ℝ) : ℂ) * I := by
  unfold Zeta23.gammaOf
  apply Complex.ext
  · simp only [Complex.div_re, Complex.sub_re, fakeZero_re, fakeZero_im, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.normSq_I, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, tk]
    norm_num
  · simp only [Complex.div_im, Complex.sub_re, fakeZero_re, fakeZero_im, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.normSq_I, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, tk]
    norm_num

lemma gauss_at (c lam u v : ℝ) :
    RvMBridge6.gaussTest c lam (((u + c : ℝ) : ℂ) + ((v : ℝ) : ℂ) * I)
      = (((u ^ 2 - v ^ 2 : ℝ) : ℂ) + ((2 * u * v : ℝ) : ℂ) * I) *
        Complex.exp (((-(2 * lam) * (u ^ 2 - v ^ 2) : ℝ) : ℂ) + ((-(4 * lam * u * v) : ℝ) : ℂ) * I) := by
  unfold RvMBridge6.gaussTest
  have h1 : (((u + c : ℝ) : ℂ) + ((v : ℝ) : ℂ) * I - (c : ℂ)) ^ 2
      = ((u ^ 2 - v ^ 2 : ℝ) : ℂ) + ((2 * u * v : ℝ) : ℂ) * I := by
    push_cast; linear_combination (v : ℂ) ^ 2 * I_sq
  rw [h1]
  congr 2
  push_cast
  ring

lemma re_gauss_at (c lam u v : ℝ) :
    (RvMBridge6.gaussTest c lam (((u + c : ℝ) : ℂ) + ((v : ℝ) : ℂ) * I)).re
      = Real.exp (-(2 * lam) * (u ^ 2 - v ^ 2)) *
        ((u ^ 2 - v ^ 2) * Real.cos (4 * lam * u * v) + 2 * u * v * Real.sin (4 * lam * u * v)) := by
  rw [gauss_at, Complex.mul_re, Complex.exp_re, Complex.exp_im]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  rw [Real.cos_neg, Real.sin_neg]
  ring

lemma norm_gauss_at (c lam u v : ℝ) :
    ‖RvMBridge6.gaussTest c lam (((u + c : ℝ) : ℂ) + ((v : ℝ) : ℂ) * I)‖
      = (u ^ 2 + v ^ 2) * Real.exp (-(2 * lam) * (u ^ 2 - v ^ 2)) := by
  rw [gauss_at, norm_mul, Complex.norm_exp]
  congr 1
  · rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add]
    rw [show (u ^ 2 - v ^ 2) ^ 2 + (2 * u * v) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

lemma gammaOf_fakeZero' (c : ℝ) (k : ℤ) (ε : ℝ) :
    Zeta23.gammaOf (fakeZero k ε) = (((tk k - c) + c : ℝ) : ℂ) + ((-(ε * x0) : ℝ) : ℂ) * I := by
  rw [gammaOf_fakeZero]; congr 2; ring

/-- The real part at a fake zero is `Aterm lam (t_k - c)`, for both signs. -/
theorem re_gauss_fake (c lam : ℝ) (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k ε))).re = Aterm lam (tk k - c) := by
  rw [gammaOf_fakeZero' c, re_gauss_at]
  unfold Aterm
  rcases hε with h | h <;> subst h
  · have e1 : (-(1 * x0)) ^ 2 = x0 ^ 2 := by ring
    rw [e1]
    have e2 : 4 * lam * (tk k - c) * -(1 * x0) = -(4 * lam * (tk k - c) * x0) := by ring
    rw [e2, Real.cos_neg, Real.sin_neg]
    ring
  · have e1 : (-(-1 * x0)) ^ 2 = x0 ^ 2 := by ring
    rw [e1]
    have e2 : 4 * lam * (tk k - c) * -(-1 * x0) = 4 * lam * (tk k - c) * x0 := by ring
    rw [e2]
    ring

theorem norm_gauss_fake (c lam : ℝ) (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ‖RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k ε))‖
      = ((tk k - c) ^ 2 + x0 ^ 2) * Real.exp (-(2 * lam) * ((tk k - c) ^ 2 - x0 ^ 2)) := by
  rw [gammaOf_fakeZero' c, norm_gauss_at]
  have e1 : (-(ε * x0)) ^ 2 = x0 ^ 2 := by
    rcases hε with h | h <;> subst h <;> ring
  rw [e1]

/-! ## C. Pointwise bounds on `Aterm` -/

lemma x0_sq_lt : x0 ^ 2 < 0.16 := by
  have h1 := x0_pos; have h2 := x0_lt; nlinarith

/-- The bracket is bounded by `u^2 + x0^2` (Cauchy-Schwarz). -/
lemma bracket_ge (lam u : ℝ) :
    -(u ^ 2 + x0 ^ 2) ≤ (u ^ 2 - x0 ^ 2) * Real.cos (4 * lam * u * x0)
      + 2 * u * x0 * Real.sin (4 * lam * u * x0) := by
  set θ := 4 * lam * u * x0
  have hsc := Real.sin_sq_add_cos_sq θ
  set P := u ^ 2 - x0 ^ 2
  set Q := 2 * u * x0
  set R := u ^ 2 + x0 ^ 2
  set B := P * Real.cos θ + Q * Real.sin θ
  have hid : B ^ 2 + (P * Real.sin θ - Q * Real.cos θ) ^ 2
      = (P ^ 2 + Q ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
  have hPQ : P ^ 2 + Q ^ 2 = R ^ 2 := by ring
  have hB2 : B ^ 2 ≤ R ^ 2 := by
    rw [hsc, mul_one, hPQ] at hid
    nlinarith [sq_nonneg (P * Real.sin θ - Q * Real.cos θ)]
  have hR : 0 ≤ R := by positivity
  by_contra hcon
  have h1 : B + R < 0 := by linarith [not_le.mp hcon]
  have h2 : B - R < 0 := by linarith
  nlinarith [mul_pos (neg_pos.mpr h1) (neg_pos.mpr h2)]

/-- Always: `Aterm >= -(u^2 + x0^2) exp(-2 lam (u^2 - x0^2))`. -/
lemma Aterm_ge_abs (lam u : ℝ) :
    -((u ^ 2 + x0 ^ 2) * Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2))) ≤ Aterm lam u := by
  unfold Aterm
  have he := Real.exp_pos (-(2 * lam) * (u ^ 2 - x0 ^ 2))
  have hb := bracket_ge lam u
  nlinarith

/-- On `|4 lam u x0| <= pi/2`: `cos >= 0` and `u sin >= 0`. -/
lemma trig_signs {lam u : ℝ} (hlam : 0 < lam) (hθ : 4 * lam * |u| * x0 ≤ Real.pi / 2) :
    0 ≤ Real.cos (4 * lam * u * x0) ∧ 0 ≤ u * Real.sin (4 * lam * u * x0) := by
  have hx := x0_pos
  have hpi := Real.pi_pos
  have habs : |4 * lam * u * x0| = 4 * lam * |u| * x0 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos hlam,
      abs_of_pos hx]
  constructor
  · apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have := neg_abs_le (4 * lam * u * x0); rw [habs] at this; linarith
    · have := le_abs_self (4 * lam * u * x0); rw [habs] at this; linarith
  · rcases le_or_gt 0 u with hu | hu
    · have h0 : 0 ≤ 4 * lam * u * x0 := by positivity
      have h1 : 4 * lam * u * x0 ≤ Real.pi := by
        rw [abs_of_nonneg hu] at hθ; linarith
      exact mul_nonneg hu (Real.sin_nonneg_of_nonneg_of_le_pi h0 h1)
    · have h0 : 0 ≤ -(4 * lam * u * x0) := by
        have : 0 < 4 * lam * (-u) * x0 := by
          have := neg_pos.mpr hu; positivity
        linarith
      have h1 : -(4 * lam * u * x0) ≤ Real.pi := by
        rw [abs_of_neg hu] at hθ; linarith
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 h1
      rw [Real.sin_neg] at hs
      nlinarith

/-- Middle range: `x0 <= |u|` and `|4 lam u x0| <= pi/2` give `Aterm >= 0`. -/
lemma Aterm_nonneg {lam u : ℝ} (hlam : 0 < lam) (h1 : x0 ^ 2 ≤ u ^ 2)
    (hθ : 4 * lam * |u| * x0 ≤ Real.pi / 2) : 0 ≤ Aterm lam u := by
  obtain ⟨hc, hs⟩ := trig_signs hlam hθ
  unfold Aterm
  have hx := x0_pos
  have he := Real.exp_pos (-(2 * lam) * (u ^ 2 - x0 ^ 2))
  have hb : 0 ≤ (u ^ 2 - x0 ^ 2) * Real.cos (4 * lam * u * x0)
      + 2 * u * x0 * Real.sin (4 * lam * u * x0) := by
    have : 0 ≤ 2 * x0 * (u * Real.sin (4 * lam * u * x0)) := by positivity
    nlinarith
  positivity

/-- Near a fake ordinate: `Aterm >= -x0^2 e^{2 lam x0^2}`. -/
lemma Aterm_ge_neg {lam u : ℝ} (hlam : 0 < lam) (hθ : 4 * lam * |u| * x0 ≤ Real.pi / 2) :
    -(x0 ^ 2 * Real.exp (2 * lam * x0 ^ 2)) ≤ Aterm lam u := by
  rcases le_or_gt (x0 ^ 2) (u ^ 2) with h | h
  · have := Aterm_nonneg hlam h hθ
    have : 0 ≤ x0 ^ 2 * Real.exp (2 * lam * x0 ^ 2) := by positivity
    linarith
  · obtain ⟨hc, hs⟩ := trig_signs hlam hθ
    have hx := x0_pos
    unfold Aterm
    set E := Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2)) with hE
    set B := (u ^ 2 - x0 ^ 2) * Real.cos (4 * lam * u * x0)
      + 2 * u * x0 * Real.sin (4 * lam * u * x0) with hB
    have hE0 : 0 < E := Real.exp_pos _
    have hEle : E ≤ Real.exp (2 * lam * x0 ^ 2) := by
      rw [hE, Real.exp_le_exp]; nlinarith [sq_nonneg u]
    have hc1 : Real.cos (4 * lam * u * x0) ≤ 1 := Real.cos_le_one _
    have hBge : -(x0 ^ 2) ≤ B := by
      have : 0 ≤ 2 * x0 * (u * Real.sin (4 * lam * u * x0)) := by positivity
      nlinarith [sq_nonneg u]
    rcases le_or_gt 0 B with hB0 | hB0
    · have : 0 ≤ E * B := mul_nonneg hE0.le hB0
      have : 0 ≤ x0 ^ 2 * Real.exp (2 * lam * x0 ^ 2) := by positivity
      linarith
    · have h1 : Real.exp (2 * lam * x0 ^ 2) * B ≤ E * B :=
        mul_le_mul_of_nonpos_right hEle hB0.le
      have h2 : Real.exp (2 * lam * x0 ^ 2) * (-(x0 ^ 2)) ≤ Real.exp (2 * lam * x0 ^ 2) * B :=
        mul_le_mul_of_nonneg_left hBge (Real.exp_pos _).le
      nlinarith

lemma exp_neg_eight_tenths : 0.44 ≤ Real.exp (-0.8) := by
  have h1 : (1.2 : ℝ) ≤ Real.exp 0.2 := by
    have := Real.add_one_le_exp (0.2 : ℝ); linarith
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp (-0.8) * Real.exp 1 = Real.exp 0.2 := by
    rw [← Real.exp_add]; norm_num
  have h4 := Real.exp_pos (-0.8)
  nlinarith

/-- Next to a fake ordinate (`pi/log 5 <= |u| <= 2 pi/log 5`) and for `lam <= 1/40`:
`Aterm >= 1`. -/
lemma Aterm_neighbor {lam u : ℝ} (hlam : 0 < lam) (hle : lam ≤ 1 / 40)
    (h1 : Real.pi / Real.log 5 ≤ |u|) (h2 : |u| ≤ 2 * (Real.pi / Real.log 5)) :
    1 ≤ Aterm lam u := by
  have hb := pi_div_log5_bounds
  have hx := x0_pos; have hx2 := x0_lt
  have hu1 : 1.9 ≤ |u| := by linarith [hb.1]
  have hu2 : |u| ≤ 4 := by linarith [hb.2]
  have hθ : 4 * lam * |u| * x0 ≤ 0.16 := by
    have : 4 * lam * |u| * x0 ≤ 4 * (1 / 40) * 4 * 0.4 := by
      have h0 : 0 ≤ |u| := abs_nonneg u
      have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 4))
        hu2 h0 (by positivity)) hx2.le hx.le (by positivity)
      linarith
    linarith
  have hθ' : 4 * lam * |u| * x0 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨hc, hs⟩ := trig_signs hlam hθ'
  have hcos : 0.9872 ≤ Real.cos (4 * lam * u * x0) := by
    have := Real.one_sub_sq_div_two_le_cos (x := 4 * lam * u * x0)
    have habs : |4 * lam * u * x0| = 4 * lam * |u| * x0 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos hlam,
        abs_of_pos hx]
    have hsq : (4 * lam * u * x0) ^ 2 ≤ 0.16 ^ 2 := by
      rw [← sq_abs, habs]
      have h0 : 0 ≤ 4 * lam * |u| * x0 := by positivity
      nlinarith
    nlinarith
  have husq : 3.61 ≤ u ^ 2 := by
    have := sq_abs u; nlinarith
  have husq2 : u ^ 2 ≤ 16 := by
    have := sq_abs u; nlinarith [abs_nonneg u]
  have hx02 := x0_sq_lt
  have hE : 0.44 ≤ Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2)) := by
    have := exp_neg_eight_tenths
    have hmono : Real.exp (-0.8) ≤ Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2)) := by
      rw [Real.exp_le_exp]
      have h0 : 0 ≤ x0 ^ 2 := sq_nonneg _
      nlinarith
    linarith
  unfold Aterm
  have hbr : 3.4 ≤ (u ^ 2 - x0 ^ 2) * Real.cos (4 * lam * u * x0)
      + 2 * u * x0 * Real.sin (4 * lam * u * x0) := by
    have : 0 ≤ 2 * x0 * (u * Real.sin (4 * lam * u * x0)) := by positivity
    nlinarith
  nlinarith

/-- `e^{v} >= v^4/24` for `v >= 0`. -/
lemma exp_ge_pow4 {v : ℝ} (hv : 0 ≤ v) : v ^ 4 / 24 ≤ Real.exp v := by
  have := Real.pow_div_factorial_le_exp v hv 4
  simpa [Nat.factorial] using this

/-- Far tail (`|u| >= pi/(8 lam x0)`, `lam <= 1/40`):
`(u^2 + x0^2) e^{-2 lam (u^2 - x0^2)} <= e^{-|u|/2} / 100`. -/
lemma tail_le {lam u : ℝ} (hlam : 0 < lam) (hle : lam ≤ 1 / 40)
    (hu : Real.pi / (8 * lam * x0) ≤ |u|) :
    (u ^ 2 + x0 ^ 2) * Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2)) ≤ Real.exp (-|u| / 2) / 100 := by
  have hx := x0_pos; have hx2 := x0_lt
  have hpi := Real.pi_gt_d2
  set v := |u| with hv
  have hv0 : 0 ≤ v := abs_nonneg u
  have hu2 : u ^ 2 = v ^ 2 := (sq_abs u).symm
  -- v >= 39
  have hU : 39 ≤ v := by
    have h1 : Real.pi / (8 * lam * x0) ≥ 3.14 / (8 * (1 / 40) * 0.4) := by
      apply div_le_div₀ (by positivity) hpi.le (mul_pos (mul_pos (by norm_num) hlam) hx)
      have : 8 * lam * x0 ≤ 8 * (1 / 40) * 0.4 := by
        have := mul_le_mul (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 8)) hx2.le hx.le
          (by positivity)
        linarith
      exact this
    norm_num at h1
    linarith
  -- 2 lam v^2 >= (pi / (4 x0)) v >= 1.9625 v
  have hkey : 1.9625 * v ≤ 2 * lam * v ^ 2 := by
    have h1 : Real.pi / (4 * x0) * v ≤ 2 * lam * v ^ 2 := by
      have hdiv : Real.pi / (8 * lam * x0) * (8 * lam * x0) = Real.pi := by
        field_simp
      have : Real.pi ≤ 8 * lam * x0 * v := by
        have := mul_le_mul_of_nonneg_right hu (by positivity : (0:ℝ) ≤ 8 * lam * x0)
        nlinarith
      have hq : Real.pi / (4 * x0) * v = Real.pi * v / (4 * x0) := by ring
      rw [hq, div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : 1.9625 ≤ Real.pi / (4 * x0) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    nlinarith
  -- e^{2 lam x0^2} <= e
  have hsmall : 2 * lam * x0 ^ 2 ≤ 1 := by
    have := x0_sq_lt
    have : 2 * lam * x0 ^ 2 ≤ 2 * (1 / 40) * 0.16 := by
      apply mul_le_mul (by linarith) this.le (sq_nonneg _) (by norm_num)
    linarith
  have he1 : Real.exp (2 * lam * x0 ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr hsmall
  have he := Real.exp_one_lt_d9
  -- factor the exponential
  have hsplit : Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2))
      = Real.exp (2 * lam * x0 ^ 2) * Real.exp (-(2 * lam * v ^ 2)) := by
    rw [← Real.exp_add, hu2]; ring_nf
  have hexp : Real.exp (-(2 * lam * v ^ 2)) ≤ Real.exp (-1.4625 * v) * Real.exp (-v / 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  -- polynomial factor against e^{1.4625 v}
  have hpoly : (v ^ 2 + 0.16) * Real.exp (-1.4625 * v) ≤ 0.0036 := by
    have h4 := exp_ge_pow4 (by positivity : (0:ℝ) ≤ 1.4625 * v)
    have hpos := Real.exp_pos (1.4625 * v)
    have hinv : Real.exp (-1.4625 * v) = (Real.exp (1.4625 * v))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have hv4 : (1.4625 * v) ^ 4 / 24 ≥ 0.19 * v ^ 4 := by nlinarith [sq_nonneg v, sq_nonneg (v ^ 2)]
    have : v ^ 2 + 0.16 ≤ 0.0036 * (0.19 * v ^ 4) := by nlinarith [sq_nonneg v]
    nlinarith
  have hx02 := x0_sq_lt
  rw [hsplit, hu2]
  have hE1 : Real.exp (2 * lam * x0 ^ 2) ≤ 2.72 := by linarith
  have hA : 0 ≤ Real.exp (-(2 * lam * v ^ 2)) := (Real.exp_pos _).le
  have hB : 0 ≤ Real.exp (-v / 2) := (Real.exp_pos _).le
  have hC : 0 ≤ Real.exp (-1.4625 * v) := (Real.exp_pos _).le
  calc (v ^ 2 + x0 ^ 2) * (Real.exp (2 * lam * x0 ^ 2) * Real.exp (-(2 * lam * v ^ 2)))
      ≤ (v ^ 2 + 0.16) * (2.72 * (Real.exp (-1.4625 * v) * Real.exp (-v / 2))) := by
        apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
        exact mul_le_mul hE1 hexp hA (by norm_num)
    _ = 2.72 * ((v ^ 2 + 0.16) * Real.exp (-1.4625 * v)) * Real.exp (-v / 2) := by ring
    _ ≤ 2.72 * 0.0036 * Real.exp (-v / 2) := by gcongr
    _ ≤ Real.exp (-v / 2) / 100 := by nlinarith

/-! ## D. The lattice of fake ordinates -/

/-- The spacing `2 pi / log 5` of the fake ordinates. -/
def spacing : ℝ := 2 * (Real.pi / Real.log 5)

lemma spacing_bounds : 3.8 < spacing ∧ spacing < 4 := by
  have h := pi_div_log5_bounds; unfold spacing; constructor <;> linarith [h.1, h.2]

lemma tk_eq (k : ℤ) : tk k = spacing * k + Real.pi / Real.log 5 := by
  unfold tk spacing; ring

/-- The first fake ordinate at or above `c`: `u_j = t_j - c` lies in `[0, spacing)`. -/
def jIdx (c : ℝ) : ℤ := ⌈(c - Real.pi / Real.log 5) / spacing⌉

lemma u_jIdx_mem (c : ℝ) : 0 ≤ tk (jIdx c) - c ∧ tk (jIdx c) - c < spacing := by
  have hs := spacing_bounds
  have hsp : 0 < spacing := by linarith
  set x := (c - Real.pi / Real.log 5) / spacing with hx
  have h1 : x ≤ (jIdx c : ℝ) := Int.le_ceil x
  have h2 : (jIdx c : ℝ) < x + 1 := Int.ceil_lt_add_one x
  rw [tk_eq]
  have hxs : x * spacing = c - Real.pi / Real.log 5 := by rw [hx]; field_simp
  constructor
  · have := mul_le_mul_of_nonneg_right h1 hsp.le; nlinarith
  · have := mul_lt_mul_of_pos_right h2 hsp; nlinarith

lemma u_shift (c : ℝ) (k : ℤ) :
    tk k - c = (tk (jIdx c) - c) + spacing * ((k - jIdx c : ℤ) : ℝ) := by
  rw [tk_eq, tk_eq]; push_cast; ring

/-- Away from the pair `{j - 1, j}` every `|u_k| >= spacing`. -/
lemma abs_u_ge_of_far (c : ℝ) {k : ℤ} (hk1 : k ≠ jIdx c - 1) (hk2 : k ≠ jIdx c) :
    spacing ≤ |tk k - c| := by
  obtain ⟨h0, h1⟩ := u_jIdx_mem c
  have hs := spacing_bounds
  rw [u_shift c k]
  rcases le_or_gt k (jIdx c) with hle | hgt
  · have hlt : k ≤ jIdx c - 2 := by omega
    have : ((k - jIdx c : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (by omega : k - jIdx c ≤ -2)
    rw [abs_of_neg (by nlinarith)]
    nlinarith
  · have : (1 : ℝ) ≤ ((k - jIdx c : ℤ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k - jIdx c)
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith

/-- `e^{-|u_k|/2} <= e^{spacing/2} r^{|k - j|}`, `r = e^{-spacing/2}`. -/
lemma exp_neg_half_abs_le (c : ℝ) (k : ℤ) :
    Real.exp (-|tk k - c| / 2) ≤
      Real.exp (spacing / 2) * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs := by
  obtain ⟨h0, h1⟩ := u_jIdx_mem c
  have hs := spacing_bounds
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp, u_shift c k]
  set m := k - jIdx c
  have hm : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hm]
  have htri : spacing * |(m : ℝ)| - spacing ≤ |(tk (jIdx c) - c) + spacing * (m : ℝ)| := by
    have e1 : |spacing * (m : ℝ)| = spacing * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos (by linarith)]
    have := abs_sub_abs_le_abs_sub (spacing * (m : ℝ)) (-(tk (jIdx c) - c))
    rw [e1, abs_neg, abs_of_nonneg h0, sub_neg_eq_add, add_comm] at this
    linarith
  nlinarith

/-- The two-sided geometric series `sum_{m in Z} r^|m| = (1 + r)/(1 - r)`. -/
lemma hasSum_two_sided {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun m : ℤ => r ^ m.natAbs) ((1 + r) / (1 - r)) := by
  have hA : HasSum (fun n : ℕ => r ^ ((n : ℤ)).natAbs) (1 - r)⁻¹ := by
    refine (hasSum_geometric_of_lt_one h0 h1).congr_fun ?_
    intro n
    rw [Int.natAbs_natCast]
  have hB : HasSum (fun n : ℕ => r ^ ((-((n : ℤ) + 1))).natAbs) (r * (1 - r)⁻¹) := by
    refine ((hasSum_geometric_of_lt_one h0 h1).mul_left r).congr_fun ?_
    intro n
    have e : (-((n : ℤ) + 1)).natAbs = n + 1 := by
      rw [Int.natAbs_neg]
      exact Int.natAbs_natCast (n + 1)
    rw [e, pow_succ]
    ring
  have h := HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => r ^ m.natAbs) hA hB
  have hne : (1 - r) ≠ 0 := by linarith
  have e : (1 - r)⁻¹ + r * (1 - r)⁻¹ = (1 + r) / (1 - r) := by
    field_simp
  rw [e] at h
  exact h

lemma hasSum_two_sided_shift {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (j : ℤ) :
    HasSum (fun k : ℤ => r ^ (k - j).natAbs) ((1 + r) / (1 - r)) := by
  have h := hasSum_two_sided h0 h1
  rw [← (Equiv.subRight j).hasSum_iff] at h
  exact h

lemma r_bounds : 0 ≤ Real.exp (-spacing / 2) ∧ Real.exp (-spacing / 2) ≤ 0.2 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have hs := spacing_bounds
  have h1 : Real.exp (-spacing / 2) ≤ Real.exp (-1.9) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (5 : ℝ) ≤ Real.exp 1.9 := by
    have ha := Real.add_one_le_exp (0.9 : ℝ)
    have hb := Real.exp_one_gt_d9
    have : Real.exp 1.9 = Real.exp 1 * Real.exp 0.9 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1, Real.exp_pos 0.9]
  have h3 : Real.exp (-1.9) = (Real.exp 1.9)⁻¹ := by rw [← Real.exp_neg]
  have h4 : (Real.exp 1.9)⁻¹ ≤ 1 / 5 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-! ## E. Summability of the fake Gaussian terms, every width -/

/-- `(u^2 + x0^2) e^{-2 lam (u^2 - x0^2)} <= M_lam e^{-|u|}` for every `u`. -/
lemma gauss_le_exp_abs {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    (u ^ 2 + x0 ^ 2) * Real.exp (-(2 * lam) * (u ^ 2 - x0 ^ 2)) ≤
      ((1 / lam + x0 ^ 2) * Real.exp (1 / (4 * lam) + 2 * lam * x0 ^ 2)) * Real.exp (-|u|) := by
  have hsq : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  set v := |u|
  have hv : 0 ≤ v := abs_nonneg u
  -- u^2 <= e^{lam u^2}/lam and v <= lam v^2 + 1/(4 lam)
  have h1 : lam * v ^ 2 + 1 ≤ Real.exp (lam * v ^ 2) := Real.add_one_le_exp _
  have h2 : v ≤ lam * v ^ 2 + 1 / (4 * lam) := by
    have : 0 ≤ lam * (v - 1 / (2 * lam)) ^ 2 := by positivity
    have e : lam * (v - 1 / (2 * lam)) ^ 2 = lam * v ^ 2 - v + 1 / (4 * lam) := by
      field_simp; ring
    linarith
  have hpoly : v ^ 2 + x0 ^ 2 ≤ (1 / lam + x0 ^ 2) * Real.exp (lam * v ^ 2) := by
    have he1 : 1 ≤ Real.exp (lam * v ^ 2) := Real.one_le_exp (by positivity)
    have : v ^ 2 ≤ (1 / lam) * Real.exp (lam * v ^ 2) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hlam]; linarith
    nlinarith [sq_nonneg x0]
  rw [hsq]
  have hstep1 : (v ^ 2 + x0 ^ 2) * Real.exp (-(2 * lam) * (v ^ 2 - x0 ^ 2))
      ≤ ((1 / lam + x0 ^ 2) * Real.exp (lam * v ^ 2)) * Real.exp (-(2 * lam) * (v ^ 2 - x0 ^ 2)) :=
    mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
  have hstep2 : Real.exp (lam * v ^ 2) * Real.exp (-(2 * lam) * (v ^ 2 - x0 ^ 2))
      = Real.exp (2 * lam * x0 ^ 2 - lam * v ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hstep3 : Real.exp (2 * lam * x0 ^ 2 - lam * v ^ 2)
      ≤ Real.exp (1 / (4 * lam) + 2 * lam * x0 ^ 2) * Real.exp (-v) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have hc0 : 0 ≤ 1 / lam + x0 ^ 2 := by positivity
  calc (v ^ 2 + x0 ^ 2) * Real.exp (-(2 * lam) * (v ^ 2 - x0 ^ 2))
      ≤ ((1 / lam + x0 ^ 2) * Real.exp (lam * v ^ 2)) * Real.exp (-(2 * lam) * (v ^ 2 - x0 ^ 2)) :=
        hstep1
    _ = (1 / lam + x0 ^ 2) * Real.exp (2 * lam * x0 ^ 2 - lam * v ^ 2) := by
        rw [mul_assoc, hstep2]
    _ ≤ (1 / lam + x0 ^ 2) * (Real.exp (1 / (4 * lam) + 2 * lam * x0 ^ 2) * Real.exp (-v)) :=
        mul_le_mul_of_nonneg_left hstep3 hc0
    _ = ((1 / lam + x0 ^ 2) * Real.exp (1 / (4 * lam) + 2 * lam * x0 ^ 2)) * Real.exp (-v) := by
        ring

/-- The fake zero side of a test `H`: the sum over all fake zeros (each simple), grouped by `k`. -/
def fakeSide (H : ℂ → ℂ) : ℂ :=
  ∑' k : ℤ, (H (Zeta23.gammaOf (fakeZero k 1)) + H (Zeta23.gammaOf (fakeZero k (-1))))

/-- The fake Gaussian terms are summable for every width `lam > 0` and centre `c`. -/
theorem summable_fake_gauss (c lam : ℝ) (hlam : 0 < lam) :
    Summable (fun k : ℤ => RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k 1))
      + RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k (-1)))) := by
  set M := (1 / lam + x0 ^ 2) * Real.exp (1 / (4 * lam) + 2 * lam * x0 ^ 2)
  set r := Real.exp (-spacing / 2)
  obtain ⟨hr0, hr1⟩ := r_bounds
  have hM : 0 ≤ M := by positivity
  have hg : Summable (fun k : ℤ => 2 * M * Real.exp (spacing / 2) * r ^ (k - jIdx c).natAbs) :=
    ((hasSum_two_sided_shift hr0 (by linarith) (jIdx c)).summable).mul_left _
  refine Summable.of_norm_bounded hg (fun k => ?_)
  have hk : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ‖RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k ε))‖
        ≤ M * Real.exp (spacing / 2) * r ^ (k - jIdx c).natAbs := by
    intro ε hε
    rw [norm_gauss_fake c lam k hε]
    have h1 := gauss_le_exp_abs hlam (tk k - c)
    have h2 := exp_neg_half_abs_le c k
    have h3 : Real.exp (-|tk k - c|) ≤ Real.exp (-|tk k - c| / 2) :=
      Real.exp_le_exp.mpr (by linarith [abs_nonneg (tk k - c)])
    calc _ ≤ M * Real.exp (-|tk k - c|) := h1
      _ ≤ M * (Real.exp (spacing / 2) * r ^ (k - jIdx c).natAbs) := by gcongr; linarith
      _ = M * Real.exp (spacing / 2) * r ^ (k - jIdx c).natAbs := by ring
  calc _ ≤ ‖RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k 1))‖
        + ‖RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k (-1)))‖ := norm_add_le _ _
    _ ≤ _ := by linarith [hk 1 (Or.inl rfl), hk (-1) (Or.inr rfl)]

/-! ## F. THE FAKE GAUSSIAN FUNCTIONAL IS NONNEGATIVE FOR `0 < lam <= 1/40`, EVERY CENTRE -/

lemma pair_ge (c : ℝ) {lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ 1 / 40) :
    1 - x0 ^ 2 * Real.exp (2 * lam * x0 ^ 2) ≤
      Aterm lam (tk (jIdx c - 1) - c) + Aterm lam (tk (jIdx c) - c) := by
  obtain ⟨h0, h1⟩ := u_jIdx_mem c
  have hs := spacing_bounds
  have hb := pi_div_log5_bounds
  have hx := x0_pos; have hx2 := x0_lt
  have hprev : tk (jIdx c - 1) - c = (tk (jIdx c) - c) - spacing := by
    rw [tk_eq, tk_eq]; push_cast; ring
  set w := tk (jIdx c) - c
  have hsp : spacing = 2 * (Real.pi / Real.log 5) := rfl
  -- small-angle condition for |u| <= spacing
  have hθ : ∀ u : ℝ, |u| ≤ spacing → 4 * lam * |u| * x0 ≤ Real.pi / 2 := by
    intro u hu
    have : 4 * lam * |u| * x0 ≤ 4 * (1 / 40) * 4 * 0.4 := by
      have h0' : 0 ≤ |u| := abs_nonneg u
      have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 4))
        (by linarith : |u| ≤ 4) h0' (by positivity)) hx2.le hx.le (by positivity)
      linarith
    linarith [Real.pi_gt_three]
  rw [hprev]
  rcases le_or_gt w (Real.pi / Real.log 5) with hw | hw
  · -- j is the nearest, j - 1 is the neighbour
    have hA := Aterm_ge_neg hlam (hθ w (by rw [abs_of_nonneg h0]; linarith))
    have hB : 1 ≤ Aterm lam (w - spacing) := by
      apply Aterm_neighbor hlam hle
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    linarith
  · -- j - 1 is the nearest, j is the neighbour
    have hA := Aterm_ge_neg hlam (hθ (w - spacing) (by rw [abs_of_neg (by linarith)]; linarith))
    have hB : 1 ≤ Aterm lam w := by
      apply Aterm_neighbor hlam hle
      · rw [abs_of_nonneg h0]; linarith
      · rw [abs_of_nonneg h0]; linarith
    linarith

lemma far_ge (c : ℝ) {lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ 1 / 40) {k : ℤ}
    (hk1 : k ≠ jIdx c - 1) (hk2 : k ≠ jIdx c) :
    -(Real.exp (spacing / 2) / 100 * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs)
      ≤ Aterm lam (tk k - c) := by
  have hfar := abs_u_ge_of_far c hk1 hk2
  have hs := spacing_bounds
  have hx := x0_pos; have hx2 := x0_lt
  have hmaj : 0 ≤ Real.exp (spacing / 2) / 100 * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs := by
    positivity
  rcases le_or_gt (4 * lam * |tk k - c| * x0) (Real.pi / 2) with hθ | hθ
  · have hsq : x0 ^ 2 ≤ (tk k - c) ^ 2 := by
      have : x0 ≤ |tk k - c| := by linarith
      have h0 : 0 ≤ x0 := hx.le
      rw [← sq_abs (tk k - c)]; nlinarith
    have := Aterm_nonneg hlam hsq hθ
    linarith
  · have hU : Real.pi / (8 * lam * x0) ≤ |tk k - c| := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h1 := Aterm_ge_abs lam (tk k - c)
    have h2 := tail_le hlam hle hU
    have h3 := exp_neg_half_abs_le c k
    have h4 : Real.exp (-|tk k - c| / 2) / 100 ≤
        Real.exp (spacing / 2) / 100 * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs := by
      have := div_le_div_of_nonneg_right h3 (by norm_num : (0:ℝ) ≤ 100)
      calc _ ≤ Real.exp (spacing / 2) * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs / 100 := this
        _ = _ := by ring
    linarith

/-- **The fake Gaussian functional is nonnegative** for every centre `c` and `0 < lam <= 1/40`
(numerically it stays positive up to `lam* = 0.1827...`, research/crux_meta-barriers N4). -/
theorem fake_gaussian_nonneg (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 1 / 40) :
    0 ≤ (fakeSide (RvMBridge6.gaussTest c lam)).re := by
  have hsum := summable_fake_gauss c lam hlam
  unfold fakeSide
  rw [Complex.re_tsum hsum]
  have hterm : ∀ k : ℤ, (RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k 1))
      + RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k (-1)))).re
      = 2 * Aterm lam (tk k - c) := by
    intro k
    rw [Complex.add_re, re_gauss_fake c lam k (Or.inl rfl), re_gauss_fake c lam k (Or.inr rfl)]
    ring
  simp_rw [hterm]
  obtain ⟨hr0, hr1⟩ := r_bounds
  have hs := spacing_bounds
  -- the tail majorant and the comparison function
  let T : ℤ → ℝ := fun k =>
    Real.exp (spacing / 2) / 100 * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs
  have hT : ∀ k, 0 ≤ T k := fun k => by
    have := Real.exp_pos (spacing / 2)
    have := pow_nonneg hr0 (k - jIdx c).natAbs
    positivity
  let g : ℤ → ℝ := fun k =>
    2 * (if k = jIdx c - 1 then Aterm lam (tk (jIdx c - 1) - c) + T k else 0)
      + 2 * (if k = jIdx c then Aterm lam (tk (jIdx c) - c) + T k else 0) - 2 * T k
  have hA : HasSum (fun k => 2 * Aterm lam (tk k - c)) (∑' k, 2 * Aterm lam (tk k - c)) := by
    have hs2 : Summable (fun k : ℤ => 2 * Aterm lam (tk k - c)) := by
      have := (Complex.hasSum_re hsum.hasSum).summable
      exact this.congr hterm
    exact hs2.hasSum
  have hgeo := hasSum_two_sided_shift hr0 (by linarith) (jIdx c)
  have hTsum : HasSum T (Real.exp (spacing / 2) / 100 *
      ((1 + Real.exp (-spacing / 2)) / (1 - Real.exp (-spacing / 2)))) :=
    hgeo.mul_left _
  have hG : HasSum g (2 * (Aterm lam (tk (jIdx c - 1) - c) + T (jIdx c - 1))
      + 2 * (Aterm lam (tk (jIdx c) - c) + T (jIdx c))
      - 2 * (Real.exp (spacing / 2) / 100 *
        ((1 + Real.exp (-spacing / 2)) / (1 - Real.exp (-spacing / 2))))) := by
    have e1 := (hasSum_ite_eq (jIdx c - 1) (Aterm lam (tk (jIdx c - 1) - c) + T (jIdx c - 1))).mul_left 2
    have e2 := (hasSum_ite_eq (jIdx c) (Aterm lam (tk (jIdx c) - c) + T (jIdx c))).mul_left 2
    have e3 := hTsum.mul_left 2
    refine ((e1.add e2).sub e3).congr_fun ?_
    intro k
    by_cases h1 : k = jIdx c - 1
    · subst h1; simp [g]
    · by_cases h2 : k = jIdx c
      · subst h2; simp [g, h1]
      · simp [g, h1, h2]
  have hle' : ∀ k, g k ≤ 2 * Aterm lam (tk k - c) := by
    intro k
    by_cases h1 : k = jIdx c - 1
    · subst h1
      have hne : jIdx c - 1 ≠ jIdx c := by omega
      simp only [g, if_pos, hne, if_false]
      simp only [mul_zero, add_zero]
      linarith
    · by_cases h2 : k = jIdx c
      · subst h2
        simp only [g, h1, if_false]
        simp only [if_true, mul_zero, zero_add]
        linarith
      · simp only [g, h1, h2, if_false, mul_zero, zero_add, zero_sub]
        have := far_ge c hlam hle h1 h2
        simp only [T]
        linarith
  have hcmp := hasSum_le hle' hG hA
  -- the lower bound is positive
  have hpair := pair_ge c hlam hle
  have hx02 := x0_sq_lt
  have hE : Real.exp (2 * lam * x0 ^ 2) ≤ Real.exp 1 := by
    rw [Real.exp_le_exp]
    have : 2 * lam * x0 ^ 2 ≤ 2 * (1 / 40) * 0.16 := by
      apply mul_le_mul (by linarith) hx02.le (sq_nonneg _) (by norm_num)
    linarith
  have he1 := Real.exp_one_lt_d9
  have hes : Real.exp (spacing / 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  have he2 : Real.exp 2 ≤ 7.39 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hgeo' : (1 + Real.exp (-spacing / 2)) / (1 - Real.exp (-spacing / 2)) ≤ 1.5 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hT0 := hT (jIdx c - 1)
  have hT1 := hT (jIdx c)
  have hx0e : x0 ^ 2 * Real.exp (2 * lam * x0 ^ 2) ≤ 0.16 * 2.72 := by
    apply mul_le_mul hx02.le (by linarith) (Real.exp_pos _).le (by norm_num)
  have htail : Real.exp (spacing / 2) / 100 *
      ((1 + Real.exp (-spacing / 2)) / (1 - Real.exp (-spacing / 2))) ≤ 7.39 / 100 * 1.5 := by
    apply mul_le_mul (by linarith) hgeo' (div_nonneg (by linarith) (by linarith)) (by norm_num)
  linarith

/-! ## G. The hybrid: zeta's zero side plus the fake one -/

/-- The zero side of the golden hybrid `xi * XiA` for a test `H`: zeta's (the corpus's
`zeroSide`, over all nontrivial zeros with multiplicity) plus the fake zeros' (all simple).
Section I proves that this is the multiplicity-weighted zero side of the entire function
`xi * XiA` (`XiHRZeroSide_eq`). -/
def hybridZeroSide (H : ℂ → ℂ) : ℂ := RvMBridge6.zeroSide H + fakeSide H

/-- **The hybrid satisfies the corpus's small-width Gaussian positivity** (`E6Bridge30`, the Wall's
hypothesis-free region `lam <= 3/2000`), exactly as zeta does. -/
theorem hybrid_gaussian_positivity_small (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 3 / 2000) :
    0 ≤ (hybridZeroSide (RvMBridge6.gaussTest c lam)).re := by
  unfold hybridZeroSide
  rw [Complex.add_re]
  have h1 := RvMBridge30.gaussian_positivity_small_lam_3e3 c lam hlam hle
  have h2 := fake_gaussian_nonneg c lam hlam (by linarith)
  linarith

/-- **The hybrid satisfies the corpus's sharp envelope** (`E6Bridge16`) at every width
`lam <= 1/40`: positivity for `|c| >= envelopeCsharp lam`, exactly as zeta does. -/
theorem hybrid_gaussian_envelope (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 1 / 40)
    (hc : RvMBridge16.envelopeCsharp lam ≤ |c|) :
    0 ≤ (hybridZeroSide (RvMBridge6.gaussTest c lam)).re := by
  unfold hybridZeroSide
  rw [Complex.add_re]
  have h1 := RvMBridge16.gaussian_positivity_envelope_sharp c lam hlam hc
  have h2 := fake_gaussian_nonneg c lam hlam hle
  linarith

/-! ## H. The functional is not blind: at width `1/2` it detects the fake zeros

At the centre `c = pi / log 5` (a fake ordinate) and width `lam = 1/2`, the fake Gaussian sum is
NEGATIVE.  So the barrier is exactly the gap between the corpus's proved widths (`<= 3/2000`,
envelope) and the Wall's `for all lam`: the positivity the corpus has proved is blind to the
golden fake, the positivity it needs is not. -/

lemma log_phi_gt : 0.38 < Real.log phi := by
  have h1 := Real.one_sub_inv_le_log_of_pos phi_pos
  have h2 : phi⁻¹ = phi - 1 := by
    have hne : phi ≠ 0 := ne_of_gt phi_pos
    have hsq := phi_sq
    field_simp
    nlinarith
  have := phi_lt
  rw [h2] at h1
  linarith

lemma x0_gt : 0.23 < x0 := by
  unfold x0; rw [lt_div_iff₀ log5_pos]
  have := log5_bounds.2; have := log_phi_gt; linarith

lemma tk_center (k : ℤ) : tk k - Real.pi / Real.log 5 = spacing * k := by
  rw [tk_eq]; ring

/-- Far terms at width `1/2`: `(u^2 + x0^2) e^{-(u^2 - x0^2)} <= e^{-|u|/2} / 50` for `|u| >= 3.8`. -/
lemma far_half {u : ℝ} (hu : 3.8 ≤ |u|) :
    (u ^ 2 + x0 ^ 2) * Real.exp (-(2 * (1 / 2)) * (u ^ 2 - x0 ^ 2)) ≤ Real.exp (-|u| / 2) / 50 := by
  have hx02 := x0_sq_lt
  set v := |u| with hv
  have hu2 : u ^ 2 = v ^ 2 := (sq_abs u).symm
  have hv0 : 0 ≤ v := abs_nonneg u
  rw [hu2]
  have hsplit : Real.exp (-(2 * (1 / 2)) * (v ^ 2 - x0 ^ 2))
      = Real.exp (x0 ^ 2) * Real.exp (-(v ^ 2 - v / 2)) * Real.exp (-v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hx0e : Real.exp (x0 ^ 2) ≤ Real.exp 0.16 := Real.exp_le_exp.mpr hx02.le
  have he16 : Real.exp 0.16 ≤ 1.2 := by
    have := Real.exp_bound' (x := (0.16 : ℝ)) (by norm_num) (by norm_num) (n := 2) (by norm_num)
    have hs : (∑ m ∈ Finset.range 2, (0.16 : ℝ) ^ m / m.factorial)
        + (0.16 : ℝ) ^ 2 * (2 + 1) / ((Nat.factorial 2) * 2) ≤ 1.2 := by
      simp [Finset.sum_range_succ, Nat.factorial]; norm_num
    linarith
  have hkey : 3.3 * v ≤ v ^ 2 - v / 2 := by nlinarith
  have hexp : Real.exp (-(v ^ 2 - v / 2)) ≤ Real.exp (-(3.3 * v)) := Real.exp_le_exp.mpr (by linarith)
  have hpoly : (v ^ 2 + 0.16) * Real.exp (-(3.3 * v)) ≤ 0.015 := by
    have h4 := exp_ge_pow4 (by positivity : (0:ℝ) ≤ 3.3 * v)
    have hpos := Real.exp_pos (3.3 * v)
    have hinv : Real.exp (-(3.3 * v)) = (Real.exp (3.3 * v))⁻¹ := by rw [Real.exp_neg]
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have hv4 : (3.3 * v) ^ 4 / 24 ≥ 4.9 * v ^ 4 := by nlinarith [sq_nonneg v, sq_nonneg (v ^ 2)]
    have : v ^ 2 + 0.16 ≤ 0.015 * (4.9 * v ^ 4) := by nlinarith [sq_nonneg v]
    nlinarith
  have hA : 0 ≤ Real.exp (-(v ^ 2 - v / 2)) := (Real.exp_pos _).le
  have hB : 0 < Real.exp (-v / 2) := Real.exp_pos _
  calc (v ^ 2 + x0 ^ 2) * (Real.exp (x0 ^ 2) * Real.exp (-(v ^ 2 - v / 2)) * Real.exp (-v / 2))
      ≤ (v ^ 2 + 0.16) * (1.2 * Real.exp (-(3.3 * v)) * Real.exp (-v / 2)) := by
        apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_right _ hB.le
        exact mul_le_mul (by linarith) hexp hA (by norm_num)
    _ = 1.2 * ((v ^ 2 + 0.16) * Real.exp (-(3.3 * v))) * Real.exp (-v / 2) := by ring
    _ ≤ 1.2 * 0.015 * Real.exp (-v / 2) := by gcongr
    _ ≤ Real.exp (-v / 2) / 50 := by nlinarith

/-- **Negative control: the Gaussian functional at width `1/2` sees the fake zeros.**  At the
centre `pi / log 5` the fake Gaussian sum is strictly negative. -/
theorem fake_gaussian_negative :
    (fakeSide (RvMBridge6.gaussTest (Real.pi / Real.log 5) (1 / 2))).re < 0 := by
  set c := Real.pi / Real.log 5
  have hsum := summable_fake_gauss c (1 / 2) (by norm_num)
  unfold fakeSide
  rw [Complex.re_tsum hsum]
  have hterm : ∀ k : ℤ, (RvMBridge6.gaussTest c (1 / 2) (Zeta23.gammaOf (fakeZero k 1))
      + RvMBridge6.gaussTest c (1 / 2) (Zeta23.gammaOf (fakeZero k (-1)))).re
      = 2 * Aterm (1 / 2) (tk k - c) := by
    intro k
    rw [Complex.add_re, re_gauss_fake c (1 / 2) k (Or.inl rfl), re_gauss_fake c (1 / 2) k (Or.inr rfl)]
    ring
  simp_rw [hterm]
  obtain ⟨hr0, hr1⟩ := r_bounds
  have hs := spacing_bounds
  have hA : HasSum (fun k => 2 * Aterm (1 / 2) (tk k - c)) (∑' k, 2 * Aterm (1 / 2) (tk k - c)) := by
    have hs2 : Summable (fun k : ℤ => 2 * Aterm (1 / 2) (tk k - c)) :=
      ((Complex.hasSum_re hsum.hasSum).summable).congr hterm
    exact hs2.hasSum
  -- the value at k = 0
  have h0 : Aterm (1 / 2) (tk 0 - c) = -(x0 ^ 2 * Real.exp (x0 ^ 2)) := by
    rw [tk_center 0]
    unfold Aterm
    simp only [Int.cast_zero, mul_zero, zero_pow two_ne_zero, zero_sub, Real.cos_zero,
      Real.sin_zero, mul_one, add_zero, zero_mul]
    ring_nf
  -- majorant
  let G : ℤ → ℝ := fun k =>
    (if k = 0 then 2 * Aterm (1 / 2) (tk 0 - c) - 2 * (1 / 50) else 0)
      + 2 * (1 / 50) * Real.exp (-spacing / 2) ^ k.natAbs
  have hgeo := hasSum_two_sided hr0 (by linarith)
  have hG : HasSum G ((2 * Aterm (1 / 2) (tk 0 - c) - 2 * (1 / 50))
      + 2 * (1 / 50) * ((1 + Real.exp (-spacing / 2)) / (1 - Real.exp (-spacing / 2)))) :=
    (hasSum_ite_eq (0 : ℤ) _).add (hgeo.mul_left _)
  have hle : ∀ k, 2 * Aterm (1 / 2) (tk k - c) ≤ G k := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [G]
    · simp only [G, hk, if_false, zero_add]
      have hu : tk k - c = spacing * k := tk_center k
      have habs : |tk k - c| = spacing * |(k : ℝ)| := by
        rw [hu, abs_mul, abs_of_pos (by linarith)]
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
        exact_mod_cast this
      have hfar : 3.8 ≤ |tk k - c| := by rw [habs]; nlinarith
      have h1 := Aterm_ge_abs (1 / 2) (tk k - c)
      have h2 := far_half hfar
      -- upper bound: Aterm <= (u^2 + x0^2) e^{...}
      have hup : Aterm (1 / 2) (tk k - c) ≤
          ((tk k - c) ^ 2 + x0 ^ 2) * Real.exp (-(2 * (1 / 2)) * ((tk k - c) ^ 2 - x0 ^ 2)) := by
        unfold Aterm
        have hb := bracket_ge (1 / 2) (tk k - c)
        set θ := 4 * (1 / 2) * (tk k - c) * x0
        have hsc := Real.sin_sq_add_cos_sq θ
        set P := (tk k - c) ^ 2 - x0 ^ 2
        set Q := 2 * (tk k - c) * x0
        set R := (tk k - c) ^ 2 + x0 ^ 2
        have hid : (P * Real.cos θ + Q * Real.sin θ) ^ 2 + (P * Real.sin θ - Q * Real.cos θ) ^ 2
            = (P ^ 2 + Q ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        have hPQ : P ^ 2 + Q ^ 2 = R ^ 2 := by ring
        have hB2 : (P * Real.cos θ + Q * Real.sin θ) ^ 2 ≤ R ^ 2 := by
          rw [hsc, mul_one, hPQ] at hid
          nlinarith [sq_nonneg (P * Real.sin θ - Q * Real.cos θ)]
        have hR : 0 ≤ R := by positivity
        have hBle : P * Real.cos θ + Q * Real.sin θ ≤ R := by
          by_contra hcon
          have h1 : R < P * Real.cos θ + Q * Real.sin θ := not_le.mp hcon
          nlinarith
        have he := Real.exp_pos (-(2 * (1 / 2)) * P)
        nlinarith
      have h3 : Real.exp (-|tk k - c| / 2) = Real.exp (-spacing / 2) ^ k.natAbs := by
        rw [habs, ← Real.exp_nat_mul]
        congr 1
        rw [Nat.cast_natAbs, Int.cast_abs]
        ring
      rw [h3] at h2
      linarith
  have hcmp := hasSum_le hle hA hG
  have hxg := x0_gt
  have hval : 2 * Aterm (1 / 2) (tk 0 - c) ≤ -(2 * 0.0529) := by
    rw [h0]
    have : 0.0529 ≤ x0 ^ 2 * Real.exp (x0 ^ 2) := by
      have h1 : 0.0529 ≤ x0 ^ 2 := by nlinarith
      have h2 : 1 ≤ Real.exp (x0 ^ 2) := Real.one_le_exp (sq_nonneg _)
      nlinarith
    linarith
  have hgeo' : (1 + Real.exp (-spacing / 2)) / (1 - Real.exp (-spacing / 2)) ≤ 1.5 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-! ## I. The hybrid's zero side IS the multiplicity-weighted zero side of `xi * XiA`

`XiHR = xi * XiA` with the corpus's own `xi` (`RvMBridge18.xi`).  Its analytic order at every point
is `zeroMult rho + [XiA rho = 0]` (orders add; `xi`'s order is the E8 multiplicity,
`RvMBridge20.analyticOrderAt_xi_eq`; every fake zero is simple).  Its zero side
`sum_rho ord_rho(XiHR) H(gammaOf rho)` therefore splits as `zeroSide H + fakeSide H` whenever both
parts converge; for the Gaussian tests they do.  So the Gaussian statements of section G are
statements about the zeros of one explicit entire function. -/

/-- The completion of the golden hybrid, with the corpus's `xi`. -/
def XiHR (s : ℂ) : ℂ := RvMBridge18.xi s * XiA s

lemma XiA_differentiable : Differentiable ℂ XiA := by
  have : XiA = fun z => 2 * Complex.cosh ((z - 1 / 2) * (Real.log 5 : ℝ)) + ((Real.sqrt 5 : ℝ) : ℂ) := by
    funext z; rw [XiA_eq]
  rw [this]
  fun_prop

lemma XiA_one_sub (s : ℂ) : XiA (1 - s) = XiA s := Xi_symm _ _ s

theorem XiHR_entire : Differentiable ℂ XiHR := RvMBridge18.xi_differentiable.mul XiA_differentiable

theorem XiHR_one_sub (s : ℂ) : XiHR (1 - s) = XiHR s := by
  unfold XiHR; rw [RvMBridgeXi.xi_one_sub, XiA_one_sub]

lemma hasDerivAt_XiA (s : ℂ) :
    HasDerivAt XiA (2 * (Complex.sinh ((s - 1 / 2) * (Real.log 5 : ℝ)) * (Real.log 5 : ℝ))) s := by
  have h1 : HasDerivAt (fun z : ℂ => (z - 1 / 2) * (Real.log 5 : ℝ)) (Real.log 5 : ℝ) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const ((Real.log 5 : ℝ) : ℂ)
  have h2 := (((Complex.hasDerivAt_cosh _).comp s h1).const_mul (2 : ℂ)).add_const
    ((Real.sqrt 5 : ℝ) : ℂ)
  have hfun : XiA = fun z => 2 * Complex.cosh ((z - 1 / 2) * (Real.log 5 : ℝ))
      + ((Real.sqrt 5 : ℝ) : ℂ) := by
    funext z; rw [XiA_eq]
  rw [hfun]
  exact h2

/-- Every zero of `XiA` is simple: the derivative `2 log 5 sinh((s - 1/2) log 5)` has
`sinh^2 = 1/4` there. -/
theorem deriv_XiA_ne_zero {s : ℂ} (hs : XiA s = 0) : deriv XiA s ≠ 0 := by
  rw [(hasDerivAt_XiA s).deriv]
  have hc : Complex.cosh ((s - 1 / 2) * (Real.log 5 : ℝ)) = -(Real.sqrt 5 : ℂ) / 2 := by
    rw [XiA_eq] at hs; linear_combination hs / 2
  have hsq := Complex.cosh_sq_sub_sinh_sq ((s - 1 / 2) * (Real.log 5 : ℝ))
  rw [hc] at hsq
  have h5 : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    rw [← Complex.ofReal_pow, sqrt5_sq]; push_cast; ring
  have hsh : Complex.sinh ((s - 1 / 2) * (Real.log 5 : ℝ)) ^ 2 = 1 / 4 := by
    linear_combination -hsq + h5 / 4
  have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt log5_pos)
  intro h0
  have : Complex.sinh ((s - 1 / 2) * (Real.log 5 : ℝ)) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · norm_num at h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hLc
  rw [this] at hsh
  norm_num at hsh

lemma analyticOrderAt_XiA (s : ℂ) :
    analyticOrderAt XiA s = (if XiA s = 0 then 1 else 0 : ℕ) := by
  have hA : AnalyticAt ℂ XiA s := XiA_differentiable.analyticAt s
  by_cases hs : XiA s = 0
  · rw [if_pos hs]
    have h := hA.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (deriv_XiA_ne_zero hs)
    have hfun : (fun z => XiA z - XiA s) = XiA := by funext z; rw [hs, sub_zero]
    rw [hfun] at h
    rw [h]; rfl
  · rw [if_neg hs]
    exact analyticOrderAt_eq_zero.mpr (Or.inr hs)

/-- **The analytic order of `XiHR` is `zeroMult + [fake zero]` at every point.** -/
theorem analyticOrderNatAt_XiHR (ρ : ℂ) :
    analyticOrderNatAt XiHR ρ = WeilExplicit.zeroMult ρ + (if XiA ρ = 0 then 1 else 0) := by
  have hx : AnalyticAt ℂ RvMBridge18.xi ρ := RvMBridge18.xi_differentiable.analyticAt ρ
  have hA : AnalyticAt ℂ XiA ρ := XiA_differentiable.analyticAt ρ
  have hxt := RvMBridge20.analyticOrderAt_xi_ne_top ρ
  have hAt : analyticOrderAt XiA ρ ≠ ⊤ := by
    rw [analyticOrderAt_XiA]; exact ENat.natCast_ne_top _
  have hmul : XiHR = RvMBridge18.xi * XiA := rfl
  rw [hmul, analyticOrderNatAt_mul hx hA hxt hAt]
  congr 1
  · unfold analyticOrderNatAt; rw [RvMBridge20.analyticOrderAt_xi_eq]; rfl
  · unfold analyticOrderNatAt; rw [analyticOrderAt_XiA]; rfl

/-- The multiplicity-weighted zero side of `XiHR`. -/
def XiHRZeroSide (H : ℂ → ℂ) : ℂ :=
  ∑' ρ : ℂ, (analyticOrderNatAt XiHR ρ : ℂ) * H (Zeta23.gammaOf ρ)

lemma fakeZero_injective (ε : ℝ) : Function.Injective (fun k : ℤ => fakeZero k ε) := by
  intro k l hkl
  have him := congrArg Complex.im hkl
  simp only [fakeZero_im] at him
  have hL := log5_pos
  have hpi := Real.pi_pos
  have : (2 * (k : ℝ) + 1) = 2 * (l : ℝ) + 1 := by
    field_simp at him
    nlinarith [him]
  have : (k : ℝ) = l := by linarith
  exact_mod_cast this

open Classical in
/-- For `rho` a fake zero, exactly one sign representation. -/
lemma fake_indicator_split (ρ : ℂ) :
    ((if XiA ρ = 0 then 1 else 0 : ℕ) : ℂ)
      = (if ρ ∈ Set.range (fun k : ℤ => fakeZero k 1) then 1 else 0)
        + (if ρ ∈ Set.range (fun k : ℤ => fakeZero k (-1)) then 1 else 0) := by
  have hx := x0_pos
  by_cases h : XiA ρ = 0
  · rw [if_pos h]
    obtain ⟨k, ε, hε, rfl⟩ := (XiA_eq_zero_iff ρ).1 h
    rcases hε with rfl | rfl
    · have hn : fakeZero k 1 ∉ Set.range (fun k : ℤ => fakeZero k (-1)) := by
        rintro ⟨l, hl⟩
        have := congrArg Complex.re hl
        simp only [fakeZero_re] at this
        linarith
      rw [if_pos (Set.mem_range_self k), if_neg hn]; norm_num
    · have hn : fakeZero k (-1) ∉ Set.range (fun k : ℤ => fakeZero k 1) := by
        rintro ⟨l, hl⟩
        have := congrArg Complex.re hl
        simp only [fakeZero_re] at this
        linarith
      rw [if_pos (Set.mem_range_self k), if_neg hn]; norm_num
  · rw [if_neg h]
    have h1 : ρ ∉ Set.range (fun k : ℤ => fakeZero k 1) := by
      rintro ⟨k, rfl⟩; exact h (XiA_fakeZero k 1 (Or.inl rfl))
    have h2 : ρ ∉ Set.range (fun k : ℤ => fakeZero k (-1)) := by
      rintro ⟨k, rfl⟩; exact h (XiA_fakeZero k (-1) (Or.inr rfl))
    rw [if_neg h1, if_neg h2]; norm_num

open Classical in
/-- Reindexing one sign of the fake zeros from `Z` to `C`. -/
lemma fake_reindex (H : ℂ → ℂ) {ε : ℝ}
    (hs : Summable (fun k : ℤ => H (Zeta23.gammaOf (fakeZero k ε)))) :
    Summable (fun ρ : ℂ => (if ρ ∈ Set.range (fun k : ℤ => fakeZero k ε) then 1 else 0)
        * H (Zeta23.gammaOf ρ)) ∧
    ∑' ρ : ℂ, (if ρ ∈ Set.range (fun k : ℤ => fakeZero k ε) then 1 else 0) * H (Zeta23.gammaOf ρ)
      = ∑' k : ℤ, H (Zeta23.gammaOf (fakeZero k ε)) := by
  set f : ℂ → ℂ := fun ρ => (if ρ ∈ Set.range (fun k : ℤ => fakeZero k ε) then 1 else 0)
      * H (Zeta23.gammaOf ρ)
  have hinj := fakeZero_injective ε
  have hzero : ∀ x ∉ Set.range (fun k : ℤ => fakeZero k ε), f x = 0 := by
    intro x hx; simp only [f, if_neg hx, zero_mul]
  have hcomp : (f ∘ fun k : ℤ => fakeZero k ε) = fun k => H (Zeta23.gammaOf (fakeZero k ε)) := by
    funext k; simp only [f, Function.comp, if_pos (Set.mem_range_self (f := fun k : ℤ => fakeZero k ε) k), one_mul]
  constructor
  · exact (hinj.summable_iff hzero).1 (by rw [hcomp]; exact hs)
  · have hsupp : Function.support f ⊆ Set.range (fun k : ℤ => fakeZero k ε) := by
      intro x hx; by_contra h; exact hx (hzero x h)
    rw [← hinj.tsum_eq hsupp]
    exact tsum_congr (fun k => by simp only [f, if_pos (Set.mem_range_self (f := fun k : ℤ => fakeZero k ε) k), one_mul])

open Classical in
/-- **The zero side of `XiHR` is `zeroSide + fakeSide`** (given convergence of the parts). -/
theorem XiHRZeroSide_eq (H : ℂ → ℂ)
    (hz : Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * H (Zeta23.gammaOf ρ)))
    (h1 : Summable (fun k : ℤ => H (Zeta23.gammaOf (fakeZero k 1))))
    (h2 : Summable (fun k : ℤ => H (Zeta23.gammaOf (fakeZero k (-1))))) :
    XiHRZeroSide H = RvMBridge6.zeroSide H + fakeSide H := by
  obtain ⟨s1, e1⟩ := fake_reindex H h1
  obtain ⟨s2, e2⟩ := fake_reindex H h2
  have hsplit : ∀ ρ : ℂ, (analyticOrderNatAt XiHR ρ : ℂ) * H (Zeta23.gammaOf ρ)
      = (WeilExplicit.zeroMult ρ : ℂ) * H (Zeta23.gammaOf ρ)
        + ((if ρ ∈ Set.range (fun k : ℤ => fakeZero k 1) then 1 else 0) * H (Zeta23.gammaOf ρ)
          + (if ρ ∈ Set.range (fun k : ℤ => fakeZero k (-1)) then 1 else 0) * H (Zeta23.gammaOf ρ)) := by
    intro ρ
    rw [analyticOrderNatAt_XiHR ρ, Nat.cast_add, fake_indicator_split ρ]
    ring
  unfold XiHRZeroSide fakeSide RvMBridge6.zeroSide
  rw [tsum_congr hsplit, hz.tsum_add (s1.add s2), s1.tsum_add s2, e1, e2, h1.tsum_add h2]

lemma summable_fake_gauss_sign (c lam : ℝ) (hlam : 0 < lam) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Summable (fun k : ℤ => RvMBridge6.gaussTest c lam (Zeta23.gammaOf (fakeZero k ε))) := by
  set M := (1 / lam + x0 ^ 2) * Real.exp (1 / (4 * lam) + 2 * lam * x0 ^ 2)
  obtain ⟨hr0, hr1⟩ := r_bounds
  have hM : 0 ≤ M := by positivity
  have hg : Summable (fun k : ℤ => M * Real.exp (spacing / 2) * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs) :=
    ((hasSum_two_sided_shift hr0 (by linarith) (jIdx c)).summable).mul_left _
  refine Summable.of_norm_bounded hg (fun k => ?_)
  rw [norm_gauss_fake c lam k hε]
  have h1 := gauss_le_exp_abs hlam (tk k - c)
  have h2 := exp_neg_half_abs_le c k
  have h3 : Real.exp (-|tk k - c|) ≤ Real.exp (-|tk k - c| / 2) :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg (tk k - c)])
  calc _ ≤ M * Real.exp (-|tk k - c|) := h1
    _ ≤ M * (Real.exp (spacing / 2) * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs) := by
        gcongr; linarith
    _ = M * Real.exp (spacing / 2) * Real.exp (-spacing / 2) ^ (k - jIdx c).natAbs := by ring

/-- **The zero side of the ENTIRE FUNCTION `xi * XiA` satisfies E6Bridge30** (every centre, every
width `<= 3/2000`), and it has an off-line zero. -/
theorem XiHR_gaussian_positivity_small (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 3 / 2000) :
    0 ≤ (XiHRZeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [XiHRZeroSide_eq _ (RvMBridge6.summable_gauss_zeroSide c lam hlam)
    (summable_fake_gauss_sign c lam hlam (Or.inl rfl))
    (summable_fake_gauss_sign c lam hlam (Or.inr rfl))]
  exact hybrid_gaussian_positivity_small c lam hlam hle

/-- **... and the E6Bridge16 envelope at every width `<= 1/40`.** -/
theorem XiHR_gaussian_envelope (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ 1 / 40)
    (hc : RvMBridge16.envelopeCsharp lam ≤ |c|) :
    0 ≤ (XiHRZeroSide (RvMBridge6.gaussTest c lam)).re := by
  rw [XiHRZeroSide_eq _ (RvMBridge6.summable_gauss_zeroSide c lam hlam)
    (summable_fake_gauss_sign c lam hlam (Or.inl rfl))
    (summable_fake_gauss_sign c lam hlam (Or.inr rfl))]
  exact hybrid_gaussian_envelope c lam hlam hle hc

theorem XiHR_offline_zero : XiHR (fakeZero 0 1) = 0 ∧ (fakeZero 0 1).re ≠ 1 / 2 := by
  refine ⟨?_, fakeZero_re_ne_half 0 (Or.inl rfl)⟩
  unfold XiHR; rw [XiA_fakeZero 0 1 (Or.inl rfl), mul_zero]

/-! ## J. The Gaussian layer of the barrier, in one statement -/

/-- **The Gaussian layer of the golden-fake barrier (kernel form).**  The multiplicity-weighted zero
side of the entire function `xi * XiA` satisfies the corpus's proved Gaussian positivity (every
centre at widths `<= 3/2000`; the sharp envelope at widths `<= 1/40`), the function is symmetric and
has an off-line zero, and the full Wall detects the fake at width `1/2`. -/
theorem gaussian_layer_barrier :
    Differentiable ℂ XiHR ∧ (∀ s, XiHR (1 - s) = XiHR s) ∧
    (∀ c lam : ℝ, 0 < lam → lam ≤ 3 / 2000 →
      0 ≤ (XiHRZeroSide (RvMBridge6.gaussTest c lam)).re) ∧
    (∀ c lam : ℝ, 0 < lam → lam ≤ 1 / 40 → RvMBridge16.envelopeCsharp lam ≤ |c| →
      0 ≤ (XiHRZeroSide (RvMBridge6.gaussTest c lam)).re) ∧
    (∃ ρ : ℂ, XiHR ρ = 0 ∧ ρ.re ≠ 1 / 2) ∧
    (fakeSide (RvMBridge6.gaussTest (Real.pi / Real.log 5) (1 / 2))).re < 0 :=
  ⟨XiHR_entire, XiHR_one_sub, XiHR_gaussian_positivity_small, XiHR_gaussian_envelope,
    ⟨fakeZero 0 1, XiHR_offline_zero⟩, fake_gaussian_negative⟩

end CruxMetaBarriersRvM

#print axioms CruxMetaBarriersRvM.Xi_symm
#print axioms CruxMetaBarriersRvM.cosh_decomp
#print axioms CruxMetaBarriersRvM.sqrt5_sq
#print axioms CruxMetaBarriersRvM.sqrt5_bounds
#print axioms CruxMetaBarriersRvM.phi_pos
#print axioms CruxMetaBarriersRvM.one_lt_phi
#print axioms CruxMetaBarriersRvM.phi_lt
#print axioms CruxMetaBarriersRvM.phi_sq
#print axioms CruxMetaBarriersRvM.cosh_log_phi
#print axioms CruxMetaBarriersRvM.log5_pos
#print axioms CruxMetaBarriersRvM.log5_bounds
#print axioms CruxMetaBarriersRvM.log_phi_pos
#print axioms CruxMetaBarriersRvM.log_phi_lt
#print axioms CruxMetaBarriersRvM.two_log_phi_lt_log5
#print axioms CruxMetaBarriersRvM.x0_pos
#print axioms CruxMetaBarriersRvM.x0_lt_half
#print axioms CruxMetaBarriersRvM.x0_lt
#print axioms CruxMetaBarriersRvM.pi_div_log5_bounds
#print axioms CruxMetaBarriersRvM.fakeZero_re
#print axioms CruxMetaBarriersRvM.fakeZero_im
#print axioms CruxMetaBarriersRvM.cosh_w0
#print axioms CruxMetaBarriersRvM.XiA_eq
#print axioms CruxMetaBarriersRvM.w_of_fakeZero
#print axioms CruxMetaBarriersRvM.XiA_fakeZero
#print axioms CruxMetaBarriersRvM.XiA_eq_zero_iff
#print axioms CruxMetaBarriersRvM.XiA_periodic
#print axioms CruxMetaBarriersRvM.fakeZero_re_mem
#print axioms CruxMetaBarriersRvM.fakeZero_re_ne_half
#print axioms CruxMetaBarriersRvM.fakeZero_abs_re_sub_half
#print axioms CruxMetaBarriersRvM.one_le_abs_two_mul_add_one
#print axioms CruxMetaBarriersRvM.fakeZero_abs_im_ge
#print axioms CruxMetaBarriersRvM.fakeZero_im_sq_ge
#print axioms CruxMetaBarriersRvM.fakeZero_in_box
#print axioms CruxMetaBarriersRvM.gammaOf_fakeZero
#print axioms CruxMetaBarriersRvM.gauss_at
#print axioms CruxMetaBarriersRvM.re_gauss_at
#print axioms CruxMetaBarriersRvM.norm_gauss_at
#print axioms CruxMetaBarriersRvM.gammaOf_fakeZero'
#print axioms CruxMetaBarriersRvM.re_gauss_fake
#print axioms CruxMetaBarriersRvM.norm_gauss_fake
#print axioms CruxMetaBarriersRvM.x0_sq_lt
#print axioms CruxMetaBarriersRvM.bracket_ge
#print axioms CruxMetaBarriersRvM.Aterm_ge_abs
#print axioms CruxMetaBarriersRvM.trig_signs
#print axioms CruxMetaBarriersRvM.Aterm_nonneg
#print axioms CruxMetaBarriersRvM.Aterm_ge_neg
#print axioms CruxMetaBarriersRvM.exp_neg_eight_tenths
#print axioms CruxMetaBarriersRvM.Aterm_neighbor
#print axioms CruxMetaBarriersRvM.exp_ge_pow4
#print axioms CruxMetaBarriersRvM.tail_le
#print axioms CruxMetaBarriersRvM.spacing_bounds
#print axioms CruxMetaBarriersRvM.tk_eq
#print axioms CruxMetaBarriersRvM.u_jIdx_mem
#print axioms CruxMetaBarriersRvM.u_shift
#print axioms CruxMetaBarriersRvM.abs_u_ge_of_far
#print axioms CruxMetaBarriersRvM.exp_neg_half_abs_le
#print axioms CruxMetaBarriersRvM.hasSum_two_sided
#print axioms CruxMetaBarriersRvM.hasSum_two_sided_shift
#print axioms CruxMetaBarriersRvM.r_bounds
#print axioms CruxMetaBarriersRvM.gauss_le_exp_abs
#print axioms CruxMetaBarriersRvM.summable_fake_gauss
#print axioms CruxMetaBarriersRvM.pair_ge
#print axioms CruxMetaBarriersRvM.far_ge
#print axioms CruxMetaBarriersRvM.fake_gaussian_nonneg
#print axioms CruxMetaBarriersRvM.hybrid_gaussian_positivity_small
#print axioms CruxMetaBarriersRvM.hybrid_gaussian_envelope
#print axioms CruxMetaBarriersRvM.log_phi_gt
#print axioms CruxMetaBarriersRvM.x0_gt
#print axioms CruxMetaBarriersRvM.tk_center
#print axioms CruxMetaBarriersRvM.far_half
#print axioms CruxMetaBarriersRvM.fake_gaussian_negative
#print axioms CruxMetaBarriersRvM.XiA_differentiable
#print axioms CruxMetaBarriersRvM.XiA_one_sub
#print axioms CruxMetaBarriersRvM.XiHR_entire
#print axioms CruxMetaBarriersRvM.XiHR_one_sub
#print axioms CruxMetaBarriersRvM.hasDerivAt_XiA
#print axioms CruxMetaBarriersRvM.deriv_XiA_ne_zero
#print axioms CruxMetaBarriersRvM.analyticOrderAt_XiA
#print axioms CruxMetaBarriersRvM.analyticOrderNatAt_XiHR
#print axioms CruxMetaBarriersRvM.fakeZero_injective
#print axioms CruxMetaBarriersRvM.fake_indicator_split
#print axioms CruxMetaBarriersRvM.fake_reindex
#print axioms CruxMetaBarriersRvM.XiHRZeroSide_eq
#print axioms CruxMetaBarriersRvM.summable_fake_gauss_sign
#print axioms CruxMetaBarriersRvM.XiHR_gaussian_positivity_small
#print axioms CruxMetaBarriersRvM.XiHR_gaussian_envelope
#print axioms CruxMetaBarriersRvM.XiHR_offline_zero
#print axioms CruxMetaBarriersRvM.gaussian_layer_barrier
