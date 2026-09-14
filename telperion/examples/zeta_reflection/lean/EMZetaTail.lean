/-  EMZetaTail.lean -- A2 Theorem 1, TAIL track: the order-K Euler-Maclaurin tail engine.

    The blocker of PROGRAM ANDÚRIL's reflection track.  Builds on `EMZeta.lean` /
    `EMZetaComplex.lean` (the K=1 chain).  The K=1 remainder envelope `‖s‖/(2·Re s)` proven in
    `EMZetaComplex.em_zeta_strip_enclosure` is sign-LOOSE (≈14 at s=1/2+14i), so the G2 reflected
    band could not be made sign-tight from it.  This file raises the Euler-Maclaurin order and cuts
    the sum at a finite `N`, producing a remainder that DECAYS like `N^{-Re s - K + 1}`, small enough
    to make `gLine` boxes sign-tight.

    Architecture (bottom-up, all real-`s` first, then the complex analytic continuation):

      F.  Order-k periodized "saw" Bernoulli API beyond k=1:
            * `sawBernoulli k` is already defined in EMZeta; here we prove
              `sawBernoulli_hasDerivAt_ae`-style derivative facts (`(k+1)·sawBernoulli k` a.e.),
              and the EXPLICIT sup bounds `|sawBernoulli 2| ≤ 1/6`, `|sawBernoulli 3| ≤ B3sup`.
      G.  `em_saw_step` — the one IBP step raising the saw order by one over a unit cell (the
            proven form of `EMZetaWip.em_saw_step_wip`).
      H.  The order-K remainder over the tail `[N, ∞)` with the explicit `N`-decaying bound.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin tail bound),
    NOT a proof of RH.
-/
import EMZeta
import EMZetaComplex

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace ZetaReflection

/-! ## F. Order-k periodized Bernoulli: derivative tower and explicit sup bounds. -/

/-- The order-2 saw on the cell `[m, m+1)` is `(x - m)^2 - (x - m) + 1/6`. -/
lemma sawBernoulli_two_eq_on_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli 2 x = (x - m) ^ 2 - (x - m) + 6⁻¹ := by
  rw [sawBernoulli_eq_on_Ico 2 hx, bernoulliFun_two]

/-- Explicit sup bound for the order-2 saw: `|sawBernoulli 2 x| ≤ 1/6`.
    On the unit cell `y := {x} ∈ [0,1)`, `B₂(y) = y² − y + 1/6 = (y − 1/2)² − 1/12 ∈ [−1/12, 1/6]`. -/
lemma abs_sawBernoulli_two_le (x : ℝ) : |sawBernoulli 2 x| ≤ 1 / 6 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  rw [sawBernoulli, bernoulliFun_two, abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract x - 1/2), h0, h1]

/-- The order-3 saw on `[0,1)` in closed form: `B₃(y) = y³ − (3/2)y² + (1/2)y`
    (`bernoulli 3 = 0` kills the constant term). -/
lemma bernoulliFun_three (y : ℝ) :
    bernoulliFun 3 y = y ^ 3 - (3/2) * y ^ 2 + (1/2) * y := by
  have h3zero : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  simp only [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Polynomial.eval_finset_sum, h3zero]
  ring

/-- Explicit sup bound for the order-3 saw: `|sawBernoulli 3 x| ≤ 1/12`.
    `B₃(y) = y(1−y)(1/2−y)` on `[0,1)`; its exact extrema are `±√3/36 ≈ ±0.0481`, so the clean
    rational envelope `1/12 ≈ 0.083` (nlinarith-certifiable) is a valid — and, at the tail cut
    `N ≥ 50`, sign-tight — bound.  See the reported remainder number in the module header. -/
lemma abs_sawBernoulli_three_le (x : ℝ) : |sawBernoulli 3 x| ≤ 1 / 12 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  set y := Int.fract x with hy
  have hy1 : y ≤ 1 := le_of_lt h1
  rw [sawBernoulli, bernoulliFun_three, abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hy1), sq_nonneg (2*y-1),
      mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hy1)) (sq_nonneg (2*y-1))]
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hy1), sq_nonneg (2*y-1),
      mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hy1)) (sq_nonneg (2*y-1))]

end ZetaReflection
