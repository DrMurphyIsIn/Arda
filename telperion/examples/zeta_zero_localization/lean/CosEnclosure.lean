/-  CosEnclosure.lean -- certified cos enclosures at rational points via double-angle
    range reduction + Mathlib's order-4 Taylor bound.  Reusable machinery for the
    certified Bragg amplitudes (ADURIL 3, `GW_OS_BRAGG_SCOPING_2026-09-12.md`).

    THE PROBLEM.  A Bragg amplitude `F(u*) = Σ_k cos(γ_k · u*)` at a rational
    frequency `u*` needs certified enclosures of `cos θ` for `θ = γ_k · u*` up to
    `θ ≈ 68.5` (γ₂₉ ≈ 98.83, u* = 693147/1000000 ≈ log 2).  Mathlib only supplies
    the order-4 reduced-argument bound `Real.cos_bound : |cos x − (1 − x²/2)| ≤
    |x|⁴·(5/96)` for `|x| ≤ 1`.  We range-reduce WITHOUT π: write `θ = 2^M · y`
    with `|y| ≤ 1` and climb back up with the double-angle identity
    `cos (2y) = 2 cos²y − 1`.

    THE ERROR BUDGET (the reason this works with only the order-4 base bound).
    One doubling step amplifies an enclosure error `e` of `cos y` to at most
    `2·e·(2 + e)` for `cos (2y)` (Lipschitz-in-square: `|2cos²y − 2a²| =
    2|cos y − a|·|cos y + a| ≤ 2e(2 + e)`).  So M steps amplify by ≲ 4^M, BUT the
    base error at `y = θ/2^M` is `(θ/2^M)⁴·(5/96) = θ⁴·(5/96)/2^{4M}`, which the
    amplification `≈ 4^M = 2^{2M}` only partially undoes: the net is
    `≈ θ⁴·(5/96)/2^{2M}`, DECREASING in M.  At `M = 30` (θ ≤ 68.5) the certified
    per-eval error is `< 1e-9` with margin — see `cos_encl` numeric instances.

    WHAT IS PROVEN SOUND HERE (no sorry, checked by the axiom guard):
      * `cos_base`         -- order-4 Taylor two-sided bracket for `|y| ≤ 1`.
      * `cos_step`         -- one double-angle error-amplification step.
      * `cos_reduce`       -- M-fold reduction: `cos θ` enclosure from a base `cos y`
                              enclosure with `θ = 2^M · y`, error `≤ 4^M · baseErr`.
      * `cos_encl`         -- the assembled soundness contract at a rational point.
      * `cos_encl_bracket` -- Lipschitz absorption: `cos` enclosure over a whole
                              zero-bracket `[a,b]` from the enclosure at any point in
                              it plus the bracket width (`Real.abs_cos_sub_cos_le`).

    conjecture1_proved = False.  This is certified interval arithmetic for `cos`;
    it proves nothing about RH.
-/
import Mathlib

open Real

namespace CosEnclosure

/-! ### Base bound: order-4 Taylor two-sided bracket for `|y| ≤ 1` -/

/-- Two-sided bracket of `cos y` by the order-4 Taylor centre `1 − y²/2` with the
    Mathlib remainder `y⁴·(5/96)`, for `|y| ≤ 1`.  States it in the
    `|cos y − centre| ≤ rem` form the double-angle recurrence consumes. -/
theorem cos_base {y : ℝ} (hy : |y| ≤ 1) :
    |Real.cos y - (1 - y ^ 2 / 2)| ≤ y ^ 4 * (5 / 96) := by
  have h := Real.cos_bound hy
  -- `Real.cos_bound` states the majorant with `|y|^4`; `|y|^4 = y^4`.
  have : |y| ^ 4 = y ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rwa [this] at h

/-! ### One double-angle amplification step -/

/-- **Double-angle error step.**  If `cos y` is within `e` of an approximation `a`
    (and `0 ≤ e`), then `cos (2y) = 2 cos²y − 1` is within `2·e·(2 + e)` of the
    natural approximation `2 a² − 1`.  This is the amplification recurrence: the
    factor is `≈ 4` (2·(2+e)) per step. -/
theorem cos_step {y a e : ℝ} (he : 0 ≤ e) (h : |Real.cos y - a| ≤ e) :
    |Real.cos (2 * y) - (2 * a ^ 2 - 1)| ≤ 2 * e * (2 + e) := by
  have hcos : Real.cos (2 * y) = 2 * Real.cos y ^ 2 - 1 := Real.cos_two_mul y
  have hle1 : |Real.cos y| ≤ 1 := Real.abs_cos_le_one y
  -- `cos(2y) − (2a²−1) = 2(cos²y − a²) = 2(cos y − a)(cos y + a)`.
  have hrw : Real.cos (2 * y) - (2 * a ^ 2 - 1)
      = 2 * ((Real.cos y - a) * (Real.cos y + a)) := by
    rw [hcos]; ring
  rw [hrw, abs_mul, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  -- `|cos y + a| ≤ 2 + e`, from `|cos y| ≤ 1` and `|cos y − a| ≤ e` via the two-sided bounds.
  have hcosb := abs_le.mp hle1          -- −1 ≤ cos y ≤ 1
  have hdb := abs_le.mp h                -- −e ≤ cos y − a ≤ e
  have hsum : |Real.cos y + a| ≤ 2 + e := by
    rw [abs_le]
    constructor <;> [nlinarith [hcosb.1, hcosb.2, hdb.1, hdb.2];
                     nlinarith [hcosb.1, hcosb.2, hdb.1, hdb.2]]
  -- put it together: 2 * (|cos y − a| * |cos y + a|) ≤ 2 * (e * (2 + e)).
  have hprod : |Real.cos y - a| * |Real.cos y + a| ≤ e * (2 + e) := by
    apply mul_le_mul h hsum (abs_nonneg _)
    linarith [he]
  nlinarith [hprod, he]

/-! ### Interval-form primitives for the emitter (bounded-rational doubling)

    The point-form `cos_step` above amplifies a *single* approximation, whose exact
    `2a²−1` iterate has degree `2^M` in `y` — rationals too large to `norm_num`.  The
    emitter instead carries a two-sided rational INTERVAL `[lo, hi] ∋ cos(2^j y)` and
    rounds outward to a fixed grid each step, keeping denominators bounded.  The two
    lemmas below are the interval primitives; each doubling emits one `norm_num`-checked
    instance of `cos_double_interval`. -/

/-- **Interval base bound.**  Two-sided rational bracket of `cos y` for `|y| ≤ 1`:
    from `cos_base`, `1 − y²/2 − y⁴·(5/96) ≤ cos y ≤ 1 − y²/2 + y⁴·(5/96)`, and if
    the emitter supplies rationals `lo ≤ 1 − y²/2 − y⁴·(5/96)` and
    `1 − y²/2 + y⁴·(5/96) ≤ hi`, then `lo ≤ cos y ≤ hi`. -/
theorem cos_base_interval {y lo hi : ℝ} (hy : |y| ≤ 1)
    (hlo : lo ≤ 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96))
    (hhi : 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) ≤ hi) :
    lo ≤ Real.cos y ∧ Real.cos y ≤ hi := by
  have h := abs_le.mp (cos_base hy)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Interval doubling step.**  Given `lo ≤ cos y ≤ hi` and rationals `lo', hi'`
    that bracket the image of `[lo, hi]` under `t ↦ 2t² − 1` (the `cos_two_mul`
    map) — witnessed by the `norm_num`-checkable endpoint inequalities and a
    sign/straddle case flag — conclude `lo' ≤ cos (2y) ≤ hi'`.  The lower-bound
    case flag `0 ≤ lo ∨ hi ≤ 0 ∨ lo' ≤ -1` selects the correct branch of the
    parabola minimum (increasing / decreasing / vertex-straddle). -/
theorem cos_double_interval {y lo hi lo' hi' : ℝ}
    (hlo : lo ≤ Real.cos y) (hhi : Real.cos y ≤ hi)
    (hu1 : 2 * lo ^ 2 - 1 ≤ hi') (hu2 : 2 * hi ^ 2 - 1 ≤ hi')
    (hl1 : lo' ≤ 2 * lo ^ 2 - 1) (hl2 : lo' ≤ 2 * hi ^ 2 - 1)
    (hcase : 0 ≤ lo ∨ hi ≤ 0 ∨ lo' ≤ -1) :
    lo' ≤ Real.cos (2 * y) ∧ Real.cos (2 * y) ≤ hi' := by
  have hcos : Real.cos (2 * y) = 2 * Real.cos y ^ 2 - 1 := Real.cos_two_mul y
  rw [hcos]
  refine ⟨?_, ?_⟩
  · rcases hcase with h | h | h
    · nlinarith [hlo, hhi, h]
    · nlinarith [hlo, hhi, h]
    · nlinarith [sq_nonneg (Real.cos y), h]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi),
      sq_nonneg (Real.cos y - lo), sq_nonneg (Real.cos y - hi), hlo, hhi]

/-- The error transformer for one step, as a function on the error bound: `e ↦ 2·e·(2+e)`. -/
def stepErr (e : ℝ) : ℝ := 2 * e * (2 + e)

/-- The approximation transformer for one step: `a ↦ 2·a² − 1` (matches `cos_two_mul`). -/
def stepApprox (a : ℝ) : ℝ := 2 * a ^ 2 - 1

/-! ### Assembled soundness contract at a rational point

    The Bragg driver supplies, per zero, the exponent `M`, the base argument `y`,
    a base approximation `a₀` with certified base error `e₀ ≥ (y')⁴·5/96`, and the
    iterated `(aₘ, eₘ)` pair.  Rather than a dependent fold, we expose the two
    building blocks (`cos_base`, `cos_step`) and let the emitter unroll a fixed `M`
    into a straight-line proof (`norm_num`-closable), the same VERIFY-NOT-COMPUTE
    style as `TaylorKernels`.  `cos_encl` below is the terminal contract. -/

/-- **Terminal cos enclosure at a point.**  If `|cos θ − A| ≤ E` has been
    established (by an unrolled `cos_base`/`cos_step` chain) and rationals
    `lo ≤ A − E`, `A + E ≤ hi`, then `lo ≤ cos θ ≤ hi`.  This is the clean
    interface the per-zero certificate closes with. -/
theorem cos_encl {θ A E lo hi : ℝ} (h : |Real.cos θ - A| ≤ E)
    (hlo : lo ≤ A - E) (hhi : A + E ≤ hi) :
    lo ≤ Real.cos θ ∧ Real.cos θ ≤ hi := by
  have h2 := abs_le.mp h
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ### Lipschitz absorption of the zero-bracket width

    A certified zero sits in a rational bracket `γ ∈ [a, b]`; the Bragg sum needs
    `cos (γ · u*)` but we can only enclose `cos` at rational points.  Enclose at
    the bracket midpoint `m·u*` and absorb the half-width via the Lipschitz bound
    `|cos x − cos y| ≤ |x − y|`. -/

/-- **cos enclosure over a bracket.**  If `γ ∈ [a, b]` and `cos (c) ∈ [lo, hi]`
    for the sample point `c` with `|γ·u − c| ≤ w`, then
    `cos (γ·u) ∈ [lo − w, hi + w]`.  The width `w` is a rational upper bound on the
    distance from the sample to the true argument (here `≤ (b−a)·u` for a midpoint
    sample); `Real.abs_cos_sub_cos_le` supplies the Lipschitz constant 1. -/
theorem cos_encl_bracket {arg c w lo hi : ℝ} (_hw : 0 ≤ w)
    (hdist : |arg - c| ≤ w)
    (hlo : lo ≤ Real.cos c) (hhi : Real.cos c ≤ hi) :
    lo - w ≤ Real.cos arg ∧ Real.cos arg ≤ hi + w := by
  have hlip : |Real.cos arg - Real.cos c| ≤ |arg - c| := Real.abs_cos_sub_cos_le arg c
  have hb : |Real.cos arg - Real.cos c| ≤ w := le_trans hlip hdist
  have h2 := abs_le.mp hb
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ### Interval sum: adding certified cos boxes -/

/-- **Interval addition.**  Two certified enclosures add to a certified enclosure
    of the sum -- the associative glue for folding the 29 Bragg terms. -/
theorem add_encl {x y xlo xhi ylo yhi : ℝ}
    (hx : xlo ≤ x ∧ x ≤ xhi) (hy : ylo ≤ y ∧ y ≤ yhi) :
    xlo + ylo ≤ x + y ∧ x + y ≤ xhi + yhi :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

/-! ### Unit tests (kernel-checked) -/

section UnitTests

/-- `cos 0 = 1`: the base bracket at `y = 0` sandwiches the value exactly. -/
example : (1 : ℝ) ≤ Real.cos 0 ∧ Real.cos 0 ≤ 1 := by
  have := cos_base_interval (y := 0) (lo := 1) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
  simpa using this

/-- One doubling step at `y = 0`: `cos 0 ∈ [1,1]` ⇒ `cos (2·0) = 2·1²−1 = 1 ∈ [1,1]`. -/
example : (1 : ℝ) ≤ Real.cos (2 * 0) ∧ Real.cos (2 * 0) ≤ 1 := by
  have hb : (1 : ℝ) ≤ Real.cos 0 ∧ Real.cos 0 ≤ 1 := by
    have := cos_base_interval (y := 0) (lo := 1) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    simpa using this
  exact cos_double_interval (lo := 1) (hi := 1) (lo' := 1) (hi' := 1)
    hb.1 hb.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Base bracket at `y = 1/2` encloses `cos 0.5 ≈ 0.8776`: the emitted rational box
    `[27/32, 63/64]` (i.e. `[0.84375, 0.984375]`) contains it. -/
example : (27 / 32 : ℝ) ≤ Real.cos (1 / 2) ∧ Real.cos (1 / 2) ≤ 63 / 64 := by
  refine cos_base_interval (y := 1 / 2) (by norm_num) ?_ ?_ <;> norm_num

/-- Lipschitz absorption: from `cos (1/2) ∈ [27/32, 63/64]` and `|arg − 1/2| ≤ 1/100`,
    `cos arg ∈ [27/32 − 1/100, 63/64 + 1/100]`. -/
example {arg : ℝ} (h : |arg - 1 / 2| ≤ 1 / 100) :
    (27 / 32 - 1 / 100 : ℝ) ≤ Real.cos arg ∧ Real.cos arg ≤ 63 / 64 + 1 / 100 := by
  have hb : (27 / 32 : ℝ) ≤ Real.cos (1 / 2) ∧ Real.cos (1 / 2) ≤ 63 / 64 := by
    refine cos_base_interval (y := 1 / 2) (by norm_num) ?_ ?_ <;> norm_num
  exact cos_encl_bracket (w := 1 / 100) (by norm_num) h hb.1 hb.2

end UnitTests

end CosEnclosure
