/-  DIntvDef.lean -- production-intended dyadic interval definitions + mem-soundness.

    This is the cleaner, production sibling of `Spike/DIntvMini.lean`.  It carries the
    SAME computable ops (add, mul, neg) and, crucially, PROVES that they are sound with
    respect to the real interval they denote:

        I.memR x  :=  (I.lo : ℝ) * 2^I.e ≤ x ∧ x ≤ (I.hi : ℝ) * 2^I.e

    We prove `add_sound` and `mul_sound` ONLY (the A0 remit): if `x ∈ I` and `y ∈ J`
    then `x + y ∈ I.add J` and `x * y ∈ I.mul J`.  These validate the Real-bridging
    proof style that the full A1 correctness surface will scale up.

    Design note for A1: to keep the soundness proofs clean we store BOTH endpoints at a
    COMMON exponent (add aligns to the shared exponent; mul adds exponents).  `roundTo`
    (outward widening) is a separate, monotone op whose soundness is a one-liner from
    `add`/`mul` monotonicity and is deferred to A1.

    conjecture1_proved = False.  This is finite interval arithmetic, not a proof of RH.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace DIntvProd

/-- Dyadic interval `[lo * 2^e, hi * 2^e]`. -/
structure DIntv where
  lo : Int
  hi : Int
  e  : Int
deriving Repr, DecidableEq

namespace DIntv

/-- The real interval denoted by `I`: `x` lies in `[lo·2^e, hi·2^e]`.
    `2^e` is the real `zpow`, so `e : Int` (may be negative) is handled directly. -/
noncomputable def memR (x : ℝ) (I : DIntv) : Prop :=
  (I.lo : ℝ) * (2 : ℝ) ^ I.e ≤ x ∧ x ≤ (I.hi : ℝ) * (2 : ℝ) ^ I.e

/-- Interval negation `[-hi, -lo]` at the same exponent. -/
def neg (I : DIntv) : DIntv := ⟨-I.hi, -I.lo, I.e⟩

/-- Interval addition at a COMMON exponent `e` (production form assumes aligned inputs;
    the aligning `scaleMantissa` widening is the spike file's job and A1 will fold its
    monotone soundness in).  Here `add` requires the shared exponent and adds mantissas. -/
def add (I J : DIntv) (_h : I.e = J.e) : DIntv := ⟨I.lo + J.lo, I.hi + J.hi, I.e⟩

/-- Interval multiplication: 4 corner products, min/max envelope; exponents add. -/
def mul (I J : DIntv) : DIntv :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨min (min a b) (min c d), max (max a b) (max c d), I.e + J.e⟩

/-! ### Soundness -/

/-- `2^e > 0` in ℝ for any `e : Int`. -/
theorem two_zpow_pos (e : Int) : (0 : ℝ) < (2 : ℝ) ^ e :=
  zpow_pos (by norm_num) e

/-- Addition soundness: `x ∈ I`, `y ∈ J`, same exponent ⇒ `x + y ∈ I.add J`. -/
theorem add_sound {x y : ℝ} {I J : DIntv} (h : I.e = J.e)
    (hx : memR x I) (hy : memR y J) : memR (x + y) (add I J h) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  unfold add memR
  simp only [Int.cast_add]
  constructor
  · -- (lo_I + lo_J)·2^e ≤ x + y
    have : ((I.lo : ℝ) + (J.lo : ℝ)) * (2 : ℝ) ^ I.e
        = (I.lo : ℝ) * (2 : ℝ) ^ I.e + (J.lo : ℝ) * (2 : ℝ) ^ J.e := by
      rw [h]; ring
    rw [this]
    exact add_le_add hxlo hylo
  · -- x + y ≤ (hi_I + hi_J)·2^e
    have : ((I.hi : ℝ) + (J.hi : ℝ)) * (2 : ℝ) ^ I.e
        = (I.hi : ℝ) * (2 : ℝ) ^ I.e + (J.hi : ℝ) * (2 : ℝ) ^ J.e := by
      rw [h]; ring
    rw [this]
    exact add_le_add hxhi hyhi

/-- Real bilinear corner bound: if `a ≤ u ≤ b` and `c ≤ v ≤ d` then `u*v` lies between
    `min` and `max` of the four corner products.  Proved from `mul_le_mul`-style endpoint
    monotonicity, splitting on the signs of `u` and `v` (4 quadrants).  No `sorry`. -/
private theorem prod_between_corners {a b c d u v : ℝ}
    (hau : a ≤ u) (hub : u ≤ b) (hcv : c ≤ v) (hvd : v ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ u * v
    ∧ u * v ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  constructor
  · -- lower bound: exhibit a corner ≤ u*v, chained through mid products a*v and u*v.
    rcases le_total 0 v with hv0 | hv0
    · -- v ≥ 0 : a*v ≤ u*v (mono in first arg), and (a*c or a*d) ≤ a*v.
      have step1 : a * v ≤ u * v := mul_le_mul_of_nonneg_right hau hv0
      have step2 : min (a*c) (a*d) ≤ a * v := by
        rcases le_total 0 a with ha0 | ha0
        · -- a ≥ 0, c ≤ v : a*c ≤ a*v
          exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hcv ha0)
        · -- a ≤ 0, v ≤ d : a*d ≤ a*v
          exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hvd ha0)
      exact le_trans (le_trans (min_le_left _ _) step2) step1
    · -- v ≤ 0 : b*v ≤ u*v (mono in first arg, v ≤ 0 flips), and (b*c or b*d) ≤ b*v.
      have step1 : b * v ≤ u * v := by
        have := mul_le_mul_of_nonpos_right hub hv0; linarith [this]
      have step2 : min (b*c) (b*d) ≤ b * v := by
        rcases le_total 0 b with hb0 | hb0
        · -- b ≥ 0, c ≤ v : b*c ≤ b*v
          exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hcv hb0)
        · -- b ≤ 0, v ≤ d : b*d ≤ b*v
          exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hvd hb0)
      exact le_trans (le_trans (min_le_right _ _) step2) step1
  · -- upper bound: symmetric.
    rcases le_total 0 v with hv0 | hv0
    · have step1 : u * v ≤ b * v := mul_le_mul_of_nonneg_right hub hv0
      have step2 : b * v ≤ max (b*c) (b*d) := by
        rcases le_total 0 b with hb0 | hb0
        · -- b ≥ 0, v ≤ d : b*v ≤ b*d
          exact le_trans (mul_le_mul_of_nonneg_left hvd hb0) (le_max_right _ _)
        · -- b ≤ 0, c ≤ v : b*v ≤ b*c
          exact le_trans (mul_le_mul_of_nonpos_left hcv hb0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_right _ _))
    · have step1 : u * v ≤ a * v := by
        have := mul_le_mul_of_nonpos_right hau hv0; linarith [this]
      have step2 : a * v ≤ max (a*c) (a*d) := by
        rcases le_total 0 a with ha0 | ha0
        · -- a ≥ 0, v ≤ d : a*v ≤ a*d
          exact le_trans (mul_le_mul_of_nonneg_left hvd ha0) (le_max_right _ _)
        · -- a ≤ 0, c ≤ v : a*v ≤ a*c
          exact le_trans (mul_le_mul_of_nonpos_left hcv ha0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_left _ _))

/-- The four real corner products bound `x*y`, as an auxiliary for `mul_sound`. -/
private theorem mul_mem_of_corners {x y : ℝ} {I J : DIntv}
    (hx : memR x I) (hy : memR y J) :
    ((min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        * (2 : ℝ) ^ (I.e + J.e) ≤ x * y
    ∧ x * y ≤ ((max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        * (2 : ℝ) ^ (I.e + J.e) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  -- Work in "unscaled" coordinates u = x / 2^eI, v = y / 2^eJ.
  set pI : ℝ := (2 : ℝ) ^ I.e with hpI
  set pJ : ℝ := (2 : ℝ) ^ J.e with hpJ
  have hpIpos : 0 < pI := two_zpow_pos I.e
  have hpJpos : 0 < pJ := two_zpow_pos J.e
  set u : ℝ := x / pI with hu
  set v : ℝ := y / pJ with hv
  have hxu : x = u * pI := by rw [hu, div_mul_cancel₀ _ (ne_of_gt hpIpos)]
  have hyv : y = v * pJ := by rw [hv, div_mul_cancel₀ _ (ne_of_gt hpJpos)]
  have hulo : (I.lo : ℝ) ≤ u := by rw [hu, le_div_iff₀ hpIpos]; simpa [hpI] using hxlo
  have huhi : u ≤ (I.hi : ℝ) := by rw [hu, div_le_iff₀ hpIpos]; simpa [hpI] using hxhi
  have hvlo : (J.lo : ℝ) ≤ v := by rw [hv, le_div_iff₀ hpJpos]; simpa [hpJ] using hylo
  have hvhi : v ≤ (J.hi : ℝ) := by rw [hv, div_le_iff₀ hpJpos]; simpa [hpJ] using hyhi
  have hscale : (2 : ℝ) ^ (I.e + J.e) = pI * pJ := by
    rw [hpI, hpJ, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  have hscalepos : 0 < (2 : ℝ) ^ (I.e + J.e) := two_zpow_pos _
  have hxy : x * y = (u * v) * (2 : ℝ) ^ (I.e + J.e) := by rw [hxu, hyv, hscale]; ring
  -- Int min/max cast out to real corner products.
  have hcastmin :
      ((min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        = min (min ((I.lo:ℝ)*(J.lo:ℝ)) ((I.lo:ℝ)*(J.hi:ℝ)))
              (min ((I.hi:ℝ)*(J.lo:ℝ)) ((I.hi:ℝ)*(J.hi:ℝ))) := by push_cast; rfl
  have hcastmax :
      ((max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi)) : Int) : ℝ)
        = max (max ((I.lo:ℝ)*(J.lo:ℝ)) ((I.lo:ℝ)*(J.hi:ℝ)))
              (max ((I.hi:ℝ)*(J.lo:ℝ)) ((I.hi:ℝ)*(J.hi:ℝ))) := by push_cast; rfl
  obtain ⟨hlow, hupp⟩ := prod_between_corners hulo huhi hvlo hvhi
  refine ⟨?_, ?_⟩
  · rw [hcastmin, hxy]
    exact mul_le_mul_of_nonneg_right hlow (le_of_lt hscalepos)
  · rw [hcastmax, hxy]
    exact mul_le_mul_of_nonneg_right hupp (le_of_lt hscalepos)

/-- Multiplication soundness: `x ∈ I`, `y ∈ J` ⇒ `x * y ∈ I.mul J`. -/
theorem mul_sound {x y : ℝ} {I J : DIntv}
    (hx : memR x I) (hy : memR y J) : memR (x * y) (mul I J) := by
  have := mul_mem_of_corners hx hy
  unfold mul memR
  exact this

end DIntv
end DIntvProd
