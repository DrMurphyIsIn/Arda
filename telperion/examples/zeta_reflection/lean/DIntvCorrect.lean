/-  DIntvCorrect.lean -- the DIntv correctness surface (A1).

    Builds on `DIntvDef`'s proven `add_sound`/`mul_sound`.  Completes the op surface with
    Real mem-soundness proofs for every operation the evaluators need:

      * `neg`, `sub`               -- exact, same/aligned exponent
      * `abs`                      -- |·| envelope (sign split)
      * `scale2`                   -- exact power-of-two rescale (no rounding)
      * `ofInt`                    -- exact integer point
      * `roundTo`                  -- directed OUTWARD truncation (the width-control primitive):
                                      memR x I → memR x (I.roundTo p).  THE key lemma.
      * `union` / `hull`           -- interval hull: memR x I → memR x (hull I J) (and sym)
      * `nonneg` / `nonpos` / `isPos` / `isNeg` / `sign?`  -- sign-definite predicates with
                                      their Real meanings
      * `ltOf` / `sepR`            -- interval comparison: I.hi·2^eI < J.lo·2^eJ
                                      ⇒ ∀ x∈I, y∈J, x < y.

    Design: `DIntvDef.DIntv` stores `lo hi : Int` at a single exponent `e : Int`, mem
    `(lo:ℝ)·2^e ≤ x ≤ (hi:ℝ)·2^e`.  `roundTo` DROPS `d` low mantissa bits, flooring `lo`
    and ceiling `hi`, and raises the exponent by `d` -- so the denoted real interval only
    GROWS.  All arithmetic is pure `Int` (no `Rat`, no division, no WF recursion).

    conjecture1_proved = False.  Finite interval arithmetic, not a proof of RH.
-/
import DIntvDef

namespace DIntvProd
namespace DIntv

/-! ### Exact / structural ops (no rounding) -/

/-- Exact integer point `[n, n]` at exponent 0. -/
def ofInt (n : Int) : DIntv := ⟨n, n, 0⟩

/-- Exact multiply-by-`2^k`: keep mantissas, shift the exponent.  No rounding, no widening. -/
def scale2 (I : DIntv) (k : Int) : DIntv := ⟨I.lo, I.hi, I.e + k⟩

/-- Interval subtraction at a COMMON exponent: `x - y ∈ I - J`.  (Aligning widening is
    `roundTo`/`alignPair`'s job; here we assume shared exponent as `add` does.) -/
def sub (I J : DIntv) (h : I.e = J.e) : DIntv := add I (neg J) (by simp [neg, h])

/-- Absolute-value envelope.  If the interval is sign-definite this is exact; if it straddles
    0 the lower end becomes 0 and the upper end is `max |lo| |hi|`.  Same exponent. -/
def abs (I : DIntv) : DIntv :=
  if 0 ≤ I.lo then I                          -- wholly ≥ 0: |·| = identity
  else if I.hi ≤ 0 then neg I                 -- wholly ≤ 0: |·| = negation
  else ⟨0, max (-I.lo) I.hi, I.e⟩             -- straddles 0

/-- Interval hull (union bound): the smallest common-exponent box containing both.
    Requires the shared exponent (evaluators align first). -/
def hull (I J : DIntv) (_h : I.e = J.e) : DIntv := ⟨min I.lo J.lo, max I.hi J.hi, I.e⟩

/-! ### Directed OUTWARD truncation -- the width-control primitive -/

/-- Floor of `m / 2^d` for `m : Int`, `d : Nat` (arithmetic right shift = floor division). -/
def floorShift (m : Int) (d : Nat) : Int := m >>> d

/-- Ceil of `m / 2^d`: `-(floor (-m / 2^d))`.  Pure Int, structural. -/
def ceilShift (m : Int) (d : Nat) : Int := -((-m) >>> d)

/-- Round OUTWARD, dropping `d` low mantissa bits: floor the lo endpoint, ceil the hi
    endpoint, and raise the exponent by `d`.  The denoted real interval only GROWS, so
    membership is preserved.  This is the primitive that keeps kernel mantissas bounded
    on long folds. -/
def roundTo (I : DIntv) (d : Nat) : DIntv :=
  ⟨floorShift I.lo d, ceilShift I.hi d, I.e + (d : Int)⟩

/-! ### Sign-definite predicates -/

/-- Wholly `≥ 0`?  (`lo ≥ 0`.) -/
def nonneg (I : DIntv) : Bool := 0 ≤ I.lo

/-- Wholly `≤ 0`?  (`hi ≤ 0`.) -/
def nonpos (I : DIntv) : Bool := I.hi ≤ 0

/-- Strictly positive?  (`lo > 0`.) -/
def isPos (I : DIntv) : Bool := 0 < I.lo

/-- Strictly negative?  (`hi < 0`.) -/
def isNeg (I : DIntv) : Bool := I.hi < 0

/-- Definite sign if 0 is excluded: `some true` = strictly +, `some false` = strictly −,
    `none` = straddles/touches 0. -/
def sign? (I : DIntv) : Option Bool :=
  if isPos I then some true
  else if isNeg I then some false
  else none

/-! ### Comparison -/

/-- Kernel-checkable strict separation: `hi_I·2^{eI} < lo_J·2^{eJ}` decides `I` entirely
    below `J`.  Compared as `Int` after aligning to the min exponent (so still Int-only).
    We encode the real inequality directly as a `Prop` here; the Bool decider lives with
    the checker in CheckBand.  This lemma is the soundness bridge. -/
def belowR (I J : DIntv) : Prop :=
  (I.hi : ℝ) * (2 : ℝ) ^ I.e < (J.lo : ℝ) * (2 : ℝ) ^ J.e

/-! ### Soundness proofs -/

/-- `ofInt` is exact: `(n:ℝ) ∈ ofInt n`. -/
theorem ofInt_sound (n : Int) : memR (n : ℝ) (ofInt n) := by
  unfold ofInt memR
  simp

/-- `scale2` soundness: `x ∈ I ⇒ x * 2^k ∈ scale2 I k`. -/
theorem scale2_sound {x : ℝ} {I : DIntv} (k : Int) (hx : memR x I) :
    memR (x * (2 : ℝ) ^ k) (scale2 I k) := by
  obtain ⟨hlo, hhi⟩ := hx
  unfold scale2 memR
  have hk : (0 : ℝ) < (2 : ℝ) ^ k := two_zpow_pos k
  have hsplit : (2 : ℝ) ^ (I.e + k) = (2 : ℝ) ^ I.e * (2 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  constructor
  · rw [hsplit]
    calc (I.lo : ℝ) * ((2:ℝ)^I.e * (2:ℝ)^k)
        = ((I.lo : ℝ) * (2:ℝ)^I.e) * (2:ℝ)^k := by ring
      _ ≤ x * (2:ℝ)^k := by exact mul_le_mul_of_nonneg_right hlo (le_of_lt hk)
  · rw [hsplit]
    calc x * (2:ℝ)^k
        ≤ ((I.hi : ℝ) * (2:ℝ)^I.e) * (2:ℝ)^k := by exact mul_le_mul_of_nonneg_right hhi (le_of_lt hk)
      _ = (I.hi : ℝ) * ((2:ℝ)^I.e * (2:ℝ)^k) := by ring

/-- `neg` soundness: `x ∈ I ⇒ -x ∈ neg I`. -/
theorem neg_sound {x : ℝ} {I : DIntv} (hx : memR x I) : memR (-x) (neg I) := by
  obtain ⟨hlo, hhi⟩ := hx
  unfold neg memR
  simp only [Int.cast_neg]
  constructor
  · -- (-hi)·2^e ≤ -x  ⇐  x ≤ hi·2^e
    have : -((I.hi : ℝ) * (2:ℝ)^I.e) ≤ -x := neg_le_neg hhi
    linarith [this]
  · -- -x ≤ (-lo)·2^e  ⇐  lo·2^e ≤ x
    have : -x ≤ -((I.lo : ℝ) * (2:ℝ)^I.e) := neg_le_neg hlo
    linarith [this]

/-- `sub` soundness: `x ∈ I`, `y ∈ J`, same exponent ⇒ `x - y ∈ sub I J`. -/
theorem sub_sound {x y : ℝ} {I J : DIntv} (h : I.e = J.e)
    (hx : memR x I) (hy : memR y J) : memR (x - y) (sub I J h) := by
  unfold sub
  have hny : memR (-y) (neg J) := neg_sound hy
  have := add_sound (I := I) (J := neg J) (by simp [neg, h]) hx hny
  simpa [sub_eq_add_neg] using this

/-- `abs` soundness: `x ∈ I ⇒ |x| ∈ abs I`. -/
theorem abs_sound {x : ℝ} {I : DIntv} (hx : memR x I) : memR (|x|) (abs I) := by
  obtain ⟨hlo, hhi⟩ := hx
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  unfold abs
  by_cases h1 : 0 ≤ I.lo
  · -- wholly ≥ 0: x ≥ lo·2^e ≥ 0, so |x| = x
    simp only [h1, if_true]
    have hlo0 : (0 : ℝ) ≤ (I.lo : ℝ) * (2:ℝ)^I.e := by
      have : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast h1
      exact mul_nonneg this (le_of_lt hepos)
    have hx0 : 0 ≤ x := le_trans hlo0 hlo
    rw [abs_of_nonneg hx0]
    exact ⟨hlo, hhi⟩
  · simp only [h1, if_false]
    by_cases h2 : I.hi ≤ 0
    · -- wholly ≤ 0: x ≤ hi·2^e ≤ 0, so |x| = -x, box = neg I
      simp only [h2, if_true]
      have hhi0 : (I.hi : ℝ) * (2:ℝ)^I.e ≤ 0 := by
        have : (I.hi : ℝ) ≤ 0 := by exact_mod_cast h2
        exact mul_nonpos_of_nonpos_of_nonneg this (le_of_lt hepos)
      have hx0 : x ≤ 0 := le_trans hhi hhi0
      rw [abs_of_nonpos hx0]
      exact neg_sound ⟨hlo, hhi⟩
    · -- straddles 0: box = [0, max(-lo, hi)]
      simp only [h2, if_false]
      unfold memR
      simp only [Int.cast_max, Int.cast_neg, Int.cast_zero]
      refine ⟨?_, ?_⟩
      · -- 0·2^e ≤ |x|
        simp only [zero_mul]
        exact abs_nonneg x
      · -- |x| ≤ max(-lo, hi)·2^e
        rw [abs_le]
        constructor
        · -- -(max(-lo,hi)·2^e) ≤ x, i.e. x ≥ lo·2^e ≥ -(max..)·2^e
          have hle : -(max (-(I.lo:ℝ)) (I.hi:ℝ)) ≤ (I.lo : ℝ) := by
            have : -(I.lo : ℝ) ≤ max (-(I.lo:ℝ)) (I.hi:ℝ) := le_max_left _ _
            linarith [this]
          calc -(max (-(I.lo:ℝ)) (I.hi:ℝ) * (2:ℝ)^I.e)
              = (-(max (-(I.lo:ℝ)) (I.hi:ℝ))) * (2:ℝ)^I.e := by ring
            _ ≤ (I.lo : ℝ) * (2:ℝ)^I.e := mul_le_mul_of_nonneg_right hle (le_of_lt hepos)
            _ ≤ x := hlo
        · -- x ≤ max(-lo,hi)·2^e, i.e. x ≤ hi·2^e ≤ max..·2^e
          have hge : (I.hi : ℝ) ≤ max (-(I.lo:ℝ)) (I.hi:ℝ) := le_max_right _ _
          calc x ≤ (I.hi : ℝ) * (2:ℝ)^I.e := hhi
            _ ≤ max (-(I.lo:ℝ)) (I.hi:ℝ) * (2:ℝ)^I.e := mul_le_mul_of_nonneg_right hge (le_of_lt hepos)

/-- `hull` soundness (left): `x ∈ I ⇒ x ∈ hull I J`. -/
theorem hull_sound_left {x : ℝ} {I J : DIntv} (h : I.e = J.e) (hx : memR x I) :
    memR x (hull I J h) := by
  obtain ⟨hlo, hhi⟩ := hx
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  unfold hull memR
  simp only [Int.cast_min, Int.cast_max]
  constructor
  · -- min(lo_I,lo_J)·2^e ≤ x  ⇐  lo_I·2^e ≤ x
    have hmin : (min (I.lo:ℝ) (J.lo:ℝ)) ≤ (I.lo:ℝ) := min_le_left _ _
    exact le_trans (mul_le_mul_of_nonneg_right hmin (le_of_lt hepos)) hlo
  · -- x ≤ max(hi_I,hi_J)·2^e  ⇐  x ≤ hi_I·2^e
    have hmax : (I.hi:ℝ) ≤ (max (I.hi:ℝ) (J.hi:ℝ)) := le_max_left _ _
    exact le_trans hhi (mul_le_mul_of_nonneg_right hmax (le_of_lt hepos))

/-- `hull` soundness (right): `y ∈ J ⇒ y ∈ hull I J`. -/
theorem hull_sound_right {y : ℝ} {I J : DIntv} (h : I.e = J.e) (hy : memR y J) :
    memR y (hull I J h) := by
  obtain ⟨hlo, hhi⟩ := hy
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  unfold hull memR
  simp only [Int.cast_min, Int.cast_max]
  -- note: hull carries I.e, and h : I.e = J.e, so y's J.e bounds rewrite to I.e
  rw [← h] at hlo hhi
  constructor
  · have hmin : (min (I.lo:ℝ) (J.lo:ℝ)) ≤ (J.lo:ℝ) := min_le_right _ _
    exact le_trans (mul_le_mul_of_nonneg_right hmin (le_of_lt hepos)) hlo
  · have hmax : (J.hi:ℝ) ≤ (max (I.hi:ℝ) (J.hi:ℝ)) := le_max_right _ _
    exact le_trans hhi (mul_le_mul_of_nonneg_right hmax (le_of_lt hepos))

/-! #### roundTo soundness -- the width-control primitive

`floorShift m d = m >>> d = ⌊m / 2^d⌋` and `ceilShift m d = ⌈m / 2^d⌉` as `Int`.  We first
establish the two integer facts `floorShift m d · 2^d ≤ m ≤ ceilShift m d · 2^d`, cast them
to ℝ, and combine with `2^e ≥ 0` and `2^(e+d) = 2^e · 2^d`. -/

/-- `Int` right shift is floor division by `2^d`: `(m >>> d) * 2^d ≤ m`. -/
theorem floorShift_le (m : Int) (d : Nat) : floorShift m d * (2 ^ d : Int) ≤ m := by
  unfold floorShift
  rw [Int.shiftRight_eq_div_pow]
  have hcast : ((2 ^ d : Nat) : Int) = (2 ^ d : Int) := by push_cast; ring
  rw [hcast]
  have hpos : (0 : Int) < (2 ^ d : Int) := by positivity
  exact Int.ediv_mul_le m (ne_of_gt hpos)

/-- `ceilShift m d * 2^d ≥ m`. -/
theorem le_ceilShift (m : Int) (d : Nat) : m ≤ ceilShift m d * (2 ^ d : Int) := by
  unfold ceilShift
  rw [Int.shiftRight_eq_div_pow]
  have hcast : ((2 ^ d : Nat) : Int) = (2 ^ d : Int) := by push_cast; ring
  rw [hcast]
  have hpos : (0 : Int) < (2 ^ d : Int) := by positivity
  have hfl : (-m) / (2 ^ d : Int) * (2 ^ d : Int) ≤ (-m) := Int.ediv_mul_le (-m) (ne_of_gt hpos)
  calc m ≤ -((-m) / (2 ^ d : Int) * (2 ^ d : Int)) := by linarith [hfl]
    _ = -((-m) / (2 ^ d : Int)) * (2 ^ d : Int) := by ring

/-- `roundTo` soundness: dropping `d` low bits with directed outward rounding preserves
    membership.  `x ∈ I ⇒ x ∈ roundTo I d`. -/
theorem roundTo_sound {x : ℝ} {I : DIntv} (d : Nat) (hx : memR x I) :
    memR x (roundTo I d) := by
  obtain ⟨hlo, hhi⟩ := hx
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  -- 2^(e+d) = 2^e · 2^d
  have hsplit : (2 : ℝ) ^ (I.e + (d:Int)) = (2 : ℝ) ^ I.e * (2 : ℝ) ^ (d:Int) := by
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  -- (2:ℝ)^(d:Int) = (2^d : Int) cast to ℝ
  have hdcast : (2 : ℝ) ^ (d:Int) = ((2 ^ d : Int) : ℝ) := by
    rw [zpow_natCast]; push_cast; ring
  unfold roundTo memR
  simp only []
  refine ⟨?_, ?_⟩
  · -- floorShift lo d · 2^(e+d) ≤ lo·2^e ≤ x
    -- from floorShift lo d · 2^d ≤ lo (Int), cast, multiply by 2^e ≥ 0
    have hInt : (floorShift I.lo d : ℝ) * ((2 ^ d : Int) : ℝ) ≤ (I.lo : ℝ) := by
      have hc : ((floorShift I.lo d * (2 ^ d : Int) : Int) : ℝ) ≤ ((I.lo : Int) : ℝ) := by
        exact_mod_cast floorShift_le I.lo d
      rw [Int.cast_mul] at hc
      exact hc
    calc (floorShift I.lo d : ℝ) * (2:ℝ)^(I.e + (d:Int))
        = ((floorShift I.lo d : ℝ) * (2:ℝ)^(d:Int)) * (2:ℝ)^I.e := by rw [hsplit]; ring
      _ = ((floorShift I.lo d : ℝ) * ((2 ^ d : Int) : ℝ)) * (2:ℝ)^I.e := by rw [hdcast]
      _ ≤ (I.lo : ℝ) * (2:ℝ)^I.e := mul_le_mul_of_nonneg_right hInt (le_of_lt hepos)
      _ ≤ x := hlo
  · -- x ≤ hi·2^e ≤ ceilShift hi d · 2^(e+d)
    have hInt : (I.hi : ℝ) ≤ (ceilShift I.hi d : ℝ) * ((2 ^ d : Int) : ℝ) := by
      have hc : ((I.hi : Int) : ℝ) ≤ ((ceilShift I.hi d * (2 ^ d : Int) : Int) : ℝ) := by
        exact_mod_cast le_ceilShift I.hi d
      rw [Int.cast_mul] at hc
      exact hc
    calc x ≤ (I.hi : ℝ) * (2:ℝ)^I.e := hhi
      _ ≤ ((ceilShift I.hi d : ℝ) * ((2 ^ d : Int) : ℝ)) * (2:ℝ)^I.e :=
          mul_le_mul_of_nonneg_right hInt (le_of_lt hepos)
      _ = ((ceilShift I.hi d : ℝ) * (2:ℝ)^(d:Int)) * (2:ℝ)^I.e := by rw [hdcast]
      _ = (ceilShift I.hi d : ℝ) * (2:ℝ)^(I.e + (d:Int)) := by rw [hsplit]; ring

/-! #### Predicate meanings -/

/-- `nonneg` is sound: if the box is flagged `nonneg` then every member is `≥ 0`. -/
theorem nonneg_sound {x : ℝ} {I : DIntv} (h : nonneg I = true) (hx : memR x I) : 0 ≤ x := by
  obtain ⟨hlo, _⟩ := hx
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  have hInt : (0 : Int) ≤ I.lo := by unfold nonneg at h; simpa using h
  have hlo0 : (0 : ℝ) ≤ (I.lo : ℝ) * (2:ℝ)^I.e := by
    have : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hInt
    exact mul_nonneg this (le_of_lt hepos)
  linarith [hlo, hlo0]

/-- `nonpos` is sound: if the box is flagged `nonpos` then every member is `≤ 0`. -/
theorem nonpos_sound {x : ℝ} {I : DIntv} (h : nonpos I = true) (hx : memR x I) : x ≤ 0 := by
  obtain ⟨_, hhi⟩ := hx
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  have hInt : I.hi ≤ (0 : Int) := by unfold nonpos at h; simpa using h
  have hhi0 : (I.hi : ℝ) * (2:ℝ)^I.e ≤ 0 := by
    have : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hInt
    exact mul_nonpos_of_nonpos_of_nonneg this (le_of_lt hepos)
  linarith [hhi, hhi0]

/-- `isPos` is sound: strictly positive box ⇒ every member `> 0`. -/
theorem isPos_sound {x : ℝ} {I : DIntv} (h : isPos I = true) (hx : memR x I) : 0 < x := by
  obtain ⟨hlo, _⟩ := hx
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  have hInt : (0 : Int) < I.lo := by unfold isPos at h; simpa using h
  have hlo0 : (0 : ℝ) < (I.lo : ℝ) * (2:ℝ)^I.e := by
    have : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hInt
    exact mul_pos this hepos
  linarith [hlo, hlo0]

/-- `isNeg` is sound: strictly negative box ⇒ every member `< 0`. -/
theorem isNeg_sound {x : ℝ} {I : DIntv} (h : isNeg I = true) (hx : memR x I) : x < 0 := by
  obtain ⟨_, hhi⟩ := hx
  have hepos : (0 : ℝ) < (2:ℝ)^I.e := two_zpow_pos I.e
  have hInt : I.hi < (0 : Int) := by unfold isNeg at h; simpa using h
  have hhi0 : (I.hi : ℝ) * (2:ℝ)^I.e < 0 := by
    have : (I.hi : ℝ) < 0 := by exact_mod_cast hInt
    exact mul_neg_of_neg_of_pos this hepos
  linarith [hhi, hhi0]

/-- `sign?` soundness (positive branch): `sign? I = some true ⇒ every member > 0`. -/
theorem sign?_pos {x : ℝ} {I : DIntv} (h : sign? I = some true) (hx : memR x I) : 0 < x := by
  apply isPos_sound _ hx
  unfold sign? at h
  by_cases hp : isPos I = true
  · exact hp
  · exfalso
    rw [if_neg hp] at h
    by_cases hn : isNeg I = true
    · rw [if_pos hn] at h; exact (by simp at h)
    · rw [if_neg hn] at h; exact (by simp at h)

/-- `sign?` soundness (negative branch): `sign? I = some false ⇒ every member < 0`. -/
theorem sign?_neg {x : ℝ} {I : DIntv} (h : sign? I = some false) (hx : memR x I) : x < 0 := by
  apply isNeg_sound _ hx
  unfold sign? at h
  by_cases hp : isPos I = true
  · rw [if_pos hp] at h; exact (by simp at h)
  · rw [if_neg hp] at h
    by_cases hn : isNeg I = true
    · exact hn
    · exfalso; rw [if_neg hn] at h; exact (by simp at h)

/-! #### Comparison soundness -/

/-- Interval separation ⇒ pointwise strict inequality: if `I` lies (as reals) strictly below
    `J`, then every member of `I` is `<` every member of `J`.  This is the box-ordering fact
    the sign chain (H1) and Backlund cells (H4) consume. -/
theorem belowR_sound {x y : ℝ} {I J : DIntv} (h : belowR I J)
    (hx : memR x I) (hy : memR y J) : x < y := by
  obtain ⟨_, hxhi⟩ := hx
  obtain ⟨hylo, _⟩ := hy
  -- x ≤ hi_I·2^eI < lo_J·2^eJ ≤ y
  unfold belowR at h
  linarith [hxhi, h, hylo]

end DIntv
end DIntvProd
