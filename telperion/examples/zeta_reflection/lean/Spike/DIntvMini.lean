/-  Spike/DIntvMini.lean -- A0 kernel-throughput benchmark core (MINIMAL).

    Minimal dyadic interval type for the A0 spike.  A `DIntv` denotes the real
    interval  [lo * 2^e, hi * 2^e].  All ops are COMPUTABLE, structural, pure
    `Int` arithmetic: no division, no `Rat`, no well-founded recursion, no proofs.
    This file is the kernel hot-path benchmark target -- it is exercised by
    `Spike/Toy.lean` under `rfl`/`decide` to measure interval-ops/sec in `whnf`.

    Soundness is NOT proved here (that is `DIntvDef.lean`).  conjecture1_proved = False.
-/
namespace Spike

/-- Dyadic interval `[lo * 2^e, hi * 2^e]` (mantissa/exponent Int pair, shared exponent). -/
structure DIntv where
  lo : Int
  hi : Int
  e  : Int
deriving Repr, DecidableEq

namespace DIntv

/-- Multiply a mantissa by `2 ^ n` for `n : Int`.  For `n ≥ 0` this is an exact left
    shift; for `n < 0` it is a directed truncation toward the correct interval end.
    `roundDir = false` truncates toward −∞ (floor), `roundDir = true` toward +∞ (ceil).
    Pure `Int`, structural (no WF recursion): uses `Int` shifts via `HShiftLeft`/`HShiftRight`. -/
@[inline] def scaleMantissa (m : Int) (n : Int) (roundDir : Bool) : Int :=
  if 0 ≤ n then
    m <<< n.toNat
  else
    let k := (-n).toNat
    -- arithmetic right shift = floor division by 2^k for `Int`
    let fl := m >>> k
    if roundDir then
      -- ceil: floor + (1 if any low bit was dropped)
      if (fl <<< k) == m then fl else fl + 1
    else
      fl

/-- Align two intervals to the smaller (more negative) exponent, widening as needed:
    the lo mantissas floor, the hi mantissas ceil, so the real interval only grows. -/
@[inline] def alignPair (I J : DIntv) : Int × Int × Int × Int × Int :=
  let e := min I.e J.e
  let iLo := scaleMantissa I.lo (I.e - e) false
  let iHi := scaleMantissa I.hi (I.e - e) true
  let jLo := scaleMantissa J.lo (J.e - e) false
  let jHi := scaleMantissa J.hi (J.e - e) true
  (e, iLo, iHi, jLo, jHi)

/-- Interval negation: `-[lo,hi] = [-hi,-lo]` (exact, no rounding). -/
@[inline] def neg (I : DIntv) : DIntv := ⟨-I.hi, -I.lo, I.e⟩

/-- Interval addition (exponent-aligned; mantissa add is exact once aligned). -/
@[inline] def add (I J : DIntv) : DIntv :=
  let (e, iLo, iHi, jLo, jHi) := alignPair I J
  ⟨iLo + jLo, iHi + jHi, e⟩

/-- Interval subtraction via `add ∘ neg`. -/
@[inline] def sub (I J : DIntv) : DIntv := add I (neg J)

/-- Interval multiplication: 4 corner products, min/max envelope.
    Exponents add; mantissa products are exact `Int` mults. -/
@[inline] def mul (I J : DIntv) : DIntv :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  let lo := min (min a b) (min c d)
  let hi := max (max a b) (max c d)
  ⟨lo, hi, I.e + J.e⟩

/-- Round to `p` mantissa bits: rescale so both endpoints fit in `p` bits, widening
    outward (lo floors, hi ceils).  Keeps kernel mantissas bounded on long folds.
    `Int.log2`-free: shifts down by a caller-chosen drop `d` (structural). -/
@[inline] def roundTo (I : DIntv) (dropBits : Nat) : DIntv :=
  if dropBits == 0 then I
  else
    let lo := scaleMantissa I.lo (-(dropBits : Int)) false
    let hi := scaleMantissa I.hi (-(dropBits : Int)) true
    ⟨lo, hi, I.e + dropBits⟩

/-- Constant dyadic point `[m,m] * 2^e`. -/
@[inline] def ofDyadic (m : Int) (e : Int) : DIntv := ⟨m, m, e⟩

/-- Does the interval lie strictly above 0 (lo > 0)? -/
@[inline] def isPos (I : DIntv) : Bool := 0 < I.lo

/-- Does the interval lie strictly below 0 (hi < 0)? -/
@[inline] def isNeg (I : DIntv) : Bool := I.hi < 0

/-- Definite sign of the interval if it excludes 0: `some true` = positive,
    `some false` = negative, `none` = straddles/touches 0. -/
@[inline] def sign? (I : DIntv) : Option Bool :=
  if isPos I then some true
  else if isNeg I then some false
  else none

end DIntv
end Spike
