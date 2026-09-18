/-  TrigReduceD.lean -- computable DIntv paired-doubling DRIVER for the trig instrument (A).

    `TrigReduce.lean` proves the REAL-valued base + double-angle brackets.  This file lifts them to a
    COMPUTABLE `DIntv`-valued driver so the operating-point certificates are a single kernel `decide`
    over `Int` arithmetic (the `checkBandFull` / `hornerD` pattern) rather than an M-step straight-line
    `norm_num` unroll.

    THE DRIVER.  A cos/sin box pair `(cb, sb) : DIntv × DIntv` at a fixed working exponent.  One step:

        cos(2y) = 2·cos²y − 1    :  cb' = (2 · cb·cb − 1)   [DIntv.mul, scale2, sub, roundTo]
        sin(2y) = 2·sin y·cos y  :  sb' = (2 · sb·cb)       [DIntv.mul, scale2, roundTo]

    Each op is a proven-sound `DIntv` primitive (`mul_sound`, `scale2_sound`, `sub_sound`,
    `roundTo_sound` from `DIntvCorrect`), so one step's soundness is a straight composition; `M` steps
    fold by induction (`iterDouble_sound`).  `roundTo` after each product keeps mantissas bounded.

    WHAT IS PROVEN SOUND HERE (no sorry; guarded by AxiomGuardTrigReduce):
      * `cosDblD` / `sinDblD` -- the two computable step maps, and their soundness
        (`cosDblD_sound` / `sinDblD_sound`): membership of `cos(2y)` / `sin(2y)` in the output box
        follows from membership of `cos y` / `sin y` in the input boxes.
      * `stepD` / `stepD_sound` -- the paired step.
      * `iterDouble` / `iterDouble_sound` -- the M-fold climb with inductive soundness.

    conjecture1_proved = False.  Certified interval arithmetic, not a proof of RH.
-/
import TrigReduce

open DIntvProd DIntvProd.DIntv

namespace TrigReduceD

/-! ## 1.  The two computable step maps. -/

/-- `2·I − 1` on `DIntv`: double via `scale2 _ 1`, subtract the exact point `1` after aligning
    exponents by outward rounding.  Here we keep it structural by NOT rounding the `−1`: we align
    `ofInt 1` up to the doubled box's exponent using `scale2` on the constant is impossible (constant
    has exponent 0), so we instead subtract using a common-exponent `add`/`neg` after `roundTo`-coarsening
    the doubled box to exponent `≥ 0`.  To stay simple and always-valid we route through the explicit
    endpoints:  `2·I − 1 = [2·lo·2^e − 1, 2·hi·2^e − 1]`.  We realize this directly on mantissas at a
    NON-POSITIVE working exponent `e ≤ 0`, where `1 = 2^{-e}·2^e` has integer mantissa `2^{-e}`. -/
def twoSqSubOne (I : DIntv) : DIntv :=
  -- I is a cos box; compute I*I, double (scale2 by 1 => exponent+1... we instead add exponent via mul),
  -- then subtract 1.  We fix everything at exponent (I.e * 2) coming out of mul, then roundTo to keep it.
  let sq := I.mul I                    -- exponent 2·I.e, mantissas up to |lo·hi|
  let dbl := scale2 sq 1               -- 2·I², exponent 2·I.e + 1
  -- subtract 1: represent 1 at dbl.e as ⟨2^{-dbl.e}, 2^{-dbl.e}, dbl.e⟩ when dbl.e ≤ 0
  -- (the working exponent is always ≤ 0 in our climb).  Guard with a runtime check; if dbl.e > 0
  -- we coarsen `one` is impossible, so we assume dbl.e ≤ 0 (true for our P-bit grid).
  let k := (-dbl.e).toNat
  let one : DIntv := ⟨(2 : Int) ^ k, (2 : Int) ^ k, dbl.e⟩
  sub dbl one (by rfl)

/-- `2·I·J` on `DIntv` (for sin: `I = sin box`, `J = cos box`). -/
def twoMul (I J : DIntv) : DIntv := scale2 (I.mul J) 1

/-- cos doubling map with outward rounding to drop `d` low bits (keep mantissas bounded). -/
def cosDblD (cb : DIntv) (d : Nat) : DIntv := (twoSqSubOne cb).roundTo d

/-- sin doubling map with outward rounding. -/
def sinDblD (sb cb : DIntv) (d : Nat) : DIntv := (twoMul sb cb).roundTo d

/-! ## 2.  Soundness of the step maps. -/

/-- `1 = one.lo·2^{one.e}` when `one = ⟨2^{-e}, 2^{-e}, e⟩` with `e ≤ 0`. -/
private theorem one_memR {e : Int} (he : e ≤ 0) :
    memR (1 : ℝ) (⟨(2:Int) ^ (-e).toNat, (2:Int) ^ (-e).toNat, e⟩ : DIntv) := by
  have hk : ((-e).toNat : Int) = -e := Int.toNat_of_nonneg (by omega)
  have hval : (((2:Int) ^ (-e).toNat : Int) : ℝ) * (2:ℝ) ^ e = 1 := by
    have hcast : (((2:Int) ^ (-e).toNat : Int) : ℝ) = (2:ℝ) ^ ((-e).toNat : Int) := by
      rw [zpow_natCast]; push_cast; ring
    rw [hcast, hk, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    simp
  refine ⟨?_, ?_⟩ <;> simp only [DIntv.memR] <;> rw [hval]

/-- **cos step soundness.**  If `cos y ∈ cb` then `cos (2y) ∈ cosDblD cb d`, provided the working
    exponent of `2·cb²` is `≤ 0` (always true for our negative-exponent grid). -/
theorem cosDblD_sound {y : ℝ} {cb : DIntv} (d : Nat)
    (hc : memR (Real.cos y) cb)
    (he : (scale2 (cb.mul cb) 1).e ≤ 0) :
    memR (Real.cos (2 * y)) (cosDblD cb d) := by
  have hcos : Real.cos (2 * y) = 2 * Real.cos y ^ 2 - 1 := Real.cos_two_mul y
  -- cos y ^2 = cos y * cos y ∈ cb.mul cb
  have hsq : memR (Real.cos y * Real.cos y) (cb.mul cb) := mul_sound hc hc
  -- 2 * (cos y * cos y) ∈ scale2 (cb.mul cb) 1
  have hdbl : memR (Real.cos y * Real.cos y * (2:ℝ) ^ (1:Int)) (scale2 (cb.mul cb) 1) :=
    scale2_sound 1 hsq
  have h2 : Real.cos y * Real.cos y * (2:ℝ) ^ (1:Int) = 2 * Real.cos y ^ 2 := by
    rw [zpow_one]; ring
  rw [h2] at hdbl
  -- subtract 1
  set dbl := scale2 (cb.mul cb) 1 with hdblDef
  have hone : memR (1 : ℝ) (⟨(2:Int) ^ (-dbl.e).toNat, (2:Int) ^ (-dbl.e).toNat, dbl.e⟩ : DIntv) :=
    one_memR he
  have hsub : memR (2 * Real.cos y ^ 2 - 1) (twoSqSubOne cb) := by
    unfold twoSqSubOne
    simp only [← hdblDef]
    exact sub_sound (by rfl) hdbl hone
  rw [hcos]
  exact roundTo_sound d hsub

/-- **sin step soundness.**  If `sin y ∈ sb` and `cos y ∈ cb` then `sin (2y) ∈ sinDblD sb cb d`. -/
theorem sinDblD_sound {y : ℝ} {sb cb : DIntv} (d : Nat)
    (hs : memR (Real.sin y) sb) (hc : memR (Real.cos y) cb) :
    memR (Real.sin (2 * y)) (sinDblD sb cb d) := by
  have hsin : Real.sin (2 * y) = 2 * Real.sin y * Real.cos y := Real.sin_two_mul y
  have hprod : memR (Real.sin y * Real.cos y) (sb.mul cb) := mul_sound hs hc
  have hdbl : memR (Real.sin y * Real.cos y * (2:ℝ) ^ (1:Int)) (scale2 (sb.mul cb) 1) :=
    scale2_sound 1 hprod
  have h2 : Real.sin y * Real.cos y * (2:ℝ) ^ (1:Int) = 2 * Real.sin y * Real.cos y := by
    rw [zpow_one]; ring
  rw [h2] at hdbl
  rw [hsin]
  exact roundTo_sound d (by unfold twoMul; exact hdbl)

/-! ## 3.  The paired step and the M-fold climb. -/

/-- Paired doubling step: `(cos y, sin y)` boxes → `(cos 2y, sin 2y)` boxes.  NOTE the sin step
    reads the OLD cos box, so we compute sin first (from old cb) then cos. -/
def stepD (p : DIntv × DIntv) (d : Nat) : DIntv × DIntv :=
  let cb := p.1
  let sb := p.2
  (cosDblD cb d, sinDblD sb cb d)

/-- **Paired step soundness.** -/
theorem stepD_sound {y : ℝ} {p : DIntv × DIntv} (d : Nat)
    (hc : memR (Real.cos y) p.1) (hs : memR (Real.sin y) p.2)
    (he : (scale2 (p.1.mul p.1) 1).e ≤ 0) :
    memR (Real.cos (2 * y)) (stepD p d).1 ∧ memR (Real.sin (2 * y)) (stepD p d).2 := by
  refine ⟨?_, ?_⟩
  · exact cosDblD_sound d hc he
  · exact sinDblD_sound d hs hc

/-- The `M`-fold climb: apply `stepD` `M` times, doubling the argument each time. -/
def iterDouble (p : DIntv × DIntv) (d : Nat) : Nat → DIntv × DIntv
  | 0 => p
  | (M+1) => stepD (iterDouble p d M) d

/-- **M-fold climb soundness.**  If the input boxes enclose `cos y`, `sin y`, and every intermediate
    cos box keeps a non-positive `2·cb²` exponent (the `he` side-conditions, discharged by `decide`
    per instance), then the output boxes enclose `cos (2^M·y)`, `sin (2^M·y)`. -/
theorem iterDouble_sound {y : ℝ} {p : DIntv × DIntv} (d : Nat) (M : ℕ)
    (hc : memR (Real.cos y) p.1) (hs : memR (Real.sin y) p.2)
    (he : ∀ k : ℕ, k < M → (scale2 (((iterDouble p d k).1).mul ((iterDouble p d k).1)) 1).e ≤ 0) :
    memR (Real.cos ((2:ℝ) ^ M * y)) (iterDouble p d M).1 ∧
    memR (Real.sin ((2:ℝ) ^ M * y)) (iterDouble p d M).2 := by
  induction M with
  | zero => simpa using ⟨hc, hs⟩
  | succ n ih =>
    have hstep := ih (fun k hk => he k (Nat.lt_succ_of_lt hk))
    -- 2^(n+1)·y = 2·(2^n·y)
    have harg : (2:ℝ) ^ (n+1) * y = 2 * ((2:ℝ) ^ n * y) := by
      rw [pow_succ]; ring
    have hen := he n (Nat.lt_succ_self n)
    have := stepD_sound (y := (2:ℝ)^n * y) (p := iterDouble p d n) d hstep.1 hstep.2 hen
    rw [harg]
    simp only [iterDouble]
    exact this

end TrigReduceD
