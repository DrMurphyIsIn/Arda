/-  AxiomGuardHeightFloor.lean -- trust-base guard for brick H3 (AND_height_floor_kernel).

    `lake env lean AxiomGuardHeightFloor.lean` prints one `#print axioms` line per new theorem of
    HeightFloorCheck / HeightFloorTrig / HeightFloorEM / HeightFloorBoxes / HeightFloor.  Every line
    must read exactly [propext, Classical.choice, Quot.sound] (the kernel-`decide` lemmas may show a
    subset): no `sorry`, no native-evaluation trust, no new constants of trust.

    The headline statement is re-stated below VERBATIM in the capstone's `hγ` form and closed by
    the proved theorem (a mismatch fails to elaborate).

    NEGATIVE CONTROLS (kernel `decide`, expected `false`): the exact checker REJECTS the whole
    rectangle as one box, and a 3-slab coarsening of the worst region -- the 32-box cover is not
    vacuous.

    conjecture1_proved = False.
-/
import HeightFloor

open HeightFloor

/-- The capstone's `hγ` binder (AllZeros_h280000_Indexed), verbatim, closed hypothesis-free. -/
example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → 55 / 16 ≤ |ρ.im| :=
  HeightFloor.height_floor_280000

/-- Every height. -/
example : ∀ H : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55 / 16 ≤ |ρ.im| :=
  HeightFloor.height_floor

section CapstoneOpens
-- the same binder under the capstone file's own `open Complex MeasureTheory Real`
open Complex MeasureTheory Real

example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → 55 / 16 ≤ |ρ.im| :=
  HeightFloor.height_floor_280000

end CapstoneOpens

/-- NEGATIVE CONTROL 1: the whole rectangle `[1/2, 1] × [0, 55/16]` as ONE box is rejected. -/
example : DI.checkAB
    (DI.evalAB ⟨2, 4, 2⟩ ⟨0, 880, 8⟩ ⟨2147483648, 3037000500, 32⟩ ⟨-3116411797, 4294967296, 32⟩
      ⟨0, 4294967296, 32⟩).1
    (DI.evalAB ⟨2, 4, 2⟩ ⟨0, 880, 8⟩ ⟨2147483648, 3037000500, 32⟩ ⟨-3116411797, 4294967296, 32⟩
      ⟨0, 4294967296, 32⟩).2 = false := by decide

/-- NEGATIVE CONTROL 2: `σ ∈ [1/2, 3/4]`, `t ∈ [165/256, 330/256]` (three slabs merged) is rejected. -/
example : DI.checkAB
    (DI.evalAB ⟨2, 3, 2⟩ ⟨165, 330, 8⟩ ⟨2553802833, 3037000500, 32⟩ ⟨2691572661, 3873432754, 32⟩
      ⟨1855603165, 3346965925, 32⟩).1
    (DI.evalAB ⟨2, 3, 2⟩ ⟨165, 330, 8⟩ ⟨2553802833, 3037000500, 32⟩ ⟨2691572661, 3873432754, 32⟩
      ⟨1855603165, 3346965925, 32⟩).2 = false := by decide


-- HeightFloorCheck
#print axioms HeightFloor.pow2_cast
#print axioms HeightFloor.DI.two_pow_pos
#print axioms HeightFloor.DI.ofInt_sound
#print axioms HeightFloor.DI.neg_sound
#print axioms HeightFloor.DI.shift_eq
#print axioms HeightFloor.DI.add_sound
#print axioms HeightFloor.DI.corners
#print axioms HeightFloor.DI.mul_sound
#print axioms HeightFloor.DI.gap_sq_le
#print axioms HeightFloor.DI.evalAB_sound
#print axioms HeightFloor.DI.checkAB_sound
#print axioms HeightFloor.DI.box_sound

-- HeightFloorTrig
#print axioms HeightFloor.exp_I_partial
#print axioms HeightFloor.cos_sin_taylor
#print axioms HeightFloor.trig_encl
#print axioms HeightFloor.abs_mul_log_two_sub_le
#print axioms HeightFloor.two_rpow_neg_div_pow
#print axioms HeightFloor.le_two_rpow_neg
#print axioms HeightFloor.two_rpow_neg_le
#print axioms HeightFloor.two_rpow_neg_nat
#print axioms HeightFloor.two_rpow_neg_mono
#print axioms HeightFloor.DI.mem_mk
#print axioms HeightFloor.mem_cos
#print axioms HeightFloor.mem_sin_low
#print axioms HeightFloor.sin_anti_of_half_pi
#print axioms HeightFloor.mem_sin_high
#print axioms HeightFloor.mem_sin_mid
#print axioms HeightFloor.mem_m

-- HeightFloorEM
#print axioms HeightFloor.G2_eq
#print axioms HeightFloor.norm_le_of_sq
#print axioms HeightFloor.two_rpow_neg_five_halves_le
#print axioms HeightFloor.tail_le
#print axioms HeightFloor.G2_norm_le_of_zero
#print axioms HeightFloor.two_cpow_neg_re_im
#print axioms HeightFloor.G2_re_im
#print axioms HeightFloor.G2_norm_gt_of_AB

-- HeightFloorBoxes
#print axioms HeightFloor.Boxes.trig_0
#print axioms HeightFloor.Boxes.trig_1
#print axioms HeightFloor.Boxes.trig_2
#print axioms HeightFloor.Boxes.trig_3
#print axioms HeightFloor.Boxes.trig_4
#print axioms HeightFloor.Boxes.trig_5
#print axioms HeightFloor.Boxes.trig_6
#print axioms HeightFloor.Boxes.trig_7
#print axioms HeightFloor.Boxes.trig_8
#print axioms HeightFloor.Boxes.trig_9
#print axioms HeightFloor.Boxes.trig_10
#print axioms HeightFloor.Boxes.trig_11
#print axioms HeightFloor.Boxes.trig_12
#print axioms HeightFloor.Boxes.trig_13
#print axioms HeightFloor.Boxes.trig_14
#print axioms HeightFloor.Boxes.trig_15
#print axioms HeightFloor.Boxes.trig_16
#print axioms HeightFloor.Boxes.m12_hi
#print axioms HeightFloor.Boxes.m34_lo
#print axioms HeightFloor.Boxes.m34_hi
#print axioms HeightFloor.Boxes.m1_lo
#print axioms HeightFloor.Boxes.box_0_0
#print axioms HeightFloor.Boxes.box_0_1
#print axioms HeightFloor.Boxes.box_0_2
#print axioms HeightFloor.Boxes.box_0_3
#print axioms HeightFloor.Boxes.box_0_4
#print axioms HeightFloor.Boxes.box_0_5
#print axioms HeightFloor.Boxes.box_0_6
#print axioms HeightFloor.Boxes.box_0_7
#print axioms HeightFloor.Boxes.box_0_8
#print axioms HeightFloor.Boxes.box_0_9
#print axioms HeightFloor.Boxes.box_0_10
#print axioms HeightFloor.Boxes.box_0_11
#print axioms HeightFloor.Boxes.box_0_12
#print axioms HeightFloor.Boxes.box_0_13
#print axioms HeightFloor.Boxes.box_0_14
#print axioms HeightFloor.Boxes.box_0_15
#print axioms HeightFloor.Boxes.box_1_0
#print axioms HeightFloor.Boxes.box_1_1
#print axioms HeightFloor.Boxes.box_1_2
#print axioms HeightFloor.Boxes.box_1_3
#print axioms HeightFloor.Boxes.box_1_4
#print axioms HeightFloor.Boxes.box_1_5
#print axioms HeightFloor.Boxes.box_1_6
#print axioms HeightFloor.Boxes.box_1_7
#print axioms HeightFloor.Boxes.box_1_8
#print axioms HeightFloor.Boxes.box_1_9
#print axioms HeightFloor.Boxes.box_1_10
#print axioms HeightFloor.Boxes.box_1_11
#print axioms HeightFloor.Boxes.box_1_12
#print axioms HeightFloor.Boxes.box_1_13
#print axioms HeightFloor.Boxes.box_1_14
#print axioms HeightFloor.Boxes.box_1_15
#print axioms HeightFloor.Boxes.slab_0
#print axioms HeightFloor.Boxes.slab_1
#print axioms HeightFloor.Boxes.G2_norm_gt

-- HeightFloor (headline)
#print axioms HeightFloor.zeta_ne_zero_low_right
#print axioms HeightFloor.strip_clear_low
#print axioms HeightFloor.height_floor
#print axioms HeightFloor.height_floor_280000
#print axioms HeightFloor.im_gt_of_zero
#print axioms HeightFloor.abs_im_gt_of_zero
