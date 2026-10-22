/- telperion 0.1.6 | family QuadraticOrderRootTable | input-hash 629a61c05a8f9642
   58 theorems, 28 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import QuadraticOrderRoot

namespace QuadraticOrderRootTable

open QuadraticOrderRoot NumberField Ideal

-- d8: the monogenic quadratic order X^2 - 0 X + 2, d = 4c - t^2 = 8; faces for p in [2, 3, 5, 7, 199].  Every face is re-decided by the kernel from the literals; the _kd corollaries are conditional on QuadInt.  conjecture1_proved = False.
theorem d8_ram_2 : 2 ∣ 4 * 2 - 0 ^ 2 := by decide
theorem d8_ram_2_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 2) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(2 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 :=
  D.ramified_of_dvd 2 (by norm_num) (by decide) d8_ram_2
theorem d8_root_3 : IsRootMod 0 2 3 1 := by decide
theorem d8_root_3_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 2) :
    (primesOver (span {(3 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(3 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 3 (by norm_num) (by decide) d8_root_3
theorem d8_noroot_5 : ∀ z : ZMod 5, z ^ 2 - (0 : ZMod 5) * z + (2 : ZMod 5) ≠ 0 := by decide
theorem d8_noroot_5_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 2) :
    (primesOver (span {(5 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(5 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 5 (by norm_num) d8_noroot_5
theorem d8_noroot_7 : ∀ z : ZMod 7, z ^ 2 - (0 : ZMod 7) * z + (2 : ZMod 7) ≠ 0 := by decide
theorem d8_noroot_7_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 2) :
    (primesOver (span {(7 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(7 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 7 (by norm_num) d8_noroot_7
set_option maxRecDepth 8192 in
theorem d8_noroot_199 : ∀ z : ZMod 199, z ^ 2 - (0 : ZMod 199) * z + (2 : ZMod 199) ≠ 0 := by decide
theorem d8_noroot_199_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 2) :
    (primesOver (span {(199 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(199 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 199 (by norm_num) d8_noroot_199
/-- `d8`: the face table (kernel-decided). -/
theorem d8 : (2 ∣ 4 * 2 - 0 ^ 2) ∧ (IsRootMod 0 2 3 1) ∧ (∀ z : ZMod 5, z ^ 2 - (0 : ZMod 5) * z + (2 : ZMod 5) ≠ 0) ∧ (∀ z : ZMod 7, z ^ 2 - (0 : ZMod 7) * z + (2 : ZMod 7) ≠ 0) ∧ (∀ z : ZMod 199, z ^ 2 - (0 : ZMod 199) * z + (2 : ZMod 199) ≠ 0) :=
  ⟨d8_ram_2, d8_root_3, d8_noroot_5, d8_noroot_7, d8_noroot_199⟩
example : (2 ∣ 4 * 2 - 0 ^ 2) ∧ (IsRootMod 0 2 3 1) ∧ (∀ z : ZMod 5, z ^ 2 - (0 : ZMod 5) * z + (2 : ZMod 5) ≠ 0) ∧ (∀ z : ZMod 7, z ^ 2 - (0 : ZMod 7) * z + (2 : ZMod 7) ≠ 0) ∧ (∀ z : ZMod 199, z ^ 2 - (0 : ZMod 199) * z + (2 : ZMod 199) ≠ 0) := d8

-- d20: the monogenic quadratic order X^2 - 0 X + 5, d = 4c - t^2 = 20; faces for p in [2, 3, 7].  Every face is re-decided by the kernel from the literals; the _kd corollaries are conditional on QuadInt.  conjecture1_proved = False.
theorem d20_ram_2 : 2 ∣ 4 * 5 - 0 ^ 2 := by decide
theorem d20_ram_2_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 5) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(2 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 :=
  D.ramified_of_dvd 2 (by norm_num) (by decide) d20_ram_2
theorem d20_root_3 : IsRootMod 0 5 3 1 := by decide
theorem d20_root_3_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 5) :
    (primesOver (span {(3 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(3 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 3 (by norm_num) (by decide) d20_root_3
theorem d20_root_7 : IsRootMod 0 5 7 3 := by decide
theorem d20_root_7_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 5) :
    (primesOver (span {(7 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(7 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 7 (by norm_num) (by decide) d20_root_7
/-- Class-number witness: p = 3 splits with root y = 1, 4p = 12 ≤ d = 20, p ≠ c = 5. -/
theorem d20_w_3 : IsWitness 0 5 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
/-- `d20`: `h ≠ 1` for the field with `𝓞 K = ℤ[θ]`, `θ² = 0θ - 5` (Rabinowitsch, witness p = 3). -/
theorem d20_classNumber_ne_one {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 5) :
    classNumber K ≠ 1 :=
  classNumber_ne_one_of_isWitness D (by decide) d20_w_3
/-- `d20`: the face table (kernel-decided). -/
theorem d20 : (2 ∣ 4 * 5 - 0 ^ 2) ∧ (IsRootMod 0 5 3 1) ∧ (IsRootMod 0 5 7 3) :=
  ⟨d20_ram_2, d20_root_3, d20_root_7⟩
example : (2 ∣ 4 * 5 - 0 ^ 2) ∧ (IsRootMod 0 5 3 1) ∧ (IsRootMod 0 5 7 3) := d20

-- d56: the monogenic quadratic order X^2 - 0 X + 14, d = 4c - t^2 = 56; faces for p in [2, 3, 5, 7].  Every face is re-decided by the kernel from the literals; the _kd corollaries are conditional on QuadInt.  conjecture1_proved = False.
theorem d56_ram_2 : 2 ∣ 4 * 14 - 0 ^ 2 := by decide
theorem d56_ram_2_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 14) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(2 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 :=
  D.ramified_of_dvd 2 (by norm_num) (by decide) d56_ram_2
theorem d56_root_3 : IsRootMod 0 14 3 1 := by decide
theorem d56_root_3_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 14) :
    (primesOver (span {(3 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(3 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 3 (by norm_num) (by decide) d56_root_3
theorem d56_root_5 : IsRootMod 0 14 5 1 := by decide
theorem d56_root_5_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 14) :
    (primesOver (span {(5 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(5 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 5 (by norm_num) (by decide) d56_root_5
theorem d56_ram_7 : 7 ∣ 4 * 14 - 0 ^ 2 := by decide
theorem d56_ram_7_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 14) :
    (primesOver (span {(7 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(7 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 :=
  D.ramified_of_dvd 7 (by norm_num) (by decide) d56_ram_7
/-- Class-number witness: p = 3 splits with root y = 1, 4p = 12 ≤ d = 56, p ≠ c = 14. -/
theorem d56_w_3 : IsWitness 0 14 3 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
/-- Class-number witness: p = 5 splits with root y = 1, 4p = 20 ≤ d = 56, p ≠ c = 14. -/
theorem d56_w_5 : IsWitness 0 14 5 1 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
/-- `d56`: `h ≠ 1` for the field with `𝓞 K = ℤ[θ]`, `θ² = 0θ - 14` (Rabinowitsch, witness p = 3). -/
theorem d56_classNumber_ne_one {K : Type*} [Field K] [NumberField K] (D : QuadInt K 0 14) :
    classNumber K ≠ 1 :=
  classNumber_ne_one_of_isWitness D (by decide) d56_w_3
/-- `d56`: the face table (kernel-decided). -/
theorem d56 : (2 ∣ 4 * 14 - 0 ^ 2) ∧ (IsRootMod 0 14 3 1) ∧ (IsRootMod 0 14 5 1) ∧ (7 ∣ 4 * 14 - 0 ^ 2) :=
  ⟨d56_ram_2, d56_root_3, d56_root_5, d56_ram_7⟩
example : (2 ∣ 4 * 14 - 0 ^ 2) ∧ (IsRootMod 0 14 3 1) ∧ (IsRootMod 0 14 5 1) ∧ (7 ∣ 4 * 14 - 0 ^ 2) := d56

-- d31: the monogenic quadratic order X^2 - 1 X + 8, d = 4c - t^2 = 31; faces for p in [2, 5, 7].  Every face is re-decided by the kernel from the literals; the _kd corollaries are conditional on QuadInt.  conjecture1_proved = False.
theorem d31_root_2 : IsRootMod 1 8 2 0 := by decide
theorem d31_root_2_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 8) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(2 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 2 (by norm_num) (by decide) d31_root_2
theorem d31_root_5 : IsRootMod 1 8 5 2 := by decide
theorem d31_root_5_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 8) :
    (primesOver (span {(5 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(5 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 5 (by norm_num) (by decide) d31_root_5
theorem d31_root_7 : IsRootMod 1 8 7 3 := by decide
theorem d31_root_7_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 8) :
    (primesOver (span {(7 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(7 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 7 (by norm_num) (by decide) d31_root_7
/-- Class-number witness: p = 2 splits with root y = 0, 4p = 8 ≤ d = 31, p ≠ c = 8. -/
theorem d31_w_2 : IsWitness 1 8 2 0 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
/-- Class-number witness: p = 5 splits with root y = 2, 4p = 20 ≤ d = 31, p ≠ c = 8. -/
theorem d31_w_5 : IsWitness 1 8 5 2 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
/-- Class-number witness: p = 7 splits with root y = 3, 4p = 28 ≤ d = 31, p ≠ c = 8. -/
theorem d31_w_7 : IsWitness 1 8 7 3 :=
  ⟨by norm_num, by decide, by decide, by decide, by decide⟩
/-- `d31`: `h ≠ 1` for the field with `𝓞 K = ℤ[θ]`, `θ² = 1θ - 8` (Rabinowitsch, witness p = 2). -/
theorem d31_classNumber_ne_one {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 8) :
    classNumber K ≠ 1 :=
  classNumber_ne_one_of_isWitness D (by decide) d31_w_2
/-- `d31`: the face table (kernel-decided). -/
theorem d31 : (IsRootMod 1 8 2 0) ∧ (IsRootMod 1 8 5 2) ∧ (IsRootMod 1 8 7 3) :=
  ⟨d31_root_2, d31_root_5, d31_root_7⟩
example : (IsRootMod 1 8 2 0) ∧ (IsRootMod 1 8 5 2) ∧ (IsRootMod 1 8 7 3) := d31

-- d163: the monogenic quadratic order X^2 - 1 X + 41, d = 4c - t^2 = 163; faces for p in [2, 3, 5, 7, 41, 163, 193].  Every face is re-decided by the kernel from the literals; the _kd corollaries are conditional on QuadInt.  conjecture1_proved = False.
theorem d163_noroot_2 : ∀ z : ZMod 2, z ^ 2 - (1 : ZMod 2) * z + (41 : ZMod 2) ≠ 0 := by decide
theorem d163_noroot_2_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 41) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(2 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 2 (by norm_num) d163_noroot_2
theorem d163_noroot_3 : ∀ z : ZMod 3, z ^ 2 - (1 : ZMod 3) * z + (41 : ZMod 3) ≠ 0 := by decide
theorem d163_noroot_3_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 41) :
    (primesOver (span {(3 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(3 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 3 (by norm_num) d163_noroot_3
theorem d163_noroot_5 : ∀ z : ZMod 5, z ^ 2 - (1 : ZMod 5) * z + (41 : ZMod 5) ≠ 0 := by decide
theorem d163_noroot_5_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 41) :
    (primesOver (span {(5 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(5 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 5 (by norm_num) d163_noroot_5
theorem d163_noroot_7 : ∀ z : ZMod 7, z ^ 2 - (1 : ZMod 7) * z + (41 : ZMod 7) ≠ 0 := by decide
theorem d163_noroot_7_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 41) :
    (primesOver (span {(7 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(7 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 7 (by norm_num) d163_noroot_7
theorem d163_root_41 : IsRootMod 1 41 41 0 := by decide
theorem d163_root_41_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 41) :
    (primesOver (span {(41 : ℤ)}) (𝓞 K)).ncard = 2 ∧ ∀ P ∈ primesOver (span {(41 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 :=
  D.split_of_isRootMod 41 (by norm_num) (by decide) d163_root_41
theorem d163_ram_163 : 163 ∣ 4 * 41 - 1 ^ 2 := by decide
theorem d163_ram_163_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 41) :
    (primesOver (span {(163 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(163 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 :=
  D.ramified_of_dvd 163 (by norm_num) (by decide) d163_ram_163
set_option maxRecDepth 8192 in
theorem d163_noroot_193 : ∀ z : ZMod 193, z ^ 2 - (1 : ZMod 193) * z + (41 : ZMod 193) ≠ 0 := by decide
theorem d163_noroot_193_kd {K : Type*} [Field K] [NumberField K] (D : QuadInt K 1 41) :
    (primesOver (span {(193 : ℤ)}) (𝓞 K)).ncard = 1 ∧ ∀ P ∈ primesOver (span {(193 : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 :=
  D.inert_of_no_root 193 (by norm_num) d163_noroot_193
/-- `d163`: the face table (kernel-decided). -/
theorem d163 : (∀ z : ZMod 2, z ^ 2 - (1 : ZMod 2) * z + (41 : ZMod 2) ≠ 0) ∧ (∀ z : ZMod 3, z ^ 2 - (1 : ZMod 3) * z + (41 : ZMod 3) ≠ 0) ∧ (∀ z : ZMod 5, z ^ 2 - (1 : ZMod 5) * z + (41 : ZMod 5) ≠ 0) ∧ (∀ z : ZMod 7, z ^ 2 - (1 : ZMod 7) * z + (41 : ZMod 7) ≠ 0) ∧ (IsRootMod 1 41 41 0) ∧ (163 ∣ 4 * 41 - 1 ^ 2) ∧ (∀ z : ZMod 193, z ^ 2 - (1 : ZMod 193) * z + (41 : ZMod 193) ≠ 0) :=
  ⟨d163_noroot_2, d163_noroot_3, d163_noroot_5, d163_noroot_7, d163_root_41, d163_ram_163, d163_noroot_193⟩
example : (∀ z : ZMod 2, z ^ 2 - (1 : ZMod 2) * z + (41 : ZMod 2) ≠ 0) ∧ (∀ z : ZMod 3, z ^ 2 - (1 : ZMod 3) * z + (41 : ZMod 3) ≠ 0) ∧ (∀ z : ZMod 5, z ^ 2 - (1 : ZMod 5) * z + (41 : ZMod 5) ≠ 0) ∧ (∀ z : ZMod 7, z ^ 2 - (1 : ZMod 7) * z + (41 : ZMod 7) ≠ 0) ∧ (IsRootMod 1 41 41 0) ∧ (163 ∣ 4 * 41 - 1 ^ 2) ∧ (∀ z : ZMod 193, z ^ 2 - (1 : ZMod 193) * z + (41 : ZMod 193) ≠ 0) := d163

end QuadraticOrderRootTable
