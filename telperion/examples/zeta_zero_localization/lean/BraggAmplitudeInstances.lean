/- telperion 0.1.6 | family BraggAmplitudeInstances | input-hash 8e8535e4764f87f5
   7 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import CosEnclosure

namespace BraggAmplitudeInstances

/-- cos-box for ordinate 1 of 3: for ANY `t ∈ [(1 / 2), (51 / 100)]`, `cos (t * u)`
    lies in the certified box (order-4 Taylor bracket at the midpoint sample + Lipschitz). -/
theorem bragg_three_u32_cosbox_1 (t : ℝ) (hta : ((1 / 2) : ℝ) ≤ t) (htb : t ≤ ((51 / 100) : ℝ)) :
    (((112795361173 / 163840000000)) : ℝ) ≤ Real.cos (t * ((3 / 2))) ∧ Real.cos (t * ((3 / 2))) ≤ ((120872222827 / 163840000000)) := by
  have hy : |(((303 / 400)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hbase : (((114024161173 / 163840000000)) : ℝ) ≤ Real.cos ((303 / 400)) ∧ Real.cos ((303 / 400)) ≤ ((119643422827 / 163840000000)) :=
    CosEnclosure.cos_base_interval (y := (((303 / 400)) : ℝ)) hy (by norm_num) (by norm_num)
  have hdist : |t * ((3 / 2)) - ((303 / 400))| ≤ ((3 / 400)) := by
    rw [abs_le]; constructor <;> nlinarith [hta, htb]
  have hbr := CosEnclosure.cos_encl_bracket (w := (((3 / 400)) : ℝ)) (by norm_num) hdist hbase.1 hbase.2
  exact ⟨le_trans (by norm_num : (((112795361173 / 163840000000)) : ℝ) ≤ ((114024161173 / 163840000000)) - ((3 / 400))) hbr.1,
    le_trans hbr.2 (by norm_num : (((119643422827 / 163840000000)) : ℝ) + ((3 / 400)) ≤ ((120872222827 / 163840000000)))⟩
/-- cos-box for ordinate 2 of 3: for ANY `t ∈ [(3 / 5), (61 / 100)]`, `cos (t * u)`
    lies in the certified box (order-4 Taylor bracket at the midpoint sample + Lipschitz). -/
theorem bragg_three_u32_cosbox_2 (t : ℝ) (hta : ((3 / 5) : ℝ) ≤ t) (htb : t ≤ ((61 / 100) : ℝ)) :
    (((89357782213 / 163840000000)) : ℝ) ≤ Real.cos (t * ((3 / 2))) ∧ Real.cos (t * ((3 / 2))) ≤ ((103390761787 / 163840000000)) := by
  have hy : |(((363 / 400)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hbase : (((90586582213 / 163840000000)) : ℝ) ≤ Real.cos ((363 / 400)) ∧ Real.cos ((363 / 400)) ≤ ((102161961787 / 163840000000)) :=
    CosEnclosure.cos_base_interval (y := (((363 / 400)) : ℝ)) hy (by norm_num) (by norm_num)
  have hdist : |t * ((3 / 2)) - ((363 / 400))| ≤ ((3 / 400)) := by
    rw [abs_le]; constructor <;> nlinarith [hta, htb]
  have hbr := CosEnclosure.cos_encl_bracket (w := (((3 / 400)) : ℝ)) (by norm_num) hdist hbase.1 hbase.2
  exact ⟨le_trans (by norm_num : (((89357782213 / 163840000000)) : ℝ) ≤ ((90586582213 / 163840000000)) - ((3 / 400))) hbr.1,
    le_trans hbr.2 (by norm_num : (((102161961787 / 163840000000)) : ℝ) + ((3 / 400)) ≤ ((103390761787 / 163840000000)))⟩
/-- cos-box for ordinate 3 of 3: for ANY `t ∈ [(2 / 5), (41 / 100)]`, `cos (t * u)`
    lies in the certified box (order-4 Taylor bracket at the midpoint sample + Lipschitz). -/
theorem bragg_three_u32_cosbox_3 (t : ℝ) (hta : ((2 / 5) : ℝ) ≤ t) (htb : t ≤ ((41 / 100) : ℝ)) :
    (((131215850533 / 163840000000)) : ℝ) ≤ Real.cos (t * ((3 / 2))) ∧ Real.cos (t * ((3 / 2))) ≤ ((135997973467 / 163840000000)) := by
  have hy : |(((243 / 400)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hbase : (((132444650533 / 163840000000)) : ℝ) ≤ Real.cos ((243 / 400)) ∧ Real.cos ((243 / 400)) ≤ ((134769173467 / 163840000000)) :=
    CosEnclosure.cos_base_interval (y := (((243 / 400)) : ℝ)) hy (by norm_num) (by norm_num)
  have hdist : |t * ((3 / 2)) - ((243 / 400))| ≤ ((3 / 400)) := by
    rw [abs_le]; constructor <;> nlinarith [hta, htb]
  have hbr := CosEnclosure.cos_encl_bracket (w := (((3 / 400)) : ℝ)) (by norm_num) hdist hbase.1 hbase.2
  exact ⟨le_trans (by norm_num : (((131215850533 / 163840000000)) : ℝ) ≤ ((132444650533 / 163840000000)) - ((3 / 400))) hbr.1,
    le_trans hbr.2 (by norm_num : (((134769173467 / 163840000000)) : ℝ) + ((3 / 400)) ≤ ((135997973467 / 163840000000)))⟩
/-- **Truncated Bragg amplitude** `F(u) = Σ_{k=1}^{3} cos(γ_k · u)` at `u = (3 / 2)`,
    for any certified ordinates `γ_k ∈ [a_k, b_k]`, lies in `[0, 3]`.  The 29-zero
    `BraggH100.bragg_amplitude_h100` fold, reduced to a 3-ordinate base-case instance.
    conjecture1_proved = False. -/
theorem bragg_three_u32 (t1 t2 t3 : ℝ)
    (ht1a : ((1 / 2) : ℝ) ≤ t1) (ht1b : t1 ≤ ((51 / 100) : ℝ))
    (ht2a : ((3 / 5) : ℝ) ≤ t2) (ht2b : t2 ≤ ((61 / 100) : ℝ))
    (ht3a : ((2 / 5) : ℝ) ≤ t3) (ht3b : t3 ≤ ((41 / 100) : ℝ)) :
    ((0) : ℝ) ≤ Real.cos (t1 * ((3 / 2))) + Real.cos (t2 * ((3 / 2))) + Real.cos (t3 * ((3 / 2))) ∧ Real.cos (t1 * ((3 / 2))) + Real.cos (t2 * ((3 / 2))) + Real.cos (t3 * ((3 / 2))) ≤ (3) := by
  have hb1 := bragg_three_u32_cosbox_1 t1 ht1a ht1b
  have hb2 := bragg_three_u32_cosbox_2 t2 ht2a ht2b
  have hb3 := bragg_three_u32_cosbox_3 t3 ht3a ht3b
  have hacc2 := CosEnclosure.add_encl ⟨hb1.1, hb1.2⟩ ⟨hb2.1, hb2.2⟩
  have hacc3 := CosEnclosure.add_encl hacc2 ⟨hb3.1, hb3.2⟩
  have hacc := hacc3
  exact ⟨by linarith [hacc.1], by linarith [hacc.2]⟩
/-- cos-box for ordinate 1 of 2: for ANY `t ∈ [(1 / 2), (51 / 100)]`, `cos (t * u)`
    lies in the certified box (order-4 Taylor bracket at the midpoint sample + Lipschitz). -/
theorem bragg_two_u1_cosbox_1 (t : ℝ) (hta : ((1 / 2) : ℝ) ≤ t) (htb : t ≤ ((51 / 100) : ℝ)) :
    (((26545155599 / 30720000000)) : ℝ) ≤ Real.cos (t * (1)) ∧ Real.cos (t * (1)) ≤ ((27060476401 / 30720000000)) := by
  have hy : |(((101 / 200)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hbase : (((26698755599 / 30720000000)) : ℝ) ≤ Real.cos ((101 / 200)) ∧ Real.cos ((101 / 200)) ≤ ((26906876401 / 30720000000)) :=
    CosEnclosure.cos_base_interval (y := (((101 / 200)) : ℝ)) hy (by norm_num) (by norm_num)
  have hdist : |t * (1) - ((101 / 200))| ≤ ((1 / 200)) := by
    rw [abs_le]; constructor <;> nlinarith [hta, htb]
  have hbr := CosEnclosure.cos_encl_bracket (w := (((1 / 200)) : ℝ)) (by norm_num) hdist hbase.1 hbase.2
  exact ⟨le_trans (by norm_num : (((26545155599 / 30720000000)) : ℝ) ≤ ((26698755599 / 30720000000)) - ((1 / 200))) hbr.1,
    le_trans hbr.2 (by norm_num : (((26906876401 / 30720000000)) : ℝ) + ((1 / 200)) ≤ ((27060476401 / 30720000000)))⟩
/-- cos-box for ordinate 2 of 2: for ANY `t ∈ [(3 / 5), (61 / 100)]`, `cos (t * u)`
    lies in the certified box (order-4 Taylor bracket at the midpoint sample + Lipschitz). -/
theorem bragg_two_u1_cosbox_2 (t : ℝ) (hta : ((3 / 5) : ℝ) ≤ t) (htb : t ≤ ((61 / 100) : ℝ)) :
    (((24729897119 / 30720000000)) : ℝ) ≤ Real.cos (t * (1)) ∧ Real.cos (t * (1)) ≤ ((25465814881 / 30720000000)) := by
  have hy : |(((121 / 200)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hbase : (((24883497119 / 30720000000)) : ℝ) ≤ Real.cos ((121 / 200)) ∧ Real.cos ((121 / 200)) ≤ ((25312214881 / 30720000000)) :=
    CosEnclosure.cos_base_interval (y := (((121 / 200)) : ℝ)) hy (by norm_num) (by norm_num)
  have hdist : |t * (1) - ((121 / 200))| ≤ ((1 / 200)) := by
    rw [abs_le]; constructor <;> nlinarith [hta, htb]
  have hbr := CosEnclosure.cos_encl_bracket (w := (((1 / 200)) : ℝ)) (by norm_num) hdist hbase.1 hbase.2
  exact ⟨le_trans (by norm_num : (((24729897119 / 30720000000)) : ℝ) ≤ ((24883497119 / 30720000000)) - ((1 / 200))) hbr.1,
    le_trans hbr.2 (by norm_num : (((25312214881 / 30720000000)) : ℝ) + ((1 / 200)) ≤ ((25465814881 / 30720000000)))⟩
/-- **Truncated Bragg amplitude** `F(u) = Σ_{k=1}^{2} cos(γ_k · u)` at `u = 1`,
    for any certified ordinates `γ_k ∈ [a_k, b_k]`, lies in `[0, 2]`.  The 29-zero
    `BraggH100.bragg_amplitude_h100` fold, reduced to a 2-ordinate base-case instance.
    conjecture1_proved = False. -/
theorem bragg_two_u1 (t1 t2 : ℝ)
    (ht1a : ((1 / 2) : ℝ) ≤ t1) (ht1b : t1 ≤ ((51 / 100) : ℝ))
    (ht2a : ((3 / 5) : ℝ) ≤ t2) (ht2b : t2 ≤ ((61 / 100) : ℝ)) :
    ((0) : ℝ) ≤ Real.cos (t1 * (1)) + Real.cos (t2 * (1)) ∧ Real.cos (t1 * (1)) + Real.cos (t2 * (1)) ≤ (2) := by
  have hb1 := bragg_two_u1_cosbox_1 t1 ht1a ht1b
  have hb2 := bragg_two_u1_cosbox_2 t2 ht2a ht2b
  have hacc2 := CosEnclosure.add_encl ⟨hb1.1, hb1.2⟩ ⟨hb2.1, hb2.2⟩
  have hacc := hacc2
  exact ⟨by linarith [hacc.1], by linarith [hacc.2]⟩

end BraggAmplitudeInstances
