/-
  R3Cert.R47HnormFalse52 -- the capstone's `Hnorm` is FALSE at aligned n = 52.

  `conjecture1_of_Hnorm` (R47TieArgmax) reduces Conjecture 1 to the tree->hub normalization

      Hnorm : ∀ t, ∃ s, Balanced s ∧ Capped s ∧ stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s).

  This file exhibits an EXACT multi-hub counterexample refuting `Hnorm` at the aligned size
  `n = 52`.  The witness is the four-core backbone

      T52 := backboneU [([],6),([],6),([],6),([],6)]   (usize = 52),

  whose objective STRICTLY EXCEEDS every Balanced+Capped single hub of size 52 -- and every
  Balanced+Capped MULTI-hub state of size 52 is impossible (each capped hub is >= 46 vertices,
  so two hubs already exceed 52).  Hence no Balanced+Capped `s` with `stateSize s = 52 = usize T52`
  can dominate `T52`; `Hnorm` fails at 52.

  All rationals are exact and match the 4-engine numerical verification.  The single-hub bound is
  routed through the existing `singleHub_le_tieArgmax` + `tieArgmax` machinery, so the only new
  numeric content is:
    * `aobj_T52_eq`         -- the exact value of `Aobj T52` (built bottom-up via `Aobj_backbone`);
    * `tieArgmax_52_lt_T52` -- the tie at size 52 is strictly below `Aobj T52` (4-triple enumeration).

  This does NOT flip `conjecture1_proved` -- it SHARPENS the residual: the fixed-n reduction is not
  merely aligned-n scoped (R47AlignedMinSize) but genuinely FALSE at aligned multi-hub sizes, so any
  future `Hnorm` proof must exclude the multi-hub-realizable sizes.  conjecture1_proved = False.

  Kernel-checked, no `sorry`.
-/
import Mathlib
import R3Cert.R47TieArgmax
import R3Cert.R47TieBroadened
import R3Cert.R47AlignedMinSize
import R3Cert.R47Backbone
import R3Cert.R47BackboneAmp
import R3Cert.R47HubState
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

set_option maxRecDepth 4000
set_option linter.constructorNameAsVariable false

/-! ### The four-core backbone witness and its cavity pieces -/

/-- Innermost core: one hub of six cherries, no arms. -/
def v4 : UTree := backboneU [([], 6)]
/-- Two cores. -/
def v3 : UTree := backboneU [([], 6), ([], 6)]
/-- Three cores. -/
def v2 : UTree := backboneU [([], 6), ([], 6), ([], 6)]
/-- **The witness**: four six-cherry cores in a path. -/
def T52 : UTree := backboneU [([], 6), ([], 6), ([], 6), ([], 6)]

/-! #### Vertex count -/

/-- `usize T52 = 52` (four cores, each `1 + 6·2 = 13` vertices). -/
theorem usize_T52 : usize T52 = 52 := by
  have h : usize T52 = stateSize [([], 6), ([], 6), ([], 6), ([], 6)] :=
    usize_backbone ([], 6) [([], 6), ([], 6), ([], 6)]
  rw [h]
  simp only [stateSize, hubSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_nil, List.sum_nil]
  norm_num

/-! #### The bottom-up cavity values

For each core `vi = backboneU (([],6) :: rest)` we compute both
`Ztot (dtSub vi)` (via `Ztot_dtSub_backbone`, arms `= []`) and
`Zopen (dtSub vi)` (via `Zopen_dtSub_node_eq`, the plain child product).
Each level substitutes the previous level's two values.  `udeg vi = 6 + (tailU rest).length + 1`. -/

theorem zt_v4 : Ztot (dtSub v4) = 6561 / 448 := by
  have h := Ztot_dtSub_backbone [] 6 []
  simp only [tailU_nil, List.length_nil, List.map_nil, List.prod_nil, List.sum_nil,
    dtChildren_nil, one_mul, mul_one] at h
  rw [v4, h]; norm_num

theorem zo_v4 : Zopen (dtSub v4) = 729 / 64 := by
  rw [v4, backboneU_eq]
  rw [Zopen_dtSub_node_eq]
  simp only [tailU_nil, List.append_nil, List.map_nil, List.map_append, List.map_replicate,
    List.prod_append, List.prod_nil, List.prod_replicate, Ztot_dtSub_cherryU]
  norm_num

theorem zt_v3 : Ztot (dtSub v3) = 6908733 / 32768 := by
  have h := Ztot_dtSub_backbone [] 6 [([], 6)]
  simp only [tailU_cons, List.map_nil, List.prod_nil, one_mul, List.sum_nil,
    List.length_cons, List.length_nil, List.map_cons, List.prod_cons, dtChildren_cons,
    dtChildren_nil, List.sum_cons] at h
  -- the single tail child is `backboneU [([],6)] = v4`
  have hchild : backboneU [([], 6)] = v4 := rfl
  rw [hchild] at h
  rw [v3, h, zt_v4, zo_v4]
  -- udeg v4 = 7 : the tail child node has length 6, so udeg = 7
  have hudeg : (udeg v4 : ℝ) = 7 := by
    rw [v4, backboneU_eq]
    simp only [tailU_nil, List.append_nil, udeg_node, List.length_map, List.length_append,
      List.length_replicate, List.length_nil]
    norm_num
  rw [hudeg]; norm_num

theorem zo_v3 : Zopen (dtSub v3) = 4782969 / 28672 := by
  rw [v3, backboneU_eq, Zopen_dtSub_node_eq]
  have hchild : tailU [([], 6)] = [v4] := rfl
  rw [hchild]
  simp only [List.map_nil, List.map_append, List.map_replicate, List.map_cons,
    List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil, Ztot_dtSub_cherryU,
    mul_one]
  rw [zt_v4]; norm_num

theorem zt_v2 : Ztot (dtSub v2) = 356039429391 / 117440512 := by
  have h := Ztot_dtSub_backbone [] 6 [([], 6), ([], 6)]
  simp only [tailU_cons, List.map_nil, List.prod_nil, one_mul, List.sum_nil,
    List.length_cons, List.length_nil, List.map_cons, List.prod_cons, dtChildren_cons,
    dtChildren_nil, List.sum_cons] at h
  have hchild : backboneU [([], 6), ([], 6)] = v3 := rfl
  rw [hchild] at h
  rw [v2, h, zt_v3, zo_v3]
  have hudeg : (udeg v3 : ℝ) = 8 := by
    rw [v3, backboneU_eq]
    have : tailU [([], 6)] = [v4] := rfl
    rw [this]
    simp only [udeg_node, List.length_map, List.length_append, List.length_replicate,
      List.length_nil, List.length_cons]
    norm_num
  rw [hudeg]; norm_num

theorem zo_v2 : Zopen (dtSub v2) = 5036466357 / 2097152 := by
  rw [v2, backboneU_eq, Zopen_dtSub_node_eq]
  have hchild : tailU [([], 6), ([], 6)] = [v3] := rfl
  rw [hchild]
  simp only [List.map_nil, List.map_append, List.map_replicate, List.map_cons,
    List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil, Ztot_dtSub_cherryU,
    mul_one]
  rw [zt_v3]; norm_num

/-- **The exact objective of the witness.**  Built from the root amplitude (`Aobj_backbone`,
    root degree = child count = 7), substituting the third-core cavity values. -/
theorem aobj_T52_eq : Aobj T52 = 1180837892027061 / 26306674688 := by
  have h := Aobj_backbone [] 6 [([], 6), ([], 6), ([], 6)] (by
    simp only [tailU_cons, List.length_nil, List.length_cons]; omega)
  simp only [tailU_cons, List.map_nil, List.prod_nil, one_mul, List.sum_nil,
    List.length_cons, List.length_nil, List.map_cons, List.prod_cons, dtChildren_cons,
    dtChildren_nil, List.sum_cons] at h
  have hchild : backboneU [([], 6), ([], 6), ([], 6)] = v2 := rfl
  rw [hchild] at h
  rw [T52, h, zt_v2, zo_v2]
  have hudeg : (udeg v2 : ℝ) = 8 := by
    rw [v2, backboneU_eq]
    have : tailU [([], 6), ([], 6)] = [v3] := rfl
    rw [this]
    simp only [udeg_node, List.length_map, List.length_append, List.length_replicate,
      List.length_nil, List.length_cons]
    norm_num
  rw [hudeg]; norm_num

/-! ### The tie at size 52 is strictly below the witness -/

/-- Every count-triple of a Balanced+Capped single hub of size 52 has `Aobj` strictly below
    `Aobj T52`.  `hubTriples 52` has exactly four elements (`11a+9b+2c = 51`, `5 <= a+b`,
    `c <= 5`); each is checked via `hub_Aobj_eq` + `norm_num`. -/
theorem hubTriple_52_lt_T52 (t : ℕ × ℕ × ℕ) (ht : t ∈ hubTriples 52) :
    Aobj (backboneU (hubState t.1 t.2.1 t.2.2)) < Aobj T52 := by
  obtain ⟨a, b, c⟩ := t
  rw [mem_hubTriples] at ht
  obtain ⟨hsz, hab, hc⟩ := ht
  simp only at hsz hab hc ⊢
  rw [aobj_T52_eq]
  -- 11a + 9b + 2c = 51, 5 <= a+b, c <= 5.  Bound each coordinate, then enumerate.
  have ha : a ≤ 4 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    first
      | (exfalso; omega)
      | (rw [hub_Aobj_eq _ _ _ (by omega)]; norm_num)

/-- **The crux refutation numeric**: the per-size single-hub tie at 52 is strictly below the
    four-core witness.  `tieArgmax 52` is `backboneU (hubState ...)` for the chosen argmax triple,
    which lies in `hubTriples 52`, hence is dominated by `hubTriple_52_lt_T52`. -/
theorem tieArgmax_52_lt_T52 : Aobj (tieArgmax 52) < Aobj T52 := by
  have hne : (hubTriples 52).Nonempty := by
    refine ⟨(0, 5, 3), ?_⟩
    rw [mem_hubTriples]; refine ⟨by norm_num, by norm_num, by norm_num⟩
  rw [tieArgmax, dif_pos hne]
  obtain ⟨hmem, _⟩ := (Finset.exists_max_image (hubTriples 52) tripleAobj hne).choose_spec
  exact hubTriple_52_lt_T52 _ hmem

/-! ### The multi-hub exclusion -/

/-- A Balanced+Capped state with `>= 2` hubs has `stateSize >= 92` (each capped hub is `>= 46`). -/
theorem capped_two_hub_size_ge_92 (s : List Hub)
    (hbal : Balanced s) (hcap : Capped s) (hlen : 2 ≤ s.length) :
    92 ≤ stateSize s := by
  match s, hlen with
  | h1 :: h2 :: t, _ =>
    obtain ⟨arms1, c1⟩ := h1
    obtain ⟨arms2, c2⟩ := h2
    have hb1 : BalancedArms arms1 := (hbal (arms1, c1) (by simp)).1
    have hcp1 : 5 ≤ arms1.length := hcap (arms1, c1) (by simp)
    have hb2 : BalancedArms arms2 := (hbal (arms2, c2) (by simp)).1
    have hcp2 : 5 ≤ arms2.length := hcap (arms2, c2) (by simp)
    have h1' : 46 ≤ stateSize [(arms1, c1)] := capped_singleHub_size_ge_46 arms1 c1 hb1 hcp1
    have h2' : 46 ≤ stateSize [(arms2, c2)] := capped_singleHub_size_ge_46 arms2 c2 hb2 hcp2
    have hsplit : stateSize ((arms1, c1) :: (arms2, c2) :: t)
        = stateSize [(arms1, c1)] + stateSize [(arms2, c2)] + stateSize t := by
      simp only [stateSize, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
      ring
    rw [hsplit]; omega

/-! ### `Hnorm` is false at 52 -/

/-- **`Hnorm` is FALSE at the aligned multi-hub size 52.**  No Balanced+Capped state of size 52
    dominates the four-core witness `T52`: multi-hub states of size 52 do not exist (each capped
    hub is `>= 46`), and the unique single-hub option is `Aobj`-dominated by the size-52 tie, which
    is strictly below `Aobj T52`. -/
theorem r47_hnorm_false_at_52 :
    ¬ ∃ s : List Hub, Balanced s ∧ Capped s ∧ stateSize s = 52 ∧
        Aobj T52 ≤ Aobj (backboneU s) := by
  rintro ⟨s, hbal, hcap, hsz, hle⟩
  -- Single-hub exclusion: length must be exactly 1.
  have hlen1 : s.length = 1 := by
    rcases Nat.lt_or_ge s.length 1 with h | h
    · -- length 0 : s = [], size 0 ≠ 52
      have hnil : s = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hnil] at hsz
      simp only [stateSize, List.map_nil, List.sum_nil] at hsz
      omega
    · rcases Nat.lt_or_ge s.length 2 with h2 | h2
      · omega
      · -- length >= 2 : size >= 92 > 52
        have := capped_two_hub_size_ge_92 s hbal hcap h2
        omega
  -- Extract the single hub.
  obtain ⟨h, rfl⟩ : ∃ h, s = [h] := by
    match s, hlen1 with
    | [h], _ => exact ⟨h, rfl⟩
  -- Single-hub bound through the tie machinery.
  have hbound : Aobj (backboneU [h]) ≤ Aobj (tieArgmax (stateSize [h])) :=
    singleHub_le_tieArgmax h hbal hcap
  rw [hsz] at hbound
  -- Chain: Aobj T52 <= Aobj (backboneU [h]) <= Aobj (tieArgmax 52) < Aobj T52.
  have hchain : Aobj T52 < Aobj T52 :=
    lt_of_le_of_lt (le_trans hle hbound) tieArgmax_52_lt_T52
  exact lt_irrefl _ hchain

/-- **The capstone `Hnorm` hypothesis is FALSE.**  `conjecture1_of_Hnorm` (`R47TieArgmax.lean:119`)
    reduces conjecture 1 to exactly this universally-quantified statement; instantiating it at the
    four-core witness `T52` (with `usize_T52`) contradicts `r47_hnorm_false_at_52`.  Hence `hwh` --
    the sole open input to `Hnorm` -- is unprovable.  conjecture1_proved = False. -/
theorem hnorm_capstone_false :
    ¬ (∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧
        stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)) := by
  intro H
  obtain ⟨s, hbal, hcap, hsz, hle⟩ := H T52
  rw [usize_T52] at hsz
  exact r47_hnorm_false_at_52 ⟨s, hbal, hcap, hsz, hle⟩

end Step3
end R3Cert
