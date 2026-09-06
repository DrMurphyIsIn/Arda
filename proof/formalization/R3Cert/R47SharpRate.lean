/-
  R3Cert.R47SharpRate -- assembling the per-size domination (`Hdom`) from the two closed cores.

  `SharpRateNF tie` (R47HdomBridge) is `Hdom`: every merge-normal Balanced+Capped state `s` is
  dominated by the tie at its own size.  This file discharges the LENGTH-1 slice at ALIGNED sizes:
  an arbitrary Balanced+Capped single hub `[(arms, c)]` (arms in {4,5}, >= 5 of them, `c <= 5`) whose
  size is `1 + 11K` reduces -- via arm-permutation invariance (`Aobj_backbone_arm_perm`) to the
  `(a,b)`-count canonical form `hubState (count 5) (count 4) c` -- to the M3 envelope `singleHub_le_tie`,
  hence is dominated by the broadened tie `tieState K (mOf K)`.

  This is the clean, aligned length-1 case.  The length-2 (`twoHub_le_tie`) and general cases require the
  tie family off the `n ≡ 1 mod 11` lattice (the open non-aligned-n layer), so full `SharpRateNF` is not
  discharged here.  `conjecture1_proved = False`.  Self-contained leaf.
-/
import Mathlib
import R3Cert.R47SingleHub2D
import R3Cert.R47ArmPerm
import R3Cert.R47Step
import R3Cert.R47Capped
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

/-- A Balanced arm list (every load in `{4,5}`) is a permutation of its `(count 5)` fives followed by
    its `(count 4)` fours -- the canonical `(a,b)` form. -/
theorem balancedArms_perm (arms : List ℕ) (h : BalancedArms arms) :
    arms.Perm (List.replicate (arms.count 5) 5 ++ List.replicate (arms.count 4) 4) := by
  rw [List.perm_iff_count]
  intro x
  rw [List.count_append, List.count_replicate, List.count_replicate]
  rcases eq_or_ne x 5 with hx5 | hx5
  · subst hx5; simp
  · rcases eq_or_ne x 4 with hx4 | hx4
    · subst hx4; simp
    · have hz : arms.count x = 0 :=
        List.count_eq_zero.mpr (fun hxin => by rcases h x hxin with h | h <;> simp_all)
      simp [hz, hx5, hx4, Ne.symm hx5, Ne.symm hx4]

/-- Every load in a Balanced arm list is 4 or 5, so its length is `count 5 + count 4`. -/
theorem balancedArms_length (arms : List ℕ) (h : BalancedArms arms) :
    arms.length = arms.count 5 + arms.count 4 := by
  have := (balancedArms_perm arms h).length_eq
  simpa [List.length_append] using this

/-- **The length-1 `Hdom` slice (aligned sizes).**  An arbitrary Balanced+Capped single hub `[(arms, c)]`
    at aligned size `11·(count 5) + 9·(count 4) + 2c = 11K` is dominated by the broadened tie
    `tieState K (mOf K)`.  Arm-permutation to the `(a,b)`-count canonical form, then `singleHub_le_tie`. -/
theorem singleHub_dominated (arms : List ℕ) (c K : ℕ) (hbal : BalancedArms arms) (hc : c ≤ 5)
    (hcap : 5 ≤ arms.length)
    (hsize : 11 * arms.count 5 + 9 * arms.count 4 + 2 * c = 11 * K) :
    Aobj (backboneU [(arms, c)]) ≤ Aobj (backboneU (tieState K (mOf K))) := by
  have hlen : arms.length = arms.count 5 + arms.count 4 := balancedArms_length arms hbal
  rw [Aobj_backbone_arm_perm c (balancedArms_perm arms hbal)]
  exact singleHub_le_tie (arms.count 5) (arms.count 4) c K hc (by omega) hsize

/-- The size of a Balanced single hub in `(a,b,c)`-count form: `1 + 11·(count 5) + 9·(count 4) + 2c`. -/
theorem stateSize_singleHub (arms : List ℕ) (c : ℕ) (hbal : BalancedArms arms) :
    stateSize [(arms, c)] = 1 + 11 * arms.count 5 + 9 * arms.count 4 + 2 * c := by
  have hsum : arms.sum = 5 * arms.count 5 + 4 * arms.count 4 := by
    have h := (balancedArms_perm arms hbal).sum_eq
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul] at h
    omega
  have hlen : arms.length = arms.count 5 + arms.count 4 := balancedArms_length arms hbal
  simp only [stateSize, hubSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hsum, hlen]; ring

/-- The per-size tie family on the ALIGNED lattice: at `n = 1 + 11K`, the broadened tie
    `tieState K (mOf K)` (`K = (n-1)/11`).  (Off the `n ≡ 1 mod 11` lattice this is the open
    non-aligned-n layer; there the definition is a placeholder, not the true maximizer.) -/
noncomputable def alignedTie (n : ℕ) : UTree := backboneU (tieState ((n - 1) / 11) (mOf ((n - 1) / 11)))

/-- **The length-1 `SharpRateNF` slice (aligned sizes), against the tie family at the state's own size.**
    A Balanced+Capped single hub `[(arms, c)]` whose size is aligned (`11 ∣ 9·count 4 + 2c`) is dominated
    by `alignedTie (stateSize [(arms, c)])`.  This is exactly the length-1 case of `Hdom`, discharged by
    the M3 envelope; the multi-hub cases need the tie off the aligned lattice (open). -/
theorem sharpRate_singleHub_aligned (arms : List ℕ) (c : ℕ) (hbal : BalancedArms arms) (hc : c ≤ 5)
    (hcap : 5 ≤ arms.length) (halign : 11 ∣ (9 * arms.count 4 + 2 * c)) :
    Aobj (backboneU [(arms, c)]) ≤ Aobj (alignedTie (stateSize [(arms, c)])) := by
  obtain ⟨K, hK⟩ := halign
  have hsz : stateSize [(arms, c)] = 1 + 11 * (arms.count 5 + K) := by
    rw [stateSize_singleHub arms c hbal]; omega
  have hfit : 11 * arms.count 5 + 9 * arms.count 4 + 2 * c = 11 * (arms.count 5 + K) := by omega
  rw [alignedTie, hsz]
  have hidx : (1 + 11 * (arms.count 5 + K) - 1) / 11 = arms.count 5 + K := by omega
  rw [hidx]
  exact singleHub_dominated arms c (arms.count 5 + K) hbal hc hcap hfit

end Step3
end R3Cert
