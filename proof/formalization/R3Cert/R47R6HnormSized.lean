import Mathlib
import R3Cert.R47R6TransferArb
import R3Cert.R47R6HnormSingleHub
import R3Cert.R47StepSize

/-!
  # Size-preserving single-hub Hnorm (fixed-n bridge)

  `conjecture1_of_layers_fixedN` (R47TopCapstoneFixedN) needs its normalization layer to
  be SIZE-PRESERVING (`stateSize s = usize t`).  The single-hub balancing machinery is
  exactly that: an arm-pair transfer `(a,b) → (a+1,b-1)` keeps the arm COUNT (list length)
  and arm-load SUM fixed (`a + b = (a+1) + (b-1)`), and the cherry load `c` untouched, so
  it conserves `hubSize = 1 + (len + 2·sum) + 2c`, hence `stateSize`.  This was implicit in
  the machinery (`transferStep_dest` records `arms'.length = arms.length`) but never
  lemmatized.

  This file adds the conservation lemmas — `TransferStep.stateSize_eq` and its chain lift
  `chain_transfer_stateSize_eq` — and packages `single_hub_reaches_balanced` into a
  size-preserving single-hub Hnorm: an all-arms-`≥3` single hub (many-arm regime) is
  `Aobj`-dominated by an `ArmBalanced` (within-one) single hub OF THE SAME SIZE.

  HONEST SCOPE.  This closes the SIZE bookkeeping for the single-hub case only.  The full
  `Hnorm` still needs (i) the arbitrary-tree → hub-state reduction (the multi-paper GTS/
  Kelmans step) and (ii) the `{k,k+1} → {4,5}` rate step (`ArmBalanced` gives within-one,
  not the extremal `{4,5}` yet).  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

/-- **`TransferStep` conserves size.**  The arm-pair transfer keeps arm count and arm-load
    sum fixed (`a + b = (a+1) + (b-1)`, `b ≥ a+2 ≥ 5 > 0`) and the cherry load untouched. -/
theorem TransferStep.stateSize_eq {s s' : List Hub} (h : TransferStep s s') :
    stateSize s' = stateSize s := by
  obtain ⟨a, b, rest, arms, arms', c, ha, hb, _, hperm, hperm', rfl, rfl⟩ := h
  have hlen : arms'.length = arms.length := by
    rw [hperm.length_eq, hperm'.length_eq]
  have hsum : arms'.sum = arms.sum := by
    rw [hperm.sum_eq, hperm'.sum_eq]
    simp only [List.sum_cons]
    omega
  simp only [stateSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hubSize,
    hlen, hsum]

/-- Size is conserved along an arbitrary-pair transfer chain. -/
theorem chain_transfer_stateSize_eq {s s' : List Hub}
    (h : Relation.ReflTransGen TransferStep s s') : stateSize s' = stateSize s := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [TransferStep.stateSize_eq hstep]; exact ih

/-- **Size-preserving single-hub Hnorm.**  Every all-arms-`≥3` single hub (many-arm
    regime) is `Aobj`-dominated by an `ArmBalanced` single hub of the SAME `stateSize`
    (same arm count, same arm-load sum, same cherry load) — the size-preserving
    normalization the fixed-n capstone consumes for single-hub inputs.

    HONEST: single-hub only, and `ArmBalanced` (within-one) not yet the extremal `{4,5}`. -/
theorem single_hub_Hnorm_sized {arms : List ℕ} {c : ℕ}
    (hfloor : ∀ x ∈ arms, 3 ≤ x) (hd6 : 6 ≤ arms.length + c) :
    ∃ arms_bal, ArmBalanced arms_bal ∧
      stateSize [(arms_bal, c)] = stateSize [(arms, c)] ∧
      Aobj (backboneU [(arms, c)]) ≤ Aobj (backboneU [(arms_bal, c)]) := by
  obtain ⟨arms_bal, hbal, hreach⟩ := single_hub_reaches_balanced hfloor hd6
  exact ⟨arms_bal, hbal, chain_transfer_stateSize_eq hreach, Aobj_transferStar_le hreach⟩

end Step3
end R3Cert
