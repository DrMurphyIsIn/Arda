/-
  R47 R6 ARBITRARY-PAIR balancing transfer -- the payoff of arm-permutation invariance.

  `Aobj_balance_le` (#118) only compares the FIRST TWO arms of a hub.  Composing it with
  arm-permutation invariance `Aobj_backbone_arm_perm` (R47ArmPerm) lifts it to a transfer
  between ANY two arms: bring the pair to the front by a permutation, apply the first-two
  step, permute back.

    * `Aobj_transfer_le`      -- single arbitrary-pair transfer is `Aobj`-monotone.
    * `TransferStep`          -- the arbitrary-pair transfer relation on hub-states
                                (up to arm reordering).  Generalizes `BalanceStep` (#120),
                                which is the identity-permutation, first-two-arms case.
    * `Aobj_transferStep_le`  -- one `TransferStep` is `Aobj`-monotone.
    * `Aobj_transferStar_le`  -- THE engine: the reflexive-transitive closure of
                                `TransferStep` is `Aobj`-monotone.  Any finite sequence of
                                arbitrary-pair transfers does not decrease `Aobj`.

  HONEST SCOPE.  Together with the termination measure + floor (R47R6BalanceTermination),
  what remains to discharge `Hreach` (hence single-hub `Hnorm`) is the PROGRESS lemma:
  whenever an all-arms-`>=3` distribution is not balanced-to-within-1, some `TransferStep`
  applies.  Not proved here.

  Self-contained; genuine proof (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47ArmPerm
import R3Cert.R47R6BalanceLeCert

namespace R3Cert
namespace Step3

open RTree

/-- **Single arbitrary-pair transfer is `Aobj`-monotone.**  If `arms` contains arms `a` and
    `b` (i.e. `arms ~ a :: b :: rest`) with `3 <= a`, `a + 2 <= b`, and `arms'` is the result
    of moving one cherry from the `b`-arm to the `a`-arm (`arms' ~ (a+1) :: (b-1) :: rest`),
    then `Aobj` does not decrease.  Proof: permute the pair to the front (`Aobj_backbone_arm_perm`),
    apply `Aobj_balance_le`, permute back. -/
theorem Aobj_transfer_le {arms arms' : List ℕ} (a b : ℕ) (rest : List ℕ) (c : ℕ)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b)
    (hperm : arms.Perm (a :: b :: rest)) (hperm' : arms'.Perm ((a + 1) :: (b - 1) :: rest))
    (hd6 : 6 ≤ arms.length + c) :
    Aobj (backboneU [(arms, c)]) ≤ Aobj (backboneU [(arms', c)]) := by
  have hlen : arms.length = (a :: b :: rest).length := hperm.length_eq
  calc Aobj (backboneU [(arms, c)])
      = Aobj (backboneU [(a :: b :: rest, c)]) := Aobj_backbone_arm_perm c hperm
    _ ≤ Aobj (backboneU [((a + 1) :: (b - 1) :: rest, c)]) :=
          Aobj_balance_le a b rest c ha hb (hlen ▸ hd6)
    _ = Aobj (backboneU [(arms', c)]) := (Aobj_backbone_arm_perm c hperm').symm

/-- The arbitrary-pair transfer relation on single-hub states (up to arm reordering).
    Generalizes `BalanceStep` (#120), which is the first-two-arms, identity-permutation case. -/
def TransferStep (s s' : List Hub) : Prop :=
  ∃ (a b : ℕ) (rest arms arms' : List ℕ) (c : ℕ),
    3 ≤ a ∧ a + 2 ≤ b ∧ 6 ≤ arms.length + c ∧
    arms.Perm (a :: b :: rest) ∧ arms'.Perm ((a + 1) :: (b - 1) :: rest) ∧
    s = [(arms, c)] ∧ s' = [(arms', c)]

/-- One `TransferStep` does not decrease `Aobj`. -/
theorem Aobj_transferStep_le {s s' : List Hub} (h : TransferStep s s') :
    Aobj (backboneU s) ≤ Aobj (backboneU s') := by
  obtain ⟨a, b, rest, arms, arms', c, ha, hb, hd, hp, hp', rfl, rfl⟩ := h
  exact Aobj_transfer_le a b rest c ha hb hp hp' hd

/-- **Arbitrary-pair transfer induction.**  The reflexive-transitive closure of
    `TransferStep` is `Aobj`-monotone: any finite sequence of arbitrary-pair balancing
    transfers does not decrease `Aobj`.  This is the engine for the single-hub balancing
    reduction (`Hnorm`). -/
theorem Aobj_transferStar_le {s s' : List Hub}
    (h : Relation.ReflTransGen TransferStep s s') :
    Aobj (backboneU s) ≤ Aobj (backboneU s') := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (Aobj_transferStep_le hstep)

end Step3
end R3Cert
