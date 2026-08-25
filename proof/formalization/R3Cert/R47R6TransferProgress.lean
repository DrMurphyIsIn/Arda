/-
  R47 R6 balancing-transfer PROGRESS -- the remaining crux for single-hub reachability.

  A single hub whose arms are all `>= 3` but NOT balanced-to-within-1 always admits a
  `TransferStep` (R47R6TransferArb).  Together with the termination measure + well-foundedness
  and the `3 <= arm` floor (R47R6BalanceTermination), this is what makes the balancing process
  reach a balanced form: well-foundedness says every transfer chain terminates, and PROGRESS
  says a terminal (no-step) state must already be balanced.

    * `ArmBalanced`             -- arms are balanced to within one (`x <= y + 1` for all pairs).
    * `transferStep_progress`   -- all-arms-`>=3` + not `ArmBalanced` + many-arm regime
                                  => some `TransferStep` applies.

  The extraction: `¬ ArmBalanced` gives two arms `a, b` with `a + 2 <= b` (both `>= 3` by the
  floor); `perm_cons_erase` twice reorders `arms ~ a :: b :: rest`, which is exactly a
  `TransferStep` to `(a+1) :: (b-1) :: rest`.

  HONEST SCOPE.  This is the progress half.  Assembling well-foundedness + progress into the
  final "every all-arms-`>=3` hub reaches a balanced one, which dominates in `Aobj`" statement
  (single-hub `Hnorm`) is the remaining step (well-founded recursion; not in this file).

  Self-contained; genuine proof (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6TransferArb

namespace R3Cert
namespace Step3

open RTree

/-- A list of arm lengths is balanced to within one: any two arms differ by at most 1. -/
def ArmBalanced (arms : List ℕ) : Prop := ∀ x ∈ arms, ∀ y ∈ arms, x ≤ y + 1

/-- **Progress.**  A single hub with all arms `>= 3` that is not balanced-to-within-1 (and is
    in the many-arm regime `6 <= |arms| + c`) admits a `TransferStep`: there is a strictly
    more-balanced neighbour.  Contrapositively, a hub that admits NO transfer is balanced. -/
theorem transferStep_progress {arms : List ℕ} {c : ℕ}
    (hfloor : ∀ x ∈ arms, 3 ≤ x) (hunbal : ¬ ArmBalanced arms)
    (hd6 : 6 ≤ arms.length + c) :
    ∃ s', TransferStep [(arms, c)] s' := by
  -- extract the unbalanced pair: `x` large, `y` small, with `y + 1 < x`
  simp only [ArmBalanced, not_forall, not_le, exists_prop] at hunbal
  obtain ⟨x, hx, y, hy, hxy⟩ := hunbal
  have hab : y + 2 ≤ x := by omega
  -- reorder `arms` so the small/large pair is at the front
  have hxin : x ∈ arms.erase y := (List.mem_erase_of_ne (by omega : x ≠ y)).mpr hx
  have hperm : arms.Perm (y :: x :: (arms.erase y).erase x) :=
    (List.perm_cons_erase hy).trans ((List.perm_cons_erase hxin).cons y)
  exact ⟨[((y + 1) :: (x - 1) :: (arms.erase y).erase x, c)],
    y, x, (arms.erase y).erase x, arms, (y + 1) :: (x - 1) :: (arms.erase y).erase x, c,
    hfloor y hy, hab, hd6, hperm, List.Perm.refl _, rfl, rfl⟩

end Step3
end R3Cert
