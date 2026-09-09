/-
  A3(2) BRIDGE, stage 2(iii): the exists-assembly -- PairCollapse6 is a THEOREM.

  Assembles the frozen selection table (candidate + selection dichotomy per `d = cA + cb`), the
  Balanced-arms transport (R47PC6Transport), and the emitted reduction certificates
  (R47PC6Reduce) into `pairCollapse6` : PairCollapse6.  For a Balanced+Capped pair
  `(armsA,cA),(armsB,cb)` set the count coordinates `a5 = armsA.count 5`, etc.; the target hub is
  the count form `hubArms (a5+b5+x) (a4+b4+y)` with cherry `c'` from the table; its Balanced /
  Capped / `hubSize` obligations are arithmetic, and the three clause inequalities come from
  `pair_stats_count` (transport the pair to count form) composed with the matching `pc6r_*`
  reduction lemma.

  This closes the last named open certificate on the m>=3 front: with `pairCollapse6`, the
  telescope `hdom_of_pairCollapse6_and_singleHubDom` (R47WPair6) gives `Hdom` at every length.
  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47PC6Transport
import R3Cert.R47PC6Reduce
import R3Cert.R47WPair6

namespace R3Cert
namespace Step3
namespace PC6

open RTree

/-! ### `hubArms` structural facts -/

theorem balancedArms_hubArms (a b : ℕ) : BalancedArms (hubArms a b) := by
  intro j hj
  simp only [hubArms, List.mem_append, List.mem_replicate] at hj
  rcases hj with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem length_hubArms (a b : ℕ) : (hubArms a b).length = a + b := by
  simp [hubArms]

theorem hubSize_hubArms (a b c : ℕ) :
    hubSize (hubArms a b, c) = 1 + (a + b) + 2 * (5 * a + 4 * b) + 2 * c := by
  simp only [hubSize, hubArms, List.length_append, List.length_replicate, List.sum_append]
  rw [show (List.replicate a 5).sum = 5 * a by rw [List.sum_replicate]; ring,
      show (List.replicate b 4).sum = 4 * b by rw [List.sum_replicate]; ring]
  omega

theorem count_sum_eq_length (arms : List ℕ) (h : BalancedArms arms) :
    arms.count 5 + arms.count 4 = arms.length := by
  have hl := (balancedArms_perm arms h).length_eq
  simp only [List.length_append, List.length_replicate] at hl
  omega

/-- `hubSize` of a Balanced hub in count coordinates. -/
theorem hubSize_count (arms : List ℕ) (c : ℕ) (h : BalancedArms arms) :
    hubSize (arms, c) = hubSize (hubArms (arms.count 5) (arms.count 4), c) := by
  have hlen : arms.count 5 + arms.count 4 = arms.length := count_sum_eq_length arms h
  have hsum : 5 * arms.count 5 + 4 * arms.count 4 = arms.sum := by
    have hp := balancedArms_perm arms h
    have := hp.sum_eq
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul] at this
    omega
  rw [hubSize_hubArms]
  simp only [hubSize]
  omega

end PC6
end Step3
end R3Cert
