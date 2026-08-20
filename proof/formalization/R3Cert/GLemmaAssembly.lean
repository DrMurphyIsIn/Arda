import R3Cert.CappedJointSkeleton

/-!
  # g-lemma step of the capped-joint induction (assembly bridge, 2026-08-20)

  Connects the abstract `gstep_le_one` (`CappedJointSkeleton`) to the *actual* g-lemma
  `g(B) = F_B·(1+μ_B/3)¹¹ ≤ γ` for a node `B`, via the cavity recursion
  `F_B = W·a_B¹¹·∏F_c` and the induction hypothesis `∏F_c ≤ ∏Bcap` (each child factor
  bounded by its cap).  With `base := (1+μ_B/3)·a_B` (the `gstep_base` identity),

      g(B) = F_B·(1+μ_B/3)¹¹ = W·base¹¹·(∏F_c),

  so `∏F_c ≤ Pbc = ∏Bcap` and `gstep_le_one` give `g(B) ≤ W·(W(5/3)¹¹) = γ`. This is the
  g-lemma half of the inductive step, abstract in the child products `(PF, Pbc, Pgl)` —
  the list-level `∏F_c ≤ ∏Bcap ≤ 1`, `∏Bcap ≤ ∏glemma` facts are the remaining bridge.
  Conditional only on `Case2Property`.  `conjecture1_proved = False`.
-/

namespace R3Cert.GLemmaAssembly

open R3Cert.GStepCore R3Cert.CappedJoint

/-- **The g-lemma inductive step.** Given the recursion `F_B = W·aB¹¹·PF`, `PF = ∏F_c`, the
    IH bounds `PF ≤ Pbc = ∏Bcap ≤ 1` and `Pbc ≤ Pgl = ∏glemma`, and `Case2Property`, the
    node satisfies the g-lemma `g(B) = F_B·(1+μ_B/3)¹¹ ≤ γ = W²·(5/3)¹¹`. -/
theorem glemma_step (h2 : Case2Property) {aB PF muB Pbc Pgl : ℚ}
    (hb0 : 0 ≤ (1 + muB / 3) * aB)
    (hPbc0 : 0 ≤ Pbc) (hPFbc : PF ≤ Pbc) (hPbc1 : Pbc ≤ 1)
    (hPgl0 : 0 ≤ Pgl) (hPbcgl : Pbc ≤ Pgl) :
    (W * aB ^ 11 * PF) * (1 + muB / 3) ^ 11 ≤ W ^ 2 * (5 / 3) ^ 11 := by
  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  have hW0 : (0 : ℚ) ≤ W := by norm_num [W]
  set base := (1 + muB / 3) * aB with hbase
  have hg : (W * aB ^ 11 * PF) * (1 + muB / 3) ^ 11 = W * base ^ 11 * PF := by
    rw [hbase]; ring
  rw [hg]
  have hb11 : (0 : ℚ) ≤ base ^ 11 := pow_nonneg hb0 11
  have hWb0 : (0 : ℚ) ≤ W * base ^ 11 := mul_nonneg hW0 hb11
  have hstep := gstep_le_one h2 hb0 hPbc0 hPbc1 hPgl0 hPbcgl
  rw [div_le_one hden] at hstep
  calc W * base ^ 11 * PF
      ≤ W * base ^ 11 * Pbc := mul_le_mul_of_nonneg_left hPFbc hWb0
    _ = W * (base ^ 11 * Pbc) := by ring
    _ ≤ W * (W * (5 / 3) ^ 11) := mul_le_mul_of_nonneg_left hstep hW0
    _ = W ^ 2 * (5 / 3) ^ 11 := by ring

end R3Cert.GLemmaAssembly
