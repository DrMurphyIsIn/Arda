/-
  The per-hub branch-ceiling step `CeilStep` (BGSCLHub), degree ≤ 6.

  For a hub of root-degree `d ≤ 6`, the concave-log tangent at the EXACT all-cherry slope `μ* = 3/(4d-1)` (which
  lies in the invariant price interval `I` for `d ≤ 6`) makes the child `S`-terms cancel exactly against the child
  SCL bound, giving `bell (node cs) ≤ A_d := (d-1)(log(3/2) − 2F*) + log((4d-1)/(3d)) − F*`.  `A_d ≤ 0` is a clean
  rational log inequality — strict for `d ≤ 5`, and EXACTLY `0` at `d = 6` (the arithmetic tie
  `(3/2)^5·(23/18) = 621/64`, i.e. the `n = 11` degree-6 near-broom).  This closes the ceiling step for `d ≤ 6`.
  (The `d ≥ 7` tail is the reachable-`y` envelope, gated in Telperion by `HighDegreeTailCertificate`.)

  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep
import R3Cert.BGSCLHub

namespace R3Cert
namespace BGSCL

/-- All-cherry ceiling, d=2: `A_2 = log(3/2) + log(7/6) − 3F* ≤ 0`. -/
theorem acl_d2 : Real.log (3/2) + Real.log (7/6) - 3*FSTAR ≤ 0 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(Real.log (3/2) + Real.log (7/6) - 3*(Real.log (621/64)/11))
      = Real.log ((3/2)^11 * (7/6)^11 * (64/621)^3) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^11 * (7/6)^11 * (64/621)^3) ≤ 0 :=
    Real.log_nonpos (by positivity) (by norm_num)
  nlinarith [hcomb, hX]

/-- All-cherry ceiling, d=3: `A_3 = 2 log(3/2) + log(11/9) − 5F* ≤ 0`. -/
theorem acl_d3 : 2*Real.log (3/2) + Real.log (11/9) - 5*FSTAR ≤ 0 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(2*Real.log (3/2) + Real.log (11/9) - 5*(Real.log (621/64)/11))
      = Real.log ((3/2)^22 * (11/9)^11 * (64/621)^5) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^22 * (11/9)^11 * (64/621)^5) ≤ 0 :=
    Real.log_nonpos (by positivity) (by norm_num)
  nlinarith [hcomb, hX]

/-- All-cherry ceiling, d=4: `A_4 = 3 log(3/2) + log(5/4) − 7F* ≤ 0`. -/
theorem acl_d4 : 3*Real.log (3/2) + Real.log (5/4) - 7*FSTAR ≤ 0 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(3*Real.log (3/2) + Real.log (5/4) - 7*(Real.log (621/64)/11))
      = Real.log ((3/2)^33 * (5/4)^11 * (64/621)^7) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^33 * (5/4)^11 * (64/621)^7) ≤ 0 :=
    Real.log_nonpos (by positivity) (by norm_num)
  nlinarith [hcomb, hX]

/-- All-cherry ceiling, d=5: `A_5 = 4 log(3/2) + log(19/15) − 9F* ≤ 0`. -/
theorem acl_d5 : 4*Real.log (3/2) + Real.log (19/15) - 9*FSTAR ≤ 0 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(4*Real.log (3/2) + Real.log (19/15) - 9*(Real.log (621/64)/11))
      = Real.log ((3/2)^44 * (19/15)^11 * (64/621)^9) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^44 * (19/15)^11 * (64/621)^9) ≤ 0 :=
    Real.log_nonpos (by positivity) (by norm_num)
  nlinarith [hcomb, hX]

/-- All-cherry ceiling, d=6: `A_6 = 5 log(3/2) + log(23/18) − 11F* ≤ 0` — EXACTLY `0` (the tie
    `(3/2)^5·(23/18) = 621/64`). -/
theorem acl_d6 : 5*Real.log (3/2) + Real.log (23/18) - 11*FSTAR ≤ 0 := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(5*Real.log (3/2) + Real.log (23/18) - 11*(Real.log (621/64)/11))
      = Real.log ((3/2)^55 * (23/18)^11 * (64/621)^11) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^55 * (23/18)^11 * (64/621)^11) ≤ 0 :=
    Real.log_nonpos (by positivity) (by norm_num)
  nlinarith [hcomb, hX]

/-- `bell cherry ≤ 0` (`log(3/2) − 2F* ≤ 0`). -/
theorem bell_cherry_nonpos : bell cherry ≤ 0 := by
  rw [bell_cherry]
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(Real.log (3/2) - 2*(Real.log (621/64)/11))
      = Real.log ((3/2)^11 * (64/621)^2) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hX : Real.log ((3/2)^11 * (64/621)^2) ≤ 0 := Real.log_nonpos (by positivity) (by norm_num)
  nlinarith [hcomb, hX]

/-- **Ceiling step, d=2** (`cs.length = 1`).  Leaf child ⟹ hub `= cherry` (`bell cherry ≤ 0`); non-leaf ⟹
    the all-cherry decouple at `μ* = 3/7` gives `bell (node cs) ≤ A_2 = log(3/2) + log(7/6) − 3F* ≤ 0`. -/
theorem ceil_hub_d2 {cs : List Branch} (hlen : cs.length = 1)
    (hchild : ∀ c ∈ cs, PSCLne c) : bell (Branch.node cs) ≤ 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
    cases cs with
    | nil => simp at hlen
    | cons c t => cases t with
      | nil => exact ⟨c, rfl⟩
      | cons _ _ => simp at hlen
  have hc1 : PSCLne c := hchild c (List.mem_cons.mpr (Or.inl rfl))
  by_cases hc : c = Branch.node []
  · subst hc
    show bell (Branch.node [Branch.node []]) ≤ 0
    have hch : Branch.node [Branch.node []] = cherry := rfl
    rw [hch]; exact bell_cherry_nonpos
  · set S := (([c] : List Branch).map bY).sum with hSdef
    have hSnn : 0 ≤ S := by
      rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
      obtain ⟨z, _, rfl⟩ := hx; exact bY_nonneg z
    have hlenR : (([c] : List Branch).length : ℝ) = 1 := by norm_num
    have hchild2 : ∀ x ∈ ([c] : List Branch), bV (3/7) x ≤ bV (3/7) cherry := by
      intro x hx; rw [List.mem_singleton] at hx; subst hx
      exact hc1 hc (3/7) (by constructor <;> norm_num)
    have hsum : (([c] : List Branch).map bell).sum
        ≤ (([c] : List Branch).length : ℝ) * bV (3/7) cherry - (3/7) * (([c] : List Branch).map bY).sum :=
      child_bell_sum_le (3/7) [c] hchild2
    rw [hlenR, ← hSdef] at hsum
    have htan := bell_node_tangent [c] (s0 := 1/3) (by norm_num)
    rw [hlenR, ← hSdef] at htan
    have hlogeq : Real.log (1 + 1/3/((1:ℝ)+1)) = Real.log (7/6) := by norm_num
    have hden : ((1:ℝ)+1)+1/3 = 7/3 := by norm_num
    rw [hlogeq, hden] at htan
    have hRHS : bell (Branch.node [c])
        ≤ (1 * bV (3/7) cherry - (3/7) * S) + (Real.log (7/6) + (S - 1/3)/(7/3) - FSTAR) := by
      linarith [htan, hsum]
    have hbridge : (1 * bV (3/7) cherry - (3/7) * S) + (Real.log (7/6) + (S - 1/3)/(7/3) - FSTAR)
        = Real.log (3/2) + Real.log (7/6) - 3*FSTAR := by
      rw [bV, bell_cherry, bY_cherry]; ring
    linarith [hRHS, hbridge, acl_d2]

/-- **Ceiling step, d=3** (`cs.length = 2`).  `μ* = 3/11 ∈ I`, `s0 = 2/3` ⟹ `bell (node cs) ≤ A_3 ≤ 0`. -/
theorem ceil_hub_d3 {cs : List Branch} (hlen : cs.length = 2)
    (hchild : ∀ c ∈ cs, PSCLne c) : bell (Branch.node cs) ≤ 0 := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨z, _, rfl⟩ := hx; exact bY_nonneg z
  have hlenR : (cs.length : ℝ) = 2 := by exact_mod_cast hlen
  have hchild2 : ∀ c ∈ cs, bV (3/11) c ≤ bV (3/11) cherry := by
    intro c hc
    by_cases hleaf : c = Branch.node []
    · subst hleaf; exact leaf_le_cherry (by norm_num)
    · exact hchild c hc hleaf (3/11) (by constructor <;> norm_num)
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (3/11) cherry - (3/11) * (cs.map bY).sum :=
    child_bell_sum_le (3/11) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 2/3) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 2/3/((2:ℝ)+1)) = Real.log (11/9) := by norm_num
  have hden : ((2:ℝ)+1)+2/3 = 11/3 := by norm_num
  rw [hlogeq, hden] at htan
  have hRHS : bell (Branch.node cs)
      ≤ (2 * bV (3/11) cherry - (3/11) * S) + (Real.log (11/9) + (S - 2/3)/(11/3) - FSTAR) := by
    linarith [htan, hsum]
  have hbridge : (2 * bV (3/11) cherry - (3/11) * S) + (Real.log (11/9) + (S - 2/3)/(11/3) - FSTAR)
      = 2*Real.log (3/2) + Real.log (11/9) - 5*FSTAR := by
    rw [bV, bell_cherry, bY_cherry]; ring
  linarith [hRHS, hbridge, acl_d3]

/-- **Ceiling step, d=4** (`cs.length = 3`).  `μ* = 1/5 ∈ I`, `s0 = 1` ⟹ `bell (node cs) ≤ A_4 ≤ 0`. -/
theorem ceil_hub_d4 {cs : List Branch} (hlen : cs.length = 3)
    (hchild : ∀ c ∈ cs, PSCLne c) : bell (Branch.node cs) ≤ 0 := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨z, _, rfl⟩ := hx; exact bY_nonneg z
  have hlenR : (cs.length : ℝ) = 3 := by exact_mod_cast hlen
  have hchild2 : ∀ c ∈ cs, bV (1/5) c ≤ bV (1/5) cherry := by
    intro c hc
    by_cases hleaf : c = Branch.node []
    · subst hleaf; exact leaf_le_cherry (by norm_num)
    · exact hchild c hc hleaf (1/5) (by constructor <;> norm_num)
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (1/5) cherry - (1/5) * (cs.map bY).sum :=
    child_bell_sum_le (1/5) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 1) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 1/((3:ℝ)+1)) = Real.log (5/4) := by norm_num
  have hden : ((3:ℝ)+1)+1 = 5 := by norm_num
  rw [hlogeq, hden] at htan
  have hRHS : bell (Branch.node cs)
      ≤ (3 * bV (1/5) cherry - (1/5) * S) + (Real.log (5/4) + (S - 1)/5 - FSTAR) := by
    linarith [htan, hsum]
  have hbridge : (3 * bV (1/5) cherry - (1/5) * S) + (Real.log (5/4) + (S - 1)/5 - FSTAR)
      = 3*Real.log (3/2) + Real.log (5/4) - 7*FSTAR := by
    rw [bV, bell_cherry, bY_cherry]; ring
  linarith [hRHS, hbridge, acl_d4]

/-- **Ceiling step, d=5** (`cs.length = 4`).  `μ* = 3/19 ∈ I`, `s0 = 4/3` ⟹ `bell (node cs) ≤ A_5 ≤ 0`. -/
theorem ceil_hub_d5 {cs : List Branch} (hlen : cs.length = 4)
    (hchild : ∀ c ∈ cs, PSCLne c) : bell (Branch.node cs) ≤ 0 := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨z, _, rfl⟩ := hx; exact bY_nonneg z
  have hlenR : (cs.length : ℝ) = 4 := by exact_mod_cast hlen
  have hchild2 : ∀ c ∈ cs, bV (3/19) c ≤ bV (3/19) cherry := by
    intro c hc
    by_cases hleaf : c = Branch.node []
    · subst hleaf; exact leaf_le_cherry (by norm_num)
    · exact hchild c hc hleaf (3/19) (by constructor <;> norm_num)
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (3/19) cherry - (3/19) * (cs.map bY).sum :=
    child_bell_sum_le (3/19) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 4/3) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 4/3/((4:ℝ)+1)) = Real.log (19/15) := by norm_num
  have hden : ((4:ℝ)+1)+4/3 = 19/3 := by norm_num
  rw [hlogeq, hden] at htan
  have hRHS : bell (Branch.node cs)
      ≤ (4 * bV (3/19) cherry - (3/19) * S) + (Real.log (19/15) + (S - 4/3)/(19/3) - FSTAR) := by
    linarith [htan, hsum]
  have hbridge : (4 * bV (3/19) cherry - (3/19) * S) + (Real.log (19/15) + (S - 4/3)/(19/3) - FSTAR)
      = 4*Real.log (3/2) + Real.log (19/15) - 9*FSTAR := by
    rw [bV, bell_cherry, bY_cherry]; ring
  linarith [hRHS, hbridge, acl_d5]

/-- **Ceiling step, d=6** (`cs.length = 5`).  `μ* = 3/23 ∈ I`, `s0 = 5/3` ⟹ `bell (node cs) ≤ A_6 = 0`
    (the exact `n=11` degree-6 tie). -/
theorem ceil_hub_d6 {cs : List Branch} (hlen : cs.length = 5)
    (hchild : ∀ c ∈ cs, PSCLne c) : bell (Branch.node cs) ≤ 0 := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨z, _, rfl⟩ := hx; exact bY_nonneg z
  have hlenR : (cs.length : ℝ) = 5 := by exact_mod_cast hlen
  have hchild2 : ∀ c ∈ cs, bV (3/23) c ≤ bV (3/23) cherry := by
    intro c hc
    by_cases hleaf : c = Branch.node []
    · subst hleaf; exact leaf_le_cherry (by norm_num)
    · exact hchild c hc hleaf (3/23) (by constructor <;> norm_num)
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (3/23) cherry - (3/23) * (cs.map bY).sum :=
    child_bell_sum_le (3/23) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 5/3) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 5/3/((5:ℝ)+1)) = Real.log (23/18) := by norm_num
  have hden : ((5:ℝ)+1)+5/3 = 23/3 := by norm_num
  rw [hlogeq, hden] at htan
  have hRHS : bell (Branch.node cs)
      ≤ (5 * bV (3/23) cherry - (3/23) * S) + (Real.log (23/18) + (S - 5/3)/(23/3) - FSTAR) := by
    linarith [htan, hsum]
  have hbridge : (5 * bV (3/23) cherry - (3/23) * S) + (Real.log (23/18) + (S - 5/3)/(23/3) - FSTAR)
      = 5*Real.log (3/2) + Real.log (23/18) - 11*FSTAR := by
    rw [bV, bell_cherry, bY_cherry]; ring
  linarith [hRHS, hbridge, acl_d6]

/-- `0 ≤ F*` (`621/64 ≥ 1`). -/
theorem fstar_nonneg : (0:ℝ) ≤ FSTAR := by
  rw [FSTAR]; exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)

/-- **The d≥7 hub-ceiling residual.**  For a hub of root-degree `d ≥ 7`, `bell (node cs) ≤ 0` given the child
    ceilings AND child SCL.  This is the ONLY residual of the whole branch-ceiling + SCL after the `d ≤ 6`
    ceilings are proven (numeric margin `+0.0015`, worst at the all-cherry hub).  It is the high-degree tail of
    the `M_d` frontier: the all-cherry price `μ* = 3/(4d-1)` falls BELOW the invariant interval `I` for `d ≥ 7`,
    so the `d ≤ 6` all-cherry decouple does not apply, and the SCL-on-`I` bound alone overshoots by `~0.004`
    (the min-`y` regime needs the reachable-`y` structure).  Gated in Telperion (`HighDegreeTailCertificate` +
    the near-broom certificates).  `conjecture1_proved = False`. -/
def CeilStepHi : Prop :=
  ∀ cs : List Branch, 6 ≤ cs.length →
    (∀ c ∈ cs, bell c ≤ 0) → (∀ c ∈ cs, PSCLne c) → bell (Branch.node cs) ≤ 0

/-- **The full per-hub ceiling step, from the d≥7 residual.**  `d ≤ 6` is PROVEN (the all-cherry decouple,
    including the exact `d = 6` arithmetic tie `acl_d6`); `d ≥ 7` is `CeilStepHi`.  Note the `d ≤ 6` ceilings
    need only the child SCL (not the child ceilings) — the child ceilings are consumed only by the tail. -/
theorem ceilStep_of_hi (hhi : CeilStepHi) : CeilStep := by
  intro cs hcc hcs
  rcases cs with _ | ⟨a, t⟩
  · rw [bell_leaf]; linarith [fstar_nonneg]
  · have h1 : 1 ≤ (a :: t).length := by simp
    rcases Nat.lt_or_ge (a :: t).length 6 with hlo | hge
    · rcases (by omega : (a :: t).length = 1 ∨ (a :: t).length = 2 ∨ (a :: t).length = 3
          ∨ (a :: t).length = 4 ∨ (a :: t).length = 5) with h | h | h | h | h
      · exact ceil_hub_d2 h hcs
      · exact ceil_hub_d3 h hcs
      · exact ceil_hub_d4 h hcs
      · exact ceil_hub_d5 h hcs
      · exact ceil_hub_d6 h hcs
    · exact hhi (a :: t) hge hcc hcs

/-- **Joint ceiling + SCL for every branch, from the d≥7 residual.**  The `d ≤ 6` ceiling — including the tight
    `n = 11` degree-6 arithmetic tie — is now PROVEN in Lean; the ENTIRE branch ceiling `∀ b, bell b ≤ 0` and the
    leaf-excluding SCL `∀ b, PSCLne b` reduce to the single high-degree-tail residual `CeilStepHi` (margin
    `+0.0015`).  `conjecture1_proved = False`. -/
theorem ceil_and_scl_of_ceilStepHi (hhi : CeilStepHi) : ∀ b, bell b ≤ 0 ∧ PSCLne b :=
  ceil_and_scl_of_ceilStep (ceilStep_of_hi hhi)

/-- The branch ceiling `∀ b, bell b ≤ 0` from the d≥7 residual. -/
theorem bell_ceiling_of_ceilStepHi (hhi : CeilStepHi) : ∀ b, bell b ≤ 0 :=
  fun b => (ceil_and_scl_of_ceilStepHi hhi b).1

/-- The SCL `∀ b, PSCLne b` from the d≥7 residual. -/
theorem scl_of_ceilStepHi (hhi : CeilStepHi) : ∀ b, PSCLne b :=
  fun b => (ceil_and_scl_of_ceilStepHi hhi b).2

end BGSCL
end R3Cert
