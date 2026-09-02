/-
  SCL FlowedHubStep assembly — the list machinery + tangent connection tying the per-degree decouple
  residuals (`BGSCLDecouple`) to the actual hub `node cs`.
  `child_bell_sum_le`: from the per-child SCL at a price `ν`, the sum bound `Σ bell(c) ≤ |cs|·bV_ν(cherry) − ν·S`.
  This feeds `bell_node_tangent` + `bY_node` + `decouple_d` to give `bV μ (node cs) ≤ bV μ cherry` for d≤6.
  (d≥7 needs the branch ceiling `bell (node cs) ≤ 0`, a separate result not yet in the SCL Lean.)
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep
import R3Cert.BGSCLDecouple
import R3Cert.BGSCLFlowed

namespace R3Cert
namespace BGSCL

/-- **The child-sum bound.**  If every child `c ∈ cs` satisfies the SCL at price `ν`
    (`bV ν c ≤ bV ν cherry`), then `Σ_c bell(c) ≤ |cs|·bV_ν(cherry) − ν·Σ_c bY(c)`.  (Since
    `bell c = bV ν c − ν·bY c ≤ bV ν cherry − ν·bY c`, summed.)  This is the list-machinery half of the
    per-hub decouple: it converts the per-child hypotheses into the single scalar `Σ bell` bound the
    tangent needs. -/
theorem child_bell_sum_le (ν : ℝ) (cs : List Branch) (h : ∀ c ∈ cs, bV ν c ≤ bV ν cherry) :
    (cs.map bell).sum ≤ (cs.length : ℝ) * bV ν cherry - ν * (cs.map bY).sum := by
  induction cs with
  | nil => simp
  | cons a t ih =>
    have ha : bell a + ν * bY a ≤ bell cherry + ν * bY cherry := by
      have h1 : bV ν a = bell a + ν * bY a := rfl
      have h2 : bV ν cherry = bell cherry + ν * bY cherry := rfl
      have := h a (List.mem_cons.mpr (Or.inl rfl)); rw [h1, h2] at this; exact this
    have iht : (t.map bell).sum ≤ (t.length : ℝ) * bV ν cherry - ν * (t.map bY).sum :=
      ih (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))
    have hVc : bV ν cherry = bell cherry + ν * bY cherry := rfl
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [hVc] at iht ⊢
    nlinarith [ha, iht]

/-- `bY b ≤ 1` for every branch (`h ≤ 1`, `bcc ≥ 0`). -/
theorem bY_le_one (b : Branch) : bY b ≤ 1 := by
  cases b with
  | node cs =>
    rw [bY_node]
    have hS : 0 ≤ (cs.map bY).sum := by
      apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
      obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
    have hlen : (0:ℝ) ≤ (cs.length:ℝ) := Nat.cast_nonneg _
    rw [div_le_one (by linarith)]; linarith

/-- A non-leaf branch `node (a :: rest)` has `bY ≤ 1/2` (denominator `≥ 2`). -/
theorem bY_nonleaf_le_half (a : Branch) (rest : List Branch) :
    bY (Branch.node (a :: rest)) ≤ 1/2 := by
  rw [bY_node]
  have hS : 0 ≤ ((a :: rest).map bY).sum := by
    apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have h1 : (1:ℝ) ≤ ((a :: rest).length : ℝ) := by
    have : (0:ℝ) ≤ (rest.length : ℝ) := Nat.cast_nonneg _
    rw [List.length_cons]; push_cast; linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Uniform child SCL at the flowed price** (`d ∈ {3..6}`): every child satisfies `bV_{μ''} c ≤ bV_{μ''} cherry`
    — leaf children via `leaf_le_cherry` (`μ'' ≤ 3/11`), non-leaf via `PSCLne` at `μ'' ∈ I`. -/
theorem child_scl_muPP {d : ℝ} (hd3 : 3 ≤ d) (hd6 : d ≤ 6) {μ : ℝ} (hμ : inI μ)
    {cs : List Branch} (hchild : ∀ c ∈ cs, PSCLne c) :
    ∀ c ∈ cs, bV (muPP d μ) c ≤ bV (muPP d μ) cherry := by
  intro c hc
  have hμ0 : (0:ℝ) ≤ μ := le_trans (by norm_num) hμ.1
  by_cases hleaf : c = Branch.node []
  · subst hleaf
    exact leaf_le_cherry (muPP_le_three_eleven hd3 hμ0)
  · exact hchild c hc hleaf (muPP d μ) (muPP_mem_I (by linarith) hd6 hμ)

/-- `Σ_c bY(c) ≤ |cs|` (each `bY ≤ 1`). -/
theorem sum_bY_le_length (cs : List Branch) : (cs.map bY).sum ≤ (cs.length : ℝ) := by
  induction cs with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have := bY_le_one a
    linarith [ih]

/-- **Hub connection, d=3** (`cs.length = 2`). -/
theorem hub_le_d3 {mu : ℝ} (hmu : inI mu) {cs : List Branch} (hlen : cs.length = 2)
    (hchild : ∀ c ∈ cs, PSCLne c) :
    bV mu (Branch.node cs) ≤ bV mu cherry := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have hlenR : (cs.length : ℝ) = 2 := by exact_mod_cast hlen
  have hSle : S ≤ 2 := by
    have := sum_bY_le_length cs; rw [hlenR] at this; rw [hSdef]; exact this
  have hmpp : muPP 3 mu = (33 - 9*mu)/121 := by rw [muPP]; ring
  have hchild2 := child_scl_muPP (d:=3) (by norm_num) (by norm_num) hmu hchild
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (muPP 3 mu) cherry - muPP 3 mu * (cs.map bY).sum :=
    child_bell_sum_le (muPP 3 mu) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 2/3) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 2/3/((2:ℝ)+1)) = Real.log (11/9) := by norm_num
  have hden : ((2:ℝ)+1)+2/3 = 11/3 := by norm_num
  rw [hlogeq, hden] at htan
  have hbY : bY (Branch.node cs) = 1 / (3 + S) := by
    have hden' : ((cs.length : ℝ) + 1) + (cs.map bY).sum = 3 + S := by rw [hlenR, ← hSdef]; ring
    rw [bY_node, hden']
  have hdec := decouple_d3 mu S hmu hSnn hSle
  have hVpp : bV (muPP 3 mu) cherry = Real.log (3/2) - 2*FSTAR + muPP 3 mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have hVc : bV mu cherry = Real.log (3/2) - 2*FSTAR + mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  -- the RHS bound on bV mu (node cs)
  have hbV : bV mu (Branch.node cs) = bell (Branch.node cs) + mu * (1/(3+S)) := by rw [bV, hbY]
  have hRHS : bV mu (Branch.node cs)
      ≤ (2 * bV (muPP 3 mu) cherry - muPP 3 mu * S
          + (Real.log (11/9) + (S - 2/3)/(11/3) - FSTAR)) + mu * (1/(3+S)) := by
    rw [hbV]; linarith [htan, hsum]
  -- the algebraic identity: RHS - bV mu cherry = decouple_d3 LHS  (μ'' expanded, μ/(3+S) shared atom)
  have hbridge : (2 * bV (muPP 3 mu) cherry - muPP 3 mu * S
        + (Real.log (11/9) + (S - 2/3)/(11/3) - FSTAR)) + mu * (1/(3+S)) - bV mu cherry
      = (2*(muPP 3 mu)/3 - mu/3 + 9*mu*S/121 - 2/11
          + (Real.log (3/2) + Real.log (11/9) - 3*FSTAR) + mu/(3+S)) := by
    rw [hVpp, hVc, hmpp]; ring
  linarith [hRHS, hbridge, hdec]

/-- **Hub connection, d=4** (`cs.length = 3`). -/
theorem hub_le_d4 {mu : ℝ} (hmu : inI mu) {cs : List Branch} (hlen : cs.length = 3)
    (hchild : ∀ c ∈ cs, PSCLne c) :
    bV mu (Branch.node cs) ≤ bV mu cherry := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have hlenR : (cs.length : ℝ) = 3 := by exact_mod_cast hlen
  have hSle : S ≤ 3 := by
    have := sum_bY_le_length cs; rw [hlenR] at this; rw [hSdef]; exact this
  have hmpp : muPP 4 mu = 3*(15 - 3*mu)/225 := by rw [muPP]; norm_num
  have hchild2 := child_scl_muPP (d:=4) (by norm_num) (by norm_num) hmu hchild
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (muPP 4 mu) cherry - muPP 4 mu * (cs.map bY).sum :=
    child_bell_sum_le (muPP 4 mu) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 1) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 1/((3:ℝ)+1)) = Real.log (5/4) := by norm_num
  have hden : ((3:ℝ)+1)+1 = 5 := by norm_num
  rw [hlogeq, hden] at htan
  have hbY : bY (Branch.node cs) = 1 / (4 + S) := by
    have hden' : ((cs.length : ℝ) + 1) + (cs.map bY).sum = 4 + S := by rw [hlenR, ← hSdef]; ring
    rw [bY_node, hden']
  -- d=4's pre-existing decouple lemma uses a non-uniform normalization; prove the UNIFORM
  -- residual (matching the clean tangent) inline via the same log gap.
  have hdS : (0:ℝ) < 4 + S := by linarith
  have hμpos : (0:ℝ) ≤ mu := le_trans (by norm_num) hmu.1
  have hdec : (muPP 4 mu) - mu/3 + 9*mu*S/225 - (3/15)
      + (2*Real.log (3/2) + Real.log (5/4) - 5*FSTAR) + mu/(4+S) ≤ 0 := by
    obtain ⟨hμlo, hμhi⟩ := hmu
    have hg := log_gap_d4
    rw [hmpp, div_eq_mul_inv mu (4+S)]
    have hinv : (4+S)⁻¹ * (4+S) = 1 := inv_mul_cancel₀ (ne_of_gt hdS)
    have hinvpos : 0 < (4+S)⁻¹ := inv_pos.mpr hdS
    nlinarith [hg, hμlo, hμhi, hSnn, hSle, hdS, hinv, hinvpos, mul_nonneg hμpos (le_of_lt hinvpos),
      mul_nonneg hμpos hSnn, mul_nonneg (mul_nonneg hμpos hSnn) (le_of_lt hinvpos),
      mul_nonneg (mul_nonneg hμpos (le_of_lt hinvpos)) hSnn]
  have hVpp : bV (muPP 4 mu) cherry = Real.log (3/2) - 2*FSTAR + muPP 4 mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have hVc : bV mu cherry = Real.log (3/2) - 2*FSTAR + mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have hbV : bV mu (Branch.node cs) = bell (Branch.node cs) + mu * (1/(4+S)) := by rw [bV, hbY]
  have hRHS : bV mu (Branch.node cs)
      ≤ ((3:ℝ) * bV (muPP 4 mu) cherry - muPP 4 mu * S
          + (Real.log (5/4) + (S - 1)/5 - FSTAR)) + mu * (1/(4+S)) := by
    rw [hbV]; linarith [htan, hsum]
  have hbridge : ((3:ℝ) * bV (muPP 4 mu) cherry - muPP 4 mu * S
        + (Real.log (5/4) + (S - 1)/5 - FSTAR)) + mu * (1/(4+S)) - bV mu cherry
      = ((muPP 4 mu) - mu/3 + 9*mu*S/225 - (3/15)
          + (2*Real.log (3/2) + Real.log (5/4) - 5*FSTAR) + mu/(4+S)) := by
    rw [hVpp, hVc, hmpp]; ring
  linarith [hRHS, hbridge, hdec]

/-- **Hub connection, d=5** (`cs.length = 4`). -/
theorem hub_le_d5 {mu : ℝ} (hmu : inI mu) {cs : List Branch} (hlen : cs.length = 4)
    (hchild : ∀ c ∈ cs, PSCLne c) :
    bV mu (Branch.node cs) ≤ bV mu cherry := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have hlenR : (cs.length : ℝ) = 4 := by exact_mod_cast hlen
  have hSle : S ≤ 4 := by
    have := sum_bY_le_length cs; rw [hlenR] at this; rw [hSdef]; exact this
  have hmpp : muPP 5 mu = 3*(19 - 3*mu)/361 := by rw [muPP]; norm_num
  have hchild2 := child_scl_muPP (d:=5) (by norm_num) (by norm_num) hmu hchild
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (muPP 5 mu) cherry - muPP 5 mu * (cs.map bY).sum :=
    child_bell_sum_le (muPP 5 mu) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 4/3) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 4/3/((4:ℝ)+1)) = Real.log (19/15) := by norm_num
  have hden : ((4:ℝ)+1)+4/3 = 19/3 := by norm_num
  rw [hlogeq, hden] at htan
  have hbY : bY (Branch.node cs) = 1 / (5 + S) := by
    have hden' : ((cs.length : ℝ) + 1) + (cs.map bY).sum = 5 + S := by rw [hlenR, ← hSdef]; ring
    rw [bY_node, hden']
  have hdec := decouple_d5 mu S hmu hSnn hSle
  have hVpp : bV (muPP 5 mu) cherry = Real.log (3/2) - 2*FSTAR + muPP 5 mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have hVc : bV mu cherry = Real.log (3/2) - 2*FSTAR + mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have hbV : bV mu (Branch.node cs) = bell (Branch.node cs) + mu * (1/(5+S)) := by rw [bV, hbY]
  have hRHS : bV mu (Branch.node cs)
      ≤ ((4:ℝ) * bV (muPP 5 mu) cherry - muPP 5 mu * S
          + (Real.log (19/15) + (S - 4/3)/(19/3) - FSTAR)) + mu * (1/(5+S)) := by
    rw [hbV]; linarith [htan, hsum]
  have hbridge : ((4:ℝ) * bV (muPP 5 mu) cherry - muPP 5 mu * S
        + (Real.log (19/15) + (S - 4/3)/(19/3) - FSTAR)) + mu * (1/(5+S)) - bV mu cherry
      = ((4*(muPP 5 mu)/3) - mu/3 + 9*mu*S/361 - (4/19)
          + (3*Real.log (3/2) + Real.log (19/15) - 7*FSTAR) + mu/(5+S)) := by
    rw [hVpp, hVc, hmpp]; ring
  linarith [hRHS, hbridge, hdec]

/-- **Hub connection, d=6** (`cs.length = 5`). -/
theorem hub_le_d6 {mu : ℝ} (hmu : inI mu) {cs : List Branch} (hlen : cs.length = 5)
    (hchild : ∀ c ∈ cs, PSCLne c) :
    bV mu (Branch.node cs) ≤ bV mu cherry := by
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have hlenR : (cs.length : ℝ) = 5 := by exact_mod_cast hlen
  have hSle : S ≤ 5 := by
    have := sum_bY_le_length cs; rw [hlenR] at this; rw [hSdef]; exact this
  have hmpp : muPP 6 mu = 3*(23 - 3*mu)/529 := by rw [muPP]; norm_num
  have hchild2 := child_scl_muPP (d:=6) (by norm_num) (by norm_num) hmu hchild
  have hsum : (cs.map bell).sum ≤ (cs.length : ℝ) * bV (muPP 6 mu) cherry - muPP 6 mu * (cs.map bY).sum :=
    child_bell_sum_le (muPP 6 mu) cs hchild2
  rw [hlenR, ← hSdef] at hsum
  have htan := bell_node_tangent cs (s0 := 5/3) (by norm_num)
  rw [hlenR, ← hSdef] at htan
  have hlogeq : Real.log (1 + 5/3/((5:ℝ)+1)) = Real.log (23/18) := by norm_num
  have hden : ((5:ℝ)+1)+5/3 = 23/3 := by norm_num
  rw [hlogeq, hden] at htan
  have hbY : bY (Branch.node cs) = 1 / (6 + S) := by
    have hden' : ((cs.length : ℝ) + 1) + (cs.map bY).sum = 6 + S := by rw [hlenR, ← hSdef]; ring
    rw [bY_node, hden']
  have hdec := decouple_d6 mu S hmu hSnn hSle
  have hVpp : bV (muPP 6 mu) cherry = Real.log (3/2) - 2*FSTAR + muPP 6 mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have hVc : bV mu cherry = Real.log (3/2) - 2*FSTAR + mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have hbV : bV mu (Branch.node cs) = bell (Branch.node cs) + mu * (1/(6+S)) := by rw [bV, hbY]
  have hRHS : bV mu (Branch.node cs)
      ≤ ((5:ℝ) * bV (muPP 6 mu) cherry - muPP 6 mu * S
          + (Real.log (23/18) + (S - 5/3)/(23/3) - FSTAR)) + mu * (1/(6+S)) := by
    rw [hbV]; linarith [htan, hsum]
  have hbridge : ((5:ℝ) * bV (muPP 6 mu) cherry - muPP 6 mu * S
        + (Real.log (23/18) + (S - 5/3)/(23/3) - FSTAR)) + mu * (1/(6+S)) - bV mu cherry
      = ((5*(muPP 6 mu)/3) - mu/3 + 9*mu*S/529 - (5/23)
          + (4*Real.log (3/2) + Real.log (23/18) - 9*FSTAR) + mu/(6+S)) := by
    rw [hVpp, hVc, hmpp]; ring
  linarith [hRHS, hbridge, hdec]

/-- **Hub connection, d=2** (`cs.length = 1`, single child).  Special: a LEAF child makes the hub
    `node [node []] = cherry` exactly (trivial equality); a NON-leaf child has `bY ≤ 1/2` (`S ≤ 1/2`),
    so `decouple_d2` applies with the child IH at `μ'' = muPP 2 μ ∈ I`. -/
theorem hub_le_d2 {mu : ℝ} (hmu : inI mu) {cs : List Branch} (hlen : cs.length = 1)
    (hchild : ∀ c ∈ cs, PSCLne c) :
    bV mu (Branch.node cs) ≤ bV mu cherry := by
  obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
    cases cs with
    | nil => simp at hlen
    | cons c t => cases t with
      | nil => exact ⟨c, rfl⟩
      | cons _ _ => simp at hlen
  have hc1 : PSCLne c := hchild c (List.mem_cons.mpr (Or.inl rfl))
  by_cases hc : c = Branch.node []
  · subst hc; exact le_of_eq rfl
  · set S := (([c] : List Branch).map bY).sum with hSdef
    have hSnn : 0 ≤ S := by
      rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
      obtain ⟨z, _, rfl⟩ := hx; exact bY_nonneg z
    have hScc : S = bY c := by rw [hSdef]; simp
    have hSle : S ≤ 1/2 := by
      rw [hScc]
      cases c with
      | node cs' => cases cs' with
        | nil => exact absurd rfl hc
        | cons a rest => exact bY_nonleaf_le_half a rest
    have hlenR : (([c] : List Branch).length : ℝ) = 1 := by norm_num
    have hmpp : muPP 2 mu = 3*(7 - 3*mu)/49 := by rw [muPP]; norm_num
    have hchild2 : ∀ x ∈ ([c] : List Branch), bV (muPP 2 mu) x ≤ bV (muPP 2 mu) cherry := by
      intro x hx
      rw [List.mem_singleton] at hx; subst hx
      exact hc1 hc (muPP 2 mu) (muPP_mem_I (by norm_num) (by norm_num) hmu)
    have hsum : (([c] : List Branch).map bell).sum
        ≤ (([c] : List Branch).length : ℝ) * bV (muPP 2 mu) cherry - muPP 2 mu * (([c] : List Branch).map bY).sum :=
      child_bell_sum_le (muPP 2 mu) [c] hchild2
    rw [hlenR, ← hSdef] at hsum
    have htan := bell_node_tangent [c] (s0 := 1/3) (by norm_num)
    rw [hlenR, ← hSdef] at htan
    have hlogeq : Real.log (1 + 1/3/((1:ℝ)+1)) = Real.log (7/6) := by norm_num
    have hden : ((1:ℝ)+1)+1/3 = 7/3 := by norm_num
    rw [hlogeq, hden] at htan
    have hbY : bY (Branch.node [c]) = 1 / (2 + S) := by
      have hden' : (([c] : List Branch).length : ℝ) + 1 + (([c] : List Branch).map bY).sum = 2 + S := by
        rw [hlenR, ← hSdef]; ring
      rw [bY_node, hden']
    have hdec := decouple_d2 mu S hmu hSnn hSle
    have hVpp : bV (muPP 2 mu) cherry = Real.log (3/2) - 2*FSTAR + muPP 2 mu * (1/3) := by
      rw [bV, bell_cherry, bY_cherry]
    have hVc : bV mu cherry = Real.log (3/2) - 2*FSTAR + mu * (1/3) := by
      rw [bV, bell_cherry, bY_cherry]
    have hbV : bV mu (Branch.node [c]) = bell (Branch.node [c]) + mu * (1/(2+S)) := by rw [bV, hbY]
    have hRHS : bV mu (Branch.node [c])
        ≤ ((1:ℝ) * bV (muPP 2 mu) cherry - muPP 2 mu * S
            + (Real.log (7/6) + (S - 1/3)/(7/3) - FSTAR)) + mu * (1/(2+S)) := by
      rw [hbV]; linarith [htan, hsum]
    have hbridge : ((1:ℝ) * bV (muPP 2 mu) cherry - muPP 2 mu * S
          + (Real.log (7/6) + (S - 1/3)/(7/3) - FSTAR)) + mu * (1/(2+S)) - bV mu cherry
        = ((muPP 2 mu)/3 - mu/3 - 1/7 + Real.log (7/6) - FSTAR + 9*mu*S/49 + mu/(2+S)) := by
      rw [hVpp, hVc, hmpp]; ring
    linarith [hRHS, hbridge, hdec]

end BGSCL
end R3Cert
