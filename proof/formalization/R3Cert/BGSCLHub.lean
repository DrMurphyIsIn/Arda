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

/-- **The cherry ceiling gap** `log(3/2) − 2 F* ≥ −1/50`.  (True value `≈ −0.00768`; margin `+0.012`.)
    `two_le_log_gap` is too loose here (`≥ −0.0248`), so combine `11·(log(3/2) − 2F*) = log(354294/385641)`
    and lower-bound via `log x ≥ 1 − 1/x` (`Real.log_le_sub_one_of_pos` on the inverse). -/
theorem cherry_ceiling_gap : (-1/50 : ℝ) ≤ Real.log (3/2) - 2*FSTAR := by
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  rw [hF]
  have hcomb : (11:ℝ)*(Real.log (3/2) - 2*(Real.log (621/64)/11))
      = Real.log ((3/2)^11 * (64/621)^2) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (64:ℝ)/621 = (621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  have hXval : ((3/2:ℝ))^11 * (64/621)^2 = 354294/385641 := by norm_num
  have hXpos : (0:ℝ) < ((3/2:ℝ))^11 * (64/621)^2 := by positivity
  have hle := Real.log_le_sub_one_of_pos (inv_pos.mpr hXpos)
  rw [Real.log_inv] at hle
  rw [hXval] at hcomb hle
  have hinvval : ((354294:ℝ)/385641)⁻¹ = 385641/354294 := by norm_num
  rw [hinvval] at hle
  linarith [hcomb, hle]

/-- **Hub connection, d≥7 ceiling** (`cs.length ≥ 6`).  For a high-degree hub the tangent decouple is loose;
    instead `bV μ (node cs) = bell(node cs) + μ·bY ≤ 0 + μ/7 ≤ bV μ cherry`, using the branch ceiling
    `bell (node cs) ≤ 0` (hypothesis; the separate not-yet-formalized result) and `bY ≤ 1/7`.  The cherry
    lower bound `μ/7 ≤ bV μ cherry` follows from `cherry_ceiling_gap` + `μ ≥ 456/3703` (`4μ/21 ≥ 1/50`). -/
theorem hub_le_highdeg {mu : ℝ} (hmu : inI mu) {cs : List Branch} (hd7 : 6 ≤ cs.length)
    (hceil : bell (Branch.node cs) ≤ 0) :
    bV mu (Branch.node cs) ≤ bV mu cherry := by
  have hμpos : (0:ℝ) ≤ mu := le_trans (by norm_num) hmu.1
  obtain ⟨hμlo, hμhi⟩ := hmu
  set S := (cs.map bY).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨z, _, rfl⟩ := hx; exact bY_nonneg z
  have hlenR : (6:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hd7
  have hden : (7:ℝ) ≤ ((cs.length : ℝ) + 1) + S := by linarith
  have hbY : bY (Branch.node cs) = 1 / (((cs.length : ℝ) + 1) + S) := by rw [bY_node, ← hSdef]
  have hbYle : bY (Branch.node cs) ≤ 1/7 := by
    rw [hbY]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hbVnode : bV mu (Branch.node cs) ≤ mu * (1/7) := by
    have hb : bV mu (Branch.node cs) = bell (Branch.node cs) + mu * bY (Branch.node cs) := rfl
    rw [hb]; nlinarith [hceil, mul_le_mul_of_nonneg_left hbYle hμpos]
  have hVc : bV mu cherry = Real.log (3/2) - 2*FSTAR + mu * (1/3) := by
    rw [bV, bell_cherry, bY_cherry]
  have h4μ : mu * (1/7) ≤ bV mu cherry := by
    rw [hVc]; nlinarith [cherry_ceiling_gap, hμlo]
  linarith [hbVnode, h4μ]

/-- **The flowed per-hub step, from the branch ceiling.**  Case split on `cs.length`: `{1..5}` route through
    `hub_le_d2..d6` (tangent decouple), `≥6` through `hub_le_highdeg` (needs `bell (node cs) ≤ 0`).  Reduces
    `FlowedHubStep` — and hence the SCL for every non-leaf branch — to the single global obligation
    `∀ b, bell b ≤ 0` (the branch ceiling).  `conjecture1_proved = False`. -/
theorem flowed_hub_step_of_ceiling (hceil : ∀ b, bell b ≤ 0) : FlowedHubStep := by
  intro cs hcs hchild mu hmu
  have hlen1 : 1 ≤ cs.length := by
    rcases cs with _ | ⟨a, t⟩
    · exact absurd rfl hcs
    · simp
  rcases Nat.lt_or_ge cs.length 6 with hlo | hhi
  · rcases (by omega : cs.length = 1 ∨ cs.length = 2 ∨ cs.length = 3 ∨ cs.length = 4 ∨ cs.length = 5)
      with h | h | h | h | h
    · exact hub_le_d2 hmu h hchild
    · exact hub_le_d3 hmu h hchild
    · exact hub_le_d4 hmu h hchild
    · exact hub_le_d5 hmu h hchild
    · exact hub_le_d6 hmu h hchild
  · exact hub_le_highdeg hmu hhi (hceil (Branch.node cs))

/-- **The SCL for every non-leaf branch, from the branch ceiling.**  Chains `flowed_hub_step_of_ceiling`
    into `scl_of_flowed_step`.  This is the full reduction of the leaf-excluding single-child lemma to the
    single global obligation `∀ b, bell b ≤ 0`.  `conjecture1_proved = False`. -/
theorem scl_of_ceiling (hceil : ∀ b, bell b ≤ 0) : ∀ b, PSCLne b :=
  scl_of_flowed_step (flowed_hub_step_of_ceiling hceil)

/-- **The per-hub ceiling step** — the SINGLE remaining obligation.  A hub `node cs` whose children each
    satisfy BOTH the branch ceiling `bell c ≤ 0` AND the leaf-excluding SCL `PSCLne c` has `bell (node cs) ≤ 0`.
    This is exactly step `1b` / `2b-lo` of the BG upper-bound ledger (the `M_d` frontier: `ell(hub) ≤ ell(B(k)) ≤ 0`),
    whose arithmetic is GATED in Telperion (`MdStepCertificate`, `NearBroomUnimodalityCertificate`,
    `HighDegreeTailCertificate`, `BroomOptimumCertificate` — all `.check()` pass).  Its shape — child ceilings +
    child SCL ⟹ hub ceiling — is precisely what those certificates consume.  `conjecture1_proved = False`. -/
def CeilStep : Prop :=
  ∀ cs : List Branch, (∀ c ∈ cs, bell c ≤ 0) → (∀ c ∈ cs, PSCLne c) → bell (Branch.node cs) ≤ 0

/-- **The joint ceiling+SCL induction.**  ONE well-founded strong induction on `|b|` proves BOTH the branch
    ceiling `bell b ≤ 0` AND the leaf-excluding SCL `PSCLne b` for every branch, reduced to the single per-hub
    ceiling step `CeilStep`.  At a hub `node cs`: the child IH supplies BOTH properties on the (smaller) children;
    `CeilStep` gives the hub ceiling `bell (node cs) ≤ 0`; then the SCL follows — `hub_le_d2..d6` (tangent
    decouple, using child SCL) for degree `≤ 6`, and `hub_le_highdeg` (using the just-proved hub ceiling) for
    degree `≥ 7`.  This ELIMINATES the free-floating `∀ b, bell b ≤ 0` hypothesis of `scl_of_ceiling`: the SCL's
    d≥7 leg now draws the ceiling from the JOINT induction hypothesis, so the sole residual is `CeilStep` itself
    — the `M_d` frontier, matching the BG ledger's single open piece exactly.  `conjecture1_proved = False`. -/
theorem ceil_and_scl_of_ceilStep (hceil : CeilStep) : ∀ b, bell b ≤ 0 ∧ PSCLne b := by
  refine scl_of_child_step bsize bchildren (fun b => bell b ≤ 0 ∧ PSCLne b) bchildren_bsize_lt
    (fun a hIH => ?_)
  cases a with
  | node cs =>
    have hcc : ∀ c ∈ cs, bell c ≤ 0 := fun c hc => (hIH c (by simpa only [bchildren] using hc)).1
    have hcs : ∀ c ∈ cs, PSCLne c := fun c hc => (hIH c (by simpa only [bchildren] using hc)).2
    have hb : bell (Branch.node cs) ≤ 0 := hceil cs hcc hcs
    refine ⟨hb, ?_⟩
    intro hne μ hμ
    have hne' : cs ≠ [] := fun h => hne (by rw [h])
    have hlen1 : 1 ≤ cs.length := by
      rcases cs with _ | ⟨a, t⟩
      · exact absurd rfl hne'
      · simp
    rcases Nat.lt_or_ge cs.length 6 with hlo | hhi
    · rcases (by omega : cs.length = 1 ∨ cs.length = 2 ∨ cs.length = 3 ∨ cs.length = 4 ∨ cs.length = 5)
        with h | h | h | h | h
      · exact hub_le_d2 hμ h hcs
      · exact hub_le_d3 hμ h hcs
      · exact hub_le_d4 hμ h hcs
      · exact hub_le_d5 hμ h hcs
      · exact hub_le_d6 hμ h hcs
    · exact hub_le_highdeg hμ hhi hb

/-- The branch ceiling `∀ b, bell b ≤ 0` from the per-hub ceiling step. -/
theorem bell_ceiling_of_ceilStep (hceil : CeilStep) : ∀ b, bell b ≤ 0 :=
  fun b => (ceil_and_scl_of_ceilStep hceil b).1

/-- The SCL `∀ b, PSCLne b` from the per-hub ceiling step (no free-floating ceiling hypothesis). -/
theorem scl_of_ceilStep (hceil : CeilStep) : ∀ b, PSCLne b :=
  fun b => (ceil_and_scl_of_ceilStep hceil b).2

end BGSCL
end R3Cert
