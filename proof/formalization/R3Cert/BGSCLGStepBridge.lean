/-
  The g-step ↔ classical-Branch-model BRIDGE (2026-09-02).

  This is the recursion-assembly `(ii)` that no file on `main` had: it connects the CappedJoint g-step machinery
  to the concrete branch ceiling `bell b ≤ 0`.  The exp-cleared ceiling quantity is `Gf b := exp(11·bell b)`
  (`= btotal(b)^11 · (64/621)^|b|`), so `Gf b ≤ 1 ⟺ bell b ≤ 0`.  It obeys the cavity recursion in product form
  (`Gf_node`), and the message `μ = bY(c)` is the cavity field.  The capped joint invariant is `Gf b ≤ capB(bY b)`
  with `capB = min(master_ub, glemma_ub, 1)`.

  `ceiling_of_gstep` reduces the WHOLE classical branch ceiling `∀ b, bell b ≤ 0` — for every rooted branch, all
  degrees — to the SINGLE per-hub message inequality `GStep` (`W·a^11·∏capB ≤ capB(μ_hub)`), via well-founded
  recursion + the achievability of `bY` (`bY_leaf = 1`, `bY_nonleaf ≤ 1/2`).  `GStep` is the honest remaining
  obligation (the CappedJoint `STEP≤1`, tight only at the `d=6` tie); it is stated as an explicit hypothesis, NOT
  proven here.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep
import R3Cert.BGSCLHub

namespace R3Cert
namespace BGSCL

open Real

/-- The exp-cleared ceiling quantity `Gf b = exp(11·bell b) = btotal(b)^11·(64/621)^|b|`.
    `Gf b ≤ 1 ⟺ bell b ≤ 0`. -/
noncomputable def Gf (b : Branch) : ℝ := Real.exp (11 * bell b)

theorem Gf_pos (b : Branch) : 0 < Gf b := Real.exp_pos _

/-- `bell b ≤ 0` from `Gf b ≤ 1`. -/
theorem bell_nonpos_of_Gf {b : Branch} (h : Gf b ≤ 1) : bell b ≤ 0 := by
  unfold Gf at h
  have := Real.exp_le_one_iff.mp h
  linarith

/-- The master-side per-message cap `master_ub(μ) = (64/621)(3/(2+μ))^11`. -/
noncomputable def masterUb (μ : ℝ) : ℝ := (64/621) * (3/(2+μ))^11
/-- The g-lemma-side per-message cap `glemma_ub(μ) = (64/621)²(5/3)^11/(1+μ/3)^11`. -/
noncomputable def glemmaUb (μ : ℝ) : ℝ := (64/621)^2 * (5/3)^11 / (1+μ/3)^11
/-- The capped child bound `Bcap(μ) = min(master_ub, glemma_ub, 1)`. -/
noncomputable def capB (μ : ℝ) : ℝ := min (masterUb μ) (min (glemmaUb μ) 1)

theorem capB_le_one (μ : ℝ) : capB μ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)

/-- `capB(1) = 64/621` (the leaf/arm value: `master_ub(1) = 64/621` is the binding min). -/
theorem capB_one : capB (1:ℝ) = 64/621 := by
  have h1 : glemmaUb 1 ≤ (1:ℝ) := by unfold glemmaUb; norm_num
  have h2 : masterUb (1:ℝ) ≤ glemmaUb 1 := by unfold masterUb glemmaUb; norm_num
  have h3 : masterUb (1:ℝ) = 64/621 := by unfold masterUb; norm_num
  unfold capB
  rw [min_eq_left h1, min_eq_left h2, h3]

/-- **PIECE 1 (master ⟸ glemma).**  On the hub range `μ ≤ 1/2`, the glemma cap is BELOW the master cap:
    `glemmaUb(μ) ≤ masterUb(μ)`.  Hence the master component of the per-hub step is a `le_trans` off the
    (proven) glemma component — no separate master proof is needed.  (`(3+μ)/(2+μ) ≥ 7/5 ⟺ μ ≤ 1/2`, and
    `(64/621)·(5/3)^11 ≤ (7/5)^11`, i.e. the integer `64·25^11 ≤ 621·21^11`.) -/
theorem glemmaUb_le_masterUb {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1/2) : glemmaUb μ ≤ masterUb μ := by
  have h2 : (0:ℝ) < 2 + μ := by linarith
  unfold glemmaUb masterUb
  rw [div_le_iff₀ (by positivity)]
  have hcombine : (3/(2+μ))^11 * (1+μ/3)^11 = ((3+μ)/(2+μ))^11 := by
    rw [← mul_pow]; congr 1; field_simp
  have hr : (7/5:ℝ) ≤ (3+μ)/(2+μ) := by rw [le_div_iff₀ h2]; linarith
  have hpow : (7/5:ℝ)^11 ≤ ((3+μ)/(2+μ))^11 := pow_le_pow_left₀ (by norm_num) hr 11
  have hcert : (64/621:ℝ)^2 * (5/3)^11 ≤ (64/621) * (7/5)^11 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 64/621)
  calc (64/621:ℝ)^2 * (5/3)^11
      ≤ (64/621) * ((3+μ)/(2+μ))^11 := by linarith [hcert, hmul]
    _ = (64/621) * (3/(2+μ))^11 * (1+μ/3)^11 := by rw [mul_assoc, hcombine]

/-- exp of a scaled branch-`bell` sum is the product of `Gf`s. -/
theorem exp_eleven_sum (cs : List Branch) :
    Real.exp (11 * (cs.map bell).sum) = (cs.map Gf).prod := by
  induction cs with
  | nil => simp [Gf]
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    rw [mul_add, Real.exp_add, ih]
    rfl

/-- **The `Gf` cavity recursion (product form).**  `Gf(node cs) = (64/621)·(1 + S/d)^11·∏ Gf(c)`,
    `S = Σ bY(c)`, `d = |cs|+1`.  (Exp of `bell_node`.) -/
theorem Gf_node (cs : List Branch) :
    Gf (Branch.node cs)
      = (64/621) * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11 * (cs.map Gf).prod := by
  have hd : (0:ℝ) < (cs.length:ℝ)+1 := by positivity
  have hSnn : (0:ℝ) ≤ (cs.map bY).sum := by
    apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have hpos : (0:ℝ) < 1 + (cs.map bY).sum / ((cs.length:ℝ)+1) := by
    have : (0:ℝ) ≤ (cs.map bY).sum / ((cs.length:ℝ)+1) := div_nonneg hSnn (le_of_lt hd)
    linarith
  have hlog : Real.exp (11 * Real.log (1 + (cs.map bY).sum / ((cs.length:ℝ)+1)))
      = (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11 := by
    rw [show (11:ℝ) * Real.log (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))
          = Real.log ((1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11) from by
        rw [Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by positivity)
  have hFneg : Real.exp (-(11 * FSTAR)) = 64/621 := by
    rw [show -(11 * FSTAR) = -Real.log (621/64) from by rw [FSTAR]; ring, Real.exp_neg,
        Real.exp_log (by norm_num)]
    norm_num
  have heq : 11 * bell (Branch.node cs)
      = 11 * (cs.map bell).sum
        + 11 * Real.log (1 + (cs.map bY).sum / ((cs.length:ℝ)+1)) + (-(11 * FSTAR)) := by
    rw [bell_node]; ring
  rw [show Gf (Branch.node cs) = Real.exp (11 * bell (Branch.node cs)) from rfl,
      heq, Real.exp_add, Real.exp_add, exp_eleven_sum, hlog, hFneg]
  ring

/-- Achievability of a cavity message: `0 < μ` and (`μ ≤ 1/2` or `μ = 1`). -/
def Achiev (μ : ℝ) : Prop := 0 < μ ∧ (μ ≤ 1/2 ∨ μ = 1)

theorem bY_pos (b : Branch) : 0 < bY b := by
  cases b with
  | node cs =>
    rw [bY_node]
    have hSnn : (0:ℝ) ≤ (cs.map bY).sum := by
      apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
      obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
    positivity

/-- `bY(b)` is achievable: leaf ⟹ `= 1`, non-leaf ⟹ `≤ 1/2`. -/
theorem bY_achievable (b : Branch) : Achiev (bY b) := by
  refine ⟨bY_pos b, ?_⟩
  cases b with
  | node cs =>
    cases cs with
    | nil => right; exact bY_leaf
    | cons a rest => left; exact bY_nonleaf_le_half a rest

/-- **The per-hub message step (`STEP≤1` in capped form).**  For a non-empty hub whose children's messages are
    achievable, the boosted product of child caps is `≤` the hub's cap.  This is the CappedJoint g-step obligation
    (`W·a^11·∏Bcap ≤ Bcap(μ_hub)`); tight only at the `d=6` all-cherry tie.  The single remaining analytic input. -/
def GStep : Prop :=
  ∀ cs : List Branch, cs ≠ [] → (∀ c ∈ cs, Achiev (bY c)) →
    (64/621 : ℝ) * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11
        * (cs.map (fun c => capB (bY c))).prod
      ≤ capB (bY (Branch.node cs))

/-- `∏ Gf(c) ≤ ∏ capB(bY c)` from the per-child bound. -/
theorem list_prod_mono (cs : List Branch) (h : ∀ c ∈ cs, Gf c ≤ capB (bY c)) :
    (cs.map Gf).prod ≤ (cs.map (fun c => capB (bY c))).prod := by
  induction cs with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha : Gf a ≤ capB (bY a) := h a (List.mem_cons.mpr (Or.inl rfl))
    have iht : (t.map Gf).prod ≤ (t.map (fun c => capB (bY c))).prod :=
      ih (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))
    have hGt : (0:ℝ) ≤ (t.map Gf).prod := by
      apply List.prod_nonneg; intro x hx; rw [List.mem_map] at hx
      obtain ⟨c, _, rfl⟩ := hx; exact le_of_lt (Gf_pos c)
    have hca : (0:ℝ) ≤ capB (bY a) := le_trans (le_of_lt (Gf_pos a)) ha
    calc Gf a * (t.map Gf).prod
        ≤ capB (bY a) * (t.map Gf).prod := mul_le_mul_of_nonneg_right ha hGt
      _ ≤ capB (bY a) * (t.map (fun c => capB (bY c))).prod := mul_le_mul_of_nonneg_left iht hca

/-- **THE BRIDGE.**  The whole classical branch ceiling `∀ b, bell b ≤ 0` — every rooted branch, all degrees —
    reduces to the single per-hub message inequality `GStep`.  Proof: the capped joint invariant `Gf b ≤ capB(bY b)`
    holds for every branch by well-founded recursion on `|b|` (leaf: `Gf(node []) = 64/621 = capB 1`; hub: the
    child IH + `Gf_node` product recursion + `list_prod_mono` + `GStep` with the achievable child messages), and
    `capB ≤ 1` gives `Gf b ≤ 1`, i.e. `bell b ≤ 0`.  `GStep` is the sole hypothesis — the honest remaining
    obligation.  `conjecture1_proved = False`. -/
theorem ceiling_of_gstep (hstep : GStep) : ∀ b, bell b ≤ 0 := by
  have hinv : ∀ b, Gf b ≤ capB (bY b) := by
    refine scl_of_child_step bsize bchildren (fun b => Gf b ≤ capB (bY b)) bchildren_bsize_lt
      (fun a hIH => ?_)
    cases a with
    | node cs =>
      have hchild : ∀ c ∈ cs, Gf c ≤ capB (bY c) :=
        fun c hc => hIH c (by simpa only [bchildren] using hc)
      rw [Gf_node]
      by_cases hcs : cs = []
      · subst hcs
        simp only [List.map_nil, List.sum_nil, List.prod_nil, List.length_nil, Nat.cast_zero]
        rw [bY_leaf, capB_one]; norm_num
      · have hprod : (cs.map Gf).prod ≤ (cs.map (fun c => capB (bY c))).prod :=
          list_prod_mono cs hchild
        have hboost : (0:ℝ) ≤ (64/621 : ℝ) * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11 := by
          have hSnn : (0:ℝ) ≤ (cs.map bY).sum := by
            apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
            obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
          positivity
        calc (64/621 : ℝ) * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11 * (cs.map Gf).prod
            ≤ (64/621 : ℝ) * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11
                * (cs.map (fun c => capB (bY c))).prod :=
              mul_le_mul_of_nonneg_left hprod hboost
          _ ≤ capB (bY (Branch.node cs)) :=
              hstep cs hcs (fun c _ => bY_achievable c)
  exact fun b => bell_nonpos_of_Gf (le_trans (hinv b) (capB_le_one _))

/-- The glemma-component per-hub step (`W·a^11·prodBcap ≤ glemmaUb(μ_hub)`) — the CappedJoint
    `gstep_le_one_achievable` (PROVEN in ℚ; all arities), transported to the classical `bY`/`Gf` setting. -/
def GlemmaStep : Prop :=
  ∀ cs : List Branch, cs ≠ [] → (∀ c ∈ cs, Achiev (bY c)) →
    (64/621 : ℝ) * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11
        * (cs.map (fun c => capB (bY c))).prod
      ≤ glemmaUb (bY (Branch.node cs))

/-- **PIECE 2 (the `≤1` step)** — `W·a^11·prodBcap ≤ 1`.  The SOLE genuinely-open obligation: it is TIGHT
    exactly at the `d=6` all-cherry tie (the `27·23 = 621` identity, `acl_d6`), strictly slack elsewhere, and is
    NOT implied by `GlemmaStep` when the hub message `< 0.306` (there both caps exceed 1).  For hub message
    `≥ 0.306` it DOES follow from `GlemmaStep` (`glemmaUb ≤ 1`); the residual is the small-message / large-hub
    tie region — the `M_d` frontier. -/
def Le1Step : Prop :=
  ∀ cs : List Branch, cs ≠ [] → (∀ c ∈ cs, Achiev (bY c)) →
    (64/621 : ℝ) * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1))^11
        * (cs.map (fun c => capB (bY c))).prod
      ≤ 1

/-- **The sharpened per-hub step**: `GStep` follows from `GlemmaStep ∧ Le1Step` — the master cap is derived from
    glemma via `glemmaUb_le_masterUb` (piece 1).  So the whole thing rests on glemma (proven) + the `≤1` step. -/
theorem gstep_of_glemma_le1 (hg : GlemmaStep) (h1 : Le1Step) : GStep := by
  intro cs hcs hach
  have hμle : bY (Branch.node cs) ≤ 1/2 := by
    cases cs with
    | nil => exact absurd rfl hcs
    | cons a rest => exact bY_nonleaf_le_half a rest
  have hgl := hg cs hcs hach
  exact le_min (le_trans hgl (glemmaUb_le_masterUb (bY_nonneg _) hμle))
    (le_min hgl (h1 cs hcs hach))

/-- **The sharpened bridge.**  The entire classical branch ceiling `∀ b, bell b ≤ 0` reduces to `GlemmaStep`
    (proven in ℚ as `gstep_le_one_achievable`) together with `Le1Step` (piece 2, the tie-tight residual).
    Master is subsumed.  `conjecture1_proved = False`. -/
theorem ceiling_of_glemma_le1 (hg : GlemmaStep) (h1 : Le1Step) : ∀ b, bell b ≤ 0 :=
  ceiling_of_gstep (gstep_of_glemma_le1 hg h1)

end BGSCL
end R3Cert
