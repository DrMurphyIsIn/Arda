/-
  The tail (deg≥5) DECOUPLE reduction (2026-09-03).

  Reusable backbone for the mixed-degree tail cells of `IsSubaction ρwit`, per the counts-exchange
  dissolution (`proof/docs/BG_SUBACTION_CONSOLIDATED_HANDOFF.md` §3.3): for a node of degree
  `d = |cs|+1 ≥ 5` (so `ρwit(node cs) = 0`), the subaction inequality
  `(log(1 + S/d) − F*) + 0 ≤ Σ_c ρwit(c)`  (`S = Σ bY(c)`)
  follows, via the concave-log tangent at ANY reference `S0`, from
    (i) a per-child lower bound  `ρwit(c) ≥ m + bY(c)/(d+S0)`  for all children, and
    (ii) `B(S0) := (d−1)·m + [F* − log(1+S0/d) + S0/(d+S0)] ≥ 0`.
  No discrete convexity: the tangent decouples the coupled `log`, and `Σ` lifts the per-child bound.
  Kernel-checked vs `R3Cert.BGSCLInduction`/`BGSCLSubaction`.  No `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionTail

namespace R3Cert
namespace BGSCL

open Real

/-- **List-lift.**  A per-child affine lower bound `m + σ·bY c ≤ ρwit c` sums to
    `(|cs|)·m + σ·(Σ bY) ≤ Σ ρwit`. -/
theorem sum_rhowit_ge (σ m : ℝ) : ∀ (cs : List Branch),
    (∀ c ∈ cs, m + σ * bY c ≤ ρwit c) →
    (cs.length : ℝ) * m + σ * (cs.map bY).sum ≤ (cs.map ρwit).sum
  | [], _ => by simp
  | a :: t, h => by
    have ha : m + σ * bY a ≤ ρwit a := h a (by simp)
    have ht := sum_rhowit_ge σ m t (fun c hc => h c (by simp [hc]))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    calc ((t.length : ℝ) + 1) * m + σ * (bY a + (t.map bY).sum)
        = (m + σ * bY a) + ((t.length : ℝ) * m + σ * (t.map bY).sum) := by ring
      _ ≤ ρwit a + (t.map ρwit).sum := add_le_add ha ht

/-- `ρwit(node cs) = 0` when the degree is ≥ 5 (`|cs| ≥ 4`). -/
theorem ρwit_node_high {cs : List Branch} (hlen : 4 ≤ cs.length) :
    ρwit (Branch.node cs) = 0 := by
  rw [ρwit]
  simp only [bcc]
  rcases hcl : cs.length with _ | _ | _ | _ | n
  · omega
  · omega
  · omega
  · omega
  · rfl

/-- **The tail DECOUPLE reduction.**  For a node of degree `d = |cs|+1 ≥ 5` (`ρwit(node cs)=0`), the
    subaction inequality reduces — via the concave-log tangent at any reference `S0 ≥ 0` — to a per-child
    lower bound (`hpc`) plus `B(S0) ≥ 0` (`hB`).  This is the mixed-degree tail closer; instantiate with the
    per-degree-class min `m` and the `S0 ∈ {(d−1)/3, (d−1)/4, (d−1)/5}` d-split. -/
theorem tail_decouple (cs : List Branch) (S0 m : ℝ)
    (hlen : 4 ≤ cs.length) (hS0 : 0 ≤ S0)
    (hpc : ∀ c ∈ cs, m + (1 / (((cs.length : ℝ) + 1) + S0)) * bY c ≤ ρwit c)
    (hB : 0 ≤ (cs.length : ℝ) * m
            + (FSTAR - Real.log (1 + S0 / ((cs.length : ℝ) + 1))
               + S0 / (((cs.length : ℝ) + 1) + S0))) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have hd_pos : (0 : ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hdS0 : (0 : ℝ) < ((cs.length : ℝ) + 1) + S0 := by positivity
  have hS_nn : (0 : ℝ) ≤ (cs.map bY).sum :=
    List.sum_nonneg (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c)
  have htan := log_tangent (d := (cs.length : ℝ) + 1) (s := (cs.map bY).sum) (s0 := S0)
    hd_pos hS_nn hS0
  have hsum := sum_rhowit_ge (1 / (((cs.length : ℝ) + 1) + S0)) m cs hpc
  have hsp : ((cs.map bY).sum - S0) / (((cs.length : ℝ) + 1) + S0)
      = (1 / (((cs.length : ℝ) + 1) + S0)) * (cs.map bY).sum
        - S0 / (((cs.length : ℝ) + 1) + S0) := by
    field_simp
  rw [ρwit_node_high hlen]
  linarith [htan, hsum, hB, hsp]

/-! ### Instantiation: the d=6 (tie) tail cell — arbitrary children, via `tail_decouple`. -/

/-- Enclosure `2F* − log(3/2) ≤ 1/96` (via `log x ≤ x−1` at `x=(621/64)²·(2/3)¹¹ ≈ 1.088`). -/
theorem cherry_anchor_le : 2 * FSTAR - Real.log (3/2) ≤ 1/96 := by
  rw [FSTAR]
  have hr := Real.log_le_sub_one_of_pos
    (show (0:ℝ) < (621/64 : ℝ) ^ (2:ℕ) * (2/3 : ℝ) ^ (11:ℕ) by positivity)
  have hsplit : Real.log ((621/64 : ℝ) ^ (2:ℕ) * (2/3 : ℝ) ^ (11:ℕ))
      = 2 * Real.log (621/64) - 11 * Real.log (3/2) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (2/3 : ℝ) = (3/2)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (621/64 : ℝ) ^ (2:ℕ) * (2/3 : ℝ) ^ (11:ℕ) - 1 ≤ 11/96 := by norm_num
  linarith

/-- Enclosure `2/23 ≤ log(3/2) − F*` (via `exp(22/23) ≤ exp 1 < 2.7182818286 ≤ (3/2)¹¹·(64/621)`). -/
theorem log32_sub_fstar_ge : (2:ℝ)/23 ≤ Real.log (3/2) - FSTAR := by
  rw [FSTAR]
  have hY : (0:ℝ) < (3/2 : ℝ) ^ (11:ℕ) * (64/621) := by positivity
  have hlog : Real.log ((3/2 : ℝ) ^ (11:ℕ) * (64/621))
      = 11 * Real.log (3/2) - Real.log (621/64) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621 : ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  have hge : (22:ℝ)/23 ≤ Real.log ((3/2 : ℝ) ^ (11:ℕ) * (64/621)) := by
    rw [Real.le_log_iff_exp_le hY]
    calc Real.exp (22/23) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
      _ ≤ (3/2 : ℝ) ^ (11:ℕ) * (64/621) := by norm_num
  rw [hlog] at hge; linarith

/-- **Per-child bound at `σ = 3/23`** (the d=6 reference).  `m + (3/23)·bY c ≤ ρwit c` for every branch,
    `m = 2F* − log(3/2) − 1/23`, by a per-degree-class check (leaf via `log32_sub_fstar_ge`; deg 3/4/≥5 via
    `cherry_anchor_le`; deg-2 via `bY ≥ 1/3`). -/
theorem phi_lb_d6 (c : Branch) :
    (2 * FSTAR - Real.log (3/2) - 1/23) + (3/23) * bY c ≤ ρwit c := by
  have hy0 := bY_nonneg c
  have hyd := bY_le_inv_deg c
  have hE3 := cherry_anchor_le
  have hEl := log32_sub_fstar_ge
  rcases hbc : bcc c with _ | _ | _ | _ | n
  · have hby1 : bY c = 1 := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact bY_leaf
    have hrc : ρwit c = FSTAR := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact ρwit_leaf
    rw [hby1, hrc]; linarith
  · have hby3 : (1:ℝ)/3 ≤ bY c := bY_ge_third_of_bcc1 c hbc
    have hrc : ρwit c = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c - 1/3) := by
      simp only [ρwit, hbc]
    rw [hrc]; linarith
  · have hby : bY c ≤ 1/3 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/32) * bY c := by simp only [ρwit, hbc]
    rw [hrc]
    nlinarith [hE3, mul_nonneg (show (0:ℝ) ≤ 1/3 - bY c by linarith)
      (show (0:ℝ) ≤ 73/736 by norm_num)]
  · have hby : bY c ≤ 1/4 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/384) * bY c := by simp only [ρwit, hbc]
    rw [hrc]; nlinarith [hE3, hby, hy0]
  · have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hby : bY c ≤ 1/5 := by
      rw [hbc] at hyd
      have hd5 : (5:ℝ) ≤ ((n + 4 : ℕ) : ℝ) + 1 := by push_cast; linarith
      have hle : (1:ℝ) / (((n + 4 : ℕ) : ℝ) + 1) ≤ 1/5 :=
        one_div_le_one_div_of_le (by norm_num) hd5
      linarith
    have hrc : ρwit c = 0 := by
      cases c with
      | node cs => simp only [bcc] at hbc; exact ρwit_node_high (by omega)
    rw [hrc]; nlinarith [hE3, hby, hy0]

/-- **The degree-6 (tie) tail cell.**  `IsSubaction ρwit` at any node of degree 6 (`|cs| = 5`, arbitrary
    children): via `tail_decouple` with `S0 = 5/3` (all-cherry reference), the per-child bound `phi_lb_d6`, and
    `B = 0` — the EXACT `27·23` identity (`tie_identity_d6`).  Closes the tie for ALL mixed child configs. -/
theorem subaction_tail_d6 (cs : List Branch) (hlen : cs.length = 5) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple cs (5/3) (2 * FSTAR - Real.log (3/2) - 1/23) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 5/3) = 3/23 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_d6 c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 5/3 / (5 + 1) = 23/18 by norm_num,
        show (5:ℝ)/3 / ((5 + 1) + 5/3) = 5/23 by norm_num]
    linarith [tie_identity_d6]

/-! ### The large-d (deg-5-min) regime: reusable per-child min over a σ-range. -/

/-- Anchor lower bound `1/500 ≤ 2F* − log(3/2)` (via `1 − 1/X ≤ log X` at `X=(621/64)²·(2/3)¹¹ ≈ 1.088`). -/
theorem cherry_anchor_ge : (1:ℝ)/500 ≤ 2 * FSTAR - Real.log (3/2) := by
  rw [FSTAR]
  set X : ℝ := (621/64:ℝ)^(2:ℕ) * (2/3:ℝ)^(11:ℕ) with hXdef
  have hXpos : (0:ℝ) < X := by rw [hXdef]; positivity
  have hli := Real.log_le_sub_one_of_pos (show (0:ℝ) < X⁻¹ by positivity)
  rw [Real.log_inv] at hli
  have hX489 : (500:ℝ)/489 ≤ X := by rw [hXdef]; norm_num
  have hinv : X⁻¹ ≤ 489/500 := by
    have hnn : (0:ℝ) ≤ X⁻¹ := le_of_lt (inv_pos.mpr hXpos)
    have hc : X * X⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hXpos)
    nlinarith [hc, mul_nonneg hnn (show (0:ℝ) ≤ X - 500/489 by linarith)]
  have hsplit : Real.log X = 2 * Real.log (621/64) - 11 * Real.log (3/2) := by
    rw [hXdef, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        show (2/3:ℝ) = (3/2)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hli
  linarith

/-- **Per-child min for the deg-5-min regime.**  For any `σ ∈ (0, 5/384]`, `(−σ/5) + σ·bY c ≤ ρwit c` for every
    branch (`m = −σ/5`), by the per-degree-class check (leaf/deg-2 via `fstar_ge_7_100`/`cherry_anchor_ge`;
    deg-3 `σ<1/32`; deg-4 `σ≤5/384`; deg≥5 `bY≤1/5`). -/
theorem phi_lb_general (σ : ℝ) (hσ0 : 0 < σ) (hσhi : σ ≤ 5/384) (c : Branch) :
    (-σ/5) + σ * bY c ≤ ρwit c := by
  have hy0 := bY_nonneg c
  have hyd := bY_le_inv_deg c
  have hanchor := cherry_anchor_ge
  have hfst : (7:ℝ)/100 ≤ FSTAR := by
    rw [FSTAR]
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (64/621:ℝ) by norm_num)
    rw [show (64/621:ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv] at h
    rw [show ((621/64:ℝ)⁻¹) = 64/621 by norm_num] at h
    linarith
  rcases hbc : bcc c with _ | _ | _ | _ | n
  · have hby1 : bY c = 1 := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact bY_leaf
    have hrc : ρwit c = FSTAR := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact ρwit_leaf
    rw [hby1, hrc]; linarith
  · have hby3 := bY_ge_third_of_bcc1 c hbc
    have hrc : ρwit c = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c - 1/3) := by simp only [ρwit, hbc]
    rw [hrc]
    nlinarith [hanchor, hσhi, mul_nonneg (show (0:ℝ) ≤ bY c - 1/3 by linarith)
      (show (0:ℝ) ≤ 1/4 - σ by linarith)]
  · have hby : bY c ≤ 1/3 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/32) * bY c := by simp only [ρwit, hbc]
    rw [hrc]
    nlinarith [hσ0, mul_nonneg hy0 (show (0:ℝ) ≤ 1/32 - σ by linarith)]
  · have hby : bY c ≤ 1/4 := by rw [hbc] at hyd; norm_num at hyd; linarith
    have hrc : ρwit c = (1/384) * bY c := by simp only [ρwit, hbc]
    rw [hrc]
    nlinarith [hσ0, mul_nonneg (show (0:ℝ) ≤ 1/4 - bY c by linarith)
      (show (0:ℝ) ≤ 5/384 - σ by linarith)]
  · have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hby : bY c ≤ 1/5 := by
      rw [hbc] at hyd
      have hd5 : (5:ℝ) ≤ ((n + 4 : ℕ) : ℝ) + 1 := by push_cast; linarith
      have hle : (1:ℝ) / (((n + 4 : ℕ) : ℝ) + 1) ≤ 1/5 :=
        one_div_le_one_div_of_le (by norm_num) hd5
      linarith
    have hrc : ρwit c = 0 := by
      cases c with
      | node cs => simp only [bcc] at hbc; exact ρwit_node_high (by omega)
    rw [hrc]; nlinarith [hσ0, hby]

/-- **The large-`d` (deg-5) tail regime, `∀ d ≥ 65`.**  `IsSubaction ρwit` at any node of degree
    `d = |cs|+1 ≥ 65` with arbitrary children — via `tail_decouple` at the all-deg-5 reference
    `S0 = |cs|/5`, the per-child min `phi_lb_general`, and `B = F* − log((6d−1)/(5d)) ≥ 0` (`log(6/5) ≤ F*`
    since `(6/5)¹¹ ≤ 621/64`).  Closes the entire infinite tail. -/
theorem subaction_tail_deg5 (cs : List Branch) (hlen : 64 ≤ cs.length) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  have hL : (64:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hlen
  have hDpos : (0:ℝ) < ((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5 := by positivity
  set σ : ℝ := 1 / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5) with hσdef
  have hσ0 : 0 < σ := by rw [hσdef]; positivity
  have hσle : σ ≤ 5/384 := by
    rw [hσdef, div_le_iff₀ hDpos]; nlinarith [hL]
  refine tail_decouple cs ((cs.length : ℝ) / 5) (-σ/5) h4 (by positivity) ?_ ?_
  · intro c _
    rw [show (1 : ℝ) / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5) = σ from hσdef.symm]
    exact phi_lb_general σ hσ0 hσle c
  · have hcancel : (cs.length : ℝ) * (-σ/5)
        + (cs.length : ℝ) / 5 / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5) = 0 := by
      rw [hσdef]; field_simp; ring
    have harg : (1 : ℝ) + (cs.length : ℝ) / 5 / ((cs.length : ℝ) + 1)
        = (6 * (cs.length : ℝ) + 5) / (5 * ((cs.length : ℝ) + 1)) := by
      field_simp; ring
    have hlogle : Real.log (1 + (cs.length : ℝ) / 5 / ((cs.length : ℝ) + 1)) ≤ FSTAR := by
      rw [harg]
      have hb65 : (6 * (cs.length : ℝ) + 5) / (5 * ((cs.length : ℝ) + 1)) ≤ 6/5 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [hL]
      have hmono : Real.log ((6 * (cs.length : ℝ) + 5) / (5 * ((cs.length : ℝ) + 1)))
          ≤ Real.log (6/5) := Real.log_le_log (by positivity) hb65
      have hlog65 : Real.log (6/5 : ℝ) ≤ FSTAR := by
        rw [FSTAR]
        have e : Real.log ((6/5 : ℝ) ^ (11:ℕ)) = 11 * Real.log (6/5) := by rw [Real.log_pow]; norm_num
        have hle : Real.log ((6/5 : ℝ) ^ (11:ℕ)) ≤ Real.log (621/64) :=
          Real.log_le_log (by positivity) (by norm_num)
        rw [e] at hle; linarith
      linarith
    linarith [hcancel, hlogle]

end BGSCL
end R3Cert
