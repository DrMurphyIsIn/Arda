/-
  Reduce-to-uniform, deg≥5 tail closed for hub degree d ∈ [5,9] (2026-09-03).

  Instantiates the counts-exchange decouple (`tail_sub_of_perchild`) against the ACTUAL
  witness `ρwit`, using the all-deg-2 reference (`Sstar = (d−1)/3`).  For d ∈ [5,9] this
  reference dominates every child degree class (at d=10 deg-4 children break it → the
  all-deg-4 reference regime, a separate slab).  Two transcendental gates + the deg-2 slope
  + a `bcc`-case analysis discharge the per-child bound.

  Kernel-checked vs `R3Cert.BGSCLInduction`.  No `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionTail
import R3Cert.BGSCLSubactionExch

namespace R3Cert
namespace BGSCL

open Real

/-- **Leaf gate.**  `2/19 ≤ log(3/2) − F*` (actual ≈ 0.199).  Via
    `11·(log(3/2)−F*) = log((3/2)¹¹·64/621) = log(6561/736)` and `exp(22/19) ≤ exp 2 = (exp 1)² ≤ 7.389057 ≤ 6561/736`. -/
theorem leaf_gate : (2 : ℝ) / 19 ≤ Real.log (3 / 2) - FSTAR := by
  rw [FSTAR]
  have hA : (0 : ℝ) < (3 / 2 : ℝ) ^ 11 * (64 / 621) := by norm_num
  have hsplit : Real.log ((3 / 2 : ℝ) ^ 11 * (64 / 621))
      = 11 * Real.log (3 / 2) - Real.log (621 / 64) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
        show (64 / 621 : ℝ) = (621 / 64 : ℝ)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  have hexp : Real.exp (22 / 19 : ℝ) ≤ 7.389057 := by
    have h1 : Real.exp (22 / 19 : ℝ) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by
      gcongr
      exact le_of_lt Real.exp_one_lt_d9
    calc Real.exp (22 / 19 : ℝ) ≤ Real.exp 1 ^ 2 := by rw [h2] at h1; exact h1
      _ ≤ (2.7182818286 : ℝ) ^ 2 := h4
      _ ≤ 7.389057 := by norm_num
  have hlog : (22 : ℝ) / 19 ≤ Real.log ((3 / 2 : ℝ) ^ 11 * (64 / 621)) := by
    rw [Real.le_log_iff_exp_le hA]
    calc Real.exp (22 / 19 : ℝ) ≤ 7.389057 := hexp
      _ ≤ (3 / 2 : ℝ) ^ 11 * (64 / 621) := by norm_num
  rw [hsplit] at hlog
  linarith

/-- **Upper gate (tight).**  `2F* − log(3/2) ≤ 419/53760` (actual ≈ 0.007707; RHS ≈ 0.007794, margin ≈ 9e-5).
    The deg-4-at-d=9 threshold — needs the exp LOWER bound (degree-4 Taylor via `Real.exp_bound`), the
    degree-1 `log x ≤ x−1` is too loose.  Covers the deg-3/deg-4/deg≥5 per-child bounds for all d ∈ [5,9]. -/
theorem upper_gate : 2 * FSTAR - Real.log (3 / 2) ≤ (419 : ℝ) / 53760 := by
  rw [FSTAR]
  have harg : (0 : ℝ) < (621 / 64 : ℝ) ^ 2 * (2 / 3) ^ 11 := by norm_num
  have hsplit : Real.log ((621 / 64 : ℝ) ^ 2 * (2 / 3) ^ 11)
      = 2 * Real.log (621 / 64) - 11 * Real.log (3 / 2) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
        show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_pow, Real.log_inv]
    push_cast; ring
  have hx : |(4609 / 53760 : ℝ)| ≤ 1 := by rw [abs_of_nonneg (by norm_num)]; norm_num
  have hb := Real.exp_bound hx (n := 4) (by norm_num)
  have hexpge : (174730835713527011327 / 160375590661128192000 : ℝ) ≤ Real.exp (4609 / 53760) := by
    have hlo := (abs_le.mp hb).1
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg] at hlo
    linarith
  have hargle : (621 / 64 : ℝ) ^ 2 * (2 / 3) ^ 11
      ≤ (174730835713527011327 / 160375590661128192000 : ℝ) := by norm_num
  have hlog : Real.log ((621 / 64 : ℝ) ^ 2 * (2 / 3) ^ 11) ≤ (4609 / 53760 : ℝ) := by
    rw [Real.log_le_iff_le_exp harg]; linarith
  rw [hsplit] at hlog
  linarith

/-- Per-child bound at d=5 (all-deg-2 reference): for EVERY branch `c`,
    `bY c/(5+4/3) + (2F*−log(3/2)−1/19) ≤ ρwit c`.  `bcc`-case analysis; every case linear (fixed d). -/
theorem tail_perchild_d5 (c : Branch) :
    bY c / ((5 : ℝ) + 4 / 3) + (2 * FSTAR - Real.log (3 / 2) - 1 / 19) ≤ ρwit c := by
  have hbd : bY c / ((5 : ℝ) + 4 / 3) = 3 * bY c / 19 := by
    rw [show (5 : ℝ) + 4 / 3 = 19 / 3 by norm_num]; ring
  rw [hbd]
  have hlf := leaf_gate
  have hup := upper_gate
  have hy0 := bY_nonneg c
  rcases hbcc : bcc c with _ | _ | _ | _ | n
  · have hy1 : bY c ≤ 1 := bY_le_one c
    simp only [ρwit, hbcc]; linarith
  · have hy13 : (1 : ℝ) / 3 ≤ bY c := bY_ge_third_of_bcc1 c hbcc
    simp only [ρwit, hbcc]; linarith
  · have hyinv := bY_le_inv_deg c
    rw [hbcc] at hyinv; norm_num at hyinv
    simp only [ρwit, hbcc]; linarith
  · have hyinv := bY_le_inv_deg c
    rw [hbcc] at hyinv; norm_num at hyinv
    simp only [ρwit, hbcc]; linarith
  · have hyinv := bY_le_inv_deg c
    rw [hbcc] at hyinv
    have hy5 : bY c ≤ 1 / 5 := by
      refine le_trans hyinv ?_
      apply one_div_le_one_div_of_le (by norm_num)
      push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    simp only [ρwit, hbcc]; linarith

/-- **Tail SUB for a degree-5 hub (d=5), any 4 children.**  The full reduce-to-uniform pipeline
    end-to-end against `ρwit`: counts-exchange decouple (`tail_sub_of_perchild`) + the all-deg-2
    reference (`tail_all_deg2`) + the per-child bound (`tail_perchild_d5`).  This is the deg≥5 tail
    cell of `IsSubaction ρwit` at d=5 (`ρwit(node)=0`).  d=6..9 are the identical instance with the
    concrete degree; d≥10 uses the all-deg-4 reference (a separate slab). -/
theorem tail_sub_d5 (cs : List Branch) (hlen : cs.length = 4) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs)
      ≤ (cs.map ρwit).sum := by
  have hr0 : ρwit (Branch.node cs) = 0 := by
    have hb : bcc (Branch.node cs) = 4 := by simp [bcc, hlen]
    simp [ρwit, hb]
  rw [hr0, add_zero, hlen]
  set L : List (ℝ × ℝ) := cs.map (fun c => (bY c, ρwit c)) with hLdef
  have hfst : (L.map Prod.fst).sum = (cs.map bY).sum := by rw [hLdef, List.map_map]; rfl
  have hsnd : (L.map Prod.snd).sum = (cs.map ρwit).sum := by rw [hLdef, List.map_map]; rfl
  have hLlen : L.length = 4 := by rw [hLdef, List.length_map, hlen]
  have hbY : ∀ p ∈ L, 0 ≤ p.1 := by
    intro p hp; rw [hLdef, List.mem_map] at hp
    obtain ⟨c, _, rfl⟩ := hp; exact bY_nonneg c
  have href : Real.log (1 + (4 / 3 : ℝ) / 5) - FSTAR ≤ 4 * (2 * FSTAR - Real.log (3 / 2)) := by
    have ht := tail_all_deg2 5 (by norm_num)
    push_cast at ht
    norm_num at ht
    rw [show (1 : ℝ) + (4 / 3) / 5 = 19 / 15 by norm_num]
    linarith
  have hchild : ∀ p ∈ L, p.1 / ((5 : ℝ) + 4 / 3) + (2 * FSTAR - Real.log (3 / 2) - 1 / 19) ≤ p.2 := by
    intro p hp; rw [hLdef, List.mem_map] at hp
    obtain ⟨c, _, rfl⟩ := hp; exact tail_perchild_d5 c
  have hconsist : 4 * (2 * FSTAR - Real.log (3 / 2))
      ≤ (4 / 3 : ℝ) / (5 + 4 / 3) + (L.length : ℝ) * (2 * FSTAR - Real.log (3 / 2) - 1 / 19) := by
    rw [hLlen]; push_cast
    rw [show (4 / 3 : ℝ) / (5 + 4 / 3) = 4 / 19 by norm_num]; linarith
  have key := tail_sub_of_perchild (d := 5) (Sstar := 4 / 3)
    (β := 2 * FSTAR - Real.log (3 / 2) - 1 / 19) (C := 4 * (2 * FSTAR - Real.log (3 / 2)))
    (by norm_num) (by norm_num) L hbY href hchild hconsist
  rw [hfst, hsnd] at key
  rw [show ((4 : ℕ) : ℝ) + 1 = 5 by norm_num]
  exact key

end BGSCL
end R3Cert
