/-
  The deg≥5 tail crux family + the 27·23 tie identity (2026-09-03).

  Two pieces of `IsSubaction ρwit` beyond the degree-3/4 core:

  * `tail_all_deg4` — the CRUX of the deg≥5 tail.  For a degree-`d` hub (`d ≥ 1`) whose children are all
    degree-4 at the maximal message `1/4` (`S = (d−1)/4`, `ρwit(node)=0`), the local excess obeys
    `log((5d−1)/(4d)) − F* ≤ (d−1)/1536`.  This is the flattest per-type tail family (`ρ = bY/384`), min
    slack `+0.0057` at `d=18`.  Proof: `log((5d−1)/(4d)) = log(5/4) + log(1 − 1/(5d)) ≤ log(5/4) − 1/(5d)`
    (concavity, `Real.log_le_sub_one_of_pos`), then the atom `log(5/4) − F* ≤ 1/55` reduces it to a rational
    quadratic in `d` with NEGATIVE discriminant (`55d² − 1591d + 16896 > 0`, via `sq_nonneg (110d − 1591)`).

  * `subaction_tail_tie_d6` — the 27·23 = 621 tie.  A degree-6 hub with five cherry children (each deg-2 at
    `bY = 1/3`, `ρwit = 2F*−log(3/2)`; `ρwit(node)=0`) meets `(SUB)` with EXACT equality, because
    `(23/18)·(3/2)⁵ = 621/64`, i.e. `log(23/18) + 5·log(3/2) = 11·F* = log(621/64)`.

  Kernel-checked, no `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction

namespace R3Cert
namespace BGSCL

open Real

/-! ### The deg≥5 tail crux: the all-degree-4 `d`-family. -/

/-- **`tail_all_deg4`.**  For every real `d ≥ 1`, `log((5d−1)/(4d)) − F* ≤ (d−1)/1536`.  This is the binding
    per-type family of the deg≥5 tail (all children degree-4 at message `1/4`); the slack is convex in `d`
    with a single interior minimum `+0.0057` at `d = 18`. -/
theorem tail_all_deg4 (d : ℝ) (hd : 1 ≤ d) :
    Real.log ((5 * d - 1) / (4 * d)) - FSTAR ≤ (d - 1) / 1536 := by
  have hd0 : (0 : ℝ) < d := by linarith
  have h5d : (0 : ℝ) < 5 * d := by linarith
  -- factor: (5d−1)/(4d) = (5/4)·(1 − 1/(5d))
  have hfact : (5 * d - 1) / (4 * d) = (5 / 4) * (1 - 1 / (5 * d)) := by
    field_simp
  have harg_pos : (0 : ℝ) < 1 - 1 / (5 * d) := by
    have : 1 / (5 * d) < 1 := by rw [div_lt_one h5d]; linarith
    linarith
  have hsplit : Real.log ((5 * d - 1) / (4 * d)) = Real.log (5 / 4) + Real.log (1 - 1 / (5 * d)) := by
    rw [hfact, Real.log_mul (by norm_num) (ne_of_gt harg_pos)]
  -- concavity: log(1 − 1/(5d)) ≤ −1/(5d)
  have hlog1 : Real.log (1 - 1 / (5 * d)) ≤ -(1 / (5 * d)) := by
    have h := Real.log_le_sub_one_of_pos harg_pos
    linarith
  -- the atom log(5/4) − F* ≤ 1/55
  have henc : Real.log (5 / 4) - FSTAR ≤ 1 / 55 := log54_sub_fstar_le'
  -- rational quadratic: 1/55 − 1/(5d) ≤ (d−1)/1536  (discriminant of 55d²−1591d+16896 is < 0)
  have hquad : (1 : ℝ) / 55 - 1 / (5 * d) ≤ (d - 1) / 1536 := by
    rw [← sub_nonneg]
    have hden : (0 : ℝ) < 422400 * d := by positivity
    have hnum : (0 : ℝ) ≤ 275 * d ^ 2 - 7955 * d + 84480 := by
      nlinarith [sq_nonneg (110 * d - 1591)]
    have hid : (d - 1) / 1536 - (1 / 55 - 1 / (5 * d))
        = (275 * d ^ 2 - 7955 * d + 84480) / (422400 * d) := by
      field_simp; ring
    rw [hid]; exact div_nonneg hnum (le_of_lt hden)
  linarith [hsplit, hlog1, henc, hquad]

/-- **`tail_all_deg3`.**  For every real `d ≥ 1`, `log((4d−1)/(3d)) − F* ≤ (d−1)/96`.  The all-degree-3 tail
    family (children at message `1/3`, `S = (d−1)/3`; `ρwit = bY/32`), min slack `+0.0119` at `d = 5`.  Same
    concavity + quadratic recipe as `tail_all_deg4`, with the atom `log(4/3) − F* ≤ 1/12` and the quadratic
    `d² − 9d + 24 > 0` (discriminant `−15`). -/
theorem tail_all_deg3 (d : ℝ) (hd : 1 ≤ d) :
    Real.log ((4 * d - 1) / (3 * d)) - FSTAR ≤ (d - 1) / 96 := by
  have hd0 : (0 : ℝ) < d := by linarith
  have h3d : (0 : ℝ) < 3 * d := by linarith
  have hfact : (4 * d - 1) / (3 * d) = (4 / 3) * (1 - 1 / (4 * d)) := by
    field_simp
  have harg_pos : (0 : ℝ) < 1 - 1 / (4 * d) := by
    have : 1 / (4 * d) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hsplit : Real.log ((4 * d - 1) / (3 * d)) = Real.log (4 / 3) + Real.log (1 - 1 / (4 * d)) := by
    rw [hfact, Real.log_mul (by norm_num) (ne_of_gt harg_pos)]
  have hlog1 : Real.log (1 - 1 / (4 * d)) ≤ -(1 / (4 * d)) := by
    have h := Real.log_le_sub_one_of_pos harg_pos
    linarith
  -- atom log(4/3) − F* ≤ 1/12  (TIGHT_HI route: fold X = (4/3)¹¹·(64/621) ≈ 2.44 > 1, Q = 11/12 > 0;
  --  degree-5 Taylor lower bound gives exp(11/12) ≥ 20637533/8294400 ≥ X)
  have henc : Real.log (4 / 3) - FSTAR ≤ 1 / 12 := by
    rw [FSTAR]
    have hXpos : (0 : ℝ) < (4 / 3 : ℝ) ^ (11 : ℕ) * (((621 / 64 : ℝ) ^ (1 : ℕ))⁻¹) := by positivity
    have hs : Real.log ((4 / 3 : ℝ) ^ (11 : ℕ) * (((621 / 64 : ℝ) ^ (1 : ℕ))⁻¹))
        = 11 * Real.log (4 / 3) - Real.log (621 / 64) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_pow]
      push_cast; ring
    have hx : |(11 / 12 : ℝ)| ≤ 1 := by rw [abs_of_nonneg (by norm_num)]; norm_num
    have hb := Real.exp_bound hx (n := 5) (by norm_num)
    have hexpge : (20637533 / 8294400 : ℝ) ≤ Real.exp (11 / 12 : ℝ) := by
      have hlo := (abs_le.mp hb).1
      norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg] at hlo
      linarith
    have hXexp : (4 / 3 : ℝ) ^ (11 : ℕ) * (((621 / 64 : ℝ) ^ (1 : ℕ))⁻¹) ≤ Real.exp (11 / 12 : ℝ) := by
      have hXle : (4 / 3 : ℝ) ^ (11 : ℕ) * (((621 / 64 : ℝ) ^ (1 : ℕ))⁻¹) ≤ (20637533 / 8294400 : ℝ) := by
        norm_num
      linarith
    have hlogX : Real.log ((4 / 3 : ℝ) ^ (11 : ℕ) * (((621 / 64 : ℝ) ^ (1 : ℕ))⁻¹)) ≤ (11 / 12 : ℝ) := by
      rw [Real.log_le_iff_le_exp hXpos]; exact hXexp
    rw [hs] at hlogX
    linarith
  -- 1/12 − 1/(4d) ≤ (d−1)/96  ⟺  d² − 9d + 24 ≥ 0 (discriminant < 0)
  have hquad : (1 : ℝ) / 12 - 1 / (4 * d) ≤ (d - 1) / 96 := by
    rw [← sub_nonneg]
    have hden : (0 : ℝ) < 96 * d := by positivity
    have hnum : (0 : ℝ) ≤ d ^ 2 - 9 * d + 24 := by nlinarith [sq_nonneg (2 * d - 9)]
    have hid : (d - 1) / 96 - (1 / 12 - 1 / (4 * d)) = (d ^ 2 - 9 * d + 24) / (96 * d) := by
      field_simp; ring
    rw [hid]; exact div_nonneg hnum (le_of_lt hden)
  linarith [hsplit, hlog1, henc, hquad]

/-! ### The 27·23 = 621 tie identity (deg-6 hub, five cherry children). -/

/-- The exact tie identity `log(23/18) + 5·log(3/2) = 11·F*`, i.e. `(23/18)·(3/2)⁵ = 621/64`. -/
theorem tie_identity_d6 : Real.log (23 / 18) + 5 * Real.log (3 / 2) = 11 * FSTAR := by
  rw [FSTAR]
  have h : Real.log (23 / 18) + 5 * Real.log (3 / 2) = Real.log (621 / 64) := by
    rw [show (621 / 64 : ℝ) = (23 / 18) * (3 / 2) ^ (5 : ℕ) by norm_num,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  rw [h]; ring

/-- **`subaction_tail_tie_d6`** — the 27·23 tie cell.  A degree-6 hub whose five children are all the cherry
    `node [leaf]` (deg-2, `bY = 1/3`, `ρwit = 2F*−log(3/2)`); the hub has `ρwit = 0` (deg ≥ 5).  `(SUB)` holds
    with EXACT equality: `log(23/18) − F* = 5·(2F*−log(3/2))`, the `621 = 27·23` face in the tail. -/
theorem subaction_tail_tie_d6 :
    (Real.log (1 + (([Branch.node [Branch.node []], Branch.node [Branch.node []],
        Branch.node [Branch.node []], Branch.node [Branch.node []],
        Branch.node [Branch.node []]]).map bY).sum
        / ((([Branch.node [Branch.node []], Branch.node [Branch.node []],
            Branch.node [Branch.node []], Branch.node [Branch.node []],
            Branch.node [Branch.node []]] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [Branch.node [Branch.node []], Branch.node [Branch.node []],
          Branch.node [Branch.node []], Branch.node [Branch.node []], Branch.node [Branch.node []]])
      ≤ (([Branch.node [Branch.node []], Branch.node [Branch.node []],
          Branch.node [Branch.node []], Branch.node [Branch.node []],
          Branch.node [Branch.node []]]).map ρwit).sum := by
  -- cherry message and ρ (as in subaction_cherry)
  have hbYc : bY (Branch.node [Branch.node []]) = 1 / 3 := by
    rw [bY_node]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, bY_leaf, Nat.cast_one, add_zero, zero_add]
    norm_num
  have hrc : ρwit (Branch.node [Branch.node []]) = 2 * FSTAR - Real.log (3 / 2) := by
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil, hbYc]; ring
  -- node has bcc = 5 ⇒ ρwit = 0
  have hrnode : ρwit (Branch.node [Branch.node [Branch.node []], Branch.node [Branch.node []],
      Branch.node [Branch.node []], Branch.node [Branch.node []], Branch.node [Branch.node []]]) = 0 := by
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, hbYc, hrc, hrnode, add_zero, Nat.reduceAdd, Nat.cast_ofNat]
  rw [show (1 : ℝ) + (1 / 3 + (1 / 3 + (1 / 3 + (1 / 3 + 1 / 3)))) / ((5 : ℝ) + 1) = 23 / 18 by norm_num]
  have hid := tie_identity_d6
  linarith

/-! ### The all-degree-2 tail family (the TIE family — tight at d=6, so the hardest of the three).

  `tail_all_deg2 (d ≥ 5) : log((4d−1)/(3d)) ≤ (2d−1)F* − (d−1)log(3/2)` (all-deg-2 hub, children at `bY=1/3`,
  `ρwit = 2F*−log(3/2)`).  Equality at d=6 (the `27·23` tie), so it is NOT closable by a single concavity bound
  over ℝ; dispatch on the natural degree: d=5 (fold), d=6 (exact via `tie_identity_d6`), d≥7 (concavity + the
  quadratic `q(x) = 4a·x² − 4(a+p)·x + 1 ≥ 0`, `a = 2F*−log(3/2)`, `p = log(4/3)−F*`, whose real roots are both
  `< 7`; via `q(x) = 4a(x−7)² + 4(13a−p)(x−7) + (1−28(p−6a))` with the two enclosures below). -/

/-- Enclosure `13a − p ≥ 0` (`a = 2F*−log(3/2)`, `p = log(4/3)−F*`), i.e. `0 ≤ 27F* − 13log(3/2) − log(4/3)`;
    the `q'(7) ≥ 0` leg.  Direct `X ≥ 1` fold `(621/64)²⁷ ≥ (3/2)¹⁴³·(4/3)¹¹`. -/
theorem henc_deg2_qp7 : (0 : ℝ) ≤ 27 * FSTAR - 13 * Real.log (3 / 2) - Real.log (4 / 3) := by
  have hX : (1 : ℝ) ≤ (621 / 64 : ℝ) ^ (27 : ℕ) / ((3 / 2 : ℝ) ^ (143 : ℕ) * (4 / 3 : ℝ) ^ (11 : ℕ)) := by
    rw [le_div_iff₀ (by positivity)]; norm_num
  have hlogX := Real.log_nonneg hX
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at hlogX
  rw [FSTAR]; push_cast at hlogX ⊢; linarith

/-- Enclosure `p − 6a ≤ 1/28`, i.e. `log(4/3) + 6log(3/2) − 13F* ≤ 1/28`; the `q(7) ≥ 0` leg.  TIGHT_HI:
    fold `Y = (4/3)¹¹·(3/2)⁶⁶·(64/621)¹³ ≈ 1.467 > 1`, `Q = 11/28`; degree-4 Taylor gives
    `exp(11/28) ≥ 29088281/19668992 ≥ Y`. -/
theorem henc_deg2_q7 : Real.log (4 / 3) + 6 * Real.log (3 / 2) - 13 * FSTAR ≤ 1 / 28 := by
  rw [FSTAR]
  have hXpos : (0 : ℝ) < (4 / 3 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (66 : ℕ) * (((621 / 64 : ℝ) ^ (13 : ℕ))⁻¹) := by
    positivity
  have hs : Real.log ((4 / 3 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (66 : ℕ) * (((621 / 64 : ℝ) ^ (13 : ℕ))⁻¹))
      = 11 * Real.log (4 / 3) + 66 * Real.log (3 / 2) - 13 * Real.log (621 / 64) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hx : |(11 / 28 : ℝ)| ≤ 1 := by rw [abs_of_nonneg (by norm_num)]; norm_num
  have hb := Real.exp_bound hx (n := 4) (by norm_num)
  have hexpge : (29088281 / 19668992 : ℝ) ≤ Real.exp (11 / 28 : ℝ) := by
    have hlo := (abs_le.mp hb).1
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg] at hlo
    linarith
  have hXexp : (4 / 3 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (66 : ℕ) * (((621 / 64 : ℝ) ^ (13 : ℕ))⁻¹)
      ≤ Real.exp (11 / 28 : ℝ) := by
    have hXle : (4 / 3 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (66 : ℕ) * (((621 / 64 : ℝ) ^ (13 : ℕ))⁻¹)
        ≤ (29088281 / 19668992 : ℝ) := by norm_num
    linarith
  have hlogX : Real.log ((4 / 3 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (66 : ℕ) * (((621 / 64 : ℝ) ^ (13 : ℕ))⁻¹))
      ≤ (11 / 28 : ℝ) := by
    rw [Real.log_le_iff_le_exp hXpos]; exact hXexp
  rw [hs] at hlogX
  linarith

/-- The all-deg-2 tail family for real `x ≥ 7` (concavity + the quadratic `q(x) ≥ 0`). -/
theorem tail_all_deg2_large (x : ℝ) (hx : 7 ≤ x) :
    Real.log ((4 * x - 1) / (3 * x)) ≤ (2 * x - 1) * FSTAR - (x - 1) * Real.log (3 / 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hfact : (4 * x - 1) / (3 * x) = (4 / 3) * (1 - 1 / (4 * x)) := by field_simp
  have harg : (0 : ℝ) < 1 - 1 / (4 * x) := by
    have : 1 / (4 * x) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hsplit : Real.log ((4 * x - 1) / (3 * x)) = Real.log (4 / 3) + Real.log (1 - 1 / (4 * x)) := by
    rw [hfact, Real.log_mul (by norm_num) (ne_of_gt harg)]
  have hlog1 : Real.log (1 - 1 / (4 * x)) ≤ -(1 / (4 * x)) := by
    have := Real.log_le_sub_one_of_pos harg; linarith
  have ha : (0 : ℝ) ≤ 2 * FSTAR - Real.log (3 / 2) := cherry_anchor_nonneg
  have hqp7 := henc_deg2_qp7
  have hq7 := henc_deg2_q7
  -- log(4/3) − 1/(4x) ≤ (2x−1)F* − (x−1)log(3/2)  ⟺  q(x) ≥ 0
  have hq : Real.log (4 / 3) - 1 / (4 * x) ≤ (2 * x - 1) * FSTAR - (x - 1) * Real.log (3 / 2) := by
    rw [← sub_nonneg]
    have h4x : (0 : ℝ) < 4 * x := by linarith
    have hpoly : (2 * x - 1) * FSTAR - (x - 1) * Real.log (3 / 2) - (Real.log (4 / 3) - 1 / (4 * x))
        = (4 * (2 * FSTAR - Real.log (3 / 2)) * x ^ 2
            - 4 * ((2 * FSTAR - Real.log (3 / 2)) + (Real.log (4 / 3) - FSTAR)) * x + 1) / (4 * x) := by
      field_simp; ring
    rw [hpoly]
    apply div_nonneg _ (le_of_lt h4x)
    nlinarith [mul_nonneg ha (sq_nonneg (x - 7)),
      mul_nonneg hqp7 (show (0 : ℝ) ≤ x - 7 by linarith), hq7, ha, hx]
  linarith [hsplit, hlog1, hq]

/-- d=5 leg of the all-deg-2 family: `log(19/15) ≤ 9F* − 4log(3/2)` (fold `X < 1`). -/
theorem tail_deg2_d5 : Real.log (19 / 15) ≤ 9 * FSTAR - 4 * Real.log (3 / 2) := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (19 / 15 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (44 : ℕ) * (((621 / 64 : ℝ) ^ (9 : ℕ))⁻¹) := by
    positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hs : Real.log ((19 / 15 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (44 : ℕ) * (((621 / 64 : ℝ) ^ (9 : ℕ))⁻¹))
      = 11 * Real.log (19 / 15) + 44 * Real.log (3 / 2) - 9 * Real.log (621 / 64) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hs] at hr
  have hnum : (19 / 15 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (44 : ℕ) * (((621 / 64 : ℝ) ^ (9 : ℕ))⁻¹) - 1 ≤ 0 := by
    norm_num
  linarith

/-- **`tail_all_deg2`** — the all-deg-2 tail family for every natural degree `d ≥ 5`.  Dispatches d=5 (fold),
    d=6 (the exact 27·23 tie via `tie_identity_d6`), d≥7 (`tail_all_deg2_large`). -/
theorem tail_all_deg2 (d : ℕ) (hd : 5 ≤ d) :
    Real.log ((4 * (d : ℝ) - 1) / (3 * d)) ≤ (2 * d - 1) * FSTAR - (d - 1) * Real.log (3 / 2) := by
  rcases (show d = 5 ∨ d = 6 ∨ 7 ≤ d by omega) with h | h | h
  · subst h
    have h5 := tail_deg2_d5
    push_cast
    rw [show (4 * (5 : ℝ) - 1) / (3 * 5) = 19 / 15 by norm_num]
    linarith
  · subst h
    have hid := tie_identity_d6
    push_cast
    rw [show (4 * (6 : ℝ) - 1) / (3 * 6) = 23 / 18 by norm_num]
    linarith
  · have hx : (7 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    exact tail_all_deg2_large (d : ℝ) hx

end BGSCL
end R3Cert
