/-
  Dogfood_enclosure_tree -- the Telperion `enclosure_tree` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 1; A N2/N3/N4, B C2, C 4.7, D 4) regenerating hand-proof sites, 2026-09-22:

    LiLadderHeight.lean   `li_rungs_of_bands_4000_upto`: n <= 18848 -> (n + 1 : R) <= 3 pi 4000 / 2
                          by Real.pi_gt_d4 (`li_height_rate_4000`, `_rate`);
    LiLadderSharp.lean    `li_rungs_of_bands_4000_upto_sharp`: n <= 25128 -> (n + 1 : R) <=
                          2 pi (4000 - 1/2) by Real.pi_gt_d6 (`li_sharp_rate_4000`, `_rate`);
    quasicrystal LeakageDictionary.lean:276-359, the nine bracket lemmas (`qc_*`), regenerated on
                          Mathlib alone -- that island (v4.32.0) is not importable here; its own
                          probe, quasicrystal/lean/Probes/Dogfood_enclosure_tree.lean, carries the
                          cross-checks against the originals;
    route coverage (`rt_*`): every tactic skeleton the sites above do not exercise.

  The block between the telperion provenance header and `end DogfoodEnclosureTree` is the FROZEN
  emitter output (examples/li_positivity/dogfood_enclosure_tree.py regenerates it; a test pins the
  bytes).  The cross-checks after it feed each emitted rate lemma to the hand theorem whose side
  condition it replaces, so the kernel confirms the regeneration is interchangeable with the hand
  `pi_gt_dN` step.  Nothing in LiLadderHeight / LiLadderSharp is modified.

  Run: cd telperion/examples/li_positivity/lean && lake env lean Probes/Dogfood_enclosure_tree.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a finite rational
  arithmetic fact about real constants (or one elementary real inequality); the cross-checks
  compose with CONDITIONAL hand theorems and inherit their hypotheses unchanged.
-/
/- telperion 0.1.6 | family DogfoodEnclosureTree | input-hash d989558949852694
   40 theorems, 54 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import LiLadderHeight
import LiLadderSharp

namespace DogfoodEnclosureTree

/-- `li_height_rate_4000_n0` -- a certified RATIONAL ENCLOSURE of `Real.pi`.
    Route: Mathlib's pi ladder rung d4 (Real.pi_gt_d4, Real.pi_lt_d4).
    Exact fold [6283/2000, 3927/1250], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem li_height_rate_4000_n0 :
    (6283 / 2000 : ℝ) < Real.pi ∧ Real.pi < (3927 / 1250 : ℝ) := by
  constructor <;> linarith [Real.pi_gt_d4, Real.pi_lt_d4]

/-- `li_height_rate_4000` -- a certified RATIONAL ENCLOSURE of `3 * Real.pi * 4000 / 2`.
    Route: division by a constant (linarith).
    Exact fold [18849, 94248/5], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem li_height_rate_4000 :
    (18849 : ℝ) < 3 * Real.pi * 4000 / 2 ∧ 3 * Real.pi * 4000 / 2 < (94248 / 5 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := li_height_rate_4000_n0
  constructor <;> linarith

/-- `li_height_rate_4000_rate` -- the RATE COROLLARY of `li_height_rate_4000`: every `n <= 18848`
    satisfies `(n + 1 : R) <= E`, because the certified lower bound
    18849 is at least 18848 + 1 = 18849 EXACTLY.  The generator refuses
    a cap the bound does not reach; it never rounds up.  A finite arithmetic
    fact; nothing about RH.  conjecture1_proved = False. -/
theorem li_height_rate_4000_rate (n : ℕ) (hn : n ≤ 18848) :
    (n + 1 : ℝ) ≤ 3 * Real.pi * 4000 / 2 := by
  obtain ⟨hlo, _hhi⟩ := li_height_rate_4000
  have hn' : (n : ℝ) ≤ (18848 : ℝ) := by exact_mod_cast hn
  linarith

/-- `li_sharp_rate_4000_n0` -- a certified RATIONAL ENCLOSURE of `Real.pi`.
    Route: Mathlib's pi ladder rung d6 (Real.pi_gt_d6, Real.pi_lt_d6).
    Exact fold [392699/125000, 3141593/1000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem li_sharp_rate_4000_n0 :
    (392699 / 125000 : ℝ) < Real.pi ∧ Real.pi < (3141593 / 1000000 : ℝ) := by
  constructor <;> linarith [Real.pi_gt_d6, Real.pi_lt_d6]

/-- `li_sharp_rate_4000` -- a certified RATIONAL ENCLOSURE of `2 * Real.pi * (4000 - 1 / 2)`.
    Route: constant scaling (linarith).
    Exact fold [3141199301/125000, 25129602407/1000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem li_sharp_rate_4000 :
    (3141199301 / 125000 : ℝ) < 2 * Real.pi * (4000 - 1 / 2) ∧
      2 * Real.pi * (4000 - 1 / 2) < (25129602407 / 1000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := li_sharp_rate_4000_n0
  constructor <;> linarith

/-- `li_sharp_rate_4000_rate` -- the RATE COROLLARY of `li_sharp_rate_4000`: every `n <= 25128`
    satisfies `(n + 1 : R) <= E`, because the certified lower bound
    3141199301/125000 is at least 25128 + 1 = 25129 EXACTLY.  The generator refuses
    a cap the bound does not reach; it never rounds up.  A finite arithmetic
    fact; nothing about RH.  conjecture1_proved = False. -/
theorem li_sharp_rate_4000_rate (n : ℕ) (hn : n ≤ 25128) :
    (n + 1 : ℝ) ≤ 2 * Real.pi * (4000 - 1 / 2) := by
  obtain ⟨hlo, _hhi⟩ := li_sharp_rate_4000
  have hn' : (n : ℝ) ≤ (25128 : ℝ) := by exact_mod_cast hn
  linarith

/-- `qc_sqrt_five_bounds` -- a certified RATIONAL ENCLOSURE of `Real.sqrt 5`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [5, 5] by rational squares (lo^2 vs 5, 5 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_sqrt_five_bounds :
    (1118033988749 / 500000000000 : ℝ) < Real.sqrt 5 ∧
      Real.sqrt 5 < (2236067977501 / 1000000000000 : ℝ) := by
  have harg : (0 : ℝ) ≤ 5 := by norm_num
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn]

/-- `qc_sqrt_inner_bounds` -- a certified RATIONAL ENCLOSURE of `Real.sqrt (10 - 2 * Real.sqrt 5)`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [2763932022499/500000000000, 1381966011251/250000000000] by rational squares (lo^2 vs 2763932022499/500000000000, 1381966011251/250000000000 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_sqrt_inner_bounds :
    (1175570504583 / 500000000000 : ℝ) < Real.sqrt (10 - 2 * Real.sqrt 5) ∧
      Real.sqrt (10 - 2 * Real.sqrt 5) < (2351141009173 / 1000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_sqrt_five_bounds
  have harg : (0 : ℝ) ≤ 10 - 2 * Real.sqrt 5 := by linarith
  have h2 : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt (10 - 2 * Real.sqrt 5) := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn, h0lo, h0hi]

/-- `qc_dhKappa_bounds` -- a certified RATIONAL ENCLOSURE of `(Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)`.
    Route: le_div_iff0 / div_le_iff0 against a certified positive denominator.
    Exact fold [351141009166/1236067977501, 351141009173/1236067977498], inside the stated bracket with slack (3506706343459/1236067977501000000000, 666445326727/309016994374500000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_dhKappa_bounds :
    (284079041 / 1000000000 : ℝ) < (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1) ∧
      (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1) < (142039523 / 500000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_sqrt_inner_bounds
  obtain ⟨h1lo, h1hi⟩ := qc_sqrt_five_bounds
  have hden : (0 : ℝ) < Real.sqrt 5 - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hden]
    linarith
  · rw [div_lt_iff₀ hden]
    linarith

/-- `qc_log_three_halves_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 2)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [6070423640075591/14971509072199680, 6070425424818551/14971509072199680], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_three_halves_bounds :
    (6070423640075591 / 14971509072199680 : ℝ) ≤ Real.log (3 / 2) ∧
      Real.log (3 / 2) ≤ (6070425424818551 / 14971509072199680 : ℝ) := by
  have hx : |((-(1 / 2)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (-(1 / 2)) = (3 / 2) by norm_num] at h
  generalize Real.log (3 / 2) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `qc_log_two_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log 2`.
    Route: Real.log_two_gt_d9 / Real.log_two_lt_d9.
    Exact fold [6931471803/10000000000, 108304247/156250000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_two_bounds :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧ Real.log 2 < (108304247 / 156250000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  norm_num at h1 h2
  constructor <;> linarith

/-- `qc_log_six_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log 6`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [52393246555737784416259/29241228656640000000000, 52393250070805106822899/29241228656640000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_six_bounds :
    (52393246555737784416259 / 29241228656640000000000 : ℝ) < Real.log 6 ∧
      Real.log 6 < (52393250070805106822899 / 29241228656640000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_log_two_bounds
  obtain ⟨h1lo, h1hi⟩ := qc_log_three_halves_bounds
  have hfold : Real.log 6 = Real.log 2 + Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : (2 * 2 : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `qc_log_three_bounds` -- a certified RATIONAL ENCLOSURE of `Real.log 3`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [32124771363880211544067/29241228656640000000000, 32124774864326919622387/29241228656640000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem qc_log_three_bounds :
    (32124771363880211544067 / 29241228656640000000000 : ℝ) < Real.log 3 ∧
      Real.log 3 < (32124774864326919622387 / 29241228656640000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := qc_log_two_bounds
  obtain ⟨h1lo, h1hi⟩ := qc_log_three_halves_bounds
  have hfold : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `rt_sqrt_two_pi_n0` -- a certified RATIONAL ENCLOSURE of `Real.pi`.
    Route: Mathlib's pi ladder rung d2 (Real.pi_gt_d2, Real.pi_lt_d2).
    Exact fold [157/50, 63/20], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_sqrt_two_pi_n0 :
    (157 / 50 : ℝ) < Real.pi ∧ Real.pi < (63 / 20 : ℝ) := by
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

/-- `rt_sqrt_two_pi` -- a certified RATIONAL ENCLOSURE of `Real.sqrt (2 * Real.pi)`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [157/25, 63/10] by rational squares (lo^2 vs 157/25, 63/10 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_sqrt_two_pi :
    (626498204307 / 250000000000 : ℝ) < Real.sqrt (2 * Real.pi) ∧
      Real.sqrt (2 * Real.pi) < (251 / 100 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_sqrt_two_pi_n0
  have harg : (0 : ℝ) ≤ 2 * Real.pi := by linarith
  have h2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn, h0lo, h0hi]

/-- `rt_sqrt_thirty_two_pi` -- a certified RATIONAL ENCLOSURE of `Real.sqrt (32 * Real.pi)`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [2512/25, 504/5] by rational squares (lo^2 vs 2512/25, 504/5 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_sqrt_thirty_two_pi :
    (10023971268913 / 1000000000000 : ℝ) < Real.sqrt (32 * Real.pi) ∧
      Real.sqrt (32 * Real.pi) < (11 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_sqrt_two_pi_n0
  have harg : (0 : ℝ) ≤ 32 * Real.pi := by linarith
  have h2 : Real.sqrt (32 * Real.pi) ^ 2 = 32 * Real.pi := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt (32 * Real.pi) := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn, h0lo, h0hi]

/-- `rt_sqrt_two` -- a certified RATIONAL ENCLOSURE of `Real.sqrt 2`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [2, 2] by rational squares (lo^2 vs 2, 2 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_sqrt_two :
    (1414213562373 / 1000000000000 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (3 / 2 : ℝ) := by
  have harg : (0 : ℝ) ≤ 2 := by norm_num
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn]

/-- `rt_pi_sq_div_six_n0` -- a certified RATIONAL ENCLOSURE of `Real.pi ^ 2`.
    Route: pow_le_pow_left0 on a nonnegative base.
    Exact fold [24649/2500, 3969/400], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_pi_sq_div_six_n0 :
    (24649 / 2500 : ℝ) ≤ Real.pi ^ 2 ∧ Real.pi ^ 2 ≤ (3969 / 400 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_sqrt_two_pi_n0
  have hnn : (0 : ℝ) ≤ (157 / 50) := by norm_num
  have hup : (0 : ℝ) ≤ Real.pi := by linarith
  have hl : ((157 / 50) : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ hnn (by linarith) 2
  have hh : Real.pi ^ 2 ≤ ((63 / 20) : ℝ) ^ 2 :=
    pow_le_pow_left₀ hup (by linarith) 2
  constructor <;> linarith

/-- `rt_pi_sq_div_six` -- a certified RATIONAL ENCLOSURE of `Real.pi ^ 2 / 6`.
    Route: division by a constant (linarith).
    Exact fold [24649/15000, 1323/800], inside the stated bracket with slack (0, 277/800).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_pi_sq_div_six :
    (24649 / 15000 : ℝ) ≤ Real.pi ^ 2 / 6 ∧ Real.pi ^ 2 / 6 < (2 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_pi_sq_div_six_n0
  constructor <;> linarith

/-- `rt_exp_half` -- a certified RATIONAL ENCLOSURE of `Real.exp (1 / 2)`.
    Route: the order-5 Real.exp_bound box (exact rational S and radius).
    Exact fold [2637/1600, 1319/800], inside the stated bracket with slack (1/8000, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_exp_half :
    (206 / 125 : ℝ) < Real.exp (1 / 2) ∧ Real.exp (1 / 2) ≤ (1319 / 800 : ℝ) := by
  have hx : |((1 / 2) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at hb1 ⊢; linarith
  · norm_num [Nat.factorial] at hb2 ⊢; linarith

/-- `rt_exp_neg_one` -- a certified RATIONAL ENCLOSURE of `Real.exp (-1)`.
    Route: the order-6 Real.exp_bound box (exact rational S and radius).
    Exact fold [1577/4320, 1591/4320], inside the stated bracket with slack (109/21600, 37/21600).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_exp_neg_one :
    (9 / 25 : ℝ) < Real.exp (-1) ∧ Real.exp (-1) < (37 / 100 : ℝ) := by
  have hx : |((-1) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at hb1 ⊢; linarith
  · norm_num [Nat.factorial] at hb2 ⊢; linarith

/-- `rt_arctan_half` -- a certified RATIONAL ENCLOSURE of `Real.arctan (1 / 2)`.
    Route: t/2 <= arctan t <= t on [0, 1] (monotoneOn_of_deriv_nonneg, Real.le_tan).
    Exact fold [1/4, 1/2], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_arctan_half :
    (1 / 4 : ℝ) ≤ Real.arctan (1 / 2) ∧ Real.arctan (1 / 2) ≤ (1 / 2 : ℝ) := by
  have hself : ∀ u : ℝ, 0 ≤ u → Real.arctan u ≤ u := by
    intro u hu
    have h := Real.le_tan (Real.arctan_nonneg.mpr hu) (Real.arctan_lt_pi_div_two u)
    rwa [Real.tan_arctan] at h
  have hhalf : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → u / 2 ≤ Real.arctan u := by
    intro u hu0 hu1
    have hderiv : ∀ x : ℝ,
        HasDerivAt (fun x => Real.arctan x - x / 2) (1 / (1 + x ^ 2) - 1 / 2) x :=
      fun x => (Real.hasDerivAt_arctan x).sub ((hasDerivAt_id x).div_const 2)
    have hmono : MonotoneOn (fun x => Real.arctan x - x / 2) (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (continuousOn_of_forall_continuousAt fun x _ => (hderiv x).continuousAt)
        (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      have : 1 / 2 ≤ 1 / (1 + x ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      linarith
    have := hmono (Set.left_mem_Icc.mpr zero_le_one) ⟨hu0, hu1⟩ hu0
    simp only [Real.arctan_zero] at this
    linarith
  have hu0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hu1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have ha1 := hhalf (1 / 2) hu0 hu1
  have ha2 := hself (1 / 2) hu0
  constructor <;> linarith

/-- `rt_arctan_abs_n0` -- a certified RATIONAL ENCLOSURE of `Real.pi`.
    Route: Mathlib's pi ladder rung d0 (Real.pi_gt_three, Real.pi_lt_four).
    Exact fold [3, 4], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_arctan_abs_n0 :
    (3 : ℝ) < Real.pi ∧ Real.pi < (4 : ℝ) := by
  constructor <;> linarith [Real.pi_gt_three, Real.pi_lt_four]

/-- `rt_arctan_abs` -- a certified RATIONAL ENCLOSURE of `Real.arctan (Real.pi - 7 / 2)`.
    Route: |arctan t| <= |t| (Real.le_tan).
    Exact fold [-1/2, 1/2], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_arctan_abs :
    (-(1 / 2) : ℝ) ≤ Real.arctan (Real.pi - 7 / 2) ∧
      Real.arctan (Real.pi - 7 / 2) ≤ (1 / 2 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_arctan_abs_n0
  have harct : ∀ t : ℝ, |Real.arctan t| ≤ |t| := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg (Real.arctan_nonneg.mpr ht), abs_of_nonneg ht]
      have h := Real.le_tan (Real.arctan_nonneg.mpr ht) (Real.arctan_lt_pi_div_two t)
      rwa [Real.tan_arctan] at h
    · have ht' : (0 : ℝ) ≤ -t := by linarith
      have h := Real.le_tan (Real.arctan_nonneg.mpr ht') (Real.arctan_lt_pi_div_two (-t))
      rw [Real.tan_arctan, Real.arctan_neg] at h
      have hneg : Real.arctan t < 0 := by
        have := Real.arctan_strictMono ht
        simpa [Real.arctan_zero] using this
      rw [abs_of_neg hneg, abs_of_neg ht]
      linarith
  have hb : |Real.pi - 7 / 2| ≤ (1 / 2 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have hall : |Real.arctan (Real.pi - 7 / 2)| ≤ (1 / 2 : ℝ) := le_trans (harct _) hb
  obtain ⟨ha1, ha2⟩ := abs_le.mp hall
  constructor <;> linarith

/-- `rt_sqrt5_mul_log2_n0` -- a certified RATIONAL ENCLOSURE of `Real.sqrt 5`.
    Route: Real.sq_sqrt + Real.sqrt_nonneg, nlinarith against two exact rational squares.
    Checked exactly against the radicand interval [5, 5] by rational squares (lo^2 vs 5, 5 vs hi^2).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_sqrt5_mul_log2_n0 :
    (2236067977499 / 1000000000000 : ℝ) < Real.sqrt 5 ∧
      Real.sqrt 5 < (894427191 / 400000000 : ℝ) := by
  have harg : (0 : ℝ) ≤ 5 := by norm_num
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt harg
  have hn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  constructor <;> nlinarith [h2, hn]

/-- `rt_sqrt5_mul_log2_n1` -- a certified RATIONAL ENCLOSURE of `Real.log 2`.
    Route: Real.log_two_gt_d9 / Real.log_two_lt_d9.
    Exact fold [6931471803/10000000000, 108304247/156250000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_sqrt5_mul_log2_n1 :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧ Real.log 2 < (108304247 / 156250000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  norm_num at h1 h2
  constructor <;> linarith

/-- `rt_sqrt5_mul_log2` -- a certified RATIONAL ENCLOSURE of `Real.sqrt 5 * Real.log 2`.
    Route: the four McCormick corner facts, closed by linarith.
    Exact fold [15499242135625556960697/10000000000000000000000, 96870263417580177/62500000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_sqrt5_mul_log2 :
    (15499242135625556960697 / 10000000000000000000000 : ℝ) ≤ Real.sqrt 5 * Real.log 2 ∧
      Real.sqrt 5 * Real.log 2 ≤ (96870263417580177 / 62500000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_sqrt5_mul_log2_n0
  obtain ⟨h1lo, h1hi⟩ := rt_sqrt5_mul_log2_n1
  have hm1 : (0 : ℝ) ≤ (Real.sqrt 5 - (2236067977499 / 1000000000000)) * (Real.log 2 - (6931471803 / 10000000000)) :=
    mul_nonneg (by linarith) (by linarith)
  have hm2 : (0 : ℝ) ≤ ((894427191 / 400000000) - Real.sqrt 5) * (Real.log 2 - (6931471803 / 10000000000)) :=
    mul_nonneg (by linarith) (by linarith)
  have hm3 : (0 : ℝ) ≤ (Real.sqrt 5 - (2236067977499 / 1000000000000)) * ((108304247 / 156250000) - Real.log 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hm4 : (0 : ℝ) ≤ ((894427191 / 400000000) - Real.sqrt 5) * ((108304247 / 156250000) - Real.log 2) :=
    mul_nonneg (by linarith) (by linarith)
  constructor <;> linarith [hm1, hm2, hm3, hm4]

/-- `rt_four_sub_pi` -- a certified RATIONAL ENCLOSURE of `(-Real.pi) + 4`.
    Route: the exact interval fold (linarith).
    Exact fold [0, 1], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_four_sub_pi :
    (0 : ℝ) < (-Real.pi) + 4 ∧ (-Real.pi) + 4 < (1 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_arctan_abs_n0
  constructor <;> linarith

/-- `rt_log_half` -- a certified RATIONAL ENCLOSURE of `Real.log (1 / 2)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-31132380480240779/44914527216599040, -31132375126011899/44914527216599040], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_log_half :
    (-(31132380480240779 / 44914527216599040) : ℝ) ≤ Real.log (1 / 2) ∧
      Real.log (1 / 2) ≤ (-(31132375126011899 / 44914527216599040) : ℝ) := by
  have hx : |((1 / 2) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (1 / 2) = (1 / 2) by norm_num] at h
  generalize Real.log (1 / 2) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `rt_log_two_split_n0` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 2)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [35924703057241649235421/88601219586316881100800, 35924703098499807205021/88601219586316881100800], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_log_two_split_n0 :
    (35924703057241649235421 / 88601219586316881100800 : ℝ) ≤ Real.log (3 / 2) ∧
      Real.log (3 / 2) ≤ (35924703098499807205021 / 88601219586316881100800 : ℝ) := by
  have hx : |((-(1 / 2)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(1 / 2)) = (3 / 2) by norm_num] at h
  generalize Real.log (3 / 2) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `rt_log_two_split_n1` -- a certified RATIONAL ENCLOSURE of `Real.log (4 / 3)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [2851064642907216388652654419/9910470327917610477675448800, 950354880969073912310797073/3303490109305870159225149600], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_log_two_split_n1 :
    (2851064642907216388652654419 / 9910470327917610477675448800 : ℝ) ≤ Real.log (4 / 3) ∧
      Real.log (4 / 3) ≤ (950354880969073912310797073 / 3303490109305870159225149600 : ℝ) := by
  have hx : |((-(1 / 3)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(1 / 3)) = (4 / 3) by norm_num] at h
  generalize Real.log (4 / 3) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `rt_log_two_split` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 2) + Real.log (4 / 3)`.
    Route: the exact interval fold (linarith).
    Exact fold [1180156435713897420040313760199629049/1702605837855381311363319627924897792, 393385478835578655033728325011057555/567535279285127103787773209308299264], inside the stated bracket with slack (215977584470362033072201911205849/665080405412258324751296729658163200000000, 232333773795822455641236405753857/1108467342353763874585494549430272000000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_log_two_split :
    (34657359 / 50000000 : ℝ) < Real.log (3 / 2) + Real.log (4 / 3) ∧
      Real.log (3 / 2) + Real.log (4 / 3) < (693147181 / 1000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_log_two_split_n0
  obtain ⟨h1lo, h1hi⟩ := rt_log_two_split_n1
  constructor <;> linarith

/-- `rt_sqrt_two_alias` -- the same enclosure as `rt_sqrt_two` (shared subtree).
    conjecture1_proved = False. -/
theorem rt_sqrt_two_alias :
    (1414213562373 / 1000000000000 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (3 / 2 : ℝ) :=
  rt_sqrt_two

/-- `rt_radicand` -- a certified RATIONAL ENCLOSURE of `10 - 2 * Real.sqrt 5`.
    Route: the exact interval fold (linarith).
    Exact fold [1105572809/200000000, 2763932022501/500000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_radicand :
    (1105572809 / 200000000 : ℝ) < 10 - 2 * Real.sqrt 5 ∧
      10 - 2 * Real.sqrt 5 < (2763932022501 / 500000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_sqrt5_mul_log2_n0
  constructor <;> linarith

/-- `rt_named_radicand_plus_exp_n0` -- a certified RATIONAL ENCLOSURE of `Real.exp (1 / 10)`.
    Route: the order-14 Real.exp_bound box (exact rational S and radius).
    Exact fold [26977135394095642634038549/24409921536000000000000000, 5395427078819128526807711/4881984307200000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_named_radicand_plus_exp_n0 :
    (26977135394095642634038549 / 24409921536000000000000000 : ℝ) ≤ Real.exp (1 / 10) ∧
      Real.exp (1 / 10) ≤ (5395427078819128526807711 / 4881984307200000000000000 : ℝ) := by
  have hx : |((1 / 10) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 14) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at hb1 ⊢; linarith
  · norm_num [Nat.factorial] at hb2 ⊢; linarith

/-- `rt_named_radicand_plus_exp` -- a certified RATIONAL ENCLOSURE of `10 - 2 * Real.sqrt 5 + Real.exp (1 / 10)`.
    Route: the exact interval fold (linarith).
    Exact fold [161911862994221215754038549/24409921536000000000000000, 32382372598854007119422111/4881984307200000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_named_radicand_plus_exp :
    (161911862994221215754038549 / 24409921536000000000000000 : ℝ) < 10 - 2 * Real.sqrt 5 + Real.exp (1 / 10) ∧
      10 - 2 * Real.sqrt 5 + Real.exp (1 / 10) < (32382372598854007119422111 / 4881984307200000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_radicand
  obtain ⟨h1lo, h1hi⟩ := rt_named_radicand_plus_exp_n0
  constructor <;> linarith

/-- `rt_pi_div_golden` -- a certified RATIONAL ENCLOSURE of `Real.pi / (Real.sqrt 5 + 1)`.
    Route: le_div_iff0 / div_le_iff0 against a certified positive denominator.
    Exact fold [1200000000/1294427191, 4000000000000/3236067977499], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_pi_div_golden :
    (1200000000 / 1294427191 : ℝ) ≤ Real.pi / (Real.sqrt 5 + 1) ∧
      Real.pi / (Real.sqrt 5 + 1) ≤ (4000000000000 / 3236067977499 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_arctan_abs_n0
  obtain ⟨h1lo, h1hi⟩ := rt_sqrt5_mul_log2_n0
  have hden : (0 : ℝ) < Real.sqrt 5 + 1 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

/-- `rt_arctan_pi_sub_three` -- a certified RATIONAL ENCLOSURE of `Real.arctan (Real.pi - 3)`.
    Route: t/2 <= arctan t <= t on [0, 1] (monotoneOn_of_deriv_nonneg, Real.le_tan).
    Exact fold [0, 1], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem rt_arctan_pi_sub_three :
    (0 : ℝ) ≤ Real.arctan (Real.pi - 3) ∧ Real.arctan (Real.pi - 3) ≤ (1 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := rt_arctan_abs_n0
  have hself : ∀ u : ℝ, 0 ≤ u → Real.arctan u ≤ u := by
    intro u hu
    have h := Real.le_tan (Real.arctan_nonneg.mpr hu) (Real.arctan_lt_pi_div_two u)
    rwa [Real.tan_arctan] at h
  have hhalf : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → u / 2 ≤ Real.arctan u := by
    intro u hu0 hu1
    have hderiv : ∀ x : ℝ,
        HasDerivAt (fun x => Real.arctan x - x / 2) (1 / (1 + x ^ 2) - 1 / 2) x :=
      fun x => (Real.hasDerivAt_arctan x).sub ((hasDerivAt_id x).div_const 2)
    have hmono : MonotoneOn (fun x => Real.arctan x - x / 2) (Set.Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (continuousOn_of_forall_continuousAt fun x _ => (hderiv x).continuousAt)
        (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      have : 1 / 2 ≤ 1 / (1 + x ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      linarith
    have := hmono (Set.left_mem_Icc.mpr zero_le_one) ⟨hu0, hu1⟩ hu0
    simp only [Real.arctan_zero] at this
    linarith
  have hu0 : (0 : ℝ) ≤ Real.pi - 3 := by linarith
  have hu1 : (Real.pi - 3 : ℝ) ≤ 1 := by linarith
  have ha1 := hhalf (Real.pi - 3) hu0 hu1
  have ha2 := hself (Real.pi - 3) hu0
  constructor <;> linarith

/-- `rt_log_add_four_le` -- the log/sqrt face (C 4.7): `log (y + 4) <= 6 * sqrt y` for
    `y >= 1`, from `log t <= t - 1` at `t = sqrt (y + 4)` and `y + 4 <= 3^2 y`.
    An elementary real inequality; nothing about RH.  conjecture1_proved = False. -/
theorem rt_log_add_four_le {y : ℝ} (hy : (1 : ℝ) ≤ y) :
    Real.log (y + 4) ≤ 6 * Real.sqrt y := by
  have h1 : Real.log (y + 4) = 2 * Real.log (Real.sqrt (y + 4)) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h2 : Real.log (Real.sqrt (y + 4)) ≤ Real.sqrt (y + 4) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
  have h3 : Real.sqrt (y + 4) ≤ 3 * Real.sqrt y := by
    rw [show (3 : ℝ) * Real.sqrt y = Real.sqrt (3 ^ 2 * y) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h4 : (0 : ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg y
  linarith

/-- `rt_log_le_two_sqrt` -- the log/sqrt face (C 4.7): `log (y) <= 2 * sqrt y` for
    `y >= 2`, from `log t <= t - 1` at `t = sqrt (y)`.
    An elementary real inequality; nothing about RH.  conjecture1_proved = False. -/
theorem rt_log_le_two_sqrt {y : ℝ} (hy : (2 : ℝ) ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hs : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hy0.le] at h1
  have h4 : (0 : ℝ) ≤ Real.sqrt y := hs.le
  linarith

end DogfoodEnclosureTree

/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the block above
    is the frozen emitter output).  Each `example` feeds an emitted rate lemma to the hand theorem
    whose side condition it replaces, so a drift in either statement fails to elaborate. -/

section CrossChecks
open DogfoodEnclosureTree

/-- `LiLadderHeight.li_rungs_of_bands_4000_upto`, with its hand `Real.pi_gt_d4` + `linarith` step
    replaced by the emitted `li_height_rate_4000_rate`.  Conditional on `hall`, exactly as the
    original; proves nothing about RH. -/
example (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    ∀ n : ℕ, n ≤ 18848 → 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re :=
  fun n hn => LiLadderHeight.li_rungs_of_bands_4000 hall n (li_height_rate_4000_rate n hn)

/-- `LiLadderHeight.li_rungs_of_bands_4000_upto_sharp` (LiLadderSharp), with its hand
    `Real.pi_gt_d6` + `nlinarith` step replaced by the emitted `li_sharp_rate_4000_rate`. -/
example (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    ∀ n : ℕ, n ≤ 25128 → 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re :=
  fun n hn => LiLadderHeight.li_rungs_of_bands_4000_sharp hall n (li_sharp_rate_4000_rate n hn)

end CrossChecks

#print axioms DogfoodEnclosureTree.li_height_rate_4000_n0
#print axioms DogfoodEnclosureTree.li_height_rate_4000
#print axioms DogfoodEnclosureTree.li_height_rate_4000_rate
#print axioms DogfoodEnclosureTree.li_sharp_rate_4000_n0
#print axioms DogfoodEnclosureTree.li_sharp_rate_4000
#print axioms DogfoodEnclosureTree.li_sharp_rate_4000_rate
#print axioms DogfoodEnclosureTree.qc_sqrt_five_bounds
#print axioms DogfoodEnclosureTree.qc_sqrt_inner_bounds
#print axioms DogfoodEnclosureTree.qc_dhKappa_bounds
#print axioms DogfoodEnclosureTree.qc_log_three_halves_bounds
#print axioms DogfoodEnclosureTree.qc_log_two_bounds
#print axioms DogfoodEnclosureTree.qc_log_six_bounds
#print axioms DogfoodEnclosureTree.qc_log_three_bounds
#print axioms DogfoodEnclosureTree.rt_sqrt_two_pi_n0
#print axioms DogfoodEnclosureTree.rt_sqrt_two_pi
#print axioms DogfoodEnclosureTree.rt_sqrt_thirty_two_pi
#print axioms DogfoodEnclosureTree.rt_sqrt_two
#print axioms DogfoodEnclosureTree.rt_pi_sq_div_six_n0
#print axioms DogfoodEnclosureTree.rt_pi_sq_div_six
#print axioms DogfoodEnclosureTree.rt_exp_half
#print axioms DogfoodEnclosureTree.rt_exp_neg_one
#print axioms DogfoodEnclosureTree.rt_arctan_half
#print axioms DogfoodEnclosureTree.rt_arctan_abs_n0
#print axioms DogfoodEnclosureTree.rt_arctan_abs
#print axioms DogfoodEnclosureTree.rt_sqrt5_mul_log2_n0
#print axioms DogfoodEnclosureTree.rt_sqrt5_mul_log2_n1
#print axioms DogfoodEnclosureTree.rt_sqrt5_mul_log2
#print axioms DogfoodEnclosureTree.rt_four_sub_pi
#print axioms DogfoodEnclosureTree.rt_log_half
#print axioms DogfoodEnclosureTree.rt_log_two_split_n0
#print axioms DogfoodEnclosureTree.rt_log_two_split_n1
#print axioms DogfoodEnclosureTree.rt_log_two_split
#print axioms DogfoodEnclosureTree.rt_sqrt_two_alias
#print axioms DogfoodEnclosureTree.rt_radicand
#print axioms DogfoodEnclosureTree.rt_named_radicand_plus_exp_n0
#print axioms DogfoodEnclosureTree.rt_named_radicand_plus_exp
#print axioms DogfoodEnclosureTree.rt_pi_div_golden
#print axioms DogfoodEnclosureTree.rt_arctan_pi_sub_three
#print axioms DogfoodEnclosureTree.rt_log_add_four_le
#print axioms DogfoodEnclosureTree.rt_log_le_two_sqrt
