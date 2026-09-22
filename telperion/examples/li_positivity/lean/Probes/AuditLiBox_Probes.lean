/- Audit probes for LiBoxRungs (auditor-forward, 2026-09-21). -/
import LiBoxRungs
open Complex LiCriterion LowHeightBox

/- 1. Chain re-composed from the pieces for rung 3 (expected SUCCESS). -/
example : 0 ≤ (taylorCoeff riemannXi 3).re :=
  taylorCoeff_re_nonneg_of_termwise 3 (fun ρ => by
    rw [liPairedSummand_three_eq]; exact re_Q4_nonneg (zOf_mem_disk ρ))
#print axioms li_rungs_lt_five

/- 2. Box 2 gives Re(ρ(1-ρ)) ≥ 1, abstractly (expected SUCCESS). -/
example (β γ : ℝ) (hbox : (β - 1 / 2) ^ 2 ≤ γ ^ 2 / 3 - 1 / 4) : 1 ≤ β * (1 - β) + γ ^ 2 := by
  nlinarith [sq_nonneg (β - 1 / 2)]

/- 3. Re q ≥ 1 puts 1/q in the disk Re z ≥ |z|², abstractly (expected SUCCESS). -/
example (q : ℂ) (hq : 1 ≤ q.re) : (q⁻¹).re ^ 2 + (q⁻¹).im ^ 2 ≤ (q⁻¹).re := by
  have hqne : q ≠ 0 := by intro h; rw [h, zero_re] at hq; norm_num at hq
  have hm : 0 < normSq q := normSq_pos.mpr hqne
  rw [inv_re, inv_im, normSq_apply] at *
  have hsum : (q.re / (q.re * q.re + q.im * q.im)) ^ 2 + (-q.im / (q.re * q.re + q.im * q.im)) ^ 2
      = 1 / (q.re * q.re + q.im * q.im) := by field_simp
  rw [hsum]
  exact (div_le_div_iff_of_pos_right hm).mpr hq

/- 4. N = 6 has no disk certificate: at z = 29/39 + (17/39) i (in the disk) Re Q6 < 0
   (expected SUCCESS; this is a fact about the polynomial, not about any zero). -/
example : let a : ℝ := 29 / 39; let b : ℝ := 17 / 39;
    a ^ 2 + b ^ 2 ≤ a ∧
    (36 * a - 105 * (a ^ 2 - b ^ 2) + 112 * (a ^ 3 - 3 * a * b ^ 2)
      - 54 * (a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4)
      + 12 * (a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4)
      - (a ^ 6 - 15 * a ^ 4 * b ^ 2 + 15 * a ^ 2 * b ^ 4 - b ^ 6)) < 0 := by
  norm_num

/- 5. Consumption at rung 4 through the packaged form (expected SUCCESS). -/
example : 0 ≤ (taylorCoeff riemannXi 4).re := li_rungs_lt_five 4 (by norm_num)

/- 6. Q5 at the disk boundary point z = 1 (t = π in Chebyshev form: 2 - 2cos(5π) = 4) (expected SUCCESS). -/
example : (Q5 1).re = 1 := by simp [Q5]; norm_num

/- 7. EXPECTED FAIL: rung 5 is not covered by li_rungs_lt_five. -/
example : 0 ≤ (taylorCoeff riemannXi 5).re := li_rungs_lt_five 5 (by norm_num)

/- 8. EXPECTED FAIL: termwise lemma refuses n = 5. -/
example (ρ : NontrivialZero) : 0 ≤ (liPairedSummand 5 ρ).re :=
  liPairedSummand_re_nonneg 5 (by norm_num) ρ
