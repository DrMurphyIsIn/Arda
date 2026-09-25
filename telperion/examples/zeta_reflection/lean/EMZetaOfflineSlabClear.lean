/-  EMZetaOfflineSlabClear.lean -- lane offline: from kernel-checked cells to an edge-clearance slab
    `EdgeClearGlue.SlabClear a b` (brick K1's numerical input, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    rows H2a/H2c).

      * `cell_zeta_ne_zero` -- ONE cell, packaged: two evaluator invariants at the center
                               `c = σc + i tc` (after `N - 1` and `N` terms, `p + 1` accumulators), the
                               kernel check `checkCell … = true`, and a handful of scalar side
                               conditions (log bracket, `r L ≤ 1`, `‖c + j‖ ≤ U`, the remainder
                               certificate, the error budget) give `ζ(s) ≠ 0` for every `s` with
                               `‖s - c‖ ≤ r`, `a ≤ Im s ≤ B`, `1/2 ≤ Re s ≤ 1`;
      * `slabClear_of_right_half` -- the reflection `ρ ↦ 1 - conj ρ` (Im-preserving) folds
                               `0 < Re < 1/2` onto `1/2 < Re < 1`, so the right half of a slab suffices.

    conjecture1_proved = False.  A finite, local nonvanishing statement; nothing about RH.
-/
import EMZetaOfflineSlabCheck
import EdgeClearGlue
import DlvpZetaSymmetry

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-- The uniform bound `N/a + 1/2 + Σ_{i<2K-1} |B_{i+2}|/(i+2)! U^(i+1)/N^(i+1)` on `‖emCorr K c N‖`. -/
noncomputable def emcB (K N : ℕ) (a U : ℝ) : ℝ :=
  (N : ℝ) / a + 1 / 2
    + ∑ i ∈ Finset.range (2 * K - 1), |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ) * U ^ (i + 1)
        / (N : ℝ) ^ (i + 1)

/-- `‖c + j‖ ≤ U` for all `j < 2K` from the single corner inequality. -/
theorem norm_add_nat_le (K : ℕ) (σc tc U : ℝ) (hσc : 0 ≤ σc) (hU0 : 0 ≤ U)
    (hU : (σc + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2) :
    ∀ j, j < 2 * K → ‖sOfG σc tc + j‖ ≤ U := by
  intro j hj
  have hjR : (j : ℝ) ≤ 2 * K - 1 := by
    have : j + 1 ≤ 2 * K := hj
    have : ((j + 1 : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hre : (sOfG σc tc + j).re = σc + j := by simp [sOfG]
  have him : (sOfG σc tc + j).im = tc := by simp [sOfG]
  have hsq : ‖sOfG σc tc + j‖ ^ 2 ≤ U ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have h1 : (σc + j) * (σc + j) ≤ (σc + (2 * K - 1 : ℝ)) ^ 2 := by
      rw [← sq]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hU0 hsq

/-- **One zero-free cell** (packaged).  See the module docstring for the hypotheses. -/
theorem cell_zeta_ne_zero (c : Cfg) (o : OCfg) (σc tc : ℝ) (hσ : σc = ((o.a : ℝ) - o.b) / o.q)
    (ht : tc = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (hK : 1 ≤ K) (hN : 2 ≤ N) (s1 s2 : StO)
    (h1 : InvO c σc tc (N - 1) s1) (h2 : InvO c σc tc N s2) (rn rd FN FD : ℕ)
    (hchk : checkCell c o K N p s1.acc s2.acc rn rd FN FD = true)
    (L a U B Qr : ℝ) (r0 : ℕ) (hL : (s2.lhi : ℝ) ≤ L * 2 ^ c.P) (hrL : (rn : ℝ) / rd * L ≤ 1)
    (ha : 0 < a) (hta : a ≤ tc) (hσc : 0 ≤ σc) (hU0 : 0 ≤ U)
    (hU : (σc + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 B (2 * K + 1) ≤ Qr ^ 2) (hr0 : 0 < r0) (hr0N : r0 ^ 2 ≤ N)
    (hbudget : Cp p * ((rn : ℝ) / rd * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U)
        + 3 * corrVar K N ((rn : ℝ) / rd) a U
        + CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) ≤ (FN : ℝ) / FD) :
    ∀ s : ℂ, ‖s - sOfG σc tc‖ ≤ (rn : ℝ) / rd → a ≤ s.im → s.im ≤ B → 1 / 2 ≤ s.re → s.re ≤ 1 →
      riemannZeta s ≠ 0 := by
  intro s hsc hsa hsB hs0 hs1
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  -- the kernel check
  have hmain := checkCell_sound c o σc tc hσ ht K N p s1.acc s2.acc rn rd FN FD h1.2.2.2.2 h2.2.2.2.2 hchk
  -- log N ≤ L
  have hlogN : Real.log N ≤ L := by
    have h2l := h2.2.2.2.1
    have : Real.log N * 2 ^ c.P ≤ L * 2 ^ c.P := le_trans h2l hL
    exact le_of_mul_le_mul_right this hP
  have hU' := norm_add_nat_le K σc tc U hσc hU0 hU
  have hcre : 0 ≤ (sOfG σc tc).re := by simp [sOfG, hσc]
  have hcim : a ≤ (sOfG σc tc).im := by simp [sOfG, hta]
  -- the region remainder
  have hsim : 0 < s.im := lt_of_lt_of_le ha hsa
  have hE := em_remainder_region K N hK (by omega) s hs0 hs1 hsim B hsB Qr hQr0 hQ r0 hr0 hr0N
  -- the budget, through the uniform bound on the correction factor
  have hemc := norm_emCorr_le K N (by omega) (sOfG σc tc) a U ha hcim hU0 hU'
  have hrL0 : (0 : ℝ) ≤ (rn : ℝ) / rd * L := by
    have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) hlogN
    positivity
  have hF : taylorErr K N p (sOfG σc tc) ((rn : ℝ) / rd) L a U
      + CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) ≤ (FN : ℝ) / FD := by
    refine le_trans ?_ hbudget
    unfold taylorErr
    have hcp := Cp_nonneg p
    have : Cp p * ((rn : ℝ) / rd * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K (sOfG σc tc) N‖)
        ≤ Cp p * ((rn : ℝ) / rd * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold emcB
      linarith
    linarith
  exact zeta_ne_zero_of_cell K N p (by omega) (sOfG σc tc) s ((rn : ℝ) / rd) L a U _ ((FN : ℝ) / FD)
    hcre hsc hlogN hrL ha hcim hsa hU0 hU' hE hF hmain

/-- **Reflection**: a slab is zero-free as soon as its right half `1/2 ≤ Re < 1` is. -/
theorem slabClear_of_right_half (a b : ℝ)
    (hR : ∀ x y : ℝ, 1 / 2 ≤ x → x < 1 → a ≤ y → y ≤ b → riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    EdgeClearGlue.SlabClear a b := by
  intro x y hx0 hx1 hya hyb hz
  by_cases hh : 1 / 2 ≤ x
  · exact hR x y hh hx1 hya hyb hz
  · push Not at hh
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    have hz' := ZeroFreeBridge.riemannZeta_reflect_line_eq_zero (ρ := (x : ℂ) + (y : ℂ) * I)
      (by rw [hre]; exact hx0) (by rw [hre]; exact hx1) hz
    have e : 1 - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * I) = ((1 - x : ℝ) : ℂ) + (y : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [e] at hz'
    exact hR (1 - x) y (by linarith) (by linarith) hya hyb hz'

/-- The disc condition from a box: `|x - σc| ≤ w`, `|y - tc| ≤ hh`, `w² + hh² ≤ r²`. -/
theorem dist_le_of_box (x y σc tc w hh r : ℝ) (hx : |x - σc| ≤ w) (hy : |y - tc| ≤ hh)
    (hr0 : 0 ≤ r) (hr : w ^ 2 + hh ^ 2 ≤ r ^ 2) :
    ‖((x : ℂ) + (y : ℂ) * I) - sOfG σc tc‖ ≤ r := by
  have e : ((x : ℂ) + (y : ℂ) * I) - sOfG σc tc = ((x - σc : ℝ) : ℂ) + ((y - tc : ℝ) : ℂ) * I := by
    simp only [sOfG]; push_cast; ring
  rw [e]
  have hsq : ‖((x - σc : ℝ) : ℂ) + ((y - tc : ℝ) : ℂ) * I‖ ^ 2 ≤ r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have h1 : (x - σc) ^ 2 ≤ w ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have h2 : (y - tc) ^ 2 ≤ hh ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hr0 hsq

end Off

end ArbEcon
