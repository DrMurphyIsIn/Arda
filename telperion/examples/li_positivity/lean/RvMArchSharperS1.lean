/-
RvMArchSharperS1 — Arc B (sharper archimedean Li constant), step S1.

The merged `RvMArchGrowth.taylorCoeff_Gammaℝ_re_growth` gives `|arch_n − (n/2)·log n| ≤ 8n`.  To
sharpen the linear term to its exact constant `(γ−1−log 2π)/2` we work with the *first difference*
`arch_{n+1} − arch_n`.  This file proves the two S1 facts:

  * `archRe_diff_eq` — the per-term difference `archRe (n+1) j − archRe n j
      = (1/(2j+2) − 1/(2j+3)) + (1 − r_j^{n+1})/(2j+3)` (`= AHterm j + Dterm (n+1) j`), where
    `AHterm j = 1/(2j+2) − 1/(2j+3)` and `Dterm m j = (1 − r_j^m)/(2j+3)`, `r_j = (2j+2)/(2j+3)`.
  * `arch_succ_sub_eq` — **THE EXACT DIFFERENCE IDENTITY**
      `arch_{n+1} − arch_n = −(γ+log π)/2 + AH + D (n+1)`,
    with `AH = ∑'_j AHterm j`, `D m = ∑'_j Dterm m j`, obtained by telescoping the tsums.
  * `AH_eq` — **`AH = 1 − log 2`**, via the harmonic partial sums
      `∑_{j<J} 1/(2j+2) = (1/2)H_J`, `∑_{j<J} 1/(2j+3) = H_{2J+1} − (1/2)H_J − 1`
    and `Real.tendsto_harmonic_sub_log` (γ cancels).

conjecture1_proved = False: this is a Γ-function fact; nothing here approaches RH.
-/
import Mathlib
import RvMArchGrowthBounds
import RvMArchGrowth

open Complex Finset Filter Topology

namespace RvMWeierstrass

/-! ### The difference series building blocks -/

/-- `r_j = (2j+2)/(2j+3)`. -/
noncomputable def ratioR (j : ℕ) : ℝ := (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)

/-- The `AH` summand `1/(2j+2) − 1/(2j+3)`. -/
noncomputable def AHterm (j : ℕ) : ℝ := 1 / (2 * (j : ℝ) + 2) - 1 / (2 * (j : ℝ) + 3)

/-- The `D` summand `Dterm m j = (1 − r_j^m)/(2j+3)`. -/
noncomputable def Dterm (m j : ℕ) : ℝ := (1 - ratioR j ^ m) / (2 * (j : ℝ) + 3)

/-- **Per-term difference identity.**  `archRe (n+1) j − archRe n j = AHterm j + Dterm (n+1) j`. -/
theorem archRe_diff_eq (n j : ℕ) :
    archRe (n + 1) j - archRe n j = AHterm j + Dterm (n + 1) j := by
  have h2 : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
  -- unfold to raw form; the ratio power `((2j+2)/(2j+3))^(n+1)` is the only nonlinear atom
  simp only [archRe, AHterm, Dterm, ratioR]
  -- `r^(n+2) = r^(n+1)·r`, then generalize the power to an atom `p`
  rw [show n + 1 + 1 = (n + 1) + 1 from rfl, pow_succ]
  generalize ((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) ^ (n + 1) = p
  -- the goal is now a rational-function identity in `p` and `↑j`
  push_cast
  field_simp
  ring

/-! ### Summability of the difference-series pieces -/

/-- `AHterm j = 1/((2j+2)(2j+3))`, an `O(1/j²)` summand. -/
theorem AHterm_eq (j : ℕ) :
    AHterm j = 1 / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3)) := by
  unfold AHterm
  have h2 : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

theorem AHterm_nonneg (j : ℕ) : 0 ≤ AHterm j := by
  rw [AHterm_eq]; positivity

/-- `AHterm` is summable (dominated by the merged `summable_tail_a` shape at `n = 0`). -/
theorem summable_AHterm : Summable AHterm := by
  have h := summable_tail_a 0
  simp only [Nat.cast_zero, zero_add] at h
  refine Summable.of_nonneg_of_le AHterm_nonneg (fun j => ?_) h
  rw [AHterm_eq]

/-- `Dterm m j ≥ 0`. -/
theorem Dterm_nonneg (m j : ℕ) : 0 ≤ Dterm m j := by
  unfold Dterm ratioR
  have hple : ((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) ^ m ≤ 1 :=
    pow_le_one₀ (archRe_r_pos j).le (archRe_r_le_one j)
  have h3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  apply div_nonneg (by linarith) h3.le

/-- Bernoulli bound on `Dterm`: `Dterm m j ≤ m/(2j+3)²`.  Uses `1 − r^m ≤ m·ε_j` from
    `(1−ε)^m ≥ 1 − m·ε` (Mathlib `one_add_mul_le_pow`). -/
theorem Dterm_le (m j : ℕ) :
    Dterm m j ≤ (m : ℝ) * (1 / (2 * (j : ℝ) + 3)) ^ 2 := by
  unfold Dterm ratioR
  have h3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  set ε : ℝ := 1 / (2 * (j : ℝ) + 3) with hε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hxge : (-2 : ℝ) ≤ -ε := by
    rw [hε]
    have : (1 : ℝ) / (2 * (j : ℝ) + 3) ≤ 1 := by rw [div_le_one h3]; linarith
    linarith
  have hbern : 1 + (m : ℝ) * (-ε) ≤ (1 + (-ε)) ^ m := by
    have := one_add_mul_le_pow hxge m
    push_cast at this ⊢
    convert this using 2
  have hr : (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) = 1 + (-ε) := by
    rw [hε]; field_simp; ring
  rw [hr]
  -- Dterm = (1 − (1−ε)^m)/(2j+3) ≤ (m·ε)/(2j+3) = m·ε² since ε = 1/(2j+3)
  rw [div_le_iff₀ h3]
  have hnum : (1 : ℝ) - (1 + (-ε)) ^ m ≤ (m : ℝ) * ε := by linarith [hbern]
  refine hnum.trans (le_of_eq ?_)
  rw [hε]; field_simp

/-- `Dterm m` is summable (dominated by `m/(2j+3)²`). -/
theorem summable_Dterm (m : ℕ) : Summable (fun j : ℕ => Dterm m j) := by
  have hf : Summable (fun j : ℕ => (m : ℝ) * (1 / (2 * (j : ℝ) + 3)) ^ 2) := by
    have hb : Summable (fun j : ℕ => (1 / (2 * (j : ℝ) + 3)) ^ 2) := by
      have h2 := summable_one_div_sq_succ
      refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) h2
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact hb.mul_left _
  exact Summable.of_nonneg_of_le (fun j => Dterm_nonneg m j) (fun j => Dterm_le m j) hf

/-- `AH = ∑'_j AHterm j`. -/
noncomputable def AH : ℝ := ∑' j : ℕ, AHterm j

/-- `D m = ∑'_j Dterm m j`. -/
noncomputable def Dseries (m : ℕ) : ℝ := ∑' j : ℕ, Dterm m j

/-! ### The exact difference identity (S1a) -/

/-- The `j`-th difference summand `archRe (n+1) j − archRe n j` is summable in `j` (difference of two
    summable series). -/
theorem summable_archRe_diff (n : ℕ) :
    Summable (fun j : ℕ => archRe (n + 1) j - archRe n j) :=
  (summable_archRe (n + 1)).sub (summable_archRe n)

/-- **THE EXACT DIFFERENCE IDENTITY (S1a).**
    `arch_{n+1} − arch_n = −(γ+log π)/2 + AH + D (n+1)`. -/
theorem arch_succ_sub_eq (n : ℕ) :
    (LiCriterion.taylorCoeff Complex.Gammaℝ (n + 1)).re
        - (LiCriterion.taylorCoeff Complex.Gammaℝ n).re
      = -((Real.eulerMascheroniConstant + Real.log Real.pi) / 2) + AH + Dseries (n + 1) := by
  set A : ℝ := (Real.eulerMascheroniConstant + Real.log Real.pi) / 2 with hA
  rw [taylorCoeff_Gammaℝ_re_eq (n + 1), taylorCoeff_Gammaℝ_re_eq n]
  rw [show -((Real.eulerMascheroniConstant + Real.log Real.pi) / 2) = -A from by rw [hA]]
  -- the tsum difference telescopes to ∑'(archRe(n+1) − archRe n)
  have htsub : (∑' j : ℕ, archRe (n + 1) j) - (∑' j : ℕ, archRe n j)
      = ∑' j : ℕ, (archRe (n + 1) j - archRe n j) :=
    (Summable.tsum_sub (summable_archRe (n + 1)) (summable_archRe n)).symm
  -- and each difference summand = AHterm + Dterm(n+1)
  have hcongr : (∑' j : ℕ, (archRe (n + 1) j - archRe n j))
      = ∑' j : ℕ, (AHterm j + Dterm (n + 1) j) :=
    tsum_congr (fun j => archRe_diff_eq n j)
  have hsplit : (∑' j : ℕ, (AHterm j + Dterm (n + 1) j)) = AH + Dseries (n + 1) :=
    Summable.tsum_add summable_AHterm (summable_Dterm (n + 1))
  push_cast
  -- reduce `(−A(n+2) − 1 + S1) − (−A(n+1) − 1 + S2)` to `−A + (S1 − S2)`
  have hSig : (∑' j : ℕ, archRe (n + 1) j) - (∑' j : ℕ, archRe n j) = AH + Dseries (n + 1) := by
    rw [htsub, hcongr, hsplit]
  linarith [hSig]

/-! ### `AH = 1 − log 2` (S1b) -/

/-- **Partial-sum identity.**  `∑_{j<J} AHterm j = H_J − H_{2J+1} + 1`, by induction on `J`
    (`Hsum` is the island's real harmonic number). -/
theorem AHterm_partial_sum (J : ℕ) :
    ∑ j ∈ Finset.range J, AHterm j = Hsum J - Hsum (2 * J + 1) + 1 := by
  induction J with
  | zero => simp [Hsum]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    -- Hsum increments
    have hHJ : Hsum (J + 1) = Hsum J + 1 / ((J : ℝ) + 1) := by
      unfold Hsum; rw [Finset.sum_range_succ]
    have h2J : Hsum (2 * (J + 1) + 1) = Hsum (2 * J + 1)
        + 1 / (2 * (J : ℝ) + 2) + 1 / (2 * (J : ℝ) + 3) := by
      unfold Hsum
      rw [show 2 * (J + 1) + 1 = (2 * J + 1) + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast; ring
    rw [hHJ, h2J, AHterm]
    have hJ1 : ((J : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (J : ℝ) + 2) ≠ 0 := by positivity
    have h3 : (2 * (J : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring

/-- The partial sums of `AHterm` tend to `1 − log 2`, using `Real.tendsto_harmonic_sub_log`
    (the `γ`'s cancel and `log J − log(2J+1) → −log 2`). -/
theorem AHterm_partial_tendsto :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J, AHterm j) atTop (nhds (1 - Real.log 2)) := by
  -- rewrite partial sum via the identity
  have hpe : (fun J : ℕ => ∑ j ∈ Finset.range J, AHterm j)
      = fun J : ℕ => (Hsum J - Real.log J) - (Hsum (2 * J + 1) - Real.log (2 * J + 1))
          + (Real.log J - Real.log (2 * J + 1)) + 1 := by
    funext J; rw [AHterm_partial_sum]; ring
  rw [hpe]
  -- piece 1: Hsum J − log J → γ
  have hγ1 : Tendsto (fun J : ℕ => Hsum J - Real.log J) atTop
      (nhds Real.eulerMascheroniConstant) := by
    have := Real.tendsto_harmonic_sub_log
    refine this.congr (fun J => ?_)
    rw [Hsum_eq_harmonic]
  -- piece 2: Hsum(2J+1) − log(2J+1) → γ  (subsequence of the same γ-limit)
  have hγ2 : Tendsto (fun J : ℕ => Hsum (2 * J + 1) - Real.log (2 * J + 1)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    have hbase : Tendsto (fun m : ℕ => Hsum m - Real.log m) atTop
        (nhds Real.eulerMascheroniConstant) := by
      have := Real.tendsto_harmonic_sub_log
      refine this.congr (fun m => ?_)
      rw [Hsum_eq_harmonic]
    have hcomp : Tendsto (fun J : ℕ => 2 * J + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (f := fun J : ℕ => J) (g := fun J : ℕ => 2 * J + 1)
        (fun J => by omega) Filter.tendsto_id
    have hsub := hbase.comp hcomp
    refine hsub.congr (fun J => ?_)
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  -- piece 3: log J − log(2J+1) → −log 2
  have hlog : Tendsto (fun J : ℕ => Real.log J - Real.log (2 * J + 1)) atTop
      (nhds (-Real.log 2)) := by
    -- log(2J+1) − log J = [log(2J+1) − log(2J)] + log 2  →  0 + log 2
    -- first bracket: `tendsto_log_comp_add_sub_log 1` at `x = 2J → ∞`
    have hbr : Tendsto (fun J : ℕ => Real.log ((2 * J : ℝ) + 1) - Real.log (2 * J : ℝ)) atTop
        (nhds 0) := by
      have hbase := Real.tendsto_log_comp_add_sub_log (1 : ℝ)
      have hcomp : Tendsto (fun J : ℕ => (2 * J : ℝ)) atTop atTop := by
        apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        exact tendsto_natCast_atTop_atTop
      exact (hbase.comp hcomp)
    -- rewrite the target as −(bracket) − log 2 (eventually, for J ≥ 1)
    have hrw : ∀ᶠ J : ℕ in atTop, Real.log (J : ℝ) - Real.log (2 * (J : ℝ) + 1)
        = -(Real.log ((2 * J : ℝ) + 1) - Real.log (2 * J : ℝ)) - Real.log 2 := by
      filter_upwards [eventually_gt_atTop 0] with J hJ
      have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
      have h2J : Real.log (2 * (J : ℝ)) = Real.log 2 + Real.log (J : ℝ) :=
        Real.log_mul (by norm_num) (ne_of_gt hJpos)
      rw [h2J]; ring
    have hlim : Tendsto (fun J : ℕ =>
        -(Real.log ((2 * J : ℝ) + 1) - Real.log (2 * J : ℝ)) - Real.log 2) atTop
        (nhds (-Real.log 2)) := by
      have := (hbr.neg).sub_const (Real.log 2)
      simpa using this
    exact hlim.congr' (hrw.mono (fun J h => h.symm))
  have hfinal := ((hγ1.sub hγ2).add hlog).add_const 1
  -- (γ − γ) + (−log 2) + 1 = 1 − log 2
  have : Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + (-Real.log 2) + 1
      = 1 - Real.log 2 := by ring
  rw [this] at hfinal
  convert hfinal using 2

/-- **`AH = 1 − log 2` (S1b).**  The tsum `AH` is the limit of its partial sums, which is `1 − log 2`. -/
theorem AH_eq : AH = 1 - Real.log 2 := by
  have hsum : HasSum AHterm (1 - Real.log 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg AHterm_nonneg]
    exact AHterm_partial_tendsto
  rw [AH, hsum.tsum_eq]
