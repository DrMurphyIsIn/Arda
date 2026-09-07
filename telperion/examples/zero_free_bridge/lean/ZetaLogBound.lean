/- SHARP NEAR-LINE GROWTH BOUND (DISCHARGED, sorry-free): `|ζ(σ+it)| ≤ 6·(1 + log|t|)`
   for `1 ≤ σ ≤ 2`, `|t| ≥ 2` — the upgrade that improves the zero-free-region rate.

   The elementary region (`riemannZeta_zero_free_poly`, `Re s > 1 - c/|t|⁵`) is limited by the
   CRUDE growth bound `|ζ| ≤ C|t|` (`zeta_strip_bound`). Replacing it with the sharp
   `|ζ| ≤ C·log|t|` cascades through `zeta_deriv_bound → zeta_hcauchy → zeta_strip_2t_bound`
   and improves the exponent from `|t|⁻⁵` toward the de la Vallée Poussin `1 - c/log|t|` region —
   WITHOUT touching the Hadamard wall.

   METHOD: truncated Euler–Maclaurin at `N ∼ |t|`, reusing the R1 Abel-summation machinery.
   From `zeta_fract_repr` (ζ(s) = s/(s-1) - s∫_{x>1}{x}x^{-s-1}) and the FINITE Abel identity
   (`sum_mul_eq_sub_integral_mul₀`, f=x^{-s}, c 0=0, c(n≥1)=1) one gets, for 0 < Re s, s ≠ 1, N ≥ 1:

       ζ(s) = Σ_{n=1}^N n^{-s} + N^{1-s}/(s-1) - s·∫_{x>N} {x} x^{-s-1} dx.        (TRUNC)

   With N = ⌊|t|⌋, σ ∈ [1,2]:
     • |Σ_{n=1}^N n^{-s}| ≤ Σ n^{-σ} ≤ Σ 1/n ≤ 1 + log N ≤ 1 + log|t|      (σ ≥ 1)
     • |N^{1-s}/(s-1)| = N^{1-σ}/|s-1| ≤ 1/|t|                              (N^{1-σ} ≤ 1, |s-1| ≥ |t|)
     • |s·∫_{x>N}{x}x^{-s-1}| ≤ |s|·N^{-σ}/σ ≤ |s|/N ≤ C                     (N ≥ |t|/2, |s| ≤ 2|t|)
   ⟹ |ζ(σ+it)| ≤ C·(1 + log|t|).

   STATUS: DISCHARGED, sorry-free (CI: zeta-log-bound-compiles green). `zeta_trunc` and the
   underlying `zeta_partial_sum_repr` hold on the full elementary strip `0 < Re s, s ≠ 1` (the
   finite Abel identity is algebraic; the tail is over a compact interval), so `zeta_log_bound`
   covers σ = 1 as well. A gap-filler FEEDING the region rate, NOT a proof of RH.
   conjecture1_proved = False.
-/
import StripReprAssembled

open MeasureTheory Filter Topology Set

namespace ZeroFreeBridge

/-- The tail integral `∫_{x>N} {x} x^{-(s+1)} dx`, as a function of the cutoff `N`. -/
noncomputable def fractTail (s : ℂ) (N : ℝ) : ℂ :=
  ∫ x in Set.Ioi N, ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)

/-- (TRUNC) truncated Euler–Maclaurin representation of ζ on `0 < Re s`, `s ≠ 1`, at integer cutoff
    `N ≥ 1`. Derived from the finite Abel identity (`zeta_partial_sum_repr`) and `zeta_fract_repr`.
    Valid on the full elementary strip (not just `Re s > 1`): the partial-sum identity is algebraic
    and the tail integral is over a compact interval. -/
theorem zeta_trunc {s : ℂ} (hs0re : 0 < s.re) (hsne1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1)
        - s * fractTail s (N : ℝ) := by
  have hmem : s ∈ stripDomain := by
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) < s.re; exact hs0re
    · simp only [Set.mem_singleton_iff]; exact hsne1
  have hrepr := zeta_fract_repr hmem
  have hpsum := zeta_partial_sum_repr hs0re hsne1 hN
  have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- `fractIntegrand` is integrable on `Ioi 1` (Re s > 0, dominated by `t^{-(σ+1)}`).
  have hint1 : IntegrableOn (fractIntegrand s) (Set.Ioi (1 : ℝ)) := by
    have hbound : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) one_pos
    have hm : AEStronglyMeasurable (fractIntegrand s) (volume.restrict (Set.Ioi (1 : ℝ))) := by
      apply Measurable.aestronglyMeasurable; unfold fractIntegrand; fun_prop
    refine Integrable.mono' hbound hm ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
    have htpos : (0 : ℝ) < t := lt_trans one_pos ht
    rw [fractIntegrand, norm_div, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t),
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, show (s + 1).re = s.re + 1 by simp [Complex.add_re],
      Real.rpow_neg htpos.le, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg htpos.le _)) (Int.fract_lt_one t).le
  -- split `∫_{Ioi 1} = ∫_{Ioc 1 N} + ∫_{Ioi N}`.
  have hsplit : fractIntegral s = (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), fractIntegrand s t)
      + fractTail s (N : ℝ) := by
    rw [fractIntegral, fractTail, ← Set.Ioc_union_Ioi_eq_Ioi hle,
      setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl _)) measurableSet_Ioi
        (hint1.mono_set Set.Ioc_subset_Ioi_self) (hint1.mono_set (Set.Ioi_subset_Ioi hle))]
    simp only [fractIntegrand]
  rw [hrepr, stripRHS, hsplit, hpsum]; ring

/-- Partial-sum bound: `‖Σ_{n=1}^N n^{-s}‖ ≤ 1 + log N` for `Re s ≥ 1`, using Mathlib's
    `harmonic_le_one_add_log` (`harmonic n ≤ 1 + log n`) after `‖n^{-s}‖ = n^{-σ} ≤ 1/n`. -/
theorem norm_partial_sum_le {s : ℂ} (hs : 1 ≤ s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1 + Real.log N := by
  calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
        rw [← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
          ← Real.rpow_neg_one (n : ℝ)]
        refine Real.rpow_le_rpow_of_exponent_le hnR ?_
        simp only [Complex.neg_re]; linarith
    _ = (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- `‖N^{1-s}‖ ≤ 1` for `Re s ≥ 1`, `N ≥ 1` (the numerator of the pole term). -/
theorem norm_cpow_one_sub_le_one {s : ℂ} (hs : 1 ≤ s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖(N : ℂ) ^ (1 - s)‖ ≤ 1 := by
  have hnR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < (N : ℝ) := by linarith
  rw [← Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  apply Real.rpow_le_one_of_one_le_of_nonpos hnR
  simp only [Complex.sub_re, Complex.one_re]; linarith

/-- `|Im s| ≤ ‖s - 1‖` (the pole-term denominator bound). -/
theorem abs_im_le_norm_sub_one (s : ℂ) : |s.im| ≤ ‖s - 1‖ := by
  have : (s - 1).im = s.im := by simp
  calc |s.im| = |(s - 1).im| := by rw [this]
    _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _

/-- The tail term `‖s · ∫_{x>N} {x} x^{-s-1}‖` is bounded by `‖s‖ / (Re s · N^{Re s})`. -/
theorem norm_tail_term_le {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖s * fractTail s (N : ℝ)‖ ≤ ‖s‖ / (s.re * (N : ℝ) ^ s.re) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  -- pointwise: ‖{x} x^{-(s+1)}‖ = {x}·x^{-(σ+1)} ≤ x^{-(σ+1)} on Ioi N
  have hpt : ∀ x ∈ Set.Ioi (N : ℝ),
      ‖((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖ ≤ (x : ℝ) ^ (-(s.re + 1)) := by
    intro x hx
    have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
    have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hf1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hf0,
      Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      show (s + 1).re = s.re + 1 by simp [Complex.add_re],
      Real.rpow_neg hxpos.le, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg hxpos.le _)) hf1
  have hint_rhs : IntegrableOn (fun x : ℝ => (x : ℝ) ^ (-(s.re + 1))) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) hNpos
  have hint_lhs : IntegrableOn
      (fun x : ℝ => ‖((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖) (Set.Ioi (N : ℝ)) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1))
        (volume.restrict (Set.Ioi (N : ℝ))) := by
      apply Measurable.aestronglyMeasurable; fun_prop
    refine hint_rhs.mono' hm.norm ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt x hx
  -- ‖fractTail‖ ≤ N^{-σ}/σ
  have htail : ‖fractTail s (N : ℝ)‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
    calc ‖fractTail s (N : ℝ)‖
        ≤ ∫ x in Set.Ioi (N : ℝ), ‖((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x in Set.Ioi (N : ℝ), (x : ℝ) ^ (-(s.re + 1)) :=
          setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi hpt
      _ = (N : ℝ) ^ (-s.re) / s.re := by
          rw [integral_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) hNpos,
            show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]
  rw [norm_mul]
  calc ‖s‖ * ‖fractTail s (N : ℝ)‖
      ≤ ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) := mul_le_mul_of_nonneg_left htail (norm_nonneg s)
    _ = ‖s‖ / (s.re * (N : ℝ) ^ s.re) := by
        rw [Real.rpow_neg hNpos.le]; field_simp

/-- THE SHARP NEAR-LINE BOUND: `|ζ(σ+it)| ≤ 6·(1 + log|t|)` for `1 ≤ σ ≤ 2`, `|t| ≥ 2`.
    Explicit UNIFORM constant (`C = 6`), so downstream a single region constant can absorb it. -/
theorem zeta_log_bound {σ t : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ 6 * (1 + Real.log |t|) := by
  set s : ℂ := (σ : ℂ) + t * Complex.I with hs_def
  have hsre : s.re = σ := by simp [hs_def]
  have hsim : s.im = t := by simp [hs_def]
  -- basic real facts about |t|
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le two_pos ht
  have hlog0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  have htne : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  -- cutoff N = ⌊|t|⌋
  set N : ℕ := ⌊|t|⌋₊ with hN_def
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNRpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNle : (N : ℝ) ≤ |t| := Nat.floor_le htpos.le
  have hNgt : |t| - 1 < (N : ℝ) := by have := Nat.lt_floor_add_one |t|; linarith
  -- s ≠ 1 and 0 < s.re
  have hsne1 : s ≠ 1 := by intro h; apply htne; rw [← hsim, h, Complex.one_im]
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have hsre1 : (1 : ℝ) ≤ s.re := by rw [hsre]; exact hσ1
  -- truncated Euler–Maclaurin at N
  have htrunc := zeta_trunc hspos hsne1 hN1
  -- Term A: ‖Σ n^{-s}‖ ≤ 1 + log N ≤ 1 + log|t|.
  have hlogle : Real.log (N : ℝ) ≤ Real.log |t| := Real.log_le_log hNRpos hNle
  have hA : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1 + Real.log |t| := by
    have := norm_partial_sum_le hsre1 hN1
    linarith
  -- Term B: ‖N^{1-s}/(s-1)‖ ≤ 1 (numerator ≤ 1, denominator ≥ |t| ≥ 2).
  have hdenge : (2 : ℝ) ≤ ‖s - 1‖ := by
    have h1 := abs_im_le_norm_sub_one s
    rw [hsim] at h1; linarith
  have hdenpos : (0 : ℝ) < ‖s - 1‖ := by linarith
  have hB : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, div_le_iff₀ hdenpos, one_mul]
    have hnum := norm_cpow_one_sub_le_one hsre1 hN1
    linarith
  -- Term C: ‖s · fractTail‖ ≤ ‖s‖/(σ·N^σ) ≤ 4.
  have hsnorm : ‖s‖ ≤ σ + |t| := by
    have h : ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := by rw [hs_def]; exact norm_add_le _ _
    rwa [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ σ), Real.norm_eq_abs] at h
  have hbpos : (0 : ℝ) < s.re * (N : ℝ) ^ s.re :=
    mul_pos hspos (Real.rpow_pos_of_pos hNRpos _)
  have hden_ge : (N : ℝ) ≤ s.re * (N : ℝ) ^ s.re := by
    have h1 : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hNR1 hsre1
    rw [Real.rpow_one] at h1
    nlinarith [h1, mul_nonneg (by linarith : (0 : ℝ) ≤ s.re - 1) (Real.rpow_nonneg hNRpos.le s.re)]
  have hC : ‖s * fractTail s (N : ℝ)‖ ≤ 4 := by
    refine le_trans (norm_tail_term_le hspos hN1) ?_
    rw [div_le_iff₀ hbpos]
    linarith [hsnorm, hden_ge, hNgt, ht, hσ2]
  -- assemble via the triangle inequality (fed to linarith as facts).
  rw [htrunc]
  have h1 := norm_sub_le ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1))
    (s * fractTail s (N : ℝ))
  have h2 := norm_add_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) ((N : ℂ) ^ (1 - s) / (s - 1))
  linarith [h1, h2, hA, hB, hC, hlog0]

/-- **CRITICAL-STRIP POLYNOMIAL GROWTH BOUND:** `‖ζ(σ+it)‖ ≤ 5·|t|` for `1/2 ≤ σ < 1`, `|t| ≥ 2`.
    This is the `σ < 1` companion to `zeta_log_bound` (which needs `σ ≥ 1`): the dVP entire-part
    re-derivation must bound `ζ` on the sphere of a disk that dips BELOW `Re = 1` (to enclose a
    nontrivial zero `ρ₀`), where no `Re ≥ 1` bound applies. A polynomial `O(|t|)` bound suffices
    downstream — it only affects the region CONSTANT (via `log‖ζ‖ = O(log|t|)`), not the rate.

    Same truncated Euler–Maclaurin at `N = ⌊|t|⌋` as `zeta_log_bound`, but with `σ < 1` the three
    terms are bounded CRUDELY (no `log` needed): Term A `‖Σ n^{-s}‖ ≤ Σ 1 = N ≤ |t|` (each
    `n^{-σ} ≤ 1`), Term B `‖N^{1-s}/(s-1)‖ = N^{1-σ}/‖s-1‖ ≤ |t|/|t| = 1` (`N^{1-σ} ≤ N` since
    `1-σ ≤ 1`), Term C `‖s·fractTail‖ ≤ ‖s‖/(σ·N^σ) ≤ 3|t|` (`σ ≥ 1/2`, `N^σ ≥ 1`).
    (The sharp partial-sum estimate lives in `DlvpZetaStripSum`; here the trivial `≤ N` is cleaner
    and gives the same `O(|t|)`.)  conjecture1_proved = False (NOT a proof of RH). -/
theorem zeta_strip_growth {σ t : ℝ} (hσ0 : 1/2 ≤ σ) (hσ1 : σ < 1) (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ 5 * |t| := by
  set s : ℂ := (σ : ℂ) + t * Complex.I with hs_def
  have hsre : s.re = σ := by simp [hs_def]
  have hsim : s.im = t := by simp [hs_def]
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le two_pos ht
  have htne : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  set N : ℕ := ⌊|t|⌋₊ with hN_def
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNRpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNle : (N : ℝ) ≤ |t| := Nat.floor_le htpos.le
  have hsne1 : s ≠ 1 := by intro h; apply htne; rw [← hsim, h, Complex.one_im]
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have htrunc := zeta_trunc hspos hsne1 hN1
  -- Term A: ‖Σ n^{-s}‖ ≤ N (each term ≤ 1, N terms) ≤ |t|
  have hA : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ |t| := by
    have h1 : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ ∑ n ∈ Finset.Icc 1 N, (1:ℝ) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      rw [← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1)
      rw [hsre]; linarith
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at h1
    exact h1.trans hNle
  -- Term B: ‖N^{1-s}/(s-1)‖ = N^{1-σ}/‖s-1‖ ≤ |t|/|t| = 1
  have hdent : |t| ≤ ‖s - 1‖ := by
    have h1 := abs_im_le_norm_sub_one s; rw [hsim] at h1; linarith
  have hdenpos : (0 : ℝ) < ‖s - 1‖ := by linarith
  have hnumB : ‖(N : ℂ) ^ (1 - s)‖ ≤ |t| := by
    rw [← Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNRpos]
    have : (1 - s).re = 1 - σ := by simp [Complex.sub_re, hsre]
    rw [this]
    calc (N:ℝ) ^ (1 - σ) ≤ (N:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNR1 (by linarith)
      _ = (N:ℝ) := Real.rpow_one _
      _ ≤ |t| := hNle
  have hB : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, div_le_iff₀ hdenpos, one_mul]
    calc ‖(N:ℂ)^(1-s)‖ ≤ |t| := hnumB
      _ ≤ ‖s-1‖ := hdent
  -- Term C: ‖s·fractTail‖ ≤ ‖s‖/(σ·N^σ) ≤ 3|t|
  have hsnorm : ‖s‖ ≤ σ + |t| := by
    have h : ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := by rw [hs_def]; exact norm_add_le _ _
    rwa [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ σ), Real.norm_eq_abs] at h
  have hNσ1 : (1:ℝ) ≤ (N:ℝ) ^ s.re := Real.one_le_rpow hNR1 hspos.le
  have hbpos : (0 : ℝ) < s.re * (N : ℝ) ^ s.re := mul_pos hspos (by linarith)
  have hbge : (1/2 : ℝ) ≤ s.re * (N : ℝ) ^ s.re := by
    have h : s.re * 1 ≤ s.re * (N:ℝ)^s.re := mul_le_mul_of_nonneg_left hNσ1 hspos.le
    rw [mul_one] at h; rw [hsre] at h ⊢; linarith
  have hC : ‖s * fractTail s (N : ℝ)‖ ≤ 3 * |t| := by
    refine le_trans (norm_tail_term_le hspos hN1) ?_
    rw [div_le_iff₀ hbpos]
    nlinarith [hsnorm, mul_le_mul_of_nonneg_left hbge htpos.le, htpos, hσ1, ht]
  -- assemble via the triangle inequality
  rw [htrunc]
  have h1 := norm_sub_le ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1))
    (s * fractTail s (N : ℝ))
  have h2 := norm_add_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) ((N : ℂ) ^ (1 - s) / (s - 1))
  linarith [h1, h2, hA, hB, hC, htpos]

end ZeroFreeBridge
