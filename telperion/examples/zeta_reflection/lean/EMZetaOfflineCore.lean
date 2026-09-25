/-  EMZetaOfflineCore.lean -- lane offline (ANDURIL Arb discharge, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    brick B6 / K2): the general-order Euler-Maclaurin representation of ζ OFF the critical line.

    `EMZetaHigh.em_zeta_order` proves the order-`m` identity
        ζ(s) = emFiniteM m s N + (-1)^(m-1) · emTail s N m / m!
    on `Re s > 0` only (it is transported from the K = 1 continuation `em_zeta_strip`).  The tail
    integral converges on the larger half-plane `Re s > 1 - m`, so the identity extends there by the
    identity theorem.  This file proves that extension and the resulting remainder bounds for
    every real part `σ > 1 - 2K` (even saw) and `σ > -2K` (odd saw):

      O1.  `emTail_eq_mellin`        -- the tail is `emC s m · mellin (sawCut m N) (1 - s - m)`;
      O2.  `emTail_differentiableAt` -- hence complex-differentiable on `Re s > 1 - m`
                                        (`mellin_differentiableAt_of_isBigO_rpow`);
      O3.  `emFiniteM_differentiableAt` -- the finite part is differentiable off `s = 1`;
      O4.  `em_zeta_order_ext`       -- THE CONTINUATION: the order-`m` identity on `Re s > 1 - m`,
                                        `s ≠ 1` (identity theorem on the convex strip
                                        `1 - m < Re s < 1`, anchored at `s = 1/2`);
      O5.  `em_zeta_orderK_enclosure_ext`, `em_zeta_orderK_enclosure_odd_ext` -- the general-K
                                        remainder bounds of `EMZetaHigh` for `σ > 1 - 2K`,
                                        resp. `σ > -2K` (so `σ = -1` is covered from `K = 1` on).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin + analytic
    continuation); it says nothing about the Riemann Hypothesis.
-/
import EMZetaHigh

open MeasureTheory Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMOff

open EMHigh

/-! ## O1. The tail as a Mellin transform. -/

/-- The periodized Bernoulli function `B̃_m`, cut off to `(N, ∞)`, as a complex function. -/
noncomputable def sawCut (m N : ℕ) (x : ℝ) : ℂ :=
  Set.indicator (Ioi (N : ℝ)) (fun y : ℝ => (sawBernoulli m y : ℂ)) x

theorem emTail_eq_mellin (m : ℕ) {N : ℕ} (s : ℂ) :
    emTail s N m = emC s m * mellin (sawCut m N) (1 - s - m) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hexp : (1 - s - (m : ℂ) - 1) = -s - (m : ℂ) := by ring
  unfold mellin sawCut
  rw [hexp]
  have h1 : (fun x : ℝ => (x : ℂ) ^ (-s - (m : ℂ)) •
        Set.indicator (Ioi (N : ℝ)) (fun y : ℝ => (sawBernoulli m y : ℂ)) x)
      = Set.indicator (Ioi (N : ℝ)) (fun x : ℝ => (x : ℂ) ^ (-s - (m : ℂ)) • (sawBernoulli m x : ℂ)) :=
    (Set.indicator_smul _ _ _).symm
  rw [h1, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hN0]
  unfold emTail
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [smul_eq_mul]
  ring

/-! ## O2. Differentiability of the tail on `Re s > 1 - m`. -/

theorem sawCut_norm_le (m N : ℕ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x : ℝ, |sawBernoulli m x| ≤ B)
    (x : ℝ) : ‖sawCut m N x‖ ≤ B := by
  unfold sawCut
  by_cases hx : x ∈ Ioi (N : ℝ)
  · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]; exact hB x
  · rw [Set.indicator_of_notMem hx, norm_zero]; exact hB0

theorem sawCut_measurable (m N : ℕ) : Measurable (sawCut m N) :=
  (Complex.measurable_ofReal.comp (sawBernoulli_measurable m)).indicator measurableSet_Ioi

theorem mellin_sawCut_differentiableAt (m : ℕ) {N : ℕ} (hN : 1 ≤ N) {w : ℂ} (hw : w.re < 0) :
    DifferentiableAt ℂ (mellin (sawCut m N)) w := by
  obtain ⟨B, hB0, hB⟩ := sawBernoulli_bounded m
  have hbound := sawCut_norm_le m N hB0 hB
  apply mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := w.re - 1)
  · apply LocallyIntegrable.locallyIntegrableOn
    rw [locallyIntegrable_iff]
    intro k hk
    exact IntegrableOn.of_bound hk.measure_lt_top
      (sawCut_measurable m N).aestronglyMeasurable B (Eventually.of_forall hbound)
  · apply Asymptotics.isBigO_of_le' (c := B)
    intro x
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hbound x
  · exact hw
  · have hev : sawCut m N =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
      unfold sawCut
      apply Set.indicator_of_notMem
      simp only [mem_Ioi, not_lt]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith [hx.2]
    exact hev.trans_isBigO (Asymptotics.isBigO_zero _ _)
  · linarith

theorem poch_differentiable (k : ℕ) : Differentiable ℂ (fun s => poch s k) := by
  induction k with
  | zero => simp only [poch]; exact differentiable_const (1 : ℂ)
  | succ k ih =>
    have e : (fun s => poch s (k + 1)) = fun s => poch s k * (s + k) := by
      funext s; rfl
    rw [e]
    exact ih.mul (differentiable_id.add (differentiable_const _))

theorem emC_differentiable (k : ℕ) : Differentiable ℂ (fun s => emC s k) := by
  have e : (fun s => emC s k) = fun s => (-1 : ℂ) ^ k * poch s k := by funext s; rfl
  rw [e]
  exact (differentiable_const _).mul (poch_differentiable k)

theorem emTail_differentiableAt (m : ℕ) {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 - (m : ℝ) < s.re) :
    DifferentiableAt ℂ (fun z => emTail z N m) s := by
  have e : (fun z => emTail z N m) = fun z => emC z m * mellin (sawCut m N) (1 - z - m) := by
    funext z; exact emTail_eq_mellin m z
  rw [e]
  apply DifferentiableAt.mul (emC_differentiable m).differentiableAt
  have hw : (1 - s - (m : ℂ)).re < 0 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.natCast_re]
    linarith
  have h1 := mellin_sawCut_differentiableAt m hN hw
  have h2 : DifferentiableAt ℂ (fun z : ℂ => 1 - z - (m : ℂ)) s := by fun_prop
  have h3 : DifferentiableAt ℂ (mellin (sawCut m N) ∘ (fun z : ℂ => 1 - z - (m : ℂ))) s :=
    DifferentiableAt.comp (f := fun z : ℂ => 1 - z - (m : ℂ)) (g := mellin (sawCut m N)) s h1 h2
  exact h3

/-! ## O3. Differentiability of the finite part off `s = 1`. -/

theorem emFiniteM_differentiableAt (m : ℕ) {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => emFiniteM m z N) s := by
  have hc : ∀ n : ℕ, 1 ≤ n → ∀ g : ℂ → ℂ, DifferentiableAt ℂ g s →
      DifferentiableAt ℂ (fun z => (n : ℂ) ^ g z) s := fun n hn g hg =>
    hg.const_cpow (Or.inl (by exact_mod_cast (show n ≠ 0 by omega)))
  unfold emFiniteM
  apply DifferentiableAt.add
  · apply DifferentiableAt.add
    · apply DifferentiableAt.add
      · apply DifferentiableAt.fun_sum
        intro n hn
        exact hc n (Finset.mem_Ico.mp hn).1 _ (differentiableAt_id.neg)
      · apply DifferentiableAt.div
        · exact hc N hN _ ((differentiableAt_const _).sub differentiableAt_id)
        · exact differentiableAt_id.sub (differentiableAt_const _)
        · exact sub_ne_zero.mpr hs1
    · exact (hc N hN _ differentiableAt_id.neg).div_const _
  · apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.mul
    · exact (((differentiableAt_const _).mul
        (poch_differentiable (i + 1)).differentiableAt).div_const _)
    · exact hc N hN _ (differentiableAt_id.neg.sub (differentiableAt_const _))

/-! ## O4. THE CONTINUATION of the order-`m` identity to `Re s > 1 - m`. -/

/-- **The order-`m` Euler-Maclaurin identity on `Re s > 1 - m`** (`m ≥ 1`, `s ≠ 1`, `N ≥ 1`):
        ζ(s) = emFiniteM m s N + (-1)^(m-1) · emTail s N m / m!.
    For `Re s > 0` this is `EMHigh.em_zeta_order`.  Both sides are analytic on the convex strip
    `1 - m < Re s < 1` (which avoids the pole) and agree near `s = 1/2`, so they agree on the strip;
    every `s` with `1 - m < Re s ≤ 0` lies in it. -/
theorem em_zeta_order_ext (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 1 - (m : ℝ) < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = emFiniteM m s N + (-1) ^ (m - 1) * emTail s N m / (m ! : ℂ) := by
  by_cases hpos : 0 < s.re
  · exact em_zeta_order m hm hpos hs1 hN
  push Not at hpos
  set U : Set ℂ := {z : ℂ | 1 - (m : ℝ) < z.re} ∩ {z : ℂ | z.re < 1} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
  have hne1 : ∀ z ∈ U, z ≠ 1 := by
    intro z hz h
    rw [h] at hz
    have := hz.2
    simp at this
  set F : ℂ → ℂ := fun z => emFiniteM m z N + (-1) ^ (m - 1) * emTail z N m / (m ! : ℂ) with hF
  have hFan : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact (emFiniteM_differentiableAt m hN (hne1 z hz)).add
      (((differentiableAt_const _).mul (emTail_differentiableAt m hN hz.1)).div_const _)
  have hZan : AnalyticOnNhd ℂ riemannZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro z hz
    exact (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalf : (1 / 2 : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · show 1 - (m : ℝ) < (1 / 2 : ℂ).re
      norm_num; linarith
    · show (1 / 2 : ℂ).re < 1
      norm_num
  have hev : riemannZeta =ᶠ[𝓝 (1 / 2 : ℂ)] F := by
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : (1 / 2 : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
      constructor <;> norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at hz; have := hz.2; simp at this
    exact em_zeta_order m hm hz.1 hz1 hN
  have heq := hZan.eqOn_of_preconnected_of_eventuallyEq hFan hUc hhalf hev
  have hlt : s.re < 1 := by linarith
  exact heq ⟨hs, hlt⟩

/-! ## O5. The general-K remainder bounds off the critical line. -/

/-- The tail bound for every `s` with `Re s + m > 1` (`EMHigh.emTail_norm_le` assumed `Re s > 0`). -/
theorem emTail_norm_le_ext (m : ℕ) {s : ℂ} (h : 1 < s.re + m) {N : ℕ} (hN : 1 ≤ N)
    {B : ℝ} (hB0 : 0 ≤ B) (hsaw : ∀ x : ℝ, |sawBernoulli m x| ≤ B) :
    ‖emTail s N m‖ ≤ B * ‖poch s m‖ * (N : ℝ) ^ (-(s.re + m - 1)) / (s.re + m - 1) := by
  have h' := em_tail_integral_bound (k := m) (s := s) (c := emC s m) (B := B) (N := N) hN h hB0 hsaw
  rw [norm_emC] at h'
  exact h'

/-- **General-K enclosure, even saw, off the line**: for `1 - 2K < Re s`, `s ≠ 1`, `N ≥ 1`,
        ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)} / (σ+2K-1). -/
theorem em_zeta_orderK_enclosure_ext (K : ℕ) (hK : 1 ≤ K) {s : ℂ}
    (hs : 1 - ((2 * K : ℕ) : ℝ) < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ‖poch s (2 * K)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K : ℕ) : ℝ) - 1)) / (s.re + ((2 * K : ℕ) : ℝ) - 1) := by
  have hm : 1 ≤ 2 * K := by omega
  have hid := em_zeta_order_ext (2 * K) hm hs hs1 hN
  rw [emFinite_eq_emFiniteM K s hN]
  have hdiff : riemannZeta s - emFiniteM (2 * K) s N
      = (-1) ^ (2 * K - 1) * emTail s N (2 * K) / ((2 * K)! : ℂ) := by
    rw [hid]; ring
  rw [hdiff]
  have hF : (0 : ℝ) < ((2 * K)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnorm : ‖(-1) ^ (2 * K - 1) * emTail s N (2 * K) / ((2 * K)! : ℂ)‖
      = ‖emTail s N (2 * K)‖ / ((2 * K)! : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    congr 1
    exact_mod_cast Complex.norm_natCast _
  rw [hnorm]
  have hbd := emTail_norm_le_ext (2 * K) (s := s) (by linarith) hN (abs_nonneg _)
    (abs_sawBernoulli_even_le K (by omega))
  have hF' : (0 : ℝ) ≤ ((2 * K)! : ℝ) := hF.le
  calc ‖emTail s N (2 * K)‖ / ((2 * K)! : ℝ)
      ≤ (|(bernoulli (2 * K) : ℝ)| * ‖poch s (2 * K)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K : ℕ) : ℝ) - 1)) / (s.re + ((2 * K : ℕ) : ℝ) - 1))
          / ((2 * K)! : ℝ) := div_le_div_of_nonneg_right hbd hF'
    _ = _ := by ring

/-- **General-K enclosure, odd saw, off the line**: for `-2K < Re s`, `s ≠ 1`, `N ≥ 1`,
        ‖ζ(s) − emFinite K s N‖ ≤ 2(1 + (π²/6−1)/2^(2K−1))/(2π)^(2K+1) · ‖(s)_{2K+1}‖
                                    · N^{−(σ+2K)} / (σ+2K). -/
theorem em_zeta_orderK_enclosure_odd_ext (K : ℕ) (hK : 1 ≤ K) {s : ℂ}
    (hs : -((2 * K : ℕ) : ℝ) < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * ‖poch s (2 * K + 1)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) := by
  have hm : 1 ≤ 2 * K + 1 := by omega
  have hs' : 1 - ((2 * K + 1 : ℕ) : ℝ) < s.re := by push_cast at hs ⊢; linarith
  have hid := em_zeta_order_ext (2 * K + 1) hm hs' hs1 hN
  rw [emFinite_eq_emFiniteM K s hN, ← emFiniteM_odd_eq K hK s N]
  have hdiff : riemannZeta s - emFiniteM (2 * K + 1) s N
      = (-1) ^ (2 * K + 1 - 1) * emTail s N (2 * K + 1) / ((2 * K + 1)! : ℂ) := by
    rw [hid]; ring
  rw [hdiff]
  have hF : (0 : ℝ) < ((2 * K + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnorm : ‖(-1) ^ (2 * K + 1 - 1) * emTail s N (2 * K + 1) / ((2 * K + 1)! : ℂ)‖
      = ‖emTail s N (2 * K + 1)‖ / ((2 * K + 1)! : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    congr 1
    exact_mod_cast Complex.norm_natCast _
  rw [hnorm]
  have hB0 : 0 ≤ 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1)
      * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
    have hpi6 : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by
      have := Real.pi_gt_three
      nlinarith
    positivity
  have hbd := emTail_norm_le_ext (2 * K + 1) (s := s) (by push_cast at hs ⊢; linarith) hN hB0
    (abs_sawBernoulli_odd_le K (by omega))
  calc ‖emTail s N (2 * K + 1)‖ / ((2 * K + 1)! : ℝ)
      ≤ (2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
          / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / ((2 * K + 1)! : ℝ) :=
        div_le_div_of_nonneg_right hbd hF.le
    _ = _ := by field_simp

end EMOff

end ZetaReflection
