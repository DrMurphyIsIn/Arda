/- THE BRIDGE: 3 Re L(s) + 4 Re L(s+it) + Re L(s+2it) >= 0 for Re s > 1,
   where L(Lambda, .) = -zeta'/zeta is the von Mangoldt L-series.
   The Mertens nonnegative-cosine certificate (3 + 4 cos + cos 2 = 2(1+cos)^2, from
   TrigNonneg), proven in-kernel to meet the actual Dirichlet series of -zeta'/zeta.
   This is the KEY INEQUALITY of the classical zero-free region -- the positivity that,
   combined with an (unformalized, research-scale) zeta growth bound, yields
   zeta(s) != 0 for Re s > 1 - c/log|t|.  A certificate FEEDING the region, NOT the
   region and NOT a proof of RH.  conjecture1_proved = False. -/
import Mathlib
open scoped Real
open Filter Topology

namespace ZeroFreeBridge

/- ===================================================================================
   RESIDUE OF THE LOGARITHMIC DERIVATIVE = ORDER.  A general complex-analysis lemma
   (NOT RH-specific): for f meromorphic at z0 of order n (a zero if n>0, a pole if n<0),
   (z - z0) * logDeriv f z -> n as z -> z0 within the punctured neighbourhood.
   Mathlib v4.32.0 has ONLY the analytic simple-zero case
   (AnalyticAt.tendsto_mul_logDeriv_simple_zero, n=1); the general-order version is a
   genuine gap here (present only on Mathlib master).  Built from the local factorization
   meromorphicOrderAt_eq_int_iff  (f =ᶠ (z-z0)^n • g, g analytic, g z0 != 0).
   =================================================================================== -/

/-- Transfer `logDeriv` through a punctured-neighbourhood eventual equality. -/
theorem logDeriv_congr_punctured {f h : ℂ → ℂ} {z₀ : ℂ} (H : f =ᶠ[𝓝[≠] z₀] h) :
    logDeriv f =ᶠ[𝓝[≠] z₀] logDeriv h := by
  obtain ⟨s, hs_mem, hs_eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp H
  rw [mem_nhdsWithin] at hs_mem
  obtain ⟨U, hUopen, hz₀U, hUsub⟩ := hs_mem
  have hmem : U ∩ {z₀}ᶜ ∈ 𝓝[≠] z₀ := by
    rw [mem_nhdsWithin]; exact ⟨U, hUopen, hz₀U, fun x hx => hx⟩
  filter_upwards [hmem] with z hz
  have hopen : IsOpen (U ∩ {z₀}ᶜ) := hUopen.inter isOpen_compl_singleton
  have hlocal : f =ᶠ[𝓝 z] h :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun x hx => hs_eq (hUsub hx))
  simp only [logDeriv, Pi.div_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]

/-- `logDeriv ((z-z0)^n • g) = n/(z-z0) + logDeriv g` off `z0`. -/
theorem logDeriv_zpow_smul_split (g : ℂ → ℂ) (z₀ w : ℂ) (n : ℤ) (hw : w ≠ z₀)
    (hg : DifferentiableAt ℂ g w) (hgw : g w ≠ 0) :
    logDeriv (fun z => (z - z₀) ^ n • g z) w = (n : ℂ) / (w - z₀) + logDeriv g w := by
  have hsub : DifferentiableAt ℂ (fun z : ℂ => z - z₀) w := by fun_prop
  have hbne : (w - z₀) ≠ 0 := sub_ne_zero.mpr hw
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (z - z₀) ^ n) w := hsub.zpow (Or.inl hbne)
  have hpne : (w - z₀) ^ n ≠ 0 := zpow_ne_zero _ hbne
  have hbase : (fun z : ℂ => (z - z₀) ^ n • g z) = (fun z => (z - z₀) ^ n * g z) := by
    funext z; rw [smul_eq_mul]
  have hld : logDeriv (fun z : ℂ => z - z₀) w = 1 / (w - z₀) := by
    have hd : deriv (fun z : ℂ => z - z₀) w = 1 := by simp
    show deriv (fun z : ℂ => z - z₀) w / (w - z₀) = 1 / (w - z₀)
    rw [hd]
  have hzp : logDeriv (fun z : ℂ => (z - z₀) ^ n) w = (n : ℂ) / (w - z₀) := by
    rw [logDeriv_fun_zpow hsub n, hld]; ring
  rw [hbase, logDeriv_mul w hpne hgw hpow hg, hzp]

/-- The analytic tail: `(z-z0) * logDeriv g z -> 0` for `g` analytic at `z0`, `g z0 != 0`. -/
theorem tendsto_sub_mul_logDeriv_zero {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    Tendsto (fun z => (z - z₀) * logDeriv g z) (𝓝[≠] z₀) (𝓝 0) := by
  have hc : ContinuousAt (logDeriv g) z₀ :=
    (hg.deriv.continuousAt).div hg.continuousAt hg0
  have h1 : Tendsto (fun z : ℂ => (z - z₀) * logDeriv g z) (𝓝[≠] z₀)
      (𝓝 ((z₀ - z₀) * logDeriv g z₀)) :=
    Tendsto.mul ((Continuous.tendsto (by fun_prop) z₀).mono_left nhdsWithin_le_nhds)
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  simpa using h1

/-- Residue of the logarithmic derivative equals the meromorphic order. -/
theorem residue_logDeriv {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ = (n : WithTop ℤ)) :
    Tendsto (fun z => (z - z₀) * logDeriv f z) (𝓝[≠] z₀) (𝓝 (n : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  have hcong : logDeriv f =ᶠ[𝓝[≠] z₀] logDeriv (fun z => (z - z₀) ^ n • g z) :=
    logDeriv_congr_punctured hfg
  have hgne : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  have hgdiff : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
    filter_upwards [(hg.eventually_analyticAt).filter_mono nhdsWithin_le_nhds] with z hz
      using hz.differentiableAt
  have hev : (fun z => (z - z₀) * logDeriv f z)
      =ᶠ[𝓝[≠] z₀] (fun z => (n : ℂ) + (z - z₀) * logDeriv g z) := by
    filter_upwards [hcong, self_mem_nhdsWithin, hgne, hgdiff] with z hz hzne hgz hgd
    have hzne' : z ≠ z₀ := hzne
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne'
    rw [hz, logDeriv_zpow_smul_split g z₀ z n hzne' hgd hgz]
    field_simp
  rw [tendsto_congr' hev]
  simpa using (tendsto_const_nhds.add (tendsto_sub_mul_logDeriv_zero hg hg0))

theorem mertens_three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h := Real.cos_two_mul θ; nlinarith [h, sq_nonneg (Real.cos θ + 1)]

theorem cpow_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (((n : ℂ)) ^ (-s)).re = (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).re = -s.re * Real.log n := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have him : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).im = -(s.im * Real.log n) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.exp_re, hre, him,
      Real.cos_neg, show -s.re * Real.log (n : ℝ) = Real.log (n : ℝ) * -s.re from by ring,
      ← Real.rpow_def_of_pos hnpos]

theorem term_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.re_ofReal_mul, cpow_re n hn s, mul_assoc]

theorem term_comb_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ 3 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 4 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [LSeries.term]
  · have hn : 1 ≤ n := hpos
    rw [term_re n hn (σ : ℂ), term_re n hn ((σ : ℂ) + (t : ℂ) * Complex.I),
        term_re n hn ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, Real.cos_zero]
    rw [mul_assoc (2 : ℝ) t (Real.log (n : ℝ))]
    have hp : (0:ℝ) < (n:ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hM : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-σ) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hp.le
    nlinarith [mul_nonneg hM (mertens_three_four_one (t * Real.log n)), hM]

theorem vonMangoldt_re_comb_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)).re
      + 4 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have hf : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hg : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hh : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hA : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re) := hf.map Complex.reCLM Complex.reCLM.cont
  have hB : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re) := hg.map Complex.reCLM Complex.reCLM.cont
  have hC : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re) := hh.map Complex.reCLM Complex.reCLM.cont
  show 0 ≤ 3 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 4 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re
  rw [Complex.re_tsum hf, Complex.re_tsum hg, Complex.re_tsum hh,
      (((hA.hasSum.mul_left 3).add (hB.hasSum.mul_left 4)).add hC.hasSum).tsum_eq.symm]
  exact tsum_nonneg (fun n => term_comb_nonneg n σ t)

/- The same positivity, restated LITERALLY about zeta's logarithmic derivative -zeta'/zeta,
   via Mathlib's  LSeries(vonMangoldt) s = -zeta'(s)/zeta(s)  (Re s > 1).  This is the exact
   form the classical zero-free-region argument uses: 3 Re(-zeta'/zeta)(sigma) + 4 Re(...)(sigma+it)
   + Re(...)(sigma+2it) >= 0.  Still NOT a proof of RH -- the region needs the log-derivative ->
   product step and the zeta growth bound (both unformalized, research-scale). -/
theorem zeta_logDeriv_comb_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have e1 : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e2 : -deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e3 : -deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  rw [e1, e2, e3]
  exact vonMangoldt_re_comb_nonneg σ t hσ

end ZeroFreeBridge
