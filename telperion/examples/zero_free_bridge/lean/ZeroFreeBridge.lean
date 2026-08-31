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

/- ===================================================================================
   THE BRIDGE-POWERED BOUNDARY CONTRADICTION (classical de la Vallee Poussin core).
   The Mertens positivity 3 Re(-zeta'/zeta)(sigma) + 4 Re(...)(sigma+it) + Re(...)(sigma+2it) >= 0
   (proven above), multiplied by (sigma-1) > 0 and taken to sigma -> 1+, forces
   3*1 - 4k - k' >= 0, where +1 is the residue of -zeta'/zeta at the simple pole s=1 and
   -k, -k' are the residues at 1+it, 1+2it (k = order of a zero at 1+it, k' >= 0 at 1+2it).
   With k >= 1 this is 3 - 4k - k' <= -1 < 0, impossible: so zeta has NO zero of order >= 1
   at 1+it.  This is exactly how the classical zero-free-region boundary (zeta(1+it) != 0)
   is forced by the 3-4-1 inequality -- routed here through -zeta'/zeta (a different internal
   path from Mathlib's product-route riemannZeta_ne_zero_of_one_le_re).

   The three residue LIMITS are taken as hypotheses (hpole/hz1/hz2): each is the real-line
   restriction of  residue_logDeriv  (proven above: (z-z0)*logDeriv f z -> order) applied to
   zeta at 1, 1+it, 1+2it -- given zeta's meromorphy/orders there.  Discharging them fully needs
   zeta's simple-pole handle at s=1 (a v4.32.0 API gap, via completedRiemannZeta) + order
   extraction + the .re/real-ray plumbing.  conjecture1_proved = False; NOT a proof of RH --
   this is the boundary (c=0) edge of the classical region, which Mathlib already has. -/
theorem zeta_boundary_contradiction (t : ℝ) (k k' : ℤ) (hk : 1 ≤ k) (hk' : 0 ≤ k')
    (hpole : Tendsto (fun σ : ℝ => (σ - 1) *
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re) (𝓝[>] (1 : ℝ)) (𝓝 1))
    (hz1 : Tendsto (fun σ : ℝ => (σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re) (𝓝[>] (1 : ℝ)) (𝓝 (-(k : ℝ))))
    (hz2 : Tendsto (fun σ : ℝ => (σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 (-(k' : ℝ)))) :
    False := by
  have hGnn : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      0 ≤ (σ - 1) * (3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have h1 : (1 : ℝ) < σ := hσ
    exact mul_nonneg (by linarith) (zeta_logDeriv_comb_nonneg σ t h1)
  have hlim := ((hpole.const_mul 3).add (hz1.const_mul 4)).add hz2
  have hval : (3 : ℝ) * 1 + 4 * (-(k : ℝ)) + (-(k' : ℝ)) = 3 - 4 * (k : ℝ) - (k' : ℝ) := by ring
  rw [hval] at hlim
  have hGlim : Tendsto (fun σ : ℝ => (σ - 1) *
      (3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re))
      (𝓝[>] (1 : ℝ)) (𝓝 (3 - 4 * (k : ℝ) - (k' : ℝ))) := by
    convert hlim using 1
    funext σ; ring
  have hge : (0 : ℝ) ≤ 3 - 4 * (k : ℝ) - (k' : ℝ) := ge_of_tendsto hGlim hGnn
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk'0 : (0 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'
  linarith

/- ===================================================================================
   IMPROVED ZERO-FREE CERTIFICATE (degree 3).  The de la Vallee Poussin polynomial
   3 + 4cos + cos2 = 2(1+cos)^2 is NOT optimal.  Optimizing the leading-order zero-free
   functional  F(P) = (sqrt a_1 - sqrt a_0)^2 / sum_{k>=1} a_k  over NONNEGATIVE cosine
   polynomials (a_k >= 0) is exactly the Mossinghoff-Trudgian 2015 program (J. Number
   Theory 157; improved region constant R_0 = 5.573412).  The (1+cos)^n family gives clean
   Fejer-Riesz certificates capturing most of the gain.  Here n = 3:
       20 + 30 cos + 12 cos2 + 2 cos3  =  8 (1 + cos)^3  >= 0,   a_1 = 30 > a_0 = 20,
   with F = 0.02296 vs 0.01436 for de la Vallee Poussin (1.60x wider region, leading order).
   Generator UNTRUSTED, Lean kernel sole arbiter.  This still only FEEDS the classical region
   CONSTANT -- it improves the constant, NOT the Vinogradov-Korobov rate 1/(log t)^{2/3}, and
   is NOT a proof of RH.  conjecture1_proved = False.
   =================================================================================== -/

/-- Fejer-Riesz backbone: `(1 + cos theta)^n >= 0` -- the SOS behind every `(1+cos)^n`
    nonnegative-cosine certificate. -/
theorem one_add_cos_pow_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ (1 + Real.cos θ) ^ n :=
  pow_nonneg (by have := Real.neg_one_le_cos θ; linarith) n

/-- The improved (degree-3) nonnegative-cosine certificate:
    `20 + 30 cos θ + 12 cos 2θ + 2 cos 3θ = 8 (1 + cos θ)^3 ≥ 0` (Fejer-Riesz SOS). -/
theorem mertens_improved (θ : ℝ) :
    0 ≤ 20 + 30 * Real.cos θ + 12 * Real.cos (2 * θ) + 2 * Real.cos (3 * θ) := by
  have h2 := Real.cos_two_mul θ
  have h3 := Real.cos_three_mul θ
  have hc : 0 ≤ 1 + Real.cos θ := by have := Real.neg_one_le_cos θ; linarith
  nlinarith [h2, h3, mul_nonneg (sq_nonneg (Real.cos θ + 1)) hc]

/-- Per-term nonnegativity of the improved combination on the von Mangoldt L-series terms
    at the four shifts `σ, σ+it, σ+2it, σ+3it`. -/
theorem term_comb4_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ 20 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 30 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + 12 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re
      + 2 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [LSeries.term]
  · have hn : 1 ≤ n := hpos
    rw [term_re n hn (σ : ℂ), term_re n hn ((σ : ℂ) + (t : ℂ) * Complex.I),
        term_re n hn ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I),
        term_re n hn ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, Real.cos_zero]
    rw [mul_assoc (2 : ℝ) t (Real.log (n : ℝ)), mul_assoc (3 : ℝ) t (Real.log (n : ℝ))]
    have hp : (0:ℝ) < (n:ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hM : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-σ) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hp.le
    nlinarith [mul_nonneg hM (mertens_improved (t * Real.log n)), hM]

/-- Summed improved positivity for the von Mangoldt L-series (Re s > 1). -/
theorem vonMangoldt_re_comb4_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 20 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)).re
      + 30 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + 12 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
      + 2 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I)).re := by
  have hf : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hg : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hh : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hi : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hA : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re) := hf.map Complex.reCLM Complex.reCLM.cont
  have hB : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re) := hg.map Complex.reCLM Complex.reCLM.cont
  have hC : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re) := hh.map Complex.reCLM Complex.reCLM.cont
  have hD : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I) n).re) := hi.map Complex.reCLM Complex.reCLM.cont
  show 0 ≤ 20 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 30 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + 12 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re
      + 2 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I) n).re
  rw [Complex.re_tsum hf, Complex.re_tsum hg, Complex.re_tsum hh, Complex.re_tsum hi,
      ((((hA.hasSum.mul_left 20).add (hB.hasSum.mul_left 30)).add (hC.hasSum.mul_left 12)).add (hD.hasSum.mul_left 2)).tsum_eq.symm]
  exact tsum_nonneg (fun n => term_comb4_nonneg n σ t)

/-- The improved positivity, restated LITERALLY about `-zeta'/zeta`: for `Re s > 1`,
    `20 Re(-ζ'/ζ)(σ) + 30 Re(-ζ'/ζ)(σ+it) + 12 Re(-ζ'/ζ)(σ+2it) + 2 Re(-ζ'/ζ)(σ+3it) ≥ 0`.
    A strictly wider zero-free-region certificate than the degree-2 Mertens one -- improving the
    region CONSTANT (Mossinghoff-Trudgian direction), NOT the rate, NOT a proof of RH. -/
theorem zeta_logDeriv_comb4_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 20 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 30 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + 12 * (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
      + 2 * (-deriv riemannZeta ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I)).re := by
  have e1 : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e2 : -deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e3 : -deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e4 : -deriv riemannZeta ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((3 * t : ℝ) : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  rw [e1, e2, e3, e4]
  exact vonMangoldt_re_comb4_nonneg σ t hσ

/- ===================================================================================
   GENERAL DEGREE-n CERTIFICATE.  Everything above is the n=2 (Mertens) and n=3 instances of
   a single statement: ANY pointwise-nonnegative cosine polynomial
       P(φ) = sum_{k < N} a k * cos (k φ) >= 0
   yields the zero-free-region positivity on -zeta'/zeta.  This subsumes the (1+cos)^n family
   (`one_add_cos_pow_nonneg`, whose cosine coefficients are all >= 0) and every Mossinghoff-Trudgian
   optimal polynomial -- the whole certificate cone, at once, for arbitrary degree.
   Generator UNTRUSTED, Lean kernel sole arbiter.  Still FEEDS the classical region constant only,
   NOT the Vinogradov-Korobov rate, NOT a proof of RH.  conjecture1_proved = False.
   =================================================================================== -/

/-- Real part of the `k`-th shifted argument `σ + i k t` is `σ`. -/
theorem shift_re (σ t : ℝ) (k : ℕ) :
    ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I).re = σ := by
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- Imaginary part of the `k`-th shifted argument `σ + i k t` is `k t`. -/
theorem shift_im (σ t : ℝ) (k : ℕ) :
    ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I).im = (k : ℝ) * t := by
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]

open Finset in
/-- GENERAL degree-`N` zero-free positivity.  For ANY coefficient sequence `a : ℕ → ℝ` whose
    cosine polynomial is pointwise nonnegative (`∀ φ, 0 ≤ ∑_{k<N} a k · cos (k φ)`), the matching
    `-ζ'/ζ` combination is nonnegative for `Re s > 1`:
      `0 ≤ ∑_{k<N} a k · Re(-ζ'/ζ)(σ + i k t)`.
    The degree-2 Mertens `(3,4,1)`, the degree-3 `(20,30,12,2)`, and the whole `2^n(1+cos)^n` family
    are instances.  A certificate FEEDING the classical zero-free-region CONSTANT, NOT a proof of RH. -/
theorem cosine_comb_zeta_nonneg (N : ℕ) (a : ℕ → ℝ)
    (hP : ∀ φ : ℝ, 0 ≤ ∑ k ∈ range N, a k * Real.cos ((k : ℝ) * φ))
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ k ∈ range N, a k *
      (-deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
        / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re := by
  have hre : ∀ k : ℕ, 1 < ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I).re := by
    intro k; rw [shift_re]; exact hσ
  have hsum : ∀ k : ℕ, Summable (fun m => (LSeries.term
      (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
        ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) m).re) := fun k =>
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (hre k)).map Complex.reCLM Complex.reCLM.cont
  -- rewrite each -ζ'/ζ as the von Mangoldt L-series, then its Re as a tsum of term.re
  have hstep : ∀ k ∈ range N,
      a k * (-deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
              / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re
        = ∑' m, a k * (LSeries.term (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
              ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) m).re := by
    intro k _
    have h1 : -deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
              / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
        = LSeries (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
              ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) :=
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hre k)).symm
    have h2 : (LSeries (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
              ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re
        = ∑' m, (LSeries.term (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
              ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) m).re :=
      Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt (hre k))
    rw [h1, h2, tsum_mul_left]
  rw [Finset.sum_congr rfl hstep,
      ← (hasSum_sum (fun k (_ : k ∈ range N) => ((hsum k).mul_left (a k)).hasSum)).tsum_eq]
  apply tsum_nonneg
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp [LSeries.term]
  · have hfac : ∀ k : ℕ, a k * (LSeries.term (fun j => (ArithmeticFunction.vonMangoldt j : ℂ))
          ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I) m).re
        = (ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ))
            * (a k * Real.cos ((k : ℝ) * (t * Real.log m))) := by
      intro k
      rw [term_re m hpos ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I), shift_re, shift_im,
          mul_assoc (k : ℝ) t (Real.log m)]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hfac k), ← Finset.mul_sum]
    exact mul_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_pos_of_pos (by exact_mod_cast hpos) _).le)
      (hP (t * Real.log m))

/- ===================================================================================
   THE HINGE.  The general positivity feeds the classical boundary conclusion: ANY admissible
   certificate forces `ζ(1+it) ≠ 0`.  "Admissible" = coefficients `a_k ≥ 0` (residue upper bounds),
   pointwise-nonnegative cosine polynomial (positivity), and the single inequality `a 0 < a 1`.
   That last condition is EXACTLY the hinge: the pole residue `+a 0` at `s=1` loses to a zero
   residue `-a 1·m` (m ≥ 1) at `1+it` precisely when `a 1 > a 0`.  The Fejer bound `a_1 < 2 a_0`
   caps how far this can be pushed.  Still the c=0 boundary (`ζ(1+it) ≠ 0` is already in Mathlib),
   NOT a proof of RH.  conjecture1_proved = False.
   =================================================================================== -/
open Finset in
theorem admissible_boundary_contradiction (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℝ)
    (hcoef : ∀ k, 0 ≤ a k) (hadm : a 0 < a 1)
    (hP : ∀ φ : ℝ, 0 ≤ ∑ k ∈ range N, a k * Real.cos ((k : ℝ) * φ))
    (t : ℝ) (r : ℕ → ℝ)
    (hr : ∀ k ∈ range N, Tendsto (fun σ : ℝ => (σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 (r k)))
    (hr0 : r 0 = 1) (hr1 : r 1 ≤ -1) (hrneg : ∀ k ∈ range N, 1 ≤ k → r k ≤ 0) :
    False := by
  have hGnn : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      0 ≤ ∑ k ∈ range N, a k * ((σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have h1 : (1 : ℝ) < σ := hσ
    have hpos := cosine_comb_zeta_nonneg N a hP σ t h1
    have heq : ∑ k ∈ range N, a k * ((σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re)
        = (σ - 1) * ∑ k ∈ range N, a k *
          (-deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
            / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [heq]; exact mul_nonneg (by linarith) hpos
  have hlim : Tendsto (fun σ : ℝ => ∑ k ∈ range N, a k * ((σ - 1) *
        (-deriv riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * Complex.I)).re))
      (𝓝[>] (1 : ℝ)) (𝓝 (∑ k ∈ range N, a k * r k)) :=
    tendsto_finset_sum _ (fun k hk => (hr k hk).const_mul (a k))
  have hge : (0 : ℝ) ≤ ∑ k ∈ range N, a k * r k := ge_of_tendsto hlim hGnn
  have h01 : ({0, 1} : Finset ℕ) ⊆ range N := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_range]; omega
  have htail : ∑ k ∈ range N \ {0, 1}, a k * r k ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton] at hk
    exact mul_nonpos_iff.mpr (Or.inl ⟨hcoef k,
      hrneg k (Finset.mem_range.mpr hk.1) (by omega)⟩)
  have hsplit : ∑ k ∈ range N, a k * r k
      = ∑ k ∈ range N \ {0, 1}, a k * r k + (a 0 * r 0 + a 1 * r 1) := by
    rw [← Finset.sum_sdiff h01, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  rw [hsplit, hr0, mul_one] at hge
  have ha1pos : 0 < a 1 := lt_of_le_of_lt (hcoef 0) hadm
  nlinarith [htail, hge, hadm, mul_le_mul_of_nonneg_left hr1 ha1pos.le]

/- ===================================================================================
   MAGNITUDE LAYER (Layer 2) -- first brick.  The reassessment
   (docs/RH_ZERO_FREE_REASSESSMENT_2026-08-30) located the frontier BEYOND the (Fejer-capped)
   positivity layer in the MAGNITUDE bound |zeta(sigma+it)|.  This is the sigma>1 BASE CASE: the
   elementary Dirichlet-triangle bound  |zeta(s)| <= sum_n (n+1)^{-Re s} = zeta(Re s).  It is NOT
   the frontier -- the zero-free-region improvement needs |zeta| growth INSIDE the critical strip
   (|zeta(sigma+it)| << |t|^{1-sigma}, or << log|t| near sigma=1), which needs Euler-Maclaurin / the
   {x}-integral continuation (the harder next piece, Mathlib-API dependent).  This brick is the honest
   base: |zeta| is finite for sigma>1, and the RHS blows up like 1/(sigma-1) as sigma->1+, which is
   exactly why the strip needs the finer bound.  A different KIND of object from the positivity certs
   (a magnitude bound, not a positivity), opening Layer 2.  conjecture1_proved = False. -/

/-- Norm of a single zeta Dirichlet-series term: `‖1/(n+1)^s‖ = (n+1)^{-Re s}`. -/
theorem norm_one_div_natAddOne_cpow (n : ℕ) (s : ℂ) :
    ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ = ((n : ℝ) + 1) ^ (-s.re) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_one, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos, Real.rpow_neg hpos.le, one_div]

/-- The `σ>1` magnitude base case: `‖ζ(s)‖ ≤ ζ(Re s)` (Dirichlet triangle inequality). -/
theorem norm_riemannZeta_le_re (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s.re) := by
  have hsum : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
      simpa [Real.rpow_neg, one_div] using Real.summable_one_div_nat_rpow.mpr hs
    have h2 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re)) :=
      ((summable_nat_add_iff 1).mpr h1).congr (fun n => by push_cast; ring_nf)
    exact h2.congr (fun n => (norm_one_div_natAddOne_cpow n s).symm)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  exact tsum_congr (fun n => norm_one_div_natAddOne_cpow n s)

/- The STRIP growth bound, reduced to its two analytic inputs.  Research (agentic campaign,
   docs/RH_ZERO_FREE_REASSESSMENT §8) confirmed Mathlib v4.32.0 has NO strip |zeta| bound and NO
   complex fractional-part integral representation, so the crude strip growth bound
       |zeta(sigma+it)| <= ||s||/||s-1|| + ||s||/sigma   (<< |t|, for 0 < sigma < 1)
   must be assembled from two analytic facts still to be formalized (the identified remaining work):
     (R) the representation  zeta(s) = s/(s-1) - s * I  with  I = integral_1^inf {x} x^{-s-1} dx
         (Re s > 0; via Abel summation + the identity theorem -- a genuine Mathlib gap-filler), and
     (B) the integral bound  ||I|| <= 1/Re s  (from |{x}| <= 1 and integral_1^inf x^{-sigma-1} = 1/sigma).
   This theorem does the (high-confidence) ASSEMBLY, taking (R),(B) as hypotheses -- exactly the style
   of `zeta_boundary_contradiction`, which likewise takes its analytic limits as hypotheses.  Crude
   growth only (~|t|), NOT the sharp |t|^{1-sigma} nor the log|t| that feeds the region; and the VK rate
   needs VMVT (absent from Mathlib).  conjecture1_proved = False. -/
theorem zeta_strip_bound_of {s I : ℂ}
    (hrepr : riemannZeta s = s / (s - 1) - s * I) (hI : ‖I‖ ≤ 1 / s.re) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  rw [hrepr]
  calc ‖s / (s - 1) - s * I‖
      ≤ ‖s / (s - 1)‖ + ‖s * I‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖I‖ := by rw [norm_div, norm_mul]
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
        have := mul_le_mul_of_nonneg_left hI (norm_nonneg s); linarith
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by rw [mul_one_div]

/-- Input (B) for `zeta_strip_bound_of`, DISCHARGED: the fractional-part integral is bounded by
    `1/Re s`, from `0 ≤ {x} < 1` and `∫_{x>1} x^{-Re s-1} dx = 1/Re s`.  Combined with `zeta_strip_bound_of`,
    the crude strip bound reduces to input (R) alone (the representation `ζ(s) = s/(s-1) - s·I`). -/
theorem zeta_repr_integral_bound {s : ℂ} (hs : 0 < s.re) :
    ‖∫ x in Set.Ioi (1 : ℝ), (Int.fract x : ℂ) / (x : ℂ) ^ (s + 1)‖ ≤ 1 / s.re := by
  have hbound : ∀ x ∈ Set.Ioi (1 : ℝ),
      ‖(Int.fract x : ℂ) / (x : ℂ) ^ (s + 1)‖ ≤ x ^ (-(s.re + 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_div, Complex.norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        Complex.add_re, Complex.one_re, abs_of_nonneg (Int.fract_nonneg x),
        Real.rpow_neg hx0.le, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_pos_of_pos hx0 _).le)
      (Int.fract_lt_one x).le
  have hdom : IntegrableOn (fun x : ℝ => x ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hf : IntegrableOn (fun x : ℝ => ‖(Int.fract x : ℂ) / (x : ℂ) ^ (s + 1)‖)
      (Set.Ioi (1 : ℝ)) := by
    refine Integrable.mono' hdom ?_ (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
    exact (Complex.continuous_ofReal.comp continuous_id).aestronglyMeasurable.norm.div
      (by fun_prop) |>.restrict
  have hval : ∫ x in Set.Ioi (1 : ℝ), x ^ (-(s.re + 1)) = 1 / s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) one_pos, Real.one_rpow]
    rw [show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]
  calc ‖∫ x in Set.Ioi (1 : ℝ), (Int.fract x : ℂ) / (x : ℂ) ^ (s + 1)‖
      ≤ ∫ x in Set.Ioi (1 : ℝ), ‖(Int.fract x : ℂ) / (x : ℂ) ^ (s + 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioi (1 : ℝ), x ^ (-(s.re + 1)) :=
        setIntegral_mono_on hf hdom measurableSet_Ioi hbound
    _ = 1 / s.re := hval

end ZeroFreeBridge
