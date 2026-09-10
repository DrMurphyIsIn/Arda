/-
RvMDigammaProd — Phase 2 brick 3 (the crux): the Weierstrass product equals 1/Γ.

Building on the convergence (RvMWeierstrass), this pins the constant `e^{γs}` by relating the partial
product to Mathlib's `GammaSeq` (the Gauss/Euler limit for Γ) and the Euler–Mascheroni limit
`harmonic n - log n → γ`.  This is the step that identifies the abstract product with `1/Γ`.

This file (b3 sub-brick 1): the CORE finite product identity
  `s · ∏_{n<N} (1 + s/(n+1)) = (∏_{j<N+1} (s+j)) / N!`
— pure finite algebra, the combinatorial heart of the GammaSeq relation.

conjecture1_proved = False.
-/
import Mathlib
import RvMWeierstrass

open Complex

namespace RvMWeierstrass

/-- **Core finite product identity.**  `s · ∏_{n<N} (1 + s/(n+1)) = (∏_{j<N+1} (s+j)) / N!`.
    Pure finite algebra: each factor `1+s/(n+1) = (s+n+1)/(n+1)`, the denominators multiply to `N!`,
    and peeling the `j=0` factor of `∏_{j<N+1}(s+j)` yields the `s·` prefactor. -/
theorem core_prod_identity (s : ℂ) (N : ℕ) :
    s * (∏ n ∈ Finset.range N, (1 + s / ((n : ℂ) + 1)))
      = (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / ((Nat.factorial N : ℕ) : ℂ) := by
  -- rewrite each factor `1 + s/(n+1) = (s + (n+1))/(n+1)`
  have hfactor : (∏ n ∈ Finset.range N, (1 + s / ((n : ℂ) + 1)))
      = (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1)))
          / (∏ n ∈ Finset.range N, ((n : ℂ) + 1)) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun n _ => ?_)
    have h := natCast_add_one_ne_zero n
    field_simp
    ring
  -- the denominator product is N!
  have hfact : (∏ n ∈ Finset.range N, ((n : ℂ) + 1)) = ((Nat.factorial N : ℕ) : ℂ) := by
    calc (∏ n ∈ Finset.range N, ((n : ℂ) + 1))
        = ∏ n ∈ Finset.range N, (((n + 1 : ℕ)) : ℂ) := by
          refine Finset.prod_congr rfl (fun n _ => ?_); push_cast; ring
      _ = (((∏ n ∈ Finset.range N, (n + 1)) : ℕ) : ℂ) := by rw [Nat.cast_prod]
      _ = ((Nat.factorial N : ℕ) : ℂ) := by rw [Finset.prod_range_add_one_eq_factorial]
  -- peel the j=0 factor of ∏_{j<N+1}(s+j)
  have hpeel : (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ)))
      = (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1))) * s := by
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [hfactor, hfact, hpeel]
  ring

/-- The complex cast of the harmonic number as a `Finset` sum of reciprocals:
    `(harmonic N : ℂ) = ∑_{n<N} 1/(n+1)`. -/
theorem harmonic_cast (N : ℕ) :
    ((harmonic N : ℚ) : ℂ) = ∑ n ∈ Finset.range N, ((n : ℂ) + 1)⁻¹ := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  push_cast; ring

/-- The exponential factors of the Weierstrass product telescope to a single exponential of the
    harmonic number: `∏_{n<N} exp(-(s/(n+1))) = exp(-(s·harmonic N))`. -/
theorem exp_factor_prod (s : ℂ) (N : ℕ) :
    (∏ n ∈ Finset.range N, Complex.exp (-(s / ((n : ℂ) + 1))))
      = Complex.exp (-(s * ((harmonic N : ℚ) : ℂ))) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [harmonic_cast, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [div_eq_mul_inv]

/-- **The partial Weierstrass product, closed form.**  Combining the core product identity with the
    exponential telescoping:
      `s · ∏_{n<N} wFactor n s = (∏_{j<N+1}(s+j))/N! · exp(-(s·harmonic N))`. -/
theorem partial_wFactor_prod (s : ℂ) (N : ℕ) :
    s * (∏ n ∈ Finset.range N, wFactor n s)
      = (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / ((Nat.factorial N : ℕ) : ℂ)
          * Complex.exp (-(s * ((harmonic N : ℚ) : ℂ))) := by
  have hsplit : (∏ n ∈ Finset.range N, wFactor n s)
      = (∏ n ∈ Finset.range N, (1 + s / ((n : ℂ) + 1)))
          * (∏ n ∈ Finset.range N, Complex.exp (-(s / ((n : ℂ) + 1)))) := by
    simp only [wFactor, Finset.prod_mul_distrib]
  rw [hsplit, ← mul_assoc, core_prod_identity, exp_factor_prod]

open Filter Topology in
/-- **The Weierstrass product equals `1/Γ` (the crux of b3).**  With the poles excluded
    (`hs : ∀ j, s + j ≠ 0`),
      `s · e^{γ·s} · ∏'_{n} (1 + s/(n+1)) e^{-s/(n+1)} = (Γ s)⁻¹`,
    the Euler–Mascheroni constant `γ` pinned by `GammaSeq_tendsto_Gamma` +
    `tendsto_harmonic_sub_log`.  The partial products equal
    `e^{s·(γ + log N − H_N)} / GammaSeq s N`, whose limit is `1/Γ s`. -/
theorem weierstrass_prod_eq_inv_Gamma {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    s * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s) * (∏' n : ℕ, wFactor n s)
      = (Complex.Gamma s)⁻¹ := by
  set γr : ℝ := Real.eulerMascheroniConstant with hγr
  -- Γ s ≠ 0 (poles excluded)
  have hsm : ∀ m : ℕ, s ≠ -(m : ℂ) := fun m h => hs m (by rw [h]; ring)
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsm
  -- the real "gamma defect" sequence  c N = γ + log N − H_N → 0
  set c : ℕ → ℝ := fun N => γr + Real.log N - (harmonic N : ℝ) with hc
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := γr)).sub Real.tendsto_harmonic_sub_log
    simp only [hγr, sub_self] at h
    refine h.congr (fun N => ?_)
    simp only [hc, hγr]; push_cast; ring
  -- the closed-form partial products
  have claimA : ∀ N : ℕ, 1 ≤ N →
      s * Complex.exp ((γr : ℂ) * s) * (∏ n ∈ Finset.range N, wFactor n s)
        = Complex.exp (s * ((c N : ℝ) : ℂ)) / Complex.GammaSeq s N := by
    intro N hN
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hprodne : (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hs j)
    have hfactne : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero N
    have hNps : (N : ℂ) ^ s ≠ 0 := fun hcon => hNne ((Complex.cpow_eq_zero_iff _ _).mp hcon).1
    -- ∏(s+j)/N!  =  N^s / GammaSeq s N
    have hgseq : (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / ((Nat.factorial N : ℕ) : ℂ)
        = (N : ℂ) ^ s / Complex.GammaSeq s N := by
      rw [Complex.GammaSeq]; field_simp
    -- N^s = exp(log N · s)
    have hNpow : (N : ℂ) ^ s = Complex.exp (((Real.log N : ℝ) : ℂ) * s) := by
      have hcast : (N : ℂ) = ((N : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.cpow_def_of_ne_zero (by exact_mod_cast hNne),
        ← Complex.ofReal_log (by positivity)]
    -- harmonic cast ℚ→ℂ factors through ℝ
    have hharm : ((harmonic N : ℚ) : ℂ) = (((harmonic N : ℝ)) : ℂ) :=
      (Complex.ofReal_ratCast _).symm
    -- merge the three exponentials
    have hexp3 : Complex.exp ((γr : ℂ) * s) * Complex.exp (((Real.log N : ℝ) : ℂ) * s)
          * Complex.exp (-(s * (((harmonic N : ℝ)) : ℂ)))
        = Complex.exp (s * ((c N : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [hc]; push_cast; ring
    calc s * Complex.exp ((γr : ℂ) * s) * (∏ n ∈ Finset.range N, wFactor n s)
        = Complex.exp ((γr : ℂ) * s) * (s * (∏ n ∈ Finset.range N, wFactor n s)) := by ring
      _ = Complex.exp ((γr : ℂ) * s)
            * ((∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / ((Nat.factorial N : ℕ) : ℂ)
                * Complex.exp (-(s * ((harmonic N : ℚ) : ℂ)))) := by
            rw [partial_wFactor_prod]
      _ = Complex.exp ((γr : ℂ) * s)
            * ((N : ℂ) ^ s / Complex.GammaSeq s N
                * Complex.exp (-(s * (((harmonic N : ℝ)) : ℂ)))) := by
            rw [hgseq, hharm]
      _ = Complex.exp ((γr : ℂ) * s) * Complex.exp (((Real.log N : ℝ) : ℂ) * s)
            * Complex.exp (-(s * (((harmonic N : ℝ)) : ℂ))) / Complex.GammaSeq s N := by
            rw [hNpow]; ring
      _ = Complex.exp (s * ((c N : ℝ) : ℂ)) / Complex.GammaSeq s N := by rw [hexp3]
  -- the GammaSeq-side limit  →  1/Γ s
  have hnum : Tendsto (fun N : ℕ => Complex.exp (s * ((c N : ℝ) : ℂ))) atTop (𝓝 1) := by
    have hcC : Tendsto (fun N : ℕ => ((c N : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hc0
    have : Tendsto (fun N : ℕ => s * ((c N : ℝ) : ℂ)) atTop (𝓝 (s * 0)) := hcC.const_mul s
    simpa [Function.comp_def] using (Complex.continuous_exp.tendsto _).comp this
  have hden : Tendsto (fun N : ℕ => Complex.GammaSeq s N) atTop (𝓝 (Complex.Gamma s)) :=
    Complex.GammaSeq_tendsto_Gamma s
  have hR : Tendsto (fun N : ℕ => Complex.exp (s * ((c N : ℝ) : ℂ)) / Complex.GammaSeq s N)
      atTop (𝓝 ((Complex.Gamma s)⁻¹)) := by
    have h : Tendsto (fun N : ℕ => Complex.exp (s * ((c N : ℝ) : ℂ)) / Complex.GammaSeq s N)
        atTop (𝓝 (1 / Complex.Gamma s)) := hnum.div hden hΓ
    rwa [one_div] at h
  -- the tprod-side limit
  have hL : Tendsto (fun N : ℕ => s * Complex.exp ((γr : ℂ) * s)
      * (∏ n ∈ Finset.range N, wFactor n s)) atTop
      (𝓝 (s * Complex.exp ((γr : ℂ) * s) * (∏' n : ℕ, wFactor n s))) := by
    have htprod : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, wFactor n s) atTop
        (𝓝 (∏' n : ℕ, wFactor n s)) :=
      (hasProdLocallyUniformlyOn_wFactor.tendstoLocallyUniformlyOn_finsetRange).tendsto_at
        (Set.mem_univ s)
    exact htprod.const_mul _
  -- transport hR along claimA to the same function as hL, then uniqueness
  have hR' : Tendsto (fun N : ℕ => s * Complex.exp ((γr : ℂ) * s)
      * (∏ n ∈ Finset.range N, wFactor n s)) atTop (𝓝 ((Complex.Gamma s)⁻¹)) := by
    refine hR.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (claimA N hN).symm
  exact tendsto_nhds_unique hL hR'

end RvMWeierstrass
