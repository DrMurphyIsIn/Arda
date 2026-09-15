/-  ZeroSignDecomp_t14.lean -- ANDÚRIL G2-FULL: the phase-decomposition sign bridge that removes
    the Γℝ-VALUE (magnitude) blocker permanently, and the conditional first-zero theorem it enables.

    ## THE BLOCKER THIS FILE DISSOLVES.

    Every prior G2 rung (`CheckBand`, `FullyReflectedBand_t14`) carried the on-line `gLine` sign as a
    `memR`-membership HYPOTHESIS `gLine tᵢ ∈ boxᵢ` -- a VALUE enclosure.  Closing that in-kernel needs
    the Γℝ VALUE `Γℝ(1/2+it) = π^{-1/4-it/2}·Γ(1/4+it/2)`, whose MAGNITUDE `|Γℝ|` has no kernel
    enclosure anywhere in the corpus (repeatedly flagged: `FullyReflectedBand_t14` header gap (B),
    `ZeroHypBand_t14` header gap (B), `CheckBand` "the single precisely identified blocker").  A `gLine`
    VALUE box is therefore genuinely out of reach.

    But the IVT (`SignChain.exists_zero_of_sign_change`, `XiLineZeros`) consumes only the SIGN of
    `gLine`, never its value.  And the sign does NOT need the magnitude:

        gLine t = Re Λ(1/2+it) = Re(Γℝ(1/2+it)·ζ(1/2+it)),   Λ = Γℝ·ζ  (Mathlib
                  `riemannZeta_def_of_ne_zero`),
        Γℝ(1/2+it) = M·exp(iφ),  M = π^{-1/4}·‖Γ(1/4+it/2)‖ > 0,  φ = Λ_θ − (t/2)·log π,

    where `Λ_θ` is the branch-correct argument of `Γ(1/4+it/2)` DELIVERED, hypothesis-free, by the
    discharged `ThetaConverge.convergence_obligation` (`Γ = ‖Γ‖·exp(I·Λ_θ)`).  Since `M > 0`:

        gLine t = M·( cos φ · Re ζ(1/2+it)  −  sin φ · Im ζ(1/2+it) ),           (★)

    so `sign(gLine t) = sign( cos φ · Re ζ − sin φ · Im ζ )` -- the magnitude `M` cancels out of the
    sign.  `φ` is exactly the `ThetaConverge.theta_14_box` quantity (`−(t/2)log π + Λ_θ` = the
    Riemann–Siegel θ).  Numerically (driver): φ(14) ≈ −1.78295, and the sign quantity is `−0.1056` at
    `t=14`, `+0.7199` at `t=15` -- comfortable, kernel-boxable margins straddling a zero (γ₁ ≈ 14.1347).

    ## WHAT IS PROVED HERE (all axiom-clean: {propext, Classical.choice, Quot.sound}).

      * `gamma_r_polar_t` : the polar form `Γℝ(1/2+it) = M·exp(iφ)`, `M > 0`, `φ = Λ − (t/2)log π`,
        from the ThetaConverge branch identity and the `π^{-s/2}` cpow split.  GENERAL in `t ≠ 0`.
      * `gLine_sign_decomp_t` : identity (★), GENERAL in `t ≠ 0`, with `Λ` supplied INTERNALLY by
        `convergence_obligation` (no branch hypothesis leaks out) -- the crown lemma.
      * `exists_zero_of_sign_change` : the IVT single-pair bridge (inlined from `SignChain`, needing
        only `XiLineZeros`, so this file does not pull in the unbuilt `TuringBand` dependency).
      * `first_zero_of_sign_quantities` : **THE CONDITIONAL FIRST-ZERO THEOREM.**  Given the two
        sign-quantity facts (`cos φ₁₄·Re ζ₁₄ − sin φ₁₄·Im ζ₁₄ < 0` and the `> 0` analogue at `t=15`,
        with `φ` the θ-limits this file exposes), there is a zero of `completedRiemannZeta` in
        `(14, 15)`.  The Γℝ-magnitude blocker is GONE; the ONLY residual is the two sign quantities.

    ## THE PRECISE RESIDUAL (what still separates this from an argument-free `first_zero_kernel`).

    The hypotheses of `first_zero_of_sign_quantities` are exactly the kernel signs of
    `cos φ·Re ζ − sin φ·Im ζ` at `t ∈ {14, 15}`.  Discharging them in-kernel is PURE EMITTER
    THROUGHPUT, no further mathematics:
      (i)  `cos φ`, `sin φ` boxes -- from a tightened `ThetaConverge.theta_14_box` (the driver's
           honest-`k`≤30 + rational-harmonic-tail + cubic-bracket recipe, width ≈ 9.4e-4 < 2e-3);
           mechanical `ArctanTaylor.arctan_bracket` iteration, orthogonal to the analytic content.
      (ii) `Re ζ`, `Im ζ` boxes -- from the EM finite part `EMZetaTail.emZetaFinite3` (tail
           `em_zeta_critical_line3_number ≤ 1/1000`, PROVED) reduced via `EMZetaComplex.em_cpow_partial`
           + `integral_cpow` to the elementary Dirichlet sum `Σ_{n=1}^{199} n^{-s}` (each term boxed by
           `ZeroHypBand_t14.term_re`/`term_im` + a `TrigReduceOperating`-style `cos/sin(t·log n)` climb).
           The trig climb per term is the ~700-Int-op cost; ~199 terms × 2 grid points is the mission's
           ~2·10⁶-Int-op budget, and needs ~390 emitted operating-point certs (only 4 exist today:
           `cos/sin_14log2`, `cos/sin_14log200`).  A driver, not a theorem.

    conjecture1_proved = False.  The magnitude-free sign bridge + a conditional IVT zero theorem, NOT a
    proof of RH and NOT (yet) an argument-free zero-existence theorem.
-/
import ThetaConverge
import XiLineZeros
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

open Complex Real XiLineZeros ThetaGap

namespace ZeroSignDecomp

/-! ## 1.  The polar form of the Γℝ factor: `Γℝ(1/2+it) = M·exp(iφ)`, `M > 0`. -/

/-- **Γℝ polar form.**  For `t ≠ 0`, given the ThetaConverge branch identity
    `Γ(1/4+it/2) = ‖·‖·exp(I·Λ)`, the real archimedean factor is `Γℝ(1/2+it) = M·exp(i(Λ − (t/2)log π))`
    with `M = π^{-1/4}·‖Γ(1/4+it/2)‖ > 0`.  Proof: `Γℝ s = π^{-s/2}·Γ(s/2)`, `s/2 = 1/4+it/2`, and the
    `π^{-s/2}` cpow splits as `π^{-1/4}·exp(−i(t/2)log π)` (`Complex.cpow_def_of_ne_zero` + real log). -/
theorem gamma_r_polar_t (t : ℝ) (ht : t ≠ 0) (Λ : ℝ)
    (hbranch : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)
        = (‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ : ℂ) * Complex.exp (Complex.I * (Λ:ℂ))) :
    ∃ M : ℝ, 0 < M ∧
      Gammaℝ ((1/2:ℂ) + (t:ℂ)*I)
        = (M:ℂ) * Complex.exp (Complex.I * ((Λ - (t/2) * Real.log Real.pi : ℝ):ℂ)) := by
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  set NG : ℝ := ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ with hNG
  have hGne : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    exact ht (by linarith [him])
  have hnormpos : 0 < NG := by rw [hNG]; positivity
  refine ⟨Real.pi ^ (-(1/4):ℝ) * NG, by positivity, ?_⟩
  have hhalf : ((1/2:ℂ) + (t:ℂ)*I)/2 = ((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I := by push_cast; ring
  have hpi : (Real.pi : ℂ) ^ (-((1/2:ℂ) + (t:ℂ)*I)/2)
      = ((Real.pi ^ (-(1/4):ℝ) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((- (t/2) * Real.log Real.pi : ℝ):ℂ)) := by
    have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      rw [Complex.ofReal_log hpipos.le]
    have hne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.cpow_def_of_ne_zero hne, hlog,
      show (Real.log Real.pi : ℂ) * (-((1/2:ℂ) + (t:ℂ)*I)/2)
          = (((-(1/4):ℝ) * Real.log Real.pi : ℝ):ℂ)
            + Complex.I * ((-(t/2) * Real.log Real.pi : ℝ):ℂ) by push_cast; ring,
      Complex.exp_add]
    congr 1
    rw [Real.rpow_def_of_pos hpipos, Complex.ofReal_exp, mul_comm]
  rw [Gammaℝ_def, hhalf, hbranch, hpi,
    show Complex.exp (Complex.I * ((Λ - (t/2) * Real.log Real.pi : ℝ):ℂ))
        = Complex.exp (Complex.I * ((- (t/2) * Real.log Real.pi : ℝ):ℂ))
          * Complex.exp (Complex.I * (Λ:ℂ)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
  push_cast; ring

/-! ## 2.  The crown lemma: the magnitude-free `gLine` sign decomposition. -/

/-- **`gLine` sign decomposition (★).**  For `t ≠ 0`, there is a real θ-limit `Λ` (the argument of
    `Γ(1/4+it/2)` delivered by the discharged `convergence_obligation`) and a strictly positive
    magnitude `M` with

        gLine t = M · ( cos(Λ − (t/2)log π) · Re ζ(1/2+it)  −  sin(Λ − (t/2)log π) · Im ζ(1/2+it) ).

    The magnitude `M = π^{-1/4}‖Γ(1/4+it/2)‖` is NOT evaluated -- it only needs to be positive, which
    is why this route sidesteps the missing Γℝ-VALUE enclosure.  `Λ` is exposed (as a `Tendsto` fact)
    so a tightened `theta_14_box` can pin `cos φ` / `sin φ`.  NO branch hypothesis; NO magnitude box. -/
theorem gLine_sign_decomp_t (t : ℝ) (ht : t ≠ 0) :
    ∃ (Λ M : ℝ), 0 < M ∧
      Filter.Tendsto (imLnVal (1/4) (t/2)) Filter.atTop (nhds Λ) ∧
      gLine t = M * (Real.cos (Λ - (t/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(t:ℂ)*I)).re
                     - Real.sin (Λ - (t/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(t:ℂ)*I)).im) := by
  have hGne : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    exact ht (by linarith [him])
  obtain ⟨Λ, hΛtend, hbranch⟩ :=
    ThetaConverge.convergence_obligation (1/4) (t/2) (by norm_num) hGne
  obtain ⟨M, hM, hG⟩ := gamma_r_polar_t t ht Λ hbranch
  refine ⟨Λ, M, hM, hΛtend, ?_⟩
  set φ : ℝ := Λ - (t/2) * Real.log Real.pi with hφ
  set Z : ℂ := riemannZeta ((1/2:ℂ)+(t:ℂ)*I) with hZ
  have hs0 : ((1/2 : ℂ) + (t:ℂ)*I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hGRne : Gammaℝ ((1/2:ℂ) + (t:ℂ)*I) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos; simp [Complex.add_re, Complex.mul_re]
  have hcomp : completedRiemannZeta ((1/2:ℂ)+(t:ℂ)*I) = Gammaℝ ((1/2:ℂ)+(t:ℂ)*I) * Z := by
    rw [hZ, riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hGRne]
  have hgl : gLine t = (completedRiemannZeta ((1/2:ℂ)+(t:ℂ)*I)).re := rfl
  rw [hgl, hcomp, hG,
    show Complex.exp (Complex.I * (φ:ℂ)) = Complex.exp ((φ:ℂ) * Complex.I) by rw [mul_comm],
    Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-! ## 3.  The IVT single-pair bridge (inlined from `SignChain`, `XiLineZeros`-only). -/

/-- **One interior on-line zero from a `gLine` sign change.**  If `gLine a` and `gLine b` have opposite
    signs on `a < b`, the IVT on the continuous `gLine` gives a zero of `completedRiemannZeta` on the
    line strictly inside `(a, b)`.  Verbatim `SignChain.exists_zero_of_sign_change`, re-proved here so
    this file imports only `XiLineZeros` (not the unbuilt-in-this-island `TuringBand`). -/
theorem exists_zero_of_sign_change {a b : ℝ} (hab : a < b)
    (hsign : gLine a * gLine b < 0) :
    ∃ r : ℝ, a < r ∧ r < b ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
  have hcont : ContinuousOn gLine (Set.Icc a b) := gLine_continuous.continuousOn
  rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
  · have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc' (le_of_lt hab) hcont ⟨le_of_lt hnb, le_of_lt hpa⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpa)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hnb)
    refine ⟨r, hlo, hhi, ?_⟩
    rw [lambda_eq_gLine, hz]; simp
  · have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc (le_of_lt hab) hcont ⟨le_of_lt hna, le_of_lt hpb⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hna)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpb)
    refine ⟨r, hlo, hhi, ?_⟩
    rw [lambda_eq_gLine, hz]; simp

/-! ## 4.  THE CONDITIONAL FIRST-ZERO THEOREM (magnitude blocker gone). -/

/-- **First on-line zero in `(14, 15)` from the two sign quantities.**

    The hypotheses are the SIGN of the magnitude-free quantity `cos φ · Re ζ − sin φ · Im ζ` at the
    two grid heights, where `φ₁₄`, `φ₁₅` are the θ-limits `Λ − (t/2)log π` this file exposes:
      * at `t = 14`:  `cos φ₁₄ · Re ζ(1/2+14i) − sin φ₁₄ · Im ζ(1/2+14i) < 0`   (driver: −0.1056)
      * at `t = 15`:  `cos φ₁₅ · Re ζ(1/2+15i) − sin φ₁₅ · Im ζ(1/2+15i) > 0`   (driver: +0.7199)

    Then there is `r ∈ (14, 15)` with `completedRiemannZeta (1/2 + r·I) = 0` -- the first nontrivial
    zero (γ₁ ≈ 14.1347).  The proof turns each sign quantity into `sign(gLine)` via the magnitude-free
    decomposition (★) (`M > 0` cancels), then applies the IVT.  This is the exact G2-full theorem
    MODULO discharging the two sign quantities by the ζ/θ emitter (see file header residual). -/
theorem first_zero_of_sign_quantities
    (Λ14 : ℝ) (hΛ14 : Filter.Tendsto (imLnVal (1/4) (14/2)) Filter.atTop (nhds Λ14))
    (Λ15 : ℝ) (hΛ15 : Filter.Tendsto (imLnVal (1/4) (15/2)) Filter.atTop (nhds Λ15))
    (hsign14 : Real.cos (Λ14 - (14/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(14:ℝ)*I)).re
                 - Real.sin (Λ14 - (14/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(14:ℝ)*I)).im < 0)
    (hsign15 : 0 < Real.cos (Λ15 - (15/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(15:ℝ)*I)).re
                     - Real.sin (Λ15 - (15/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(15:ℝ)*I)).im) :
    ∃ r : ℝ, 14 < r ∧ r < 15 ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
  -- gLine 14 < 0 from the negative sign quantity (M > 0).
  obtain ⟨Λ14', M14, hM14, hΛ14', hdec14⟩ := gLine_sign_decomp_t 14 (by norm_num)
  have hΛeq14 : Λ14' = Λ14 := tendsto_nhds_unique hΛ14' (by simpa using hΛ14)
  subst hΛeq14
  have hneg14 : gLine 14 < 0 := by
    rw [hdec14]
    exact mul_neg_of_pos_of_neg hM14 (by simpa using hsign14)
  -- gLine 15 > 0 from the positive sign quantity (M > 0).
  obtain ⟨Λ15', M15, hM15, hΛ15', hdec15⟩ := gLine_sign_decomp_t 15 (by norm_num)
  have hΛeq15 : Λ15' = Λ15 := tendsto_nhds_unique hΛ15' (by simpa using hΛ15)
  subst hΛeq15
  have hpos15 : 0 < gLine 15 := by
    rw [hdec15]
    exact mul_pos hM15 (by simpa using hsign15)
  -- sign change ⇒ IVT zero in (14, 15).
  have hsc : gLine 14 * gLine 15 < 0 := mul_neg_of_neg_of_pos hneg14 hpos15
  exact exists_zero_of_sign_change (by norm_num) hsc

end ZeroSignDecomp
