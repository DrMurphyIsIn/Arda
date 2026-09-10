/-
RvMDigammaComplete — Phase 2 brick 4 (part 4, FINAL): the digamma series for `Complex.digamma`.

Completes b4.  `logDeriv_tprod_wFactor` gave the digamma series via the Weierstrass product's
log-derivative; this identifies it with the named `Complex.digamma`.

The bridge: the entire function `G z = z·e^{γz}·∏'_n wFactor n z` equals `(Γ z)⁻¹` on the pole
complement (b3), and both are continuous with the pole complement dense (countable complement), so
`G = (Γ ·)⁻¹` EVERYWHERE (`Continuous.ext_on`).  Hence `logDeriv G s = logDeriv (Γ ·)⁻¹ s =
−digamma s`, while the product rule gives `logDeriv G s = 1/s + γ + ∑'(1/(s+n+1) − 1/(n+1))`.

  * `digamma_series` — `digamma s = −1/s − γ − ∑'_n (1/(s+(n+1)) − 1/(n+1))`  (poles excluded).

This is the first digamma series representation in the corpus (Mathlib has none).
conjecture1_proved = False.
-/
import Mathlib
import RvMDigammaTprod

open Complex Filter Topology

namespace RvMWeierstrass

set_option maxHeartbeats 2000000 in
/-- **The digamma series** (b4 complete).  For `s` off the non-positive integers,
    `digamma s = −1/s − γ − ∑'_n (1/(s+(n+1)) − 1/(n+1))`. -/
theorem digamma_series {s : ℂ} (hs : ∀ j : ℕ, s + (j : ℂ) ≠ 0) :
    Complex.digamma s = -(1 / s) - (Real.eulerMascheroniConstant : ℂ)
      - ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
  set γr : ℝ := Real.eulerMascheroniConstant with hγr
  have hsm : ∀ m : ℕ, s ≠ -(m : ℂ) := fun m h => hs m (by rw [h]; ring)
  have hsne : s ≠ 0 := by have := hs 0; simpa using this
  have hgne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsm
  -- the product function: continuity + differentiability from b2's local-uniform convergence
  have hlu := hasProdLocallyUniformlyOn_wFactor.tendstoLocallyUniformlyOn_finsetRange
  have hpartcont : ∀ N : ℕ, ContinuousOn (fun z : ℂ => ∏ n ∈ Finset.range N, wFactor n z)
      (Set.univ : Set ℂ) := by
    intro N; apply Continuous.continuousOn; unfold wFactor; fun_prop
  have hPcont : Continuous (fun z : ℂ => ∏' n : ℕ, wFactor n z) := by
    rw [← continuousOn_univ]
    exact hlu.continuousOn ((Filter.Eventually.of_forall hpartcont).frequently)
  have hPdiff : Differentiable ℂ (fun z : ℂ => ∏' n : ℕ, wFactor n z) := by
    rw [← differentiableOn_univ]
    refine hlu.differentiableOn (Filter.Eventually.of_forall (fun N => ?_)) isOpen_univ
    apply Differentiable.differentiableOn; unfold wFactor; fun_prop
  -- G z = z·e^{γz}·∏' wFactor n z equals (Γ z)⁻¹ EVERYWHERE (continuity + dense agreement)
  have hGcont : Continuous (fun z : ℂ => z * Complex.exp ((γr : ℂ) * z)
      * ∏' n : ℕ, wFactor n z) :=
    (continuous_id.mul (by fun_prop)).mul hPcont
  have hInvCont : Continuous (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  have hdense : Dense (Set.range (fun n : ℕ => -(n : ℂ)))ᶜ :=
    (Set.countable_range _).dense_compl ℂ
  have hGeq : (fun z : ℂ => z * Complex.exp ((γr : ℂ) * z) * ∏' n : ℕ, wFactor n z)
      = (fun z : ℂ => (Complex.Gamma z)⁻¹) := by
    refine Continuous.ext_on hdense hGcont hInvCont (fun z hz => ?_)
    have hsz : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := fun j hj => hz ⟨j, by linear_combination -hj⟩
    exact weierstrass_prod_eq_inv_Gamma hsz
  -- logDeriv of the reciprocal-Γ side = −digamma
  have hrecip : logDeriv (fun z : ℂ => (Complex.Gamma z)⁻¹) s = -Complex.digamma s := by
    have hgd : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s hsm
    have hcomp : (fun z : ℂ => (Complex.Gamma z)⁻¹) = (fun w : ℂ => w⁻¹) ∘ Complex.Gamma := rfl
    rw [hcomp, logDeriv_comp (differentiableAt_inv hgne) hgd, logDeriv_inv, Complex.digamma_def,
      logDeriv_apply]
    field_simp
  -- logDeriv of the exponential factor
  have hexpderiv : HasDerivAt (fun z : ℂ => Complex.exp ((γr : ℂ) * z))
      (Complex.exp ((γr : ℂ) * s) * (γr : ℂ)) s := by
    have h1 : HasDerivAt (fun z : ℂ => (γr : ℂ) * z) (γr : ℂ) s := by
      simpa using (hasDerivAt_id s).const_mul (γr : ℂ)
    simpa using h1.cexp
  have hexplog : logDeriv (fun z : ℂ => Complex.exp ((γr : ℂ) * z)) s = (γr : ℂ) := by
    rw [logDeriv_apply, hexpderiv.deriv, mul_comm]
    exact mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)
  -- product rule on G
  have hlin : logDeriv (fun z : ℂ => z * Complex.exp ((γr : ℂ) * z)) s = 1 / s + (γr : ℂ) := by
    rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z => Complex.exp ((γr : ℂ) * z)) s hsne
        (Complex.exp_ne_zero _) (by fun_prop) hexpderiv.differentiableAt, logDeriv_id', hexplog]
  have hPne : (∏' n : ℕ, wFactor n s) ≠ 0 := by
    intro hzero
    have hb3 := weierstrass_prod_eq_inv_Gamma hs
    rw [hzero, mul_zero] at hb3
    exact (inv_ne_zero hgne) hb3.symm
  have hGlog : logDeriv (fun z : ℂ => z * Complex.exp ((γr : ℂ) * z) * ∏' n : ℕ, wFactor n z) s
      = (1 / s + (γr : ℂ)) + ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
    rw [logDeriv_mul (f := fun z : ℂ => z * Complex.exp ((γr : ℂ) * z))
        (g := fun z => ∏' n : ℕ, wFactor n z) s (mul_ne_zero hsne (Complex.exp_ne_zero _)) hPne
        (by fun_prop) (hPdiff s), hlin, logDeriv_tprod_wFactor hs]
  -- combine: −digamma s = logDeriv G s = (1/s + γ) + series
  have hmain : -Complex.digamma s
      = (1 / s + (γr : ℂ)) + ∑' n : ℕ, (1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1)) := by
    rw [← hGlog, hGeq, hrecip]
  linear_combination -hmain

end RvMWeierstrass
