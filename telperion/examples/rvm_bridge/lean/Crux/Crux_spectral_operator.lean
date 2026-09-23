/-
  Crux_spectral_operator.lean (rvm_bridge island) -- the zeta instance of the Weil-Pontryagin
  window realization: the sesquilinear Weil form of Mathlib's riemannZeta, its zero-side
  representation, its translation invariance, and the bound "Pontryagin index <= number of
  off-line zero pairs", all on the unconditional explicit formula of E6Bridge4.

  conjecture1_proved = False.  Nothing here moves RH.  `rh_iff_weil_negIndex_zero` is Weil's
  criterion restated as "kappa = 0" -- a relabeling, labelled as such.  The index bound
  `weil_negIndex_le_offline` is vacuous if there are infinitely many off-line zeros, and under RH
  it only says kappa = 0.  The Davenport-Heilbronn function D satisfies the same explicit-formula
  structure (functional equation, no Euler product); every statement below has a D analogue, and
  D's off-line zeros make its index positive (negative control: see the research README).

  Checked by: cd telperion/examples/rvm_bridge/lean && lake env lean Crux/Crux_spectral_operator.lean
  (Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 @ fbdc36bb).  No `sorry`, no `native_decide`, no
  `opaque`, no new `axiom`.  The `#print axioms` block at the end reports only propext,
  Classical.choice, Quot.sound.

  CONSUMED (all unconditional on this island): RvMBridge4.limit_explicit_formula,
  RvMBridge4.weilKernel_eq_paperFT_gammaOf, RvMBridge4.zeroMult_eq_zero_of_not_nontrivial,
  RvMBridge5.autocorr_eq_weilTest, RvMBridge9.weil_positivity_implies_rh,
  Zeta23.EF.paperFT_weilTest, Zeta23.paperFT_deriv, Zeta23.RH_implies_on_line.

  WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
  * `weilSesq f g := weilForm (f ⋆ g~)` and its zero side (`weilSesq_hasSum`):
        B(f, g) = Σ_ρ m(ρ) f^(γ_ρ) conj g^(conj γ_ρ),   γ_ρ = (ρ - 1/2)/i,
    for all smooth compactly supported f, g.  On-line zeros give |f^(γ)|² terms, an off-line
    pair {ρ, 1 - conj ρ} gives a hyperbolic term (γ_{1 - conj ρ} = conj γ_ρ, `gammaOf_one_sub_conj`).
  * `weilSesq_deriv_symm`: B(f', g) + B(f, g') = 0, i.e. multiplication by z is B-symmetric.  This
    is the translation-invariance hypothesis of the Pontryagin-Caratheodory-Fejer theorem proved
    abstractly on the li_positivity island (file of the same name).
  * `weil_negIndex_le_offline`: if S contains one member of every off-line pair {ρ, 1 - conj ρ} of
    nontrivial zeros, every family of Weil tests spanning a Weil-negative-definite subspace has at
    most |S| members.  Windows: `KappaWindowLE`, `kappaWindow_mono`, `kappaWindow_le_offline`
    (kappa(x) is nondecreasing and bounded by the number of off-line pairs, for every window).
  * `weilForm_autocorr_smul` (scaling) and `rh_iff_weil_negIndex_zero` (relabeling of Weil).
  * Linearity of the transform on finite combinations (`paperFT_sum`, `paperFT_smul`) and closure
    of the test class (`isWeilTest_sum`, `isWeilTest_weilTest`, `isWeilTest_deriv`).

  DOES NOT ESTABLISH: kappa_zeta = 0 (that is RH); any lower bound kappa(x) >= #resolved pairs for
  finite windows (the detection theorem is THEOREM-paper-proof in the research README, its
  algebra is kernel-checked on li_positivity); the eigenvector theory of the window operator
  (eigenvectors are in L²(window), not in the smooth test class used here), hence the application
  of the abstract Pontryagin-Caratheodory-Fejer theorem to zeta is paper glue; the Locator.
-/
import E6Bridge9

open Zeta23 Complex MeasureTheory WeilExplicit
open scoped ComplexConjugate

noncomputable section

namespace CruxSpectralOperator

/-! ## 1. The test class, finite linear combinations, and the sesquilinear Weil form -/

lemma isWeilTest_zero : IsWeilTest (0 : ℝ → ℂ) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩

lemma isWeilTest_add {f g : ℝ → ℂ} (hf : IsWeilTest f) (hg : IsWeilTest g) :
    IsWeilTest (f + g) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

lemma isWeilTest_smul (c : ℂ) {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (c • f) := by
  refine ⟨hf.1.const_smul c, ?_⟩
  have : (c • f) = (fun _ : ℝ => c) • f := rfl
  rw [this]
  exact hf.2.smul_left

lemma isWeilTest_sum {n : ℕ} (c : Fin n → ℂ) (g : Fin n → ℝ → ℂ)
    (hg : ∀ i, IsWeilTest (g i)) : IsWeilTest (∑ i, c i • g i) := by
  refine Finset.sum_induction _ IsWeilTest (fun f h hf hh => isWeilTest_add hf hh)
    isWeilTest_zero ?_
  intro i _
  exact isWeilTest_smul (c i) (hg i)

lemma isWeilTest_weilTest {f g : ℝ → ℂ} (hf : IsWeilTest f) (hg : IsWeilTest g) :
    IsWeilTest (Zeta23.EF.weilTest f g) := by
  refine ⟨?_, Zeta23.EF.weilTest_hasCompactSupport hf.2 hg.2⟩
  unfold Zeta23.EF.weilTest
  exact hf.2.contDiff_convolution_left _ hf.1
    (Zeta23.EF.continuous_tilde hg.1.continuous).locallyIntegrable

lemma isWeilTest_deriv {f : ℝ → ℂ} (hf : IsWeilTest f) : IsWeilTest (deriv f) :=
  ⟨(contDiff_infty_iff_deriv.mp hf.1).2, hf.2.deriv⟩

/-- The sesquilinear Weil form `B(f, g) = W(f ⋆ g~)` read from the primes side. -/
def weilSesq (f g : ℝ → ℂ) : ℂ := weilForm (Zeta23.EF.weilTest f g)

lemma weilForm_autocorr_eq (g : ℝ → ℂ) : weilForm (autocorr g) = weilSesq g g := by
  rw [weilSesq, RvMBridge5.autocorr_eq_weilTest]

/-- **Zero-side representation of the sesquilinear Weil form** (unconditional; from the E8
explicit formula and the transform factorisation): `B(f,g) = Σ_ρ m(ρ) f̂(γ_ρ) conj ĝ(conj γ_ρ)`. -/
theorem weilSesq_hasSum {f g : ℝ → ℂ} (hf : IsWeilTest f) (hg : IsWeilTest g) :
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ)
        * (paperFT f (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ))))) (weilSesq f g) := by
  have h := (RvMBridge4.limit_explicit_formula _ (isWeilTest_weilTest hf hg)).2
  have hk : ∀ ρ, weilKernel (Zeta23.EF.weilTest f g) ρ
      = paperFT f (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ))) := fun ρ => by
    rw [RvMBridge4.weilKernel_eq_paperFT_gammaOf,
      Zeta23.EF.paperFT_weilTest hf.1.continuous hg.1.continuous hf.2 hg.2]
  simp only [hk] at h
  exact h

/-- **Translation invariance of the zeta Weil form, in Fourier form** (unconditional):
multiplication by `z` is symmetric, `B(f', g) + B(f, g') = 0`.  This is the hypothesis `hZ` of
the abstract Pontryagin--Caratheodory--Fejer theorem (li_positivity island, same file name). -/
theorem weilSesq_deriv_symm {f g : ℝ → ℂ} (hf : IsWeilTest f) (hg : IsWeilTest g) :
    weilSesq (deriv f) g + weilSesq f (deriv g) = 0 := by
  have h1 := weilSesq_hasSum (isWeilTest_deriv hf) hg
  have h2 := weilSesq_hasSum hf (isWeilTest_deriv hg)
  have h3 := h1.add h2
  have hzero : ∀ ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ)
        * (paperFT (deriv f) (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ))))
      + (WeilExplicit.zeroMult ρ : ℂ)
        * (paperFT f (gammaOf ρ) * conj (paperFT (deriv g) (conj (gammaOf ρ)))) = 0 := by
    intro ρ
    rw [Zeta23.paperFT_deriv (contDiff_infty.mp hf.1 1) hf.2,
      Zeta23.paperFT_deriv (contDiff_infty.mp hg.1 1) hg.2]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
    ring
  simp only [hzero] at h3
  exact h3.unique hasSum_zero

/-! ## 2. Linearity of the transform on finite combinations -/

lemma integrable_paperFT_integrand {f : ℝ → ℂ} (hf : IsWeilTest f) (z : ℂ) :
    Integrable (fun u : ℝ => f u * Complex.exp (Complex.I * z * (u : ℂ))) := by
  have hc : Continuous (fun u : ℝ => f u * Complex.exp (Complex.I * z * (u : ℂ))) := by
    have := hf.1.continuous
    fun_prop
  refine hc.integrable_of_hasCompactSupport ?_
  exact hf.2.mul_right

lemma paperFT_sum {n : ℕ} (c : Fin n → ℂ) (g : Fin n → ℝ → ℂ) (hg : ∀ i, IsWeilTest (g i))
    (z : ℂ) : paperFT (∑ i, c i • g i) z = ∑ i, c i * paperFT (g i) z := by
  unfold paperFT
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring
  · intro i _
    have := (integrable_paperFT_integrand (hg i) z).const_mul (c i)
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring

lemma paperFT_smul (c : ℂ) (g : ℝ → ℂ) (z : ℂ) : paperFT (c • g) z = c * paperFT g z := by
  unfold paperFT
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 3. The Pontryagin index of the zeta Weil form is at most the number of off-line pairs -/

/-- `g` spans a subspace of Weil tests on which the Weil form `W(g ⋆ g~)` is negative definite. -/
def IsWeilNegFamily {n : ℕ} (g : Fin n → ℝ → ℂ) : Prop :=
  (∀ i, IsWeilTest (g i)) ∧
    ∀ c : Fin n → ℂ, c ≠ 0 → (weilForm (autocorr (∑ i, c i • g i))).re < 0

/-- Coefficient-space codimension bound (as in the li_positivity file). -/
theorem card_le_of_nonneg_on_ker {n : ℕ} {ι : Type*} [Fintype ι] (Q : (Fin n → ℂ) → ℝ)
    (ℓ : (Fin n → ℂ) →ₗ[ℂ] (ι → ℂ)) (hQ : ∀ c, ℓ c = 0 → 0 ≤ Q c)
    (hneg : ∀ c, c ≠ 0 → Q c < 0) : n ≤ Fintype.card ι := by
  by_contra h
  have h' : Fintype.card ι < n := lt_of_not_ge h
  have hk : LinearMap.ker ℓ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact h')
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact absurd (hQ c (LinearMap.mem_ker.mp hc)) (not_le.mpr (hneg c hc0))

/-- On the critical line the ordinate `γ_ρ = (ρ - 1/2)/i` is real. -/
lemma conj_gammaOf_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : conj (gammaOf ρ) = gammaOf ρ := by
  rw [Complex.conj_eq_iff_im]
  unfold gammaOf
  rw [Complex.div_I]
  simp [h]

/-- The functional-equation partner `1 - conj ρ` has ordinate `conj γ_ρ`. -/
lemma gammaOf_one_sub_conj (ρ : ℂ) : gammaOf (1 - conj ρ) = conj (gammaOf ρ) := by
  unfold gammaOf
  rw [map_div₀, map_sub, Complex.conj_I]
  have : conj (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, Complex.conj_ofNat]
  rw [this]
  field_simp
  ring

/-- **Zero-side positivity off `S`.** If `ĥ` vanishes at the ordinates of a set `S` containing one
member of every off-line pair `{ρ, 1 - conj ρ}`, every zero-side term of `W(h ⋆ h~)` has
nonnegative real part: on-line terms are `m |ĥ(γ)|²`, off-line terms vanish. -/
lemma zeroSide_term_re_nonneg (S : Finset ℂ)
    (hS : ∀ ρ, WeilExplicit.zeroMult ρ ≠ 0 → ρ.re ≠ 1 / 2 → ρ ∈ S ∨ 1 - conj ρ ∈ S)
    (h : ℝ → ℂ) (hvan : ∀ s ∈ S, paperFT h (gammaOf s) = 0) (ρ : ℂ) :
    0 ≤ ((WeilExplicit.zeroMult ρ : ℂ)
        * (paperFT h (gammaOf ρ) * conj (paperFT h (conj (gammaOf ρ))))).re := by
  by_cases hm : WeilExplicit.zeroMult ρ = 0
  · simp [hm]
  by_cases hre : ρ.re = 1 / 2
  · rw [conj_gammaOf_of_re hre, Complex.mul_conj]
    have : ((WeilExplicit.zeroMult ρ : ℂ) * (Complex.normSq (paperFT h (gammaOf ρ)) : ℂ))
        = (((WeilExplicit.zeroMult ρ : ℝ) * Complex.normSq (paperFT h (gammaOf ρ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  · rcases hS ρ hm hre with hρ | hρ
    · rw [hvan ρ hρ]; simp
    · have h0 : paperFT h (conj (gammaOf ρ)) = 0 := by
        rw [← gammaOf_one_sub_conj]; exact hvan _ hρ
      rw [h0]; simp

/-- **Weil positivity on a finite-codimension subspace.** -/
theorem weilForm_autocorr_re_nonneg_of_vanish (S : Finset ℂ)
    (hS : ∀ ρ, WeilExplicit.zeroMult ρ ≠ 0 → ρ.re ≠ 1 / 2 → ρ ∈ S ∨ 1 - conj ρ ∈ S)
    {h : ℝ → ℂ} (hh : IsWeilTest h) (hvan : ∀ s ∈ S, paperFT h (gammaOf s) = 0) :
    0 ≤ (weilForm (autocorr h)).re := by
  rw [weilForm_autocorr_eq]
  exact (Complex.hasSum_re (weilSesq_hasSum hh hh)).nonneg
    (fun ρ => zeroSide_term_re_nonneg S hS h hvan ρ)

/-- **The Pontryagin index of the zeta Weil form is at most the number of off-line pairs**
(unconditional, kernel-checked).  If `S` contains one member of every pair `{ρ, 1 - conj ρ}` of
nontrivial zeros off the critical line, then every family of Weil tests spanning a
Weil-negative-definite subspace has at most `|S|` members.  Under RH take `S = ∅`. -/
theorem weil_negIndex_le_offline (S : Finset ℂ)
    (hS : ∀ ρ, WeilExplicit.zeroMult ρ ≠ 0 → ρ.re ≠ 1 / 2 → ρ ∈ S ∨ 1 - conj ρ ∈ S)
    {n : ℕ} (g : Fin n → ℝ → ℂ) (hg : IsWeilNegFamily g) : n ≤ S.card := by
  let M : Matrix S (Fin n) ℂ := fun s i => paperFT (g i) (gammaOf s)
  have hcard : Fintype.card S = S.card := Fintype.card_coe S
  rw [← hcard]
  refine card_le_of_nonneg_on_ker (fun c => (weilForm (autocorr (∑ i, c i • g i))).re)
    M.mulVecLin ?_ hg.2
  intro c hc
  refine weilForm_autocorr_re_nonneg_of_vanish S hS (isWeilTest_sum c g hg.1) ?_
  intro s hs
  rw [paperFT_sum c g hg.1]
  have := congrFun hc ⟨s, hs⟩
  simp only [Pi.zero_apply, M] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Scaling: `W((c g) ⋆ (c g)~) = |c|² W(g ⋆ g~)`. -/
lemma weilForm_autocorr_smul (c : ℂ) {g : ℝ → ℂ} (hg : IsWeilTest g) :
    weilForm (autocorr (c • g)) = (Complex.normSq c : ℂ) * weilForm (autocorr g) := by
  rw [weilForm_autocorr_eq, weilForm_autocorr_eq]
  have h1 := weilSesq_hasSum (isWeilTest_smul c hg) (isWeilTest_smul c hg)
  have h2 := (weilSesq_hasSum hg hg).mul_left (Complex.normSq c : ℂ)
  refine h1.unique (h2.congr_fun ?_)
  intro ρ
  simp only [paperFT_smul, map_mul]
  rw [← Complex.mul_conj c]
  ring

/-- **Weil's criterion as a Pontryagin-index statement** (a relabeling of Weil's criterion, NOT
progress on RH): RH holds iff the zeta Weil form has negative index `0`, i.e. no nonempty family
of Weil tests spans a Weil-negative-definite subspace. -/
theorem rh_iff_weil_negIndex_zero :
    RiemannHypothesis ↔ ∀ (n : ℕ) (g : Fin n → ℝ → ℂ), IsWeilNegFamily g → n = 0 := by
  constructor
  · intro hRH n g hg
    have hS : ∀ ρ, WeilExplicit.zeroMult ρ ≠ 0 → ρ.re ≠ 1 / 2 → ρ ∈ (∅ : Finset ℂ) ∨
        1 - conj ρ ∈ (∅ : Finset ℂ) := by
      intro ρ hm hre
      exfalso
      apply hre
      by_contra hnt
      have hz : IsNontrivialZero ρ := by
        by_contra hz
        exact hm (RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hz)
      exact hnt (Zeta23.RH_implies_on_line hRH hz)
    have := weil_negIndex_le_offline ∅ hS g hg
    simpa using this
  · intro h
    apply RvMBridge9.weil_positivity_implies_rh
    intro g hg
    by_contra hneg
    have hneg' : (weilForm (autocorr g)).re < 0 := lt_of_not_ge hneg
    have h1 := h 1 (fun _ => g) ⟨fun _ => hg, fun c hc => ?_⟩
    · exact one_ne_zero h1
    · have hc0 : c 0 ≠ 0 := by
        intro h0; apply hc; funext i; rw [Subsingleton.elim i 0, h0]; rfl
      rw [Fin.sum_univ_one, weilForm_autocorr_smul (c 0) hg, Complex.re_ofReal_mul]
      exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc0) hneg'

/-! ## 4. Windows -/

/-- `κ(L) ≤ K`: every Weil-negative family of tests supported in the window `[-L/2, L/2]` (the
Connes--Consani--Moscovici window `[x^{-1/2}, x^{1/2}]`, `L = log x`) has at most `K` members. -/
def KappaWindowLE (L : ℝ) (K : ℕ) : Prop :=
  ∀ (n : ℕ) (g : Fin n → ℝ → ℂ), IsWeilNegFamily g →
    (∀ i, tsupport (g i) ⊆ Set.Icc (-(L / 2)) (L / 2)) → n ≤ K

/-- `κ` is nondecreasing in the window. -/
theorem kappaWindow_mono {L L' : ℝ} (hLL : L ≤ L') {K : ℕ} (h : KappaWindowLE L' K) :
    KappaWindowLE L K := by
  intro n g hg hsupp
  refine h n g hg fun i => (hsupp i).trans ?_
  intro u hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- Every window: `κ(x) ≤ #off-line pairs`. -/
theorem kappaWindow_le_offline (S : Finset ℂ)
    (hS : ∀ ρ, WeilExplicit.zeroMult ρ ≠ 0 → ρ.re ≠ 1 / 2 → ρ ∈ S ∨ 1 - conj ρ ∈ S) (L : ℝ) :
    KappaWindowLE L S.card :=
  fun _ g hg _ => weil_negIndex_le_offline S hS g hg

end CruxSpectralOperator

#print axioms CruxSpectralOperator.isWeilTest_zero
#print axioms CruxSpectralOperator.isWeilTest_add
#print axioms CruxSpectralOperator.isWeilTest_smul
#print axioms CruxSpectralOperator.isWeilTest_sum
#print axioms CruxSpectralOperator.isWeilTest_weilTest
#print axioms CruxSpectralOperator.isWeilTest_deriv
#print axioms CruxSpectralOperator.weilForm_autocorr_eq
#print axioms CruxSpectralOperator.weilSesq_hasSum
#print axioms CruxSpectralOperator.weilSesq_deriv_symm
#print axioms CruxSpectralOperator.integrable_paperFT_integrand
#print axioms CruxSpectralOperator.paperFT_sum
#print axioms CruxSpectralOperator.paperFT_smul
#print axioms CruxSpectralOperator.card_le_of_nonneg_on_ker
#print axioms CruxSpectralOperator.conj_gammaOf_of_re
#print axioms CruxSpectralOperator.gammaOf_one_sub_conj
#print axioms CruxSpectralOperator.zeroSide_term_re_nonneg
#print axioms CruxSpectralOperator.weilForm_autocorr_re_nonneg_of_vanish
#print axioms CruxSpectralOperator.weil_negIndex_le_offline
#print axioms CruxSpectralOperator.weilForm_autocorr_smul
#print axioms CruxSpectralOperator.rh_iff_weil_negIndex_zero
#print axioms CruxSpectralOperator.kappaWindow_mono
#print axioms CruxSpectralOperator.kappaWindow_le_offline
