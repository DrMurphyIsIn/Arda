/-
  FamilyWeilSymbol -- the frequency-side SYMBOL REPRESENTATION of the parametric degree-<= 2 Weil
  form (Stage 1a of the quadratic-family programme, 2026-09-25): Zhu eq. (2) (ZhuSymbol.lean,
  merged via #606) generalised from zeta to every FormData D with admissible gamma shifts.

  THE SYMBOL.  For D = (weights c, shifts, logq) and a support parameter L,
      symbolF D L t = Σ_{mu ∈ shifts} Re psi((1 + 2 mu)/4 + i t/2) - |shifts| log pi + logq
                      - Σ_{log n < 2L} (2 c(n)/sqrt n) cos(t log n)
  (the island's normalisation: archSideF carries (1/2pi) ∫ h_g(r) symbolArch D r dr, the pole
  terms H_g(0) + H_g(1), and the g(0) (logq - |shifts| log pi) term; primeSideF carries
  Σ c(n)/sqrt n (g(log n) + g(-log n))).  At the zeta data symbolF zetaData L = Zhu's weilSymbol L
  (symbolF_zeta); at the quadratic data
      symbolQ d L t = psiR t + psiShift mu_d t - 2 log pi + log|d|
                      - Σ_{log n < 2L} (2 weightQ d n / sqrt n) cos(t log n)   (symbolQ_eq),
  the memo's Psi_d with s_eps replaced by the exact conductor term log|d| (the cell symbol
  symbolCell N eps neg L has conductor term 0 and the cut weights).

  THE THEOREM (symbol_representation_ofReal_F; symbolRepresentationF for real even tests,
  symbolRepresentationF_odd for real odd tests): for D with admissible shifts, v real of definite
  parity eps (eps^2 = 1), a Weil test supported in [-L, L], f = ofReal ∘ v,
      Re weilFormF D (autocorr f) = 2 eps |F(i/2)|^2 + (1/2pi) ∫ |F(t)|^2 symbolF D L t dt,
  F(t) = weilKernel f (1/2 + it), F(i/2) = weilKernel f 0.  The route is EXACTLY Zhu's
  (RvMBridgeZhu.symbol_representation_ofReal): pole terms by the transform factorisation and
  parity, g(0) = ‖f‖^2 = (1/2pi) ∫ |F|^2 by Fourier inversion at 0, the archimedean integral
  pointwise |F|^2 symbolArch, the prime side by Fourier inversion at log n with the FINITE comb;
  the ONE new analytic input is the integrability of |F|^2 psiShift mu for admissible mu
  (FamilyWeilDigamma.integrable_hsq_mul_psiShift).  Zhu's zeta theorem is RECOVERED as an
  instance (symbolRepresentation_of_family: the family theorem at zetaData proves the registry's
  WeilWindow.SymbolRepresentation L; symbolRepresentation_agree: both routes give the same value).

  The finite-window forms (symbolF_eq_fin: the comb over n < N when 2L <= log N) are what the
  Stage 1 certificates read; no certificate is cut here.

  DISCLOSURE.  weilFormF D is the frequency-side DEFINITION of FamilyWeilForm; only at the zeta
  data is it the island's explicit-formula functional.  Nothing about positivity is proved.
  conjecture1_proved = False.
-/
import FamilyWeilDigamma
import ZhuSymbol

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace FamilyWeil
open WeilExplicit RvMBridge4 RvMBridge5 RvMBridge11 RvMBridge31 RvMBridgeZhu

/-! ## A. The symbol. -/

/-- The parametric Weil symbol (Zhu eq. (3) generalised): the digamma symbol of the shifts, the
`log pi` terms, the conductor term, and the finite comb of the weights. -/
def symbolF (D : FormData) (L : ℝ) (t : ℝ) : ℝ :=
  symbolArch D t - (D.shifts.length : ℝ) * Real.log Real.pi + D.logq
    - ∑' n : ℕ, if Real.log n < 2 * L then
        2 * D.c n / Real.sqrt n * Real.cos (t * Real.log n) else 0

/-- Data with admissible shifts (`-1/2 < mu < 3/2`, abscissa in `(0, 1)`). -/
def ShiftsOK (D : FormData) : Prop := ∀ μ ∈ D.shifts, ShiftOK μ

lemma shiftsOK_zeta : ShiftsOK zetaData := by
  intro μ hμ
  simp only [zetaData, List.mem_singleton] at hμ
  rw [hμ]
  exact shiftOK_zero

lemma shiftsOK_quad (d : ℤ) : ShiftsOK (quadData d) := by
  intro μ hμ
  simp only [quadData, List.mem_cons, List.not_mem_nil, or_false] at hμ
  rcases hμ with h | h
  · rw [h]; exact shiftOK_zero
  · rw [h]; exact shiftOK_muOf _

lemma shiftsOK_cell (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) : ShiftsOK (cellData N ε neg) := by
  intro μ hμ
  simp only [cellData, List.mem_cons, List.not_mem_nil, or_false] at hμ
  rcases hμ with h | h
  · rw [h]; exact shiftOK_zero
  · rw [h]; exact shiftOK_muOf _

/-- At the zeta data the symbol is Zhu's `weilSymbol`. -/
theorem symbolF_zeta (L t : ℝ) : symbolF zetaData L t = WeilWindow.weilSymbol L t := by
  unfold symbolF WeilWindow.weilSymbol
  rw [symbolArch_zeta]
  simp only [zetaData, List.length_cons, List.length_nil, zero_add, Nat.cast_one, one_mul, add_zero]

/-! ## B. Integrability of the archimedean weight. -/

/-- The digamma symbol of a list of shifts. -/
def symbolList (l : List ℝ) (r : ℝ) : ℝ := (l.map (fun μ => psiShift μ r)).sum

lemma symbolArch_eq_symbolList (D : FormData) (r : ℝ) : symbolArch D r = symbolList D.shifts r := rfl

lemma integrable_mul_symbolList {F : ℝ → ℝ} (hF : Integrable F) (hF0 : ∀ r, 0 ≤ F r)
    (hFpsi : Integrable (fun r => F r * psiR r)) :
    ∀ l : List ℝ, (∀ μ ∈ l, ShiftOK μ) → Integrable (fun r => F r * symbolList l r) := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [symbolList, List.map_nil, List.sum_nil, mul_zero]
    exact integrable_zero _ _ _
  | cons μ l ih =>
    intro hl
    have hμ : ShiftOK μ := hl μ (List.mem_cons_self ..)
    have hl' : ∀ μ' ∈ l, ShiftOK μ' := fun μ' h => hl μ' (List.mem_cons_of_mem _ h)
    have e : (fun r => F r * symbolList (μ :: l) r)
        = fun r => F r * psiShift μ r + F r * symbolList l r := by
      funext r
      simp only [symbolList, List.map_cons, List.sum_cons]
      ring
    rw [e]
    exact (integrable_mul_psiShift hF hF0 hFpsi hμ).add (ih hl')

theorem integrable_mul_symbolArch {F : ℝ → ℝ} (hF : Integrable F) (hF0 : ∀ r, 0 ≤ F r)
    (hFpsi : Integrable (fun r => F r * psiR r)) {D : FormData} (hD : ShiftsOK D) :
    Integrable (fun r => F r * symbolArch D r) :=
  integrable_mul_symbolList hF hF0 hFpsi D.shifts hD

/-! ## C. The symbol representation. -/

/-- **The symbol representation of the parametric form** for `f = ofReal ∘ v`, `v(-u) = ε v(u)`,
`ε² = 1`: `Re weilFormF D (autocorr f) = 2 ε |F(i/2)|² + (1/2π) ∫ |F|² symbolF D L`. -/
theorem symbol_representation_ofReal_F (D : FormData) (hD : ShiftsOK D) {v : ℝ → ℝ} {L ε : ℝ}
    (hε : ε * ε = 1) (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = ε * v u)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Set.Icc (-L) L) :
    (weilFormF D (autocorr (fun u => (v u : ℂ)))).re
      = 2 * ε * ‖weilKernel (fun u => (v u : ℂ)) 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (t : ℂ) * I)‖ ^ 2
            * symbolF D L t := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ) with hfC
  set g : ℝ → ℂ := autocorr fC with hgdef
  have hg : IsWeilTest g := isWeilTest_autocorr hf
  have hcont : Continuous fC := hf.1.continuous
  have hcs : HasCompactSupport fC := hf.2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the transform on the line and the archimedean symbol
  set F : ℝ → ℝ := fun r => ‖weilKernel fC (1 / 2 + (r : ℂ) * I)‖ ^ 2 with hF
  set sA : ℝ → ℝ := fun r => symbolArch D r with hsA
  have hFhsq : F = hsq fC := by
    funext r
    rw [hF]
    simp only
    rw [weilKernel_line]
    rfl
  have hF0 : ∀ r, 0 ≤ F r := fun r => by rw [hF]; positivity
  have hline : ∀ r : ℝ, paperFT g r = (F r : ℂ) := by
    intro r
    rw [← weilKernel_line, hgdef, weilKernel_autocorr_line hf, hF]
    simp only
    rw [weilKernel_line]
    push_cast
    ring
  /- pole terms -/
  have hcI : (starRingEnd ℂ) (I / 2) = -(I / 2) := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hcI' : (starRingEnd ℂ) (-I / 2) = I / 2 := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hpole0 : weilKernel g 0 = ((ε * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_zero, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hcont hcont hcs hcs, hcI,
      hfC, paperFT_neg_of_parity hε hev, map_mul, Complex.conj_ofReal, mul_left_comm,
      Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hpole1 : weilKernel g 1 = ((ε * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_one, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hcont hcont hcs hcs, hcI',
      hfC, neg_div, paperFT_neg_of_parity hε hev, mul_assoc, Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  /- g(0) = ‖f‖² and Plancherel -/
  have hg0 : g 0 = ((∫ x : ℝ, ‖fC x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hgdef]
    unfold WeilExplicit.autocorr
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [sub_zero, Complex.mul_conj']
    push_cast
    ring
  have hFint : Integrable F := by
    have := (integrable_paperFT hg).re
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp [hline r]
  have hplan : (∫ x : ℝ, ‖fC x‖ ^ 2) = (1 / (2 * Real.pi)) * ∫ r, F r := by
    have h := inversion_zero hg
    rw [hg0] at h
    have h2 : ∫ r : ℝ, paperFT g r = ((∫ r, F r : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext r
      exact hline r
    rw [h2] at h
    have h3 : ((1 / (2 * Real.pi) * ∫ r, F r : ℝ) : ℂ) = ((∫ x : ℝ, ‖fC x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact h
    exact (Complex.ofReal_inj.mp h3).symm
  /- the archimedean integral -/
  have harch_pt : ∀ r : ℝ, weilKernel g (1 / 2 + (r : ℂ) * I) * ((symbolArch D r : ℝ) : ℂ)
      = ((F r * sA r : ℝ) : ℂ) := by
    intro r
    rw [hgdef, weilKernel_autocorr_line hf, hF, hsA]
    simp only
    rw [weilKernel_line]
    push_cast
    ring
  have harch : ∫ r : ℝ, weilKernel g (1 / 2 + (r : ℂ) * I) * ((symbolArch D r : ℝ) : ℂ)
      = ((∫ r, F r * sA r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    exact harch_pt r
  have hFpsiR : Integrable (fun r => F r * psiR r) := by
    rw [hFhsq]
    exact integrable_hsq_mul_psiR hf
  have hFpsi : Integrable (fun r => F r * sA r) :=
    integrable_mul_symbolArch hFint hF0 hFpsiR hD
  /- the prime side -/
  set A : ℝ → ℝ := fun y => (g y).re with hA
  have hgA : g = fun y => (A y : ℂ) := by
    funext y
    rw [hA]
    simp only
    rw [hgdef, autocorr_ofReal_eq]
    simp
  have hAc : Continuous A := Complex.continuous_re.comp hg.1.continuous
  have hAi : Integrable A := by
    exact (hg.1.continuous.integrable_of_hasCompactSupport (μ := volume) hg.2).re
  have hFT : ∀ r : ℝ, paperFT (fun u => (A u : ℂ)) r = (F r : ℂ) := by
    intro r
    rw [← hgA]
    exact hline r
  have hcosint : ∀ n : ℕ, ∫ r, F r * Real.cos (r * Real.log n) = 2 * Real.pi * A (Real.log n) :=
    fun n => Taper.integral_mul_cos_of_paperFT_eq hAc hAi hFint hFT (Real.log n)
  have hgeven : ∀ y, g (-y) = g y := fun y => by
    rw [hgdef]
    exact autocorr_neg_of_parity hε hev y
  have hgzero : ∀ y, 2 * L ≤ |y| → g y = 0 := fun y hy => by
    rw [hgdef]
    exact autocorr_eq_zero_of_two_mul_le hsupp hy
  -- the real prime term
  set term : ℕ → ℝ := fun n => if Real.log n < 2 * L then
      2 * D.c n / Real.sqrt n * ∫ r, F r * Real.cos (r * Real.log n)
    else 0 with hterm
  have hprime_pt : ∀ n : ℕ,
      ((D.c n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))
        = (((1 / (2 * Real.pi)) * term n : ℝ) : ℂ) := by
    intro n
    rw [hterm]
    simp only
    split_ifs with hn
    · rw [hgeven, hcosint n]
      have hgn : g (Real.log n) = (A (Real.log n) : ℂ) := by rw [hgA]
      rw [hgn]
      push_cast
      field_simp
      ring
    · have h1 : g (Real.log n) = 0 := hgzero _ ((not_lt.mp hn).trans (le_abs_self _))
      have h2 : g (-Real.log n) = 0 :=
        hgzero _ (by rw [abs_neg]; exact (not_lt.mp hn).trans (le_abs_self _))
      rw [h1, h2]
      simp
  -- the comb is finite
  set N0 : ℕ := ⌈Real.exp (2 * L)⌉₊ + 1 with hN0
  have hbig : ∀ n : ℕ, n ∉ Finset.range N0 → ¬ Real.log n < 2 * L := by
    intro n hn hlt
    have hn' : N0 ≤ n := by simpa [Finset.mem_range] using hn
    have h1 : Real.exp (2 * L) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * L))
      have h2 : ((⌈Real.exp (2 * L)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have h3 : 2 * L < Real.log n := by
      rw [← Real.log_exp (2 * L)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hprime : primeSideF D g = (((1 / (2 * Real.pi)) * ∑ n ∈ Finset.range N0, term n : ℝ) : ℂ) := by
    unfold primeSideF
    have hvan : ∀ n ∉ Finset.range N0, term n = 0 := fun n hn => by
      rw [hterm]; simp only; rw [if_neg (hbig n hn)]
    rw [tsum_congr hprime_pt, ← Complex.ofReal_tsum, tsum_mul_left,
      tsum_eq_sum (s := Finset.range N0) hvan]
  /- the symbol as a finite sum, and the interchange -/
  set cst : ℝ := D.logq - (D.shifts.length : ℝ) * Real.log Real.pi with hcst
  have hsym : ∀ t : ℝ, symbolF D L t = sA t + cst
      - ∑ n ∈ Finset.range N0, (if Real.log n < 2 * L then
          2 * D.c n / Real.sqrt n * Real.cos (t * Real.log n) else 0) := by
    intro t
    unfold symbolF
    rw [tsum_eq_sum (s := Finset.range N0) (fun n hn => by rw [if_neg (hbig n hn)]), hsA, hcst]
    simp only
    ring
  have hcosI : ∀ n : ℕ, Integrable (fun r => F r * Real.cos (r * Real.log n)) := by
    intro n
    have h := hFint.bdd_mul (c := 1)
      (by fun_prop : Continuous fun r : ℝ => Real.cos (r * Real.log n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    exact h.congr (Filter.Eventually.of_forall fun r => mul_comm _ _)
  have htermI : ∀ n ∈ Finset.range N0, Integrable (fun r => F r * (if Real.log n < 2 * L then
      2 * D.c n / Real.sqrt n * Real.cos (r * Real.log n) else 0)) := by
    intro n _
    split_ifs with hn
    · have := (hcosI n).const_mul (2 * D.c n / Real.sqrt n)
      exact this.congr (Filter.Eventually.of_forall fun r => by simp only; ring)
    · simp
  have hint : ∫ t : ℝ, F t * symbolF D L t
      = (∫ r, F r * sA r) + cst * (∫ r, F r) - ∑ n ∈ Finset.range N0, term n := by
    have e : (fun t : ℝ => F t * symbolF D L t)
        = fun t => (F t * sA t + F t * cst)
          - ∑ n ∈ Finset.range N0, F t * (if Real.log n < 2 * L then
              2 * D.c n / Real.sqrt n * Real.cos (t * Real.log n) else 0) := by
      funext t
      rw [hsym t, ← Finset.mul_sum]
      ring
    have hI1 : Integrable (fun t => F t * sA t + F t * cst) :=
      hFpsi.add (hFint.mul_const _)
    have hI2 : Integrable (fun t => F t * cst) := hFint.mul_const _
    rw [e, integral_sub hI1 (integrable_finsetSum _ htermI),
      integral_add hFpsi hI2, integral_mul_const, integral_finsetSum _ htermI]
    have hterm_eq : ∀ n ∈ Finset.range N0,
        (∫ t, F t * (if Real.log n < 2 * L then
          2 * D.c n / Real.sqrt n * Real.cos (t * Real.log n) else 0))
          = term n := by
      intro n _
      rw [hterm]
      simp only
      split_ifs with hn
      · rw [← integral_const_mul]
        congr 1
        funext t
        ring
      · simp
    rw [Finset.sum_congr rfl hterm_eq]
    ring
  /- assembly -/
  have hcomplex : archSideF D g - primeSideF D g
      = ((2 * ε * ‖weilKernel fC 0‖ ^ 2 + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, F t * symbolF D L t : ℝ) : ℂ) := by
    unfold archSideF
    rw [hpole0, hpole1, hg0, harch, hprime, hint, hplan, hcst]
    push_cast
    ring
  rw [weilFormF, hcomplex, Complex.ofReal_re]

/-- **The family symbol representation, real even tests** (the shape of the registry's
`WeilWindow.SymbolRepresentation`, with `symbolF D L` in place of Zhu's `weilSymbol L`). -/
theorem symbolRepresentationF (D : FormData) (hD : ShiftsOK D) (L : ℝ) :
    ∀ f : ℝ → ℂ, IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = f x) →
      tsupport f ⊆ Set.Icc (-L) L →
      (weilFormF D (autocorr f)).re
        = 2 * ‖weilKernel f 0‖ ^ 2
          + (1 / (2 * Real.pi)) *
            ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * symbolF D L t := by
  intro f hf hreal hev hsupp
  obtain ⟨v, rfl⟩ : ∃ v : ℝ → ℝ, f = fun u => (v u : ℂ) :=
    ⟨fun u => (f u).re, funext fun u => Complex.ext (by simp) (by simp [hreal u])⟩
  have hev' : ∀ u, v (-u) = 1 * v u := fun u => by
    have h : ((v (-u) : ℝ) : ℂ) = (v u : ℝ) := hev u
    rw [one_mul]
    exact_mod_cast h
  have := symbol_representation_ofReal_F D hD (ε := 1) (by norm_num) hf hev' hsupp
  rw [this]
  ring

/-- **The family symbol representation, real odd tests** (Zhu Lemma 6.1 shape: the pole term
changes sign). -/
theorem symbolRepresentationF_odd (D : FormData) (hD : ShiftsOK D) (L : ℝ) :
    ∀ f : ℝ → ℂ, IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = -f x) →
      tsupport f ⊆ Set.Icc (-L) L →
      (weilFormF D (autocorr f)).re
        = -2 * ‖weilKernel f 0‖ ^ 2
          + (1 / (2 * Real.pi)) *
            ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * symbolF D L t := by
  intro f hf hreal hodd hsupp
  obtain ⟨v, rfl⟩ : ∃ v : ℝ → ℝ, f = fun u => (v u : ℂ) :=
    ⟨fun u => (f u).re, funext fun u => Complex.ext (by simp) (by simp [hreal u])⟩
  have hodd' : ∀ u, v (-u) = -1 * v u := fun u => by
    have h : ((v (-u) : ℝ) : ℂ) = -(v u : ℝ) := hodd u
    rw [neg_one_mul]
    exact_mod_cast h
  have := symbol_representation_ofReal_F D hD (ε := -1) (by norm_num) hf hodd' hsupp
  rw [this]
  ring

/-! ## D. The zeta instance recovers Zhu's theorem. -/

/-- **Zhu eq. (2) from the family theorem**: the registry's `WeilWindow.SymbolRepresentation L`,
proved through `symbolRepresentationF` at `zetaData` (via `weilFormF_zeta` and `symbolF_zeta`),
not by copying `RvMBridgeZhu.symbolRepresentation`. -/
theorem symbolRepresentation_of_family (L : ℝ) : WeilWindow.SymbolRepresentation L := by
  intro f hf hreal hev hsupp
  have h := symbolRepresentationF zetaData shiftsOK_zeta L f hf hreal hev hsupp
  rw [weilFormF_zeta] at h
  rw [weilForm_autocorr_eq, h]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [symbolF_zeta]

/-- The two routes to Zhu's theorem give the same value on every real even test: the family
representation at the zeta data and Zhu's own representation agree. -/
theorem symbolRepresentation_agree (L : ℝ) (f : ℝ → ℂ) (hf : IsWeilTest f)
    (hreal : ∀ x, (f x).im = 0) (hev : ∀ x, f (-x) = f x) (hsupp : tsupport f ⊆ Set.Icc (-L) L) :
    2 * ‖weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * symbolF zetaData L t
      = 2 * ‖weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * WeilWindow.weilSymbol L t := by
  have h1 := symbolRepresentationF zetaData shiftsOK_zeta L f hf hreal hev hsupp
  have h2 := RvMBridgeZhu.symbolRepresentation L f hf hreal hev hsupp
  rw [weilFormF_zeta] at h1
  rw [weilForm_autocorr_eq] at h2
  rw [← h1, ← h2]

/-! ## E. The quadratic instance and the cell symbol. -/

/-- The symbol of `zeta_K`, `K = Q(sqrt d)`. -/
def symbolQ (d : ℤ) (L t : ℝ) : ℝ := symbolF (quadData d) L t

/-- The symbol of a `(pattern, sign)` cell cut at `N`: conductor term `0`, cut weights. -/
def symbolCell (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) (L t : ℝ) : ℝ := symbolF (cellData N ε neg) L t

/-- The memo's `Psi_d`: two digammas, `-2 log pi`, the exact conductor term `log|d|`, the comb of
the weights `c_d(n) = weightQ d n` with coefficient `-2 c_d(n) n^{-1/2}` on `cos(t log n)`. -/
theorem symbolQ_eq (d : ℤ) (L t : ℝ) :
    symbolQ d L t = psiR t + psiShift (muOf (decide (d < 0))) t - 2 * Real.log Real.pi
      + Real.log (d.natAbs : ℝ)
      - ∑' n : ℕ, if Real.log n < 2 * L then
          2 * weightQ d n / Real.sqrt n * Real.cos (t * Real.log n) else 0 := by
  unfold symbolQ symbolF
  rw [symbolArch_quad]
  simp only [quadData, List.length_cons, List.length_nil]
  push_cast
  ring

theorem symbolCell_eq (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) (L t : ℝ) :
    symbolCell N ε neg L t = psiR t + psiShift (muOf neg) t - 2 * Real.log Real.pi
      - ∑' n : ℕ, if Real.log n < 2 * L then
          2 * cellWeight N ε n / Real.sqrt n * Real.cos (t * Real.log n) else 0 := by
  unfold symbolCell symbolF symbolArch
  simp only [cellData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    psiShift_zero, List.length_cons, List.length_nil]
  push_cast
  ring

/-- The symbol representation of `weilFormQ d` on real even tests. -/
theorem weilFormQ_symbol (d : ℤ) (L : ℝ) (f : ℝ → ℂ) (hf : IsWeilTest f)
    (hreal : ∀ x, (f x).im = 0) (hev : ∀ x, f (-x) = f x) (hsupp : tsupport f ⊆ Set.Icc (-L) L) :
    (weilFormQ d (autocorr f)).re
      = 2 * ‖weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * symbolQ d L t :=
  symbolRepresentationF (quadData d) (shiftsOK_quad d) L f hf hreal hev hsupp

/-- The symbol representation of `weilFormQ d` on real odd tests. -/
theorem weilFormQ_symbol_odd (d : ℤ) (L : ℝ) (f : ℝ → ℂ) (hf : IsWeilTest f)
    (hreal : ∀ x, (f x).im = 0) (hodd : ∀ x, f (-x) = -f x)
    (hsupp : tsupport f ⊆ Set.Icc (-L) L) :
    (weilFormQ d (autocorr f)).re
      = -2 * ‖weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * symbolQ d L t :=
  symbolRepresentationF_odd (quadData d) (shiftsOK_quad d) L f hf hreal hodd hsupp

/-- The symbol representation of a cell form on real even tests. -/
theorem cellForm_symbol (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) (L : ℝ) (f : ℝ → ℂ) (hf : IsWeilTest f)
    (hreal : ∀ x, (f x).im = 0) (hev : ∀ x, f (-x) = f x) (hsupp : tsupport f ⊆ Set.Icc (-L) L) :
    (cellForm N ε neg (autocorr f)).re
      = 2 * ‖weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * symbolCell N ε neg L t :=
  symbolRepresentationF (cellData N ε neg) (shiftsOK_cell N ε neg) L f hf hreal hev hsupp

/-- The symbol representation of a cell form on real odd tests. -/
theorem cellForm_symbol_odd (N : ℕ) (ε : ℕ → ℤ) (neg : Bool) (L : ℝ) (f : ℝ → ℂ)
    (hf : IsWeilTest f) (hreal : ∀ x, (f x).im = 0) (hodd : ∀ x, f (-x) = -f x)
    (hsupp : tsupport f ⊆ Set.Icc (-L) L) :
    (cellForm N ε neg (autocorr f)).re
      = -2 * ‖weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖weilKernel f (1 / 2 + (t : ℂ) * I)‖ ^ 2 * symbolCell N ε neg L t :=
  symbolRepresentationF_odd (cellData N ε neg) (shiftsOK_cell N ε neg) L f hf hreal hodd hsupp

/-! ## F. The finite-window forms of the symbol. -/

/-- On a window `2L <= log N` the comb is the finite sum over `n < N`. -/
theorem symbolF_eq_fin (D : FormData) {L : ℝ} {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N)
    (t : ℝ) :
    symbolF D L t = symbolArch D t - (D.shifts.length : ℝ) * Real.log Real.pi + D.logq
      - ∑ n ∈ Finset.range N, (if Real.log n < 2 * L then
          2 * D.c n / Real.sqrt n * Real.cos (t * Real.log n) else 0) := by
  unfold symbolF
  congr 1
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hlog : Real.log N ≤ Real.log n :=
    Real.log_le_log (Nat.cast_pos.mpr hN) (by exact_mod_cast hn)
  rw [if_neg (by linarith)]

/-- The comb of the quadratic symbol on a window `2L <= log N`, as a finite sum. -/
theorem symbolQ_eq_fin (d : ℤ) {L : ℝ} {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N) (t : ℝ) :
    symbolQ d L t = psiR t + psiShift (muOf (decide (d < 0))) t - 2 * Real.log Real.pi
      + Real.log (d.natAbs : ℝ)
      - ∑ n ∈ Finset.range N, (if Real.log n < 2 * L then
          2 * weightQ d n / Real.sqrt n * Real.cos (t * Real.log n) else 0) := by
  unfold symbolQ
  rw [symbolF_eq_fin _ hN hL, symbolArch_quad]
  simp only [quadData, List.length_cons, List.length_nil]
  push_cast
  ring

/-- The cell symbol and the quadratic symbol of a member agree on the window (the weights agree
below `N`, the conductor term is the only difference). -/
theorem symbolQ_eq_symbolCell_add (d : ℤ) {L : ℝ} {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N)
    (t : ℝ) :
    symbolQ d L t = symbolCell N (kronSym d) (decide (d < 0)) L t + Real.log (d.natAbs : ℝ) := by
  unfold symbolCell
  rw [symbolQ_eq_fin d hN hL, symbolF_eq_fin _ hN hL]
  unfold symbolArch
  simp only [cellData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    psiShift_zero, List.length_cons, List.length_nil]
  have hsum : ∑ n ∈ Finset.range N, (if Real.log n < 2 * L then
        2 * weightQ d n / Real.sqrt n * Real.cos (t * Real.log n) else 0)
      = ∑ n ∈ Finset.range N, (if Real.log n < 2 * L then
        2 * cellWeight N (kronSym d) n / Real.sqrt n * Real.cos (t * Real.log n) else 0) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [weightQ_eq_cellWeight d (Finset.mem_range.mp hn)]
  rw [hsum]
  push_cast
  ring

end FamilyWeil

end
