/-
  Crux_dynamics_ergodic.lean -- buildable core of "Unitarity = PNT: the Lax-Phillips edge theorem
  for the modular surface, with a resonance cooked control, a Hecke-wave identity and a
  Hecke-orbit negative control" (lens: dynamics, ergodic theory, dynamical zeta functions).

  conjecture1_proved = False.  RH is open and nothing here bears on the location of the zeros of
  zeta.  The file is a NO-GO theorem about a class of methods (the unitary scattering channel of
  PSL(2,Z)\H), plus kernel checks of known facts and of known relabelings, each flagged as such.

  SETTING.  For an entire `Λ` with `Λ(1 - w) = Λ(w)` and `Λ(conj w) = conj (Λ w)` put
  `φ_Λ(s) = Λ(2s - 1)/Λ(2s)`.  For `Λ = ξ` (LiCriterion's entire `riemannXi`) this is the
  Eisenstein scattering matrix of PSL(2,Z) with its residual pole at `s = 1` divided out
  (see CORRECTIONS).  Resonances are the zeros of `ξ(2s)`, i.e. `s = ρ/2`.

  ESTABLISHES (kernel-checked; every theorem below prints [propext, Classical.choice, Quot.sound];
  no `sorry`; single-file elaboration against the prebuilt island Mathlib + LiCriterion):

  A. Finite orbit core (ported from ResonanceEdge.lean, plus multiplicity-correct bookkeeping).
     `scat_inner`, `scat_unimodular_on_line`, `scat_pole_of_re_gt_one`, `scat_edge_iff`: the
     factor of one functional-equation quadruple is contractive on `Re s ≥ 1/2` iff
     `0 ≤ Re ρ ≤ 1`, and unimodular on the axis.  Zero multisets closed under
     `ι w = 1 - conj w` (a simple zero on the line is `[ρ, conj ρ]`, not a doubled quadruple).
     The shifted (Hermite–Biehler) channel `chNum/chDen` at shift `h`: `ch_edge_iff`
     (pole-free and contractive on `Re u > 1/2` iff every zero has `|Re w - 1/2| ≤ h`),
     `rh_finite_iff_all_channels`, `unitary_channel_iff` (`h = 1/2` is the modular scattering
     matrix: `chNum_half`, `chDen_half`), `cooked_quadruple_threshold` (`ρ₀ = 3/4 + 20 i` is
     invisible to every channel `h ≥ 1/4`, in particular the unitary one, and seen by every
     `h < 1/4`).
  B. The real `ξ`.  `xi_inner`: `‖ξ(2s - 1)‖ ≤ ‖ξ(2s)‖` for `Re s ≥ 1/2`, from the upstream
     unconditional genus-one paired Hadamard factorisation (LiCriterion) and the termwise gap
     `|ρ + conj v|² - |ρ - v|² = 4 Re ρ Re v`.  `xi_unitary`, `scatXi_norm_le_one`,
     `scatXi_norm_eq_one`, `scatXi_differentiableAt`, `modScat_eq`, `scatXi_one_ne_zero`.
  C. Birman–Krein.  `bk_of_inner`: for ANY entire `Λ` with the functional equation and reality,
     contractivity forces `Re (conj Λ(1 + 2it) · Λ'(1 + 2it)) ≥ 0` (one-sided derivative at the
     axis).  `bk_phase_identity`: `logDeriv φ_Λ (1/2 + it) = -4 Re (Λ'/Λ)(1 + 2it)`.  So
     Birman–Krein positivity is the `σ = 1` slice of the rational face and carries nothing
     beyond contractivity.
  D. THE CHANNEL NO-GO.  `ChannelAxioms Λ` = entire, functional equation, reality, the edge (no
     zero on `Re w ≥ 1`), contractivity, unimodularity on the axis, weak BK positivity.
     `channelAxioms_xi` (the real `ξ` satisfies all of them); `channelAxioms_mul_quad`,
     `channelAxioms_mul_quadList` (the class is closed under multiplying by the quadruple of ANY
     finite set of points of the open strip); `fakeXi = ξ · Q_{ρ₀}`, `fakeXi_offline_zero`;
     `channel_axioms_do_not_imply_rh`:
       `¬ ∀ Λ, ChannelAxioms Λ → every zero of Λ in the strip has Re = 1/2`.
     `channel_realizes_any_strip_zero`, `channel_zeros_in_closed_strip`, and
     `inner_forces_partner` (contractivity cannot see zeros on the edge `Re w = 1`: a zero at or
     beyond the edge must come with a partner at `w - 1`, i.e. cancel).
  E. Exchange rate (RELABELINGS, flagged; used only to price an improvement).  `xi_shift_inner`,
     `zero_free_strip_iff_shift_contractive` (for every `h₀`: all zeros in `|Re ρ - 1/2| ≤ h₀`
     iff every shift `h > h₀` is contractive; the converse direction uses countability of the
     zero set), `rh_iff_all_shifts_contractive` (Mathlib's `RiemannHypothesis`),
     `xi_unitary_channel_contractive` (`h = 1/2`, unconditional: the unitary channel is the free
     end of the family), `rh_iff_resonances_on_quarter_line` (Lax–Phillips: RH iff every
     resonance `s = ρ/2` has `Re s = 1/4`).
  F. Hecke–wave identity, scalar core: `hecke_wave`, `heckeEig` (`λ_n(s) = Σ_{ad=n} (a/d)^{s-1/2}`),
     `heckeEig_one_sub`, `heckeEig_fun_of_laplace` (on unitary AND resonant states the Hecke
     eigenvalue is a function of the Laplace eigenvalue `s(1 - s)`), `heckeEig_conj`,
     `heckeEig_real_on_axis`, `heckeEig_prime` (`λ_p(1/2 + ir) = 2 cos (r log p)`).
  G. Emergent unitarity: `finite_euler_blowup_on_axis` (every finite Euler truncation of the
     scattering matrix blows up along the unitary axis at `s = 1/2`; `|φ| = 1` is global).
  H. Hecke-orbit correction: `two_I_mem_T2`, `three_I_mem_T3`, `four_I_mem_T4`,
     `hecke_neighbour_mem`, `euler2_disc16_zeros_on_line` (the class-number-one point `2i`:
     extra Euler factor on the line), `euler3_disc36_zeros_on_line` (at the class-number-two
     point `3i` the local correction is on the line too; its certified off-line zeros come from
     the genus sum of two Euler products).

  CORRECTIONS TO THE SUBMITTED IDEA (found while building):
  * Normalisation.  The scattering matrix is `φ(s) = Λ(2s - 1)/Λ(2s)` with
    `Λ = completedRiemannZeta`; it has the pole of the residual spectrum (the constants) at
    `s = 1` and is NOT bounded on `Re s > 1/2`.  The contractive object is
    `φ_ξ(s) = φ(s) · (s - 1)/s` (`modScat_eq`, `scatXi_one_ne_zero`).
  * Contractivity of `φ_ξ` needs only zeros in the CLOSED strip, not PNT: zeros on the edge
    cancel (`inner_forces_partner`).  The PNT content of the channel is regularity on the axis,
    the `edge` field.  (The kernel proof of `xi_inner` routes through the upstream zero-set
    description, which consumes Mathlib's zero-free line; mathematically it is not needed.)
    "Unitarity = PNT" is right for the full channel data, not for contractivity alone.
  * Multiplicity: the quadruple `{ρ, conj ρ, 1 - ρ, 1 - conj ρ}` double-counts a zero on the
    line; the correct bookkeeping is an `ι`-closed multiset (section 3).
  * Hecke orbit: `2i ∈ T_2(i)` has discriminant `-16` and class number `1`, and the extra Euler
    factor `1 - 2^{-s} + 2^{1-2s}` of `x² + 4y²` has all its zeros on `Re s = 1/2`
    (`euler2_disc16_zeros_on_line`), so RH at `2i` is RH at `i`.  The Hecke orbit of `i` is not
    "`i` plus class-number `≥ 2` points": it contains exactly two class-number-one points, `i`
    and `2i` (`h(-4f²) = 1` iff `f ∈ {1, 2}`; see the research README).  The consequence drawn
    in the idea (no open or almost-everywhere property of the base point implies RH at `i`) does
    not depend on this; it rests on the base-point genericity theorem (paper proof).

  DOES NOT ESTABLISH:
  * Anything about the zeros of zeta.  RH is open; conjecture1_proved = False.
  * The infinite form for EVERY `Λ` of order one with the functional equation and reality:
    kernel-checked here only for `ξ` and for `ξ` times finitely many quadruples; the general case
    needs the paired Hadamard factorisation of an arbitrary order-one `Λ` (paper proof).
  * Realizability (every inner function is the scattering matrix of an abstract Lax–Phillips
    system; Sz.-Nagy–Foias): classical, not formalized.
  * The operator form of the Hecke–wave identity (`T_n E(·, s) = λ_n(s) E(·, s)` and the
    Eisenstein transform); only the scalar core is here.
  * Axis regularity of `E(z, s)` iff `ξ(1 + it) ≠ 0` (Sarnak): classical, not formalized.
  * Strict Birman–Krein positivity (`> 0`): only the weak form (`≥ 0`) is kernel-checked.
  * Base-point genericity (`E(x + iy, ·)` has zeros with `Re s > 1` when `x, y` are
    algebraically independent): paper proof only.
  * The genus identities at the orbit points (`Z_{x²+4y²}(s) = 2 ζ(s) L(s, χ₋₄)(1 - 2^{-s} + 2^{1-2s})`
    at `2i`, and the analogues at `3i`, `4i`): classical genus theory, checked EXACTLY on the
    Dirichlet coefficients `n ≤ 4000` and against a rigorous Fourier expansion in the research
    directory, not in the kernel.  Likewise the Arb certificates of off-line zeros at `3i`, `4i`.
-/
import Mathlib
import Lc.LiCriterion.XiOrderBridge

open Complex ComplexConjugate

noncomputable section

namespace CruxDynamicsErgodic

/-! ## 1. Gap identities -/

/-- The Blaschke gap identity for the half-plane `Re s > 1/2` (reflection `a ↦ 1 - conj a`). -/
theorem blaschke_gap (s a : ℂ) :
    Complex.normSq (s - (1 - conj a)) - Complex.normSq (s - a)
      = (2 * s.re - 1) * (2 * a.re - 1) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Doubled form of the gap identity: the scattering zero `b/2` against its pole. -/
theorem doubled_gap (b s : ℂ) :
    Complex.normSq ((2 - conj b) - 2 * s) - Complex.normSq (b - 2 * s)
      = 4 * (b.re - 1) * (2 * s.re - 1) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  norm_num
  ring

/-- The reflection in the unitary axis `Re w = 1/2`: `ι w = 1 - conj w`.  For a function with
`Λ(1 - w) = Λ(w)` and `Λ(conj w) = conj (Λ w)` it maps zeros to zeros. -/
def iota (w : ℂ) : ℂ := 1 - conj w

@[simp] lemma iota_re (w : ℂ) : (iota w).re = 1 - w.re := by simp [iota]

@[simp] lemma iota_iota (w : ℂ) : iota (iota w) = w := by simp [iota]

/-- Shifted gap identity (the Hermite–Biehler shift `h`): numerator factor `w - u + h` against
the denominator factor of the reflected zero, `ι w - u - h`. -/
theorem shifted_gap (w u : ℂ) (h : ℝ) :
    Complex.normSq (iota w - u - h) - Complex.normSq (w - u + h)
      = (2 * w.re - 1 + 2 * h) * (2 * u.re - 1) := by
  simp only [iota, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma norm_le_of_normSq_le {a b : ℂ} (h : Complex.normSq a ≤ Complex.normSq b) : ‖a‖ ≤ ‖b‖ := by
  have e1 : ‖a‖ ^ 2 = Complex.normSq a := Complex.sq_norm _
  have e2 : ‖b‖ ^ 2 = Complex.normSq b := Complex.sq_norm _
  have : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by rw [e1, e2]; exact h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

lemma norm_eq_of_normSq_eq {a b : ℂ} (h : Complex.normSq a = Complex.normSq b) : ‖a‖ = ‖b‖ := by
  have e1 : ‖a‖ ^ 2 = Complex.normSq a := Complex.sq_norm _
  have e2 : ‖b‖ ^ 2 = Complex.normSq b := Complex.sq_norm _
  have : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by rw [e1, e2, h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

theorem doubled_le {b s : ℂ} (hs : 1 / 2 ≤ s.re) (hb : 1 ≤ b.re) :
    ‖b - 2 * s‖ ≤ ‖(2 - conj b) - 2 * s‖ := by
  have h := doubled_gap b s
  have hnn : 0 ≤ 4 * (b.re - 1) * (2 * s.re - 1) := by
    apply mul_nonneg
    · apply mul_nonneg <;> linarith
    · linarith
  exact norm_le_of_normSq_le (by linarith)

theorem doubled_eq_on_line {b s : ℂ} (hs : s.re = 1 / 2) :
    ‖b - 2 * s‖ = ‖(2 - conj b) - 2 * s‖ := by
  have h := doubled_gap b s
  rw [hs] at h
  exact norm_eq_of_normSq_eq (by linarith)

/-! ## 2. The functional-equation quadruple (ported from `ResonanceEdge.lean`) -/

/-- Numerator of the quadruple factor of `φ(s) = Λ(2s-1)/Λ(2s)`:
`∏_{w ∈ {ρ, conj ρ, 1-ρ, 1-conj ρ}} (w + 1 - 2s)`. -/
def scatNum (ρ s : ℂ) : ℂ :=
  (ρ + 1 - 2 * s) * (conj ρ + 1 - 2 * s) * ((1 - ρ) + 1 - 2 * s) * ((1 - conj ρ) + 1 - 2 * s)

/-- Denominator `∏_w (w - 2s)`; its zeros are the resonances `w/2`. -/
def scatDen (ρ s : ℂ) : ℂ :=
  (ρ - 2 * s) * (conj ρ - 2 * s) * ((1 - ρ) - 2 * s) * ((1 - conj ρ) - 2 * s)

private lemma g1 (ρ : ℂ) : (2 - conj (ρ + 1)) = 1 - conj ρ := by simp [map_add]; ring
private lemma g2 (ρ : ℂ) : (2 - conj (conj ρ + 1)) = 1 - ρ := by simp [map_add]; ring
private lemma g3 (ρ : ℂ) : (2 - conj (2 - ρ)) = conj ρ := by
  apply Complex.ext <;> simp
private lemma g4 (ρ : ℂ) : (2 - conj (2 - conj ρ)) = ρ := by
  apply Complex.ext <;> simp

/-- Edge theorem, one quadruple: if `0 ≤ Re ρ ≤ 1` the quadruple factor has modulus at most one
on the closed half-plane `Re s ≥ 1/2`. -/
theorem scat_inner {ρ s : ℂ} (hs : 1 / 2 ≤ s.re) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    ‖scatNum ρ s‖ ≤ ‖scatDen ρ s‖ := by
  have k1 : ‖(ρ + 1) - 2 * s‖ ≤ ‖(1 - conj ρ) - 2 * s‖ := by
    have := doubled_le (b := ρ + 1) hs (by simp; linarith)
    rwa [g1] at this
  have k2 : ‖(conj ρ + 1) - 2 * s‖ ≤ ‖(1 - ρ) - 2 * s‖ := by
    have := doubled_le (b := conj ρ + 1) hs (by simp; linarith)
    rwa [g2] at this
  have k3 : ‖(2 - ρ) - 2 * s‖ ≤ ‖conj ρ - 2 * s‖ := by
    have := doubled_le (b := 2 - ρ) hs (by simp; linarith)
    rwa [g3] at this
  have k4 : ‖(2 - conj ρ) - 2 * s‖ ≤ ‖ρ - 2 * s‖ := by
    have := doubled_le (b := 2 - conj ρ) hs (by simp; linarith)
    rwa [g4] at this
  have eN : scatNum ρ s = ((ρ + 1) - 2 * s) * ((conj ρ + 1) - 2 * s) * ((2 - ρ) - 2 * s)
      * ((2 - conj ρ) - 2 * s) := by unfold scatNum; ring
  have eD : scatDen ρ s = ((1 - conj ρ) - 2 * s) * ((1 - ρ) - 2 * s) * (conj ρ - 2 * s)
      * (ρ - 2 * s) := by unfold scatDen; ring
  rw [eN, eD, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  gcongr

/-- On the unitary axis the quadruple factor is unimodular (no hypothesis on `ρ`). -/
theorem scat_unimodular_on_line {ρ s : ℂ} (hs : s.re = 1 / 2) :
    ‖scatNum ρ s‖ = ‖scatDen ρ s‖ := by
  have k1 := doubled_eq_on_line (b := ρ + 1) hs
  have k2 := doubled_eq_on_line (b := conj ρ + 1) hs
  have k3 := doubled_eq_on_line (b := 2 - ρ) hs
  have k4 := doubled_eq_on_line (b := 2 - conj ρ) hs
  rw [g1] at k1; rw [g2] at k2; rw [g3] at k3; rw [g4] at k4
  have eN : scatNum ρ s = ((ρ + 1) - 2 * s) * ((conj ρ + 1) - 2 * s) * ((2 - ρ) - 2 * s)
      * ((2 - conj ρ) - 2 * s) := by unfold scatNum; ring
  have eD : scatDen ρ s = ((1 - conj ρ) - 2 * s) * ((1 - ρ) - 2 * s) * (conj ρ - 2 * s)
      * (ρ - 2 * s) := by unfold scatDen; ring
  rw [eN, eD, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, k1, k2, k3, k4]

/-- Beyond the edge: if `Re ρ > 1` the quadruple factor has a pole (resonance) at `s = ρ/2`,
strictly inside `Re s > 1/2`; the numerator does not vanish there. -/
theorem scat_pole_of_re_gt_one {ρ : ℂ} (h : 1 < ρ.re) :
    1 / 2 < (ρ / 2).re ∧ scatDen ρ (ρ / 2) = 0 ∧ scatNum ρ (ρ / 2) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp; linarith
  · unfold scatDen; ring
  · unfold scatNum
    have e : (ρ + 1 - 2 * (ρ / 2)) * (conj ρ + 1 - 2 * (ρ / 2)) * ((1 - ρ) + 1 - 2 * (ρ / 2))
        * ((1 - conj ρ) + 1 - 2 * (ρ / 2))
        = (conj ρ + 1 - ρ) * (2 - 2 * ρ) * (2 - conj ρ - ρ) := by ring
    rw [e]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · intro hz; have := congrArg Complex.re hz; simp at this
    · intro hz; have := congrArg Complex.re hz; simp at this; linarith
    · intro hz; have := congrArg Complex.re hz; simp at this; linarith

/-- Single-quadruple edge characterisation: the quadruple factor is a bounded (`≤ 1`) analytic
factor on the open half-plane `Re s > 1/2` iff `0 ≤ Re ρ ≤ 1`. -/
theorem scat_edge_iff (ρ : ℂ) :
    (∀ s : ℂ, 1 / 2 < s.re → scatDen ρ s ≠ 0 ∧ ‖scatNum ρ s‖ ≤ ‖scatDen ρ s‖)
      ↔ (0 ≤ ρ.re ∧ ρ.re ≤ 1) := by
  constructor
  · intro H
    by_contra hc
    rcases not_and_or.mp hc with h0 | h1
    · rw [not_le] at h0
      have hre : 1 / 2 < ((1 - conj ρ) / 2).re := by simp; linarith
      have := (H _ hre).1
      apply this; unfold scatDen; ring
    · rw [not_le] at h1
      obtain ⟨hre, hD, -⟩ := scat_pole_of_re_gt_one h1
      exact (H _ hre).1 hD
  · rintro ⟨h0, h1⟩ s hs
    refine ⟨?_, scat_inner hs.le h0 h1⟩
    unfold scatDen
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
      (intro hz; have := congrArg Complex.re hz; simp at this; linarith)

/-- Fake-ξ control (finite form): an off-line quadruple strictly inside the critical strip,
`Re ρ = 3/4`, passes the scattering test. -/
theorem fake_offline_quadruple_is_inner :
    ∃ ρ : ℂ, ρ.re ≠ 1 / 2 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      ∀ s : ℂ, 1 / 2 < s.re → scatDen ρ s ≠ 0 ∧ ‖scatNum ρ s‖ ≤ ‖scatDen ρ s‖ := by
  refine ⟨⟨3 / 4, 20⟩, by norm_num, by norm_num, by norm_num, ?_⟩
  exact (scat_edge_iff _).mpr ⟨by norm_num, by norm_num⟩

/-- Cooked control, finite form: for any finite list of quadruple representatives in the closed
strip `0 ≤ Re ρ ≤ 1` (on-line or not), `∏ scatNum / ∏ scatDen` is contractive on `Re s ≥ 1/2`. -/
theorem scat_inner_list (L : List ℂ) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hL : ∀ ρ ∈ L, 0 ≤ ρ.re ∧ ρ.re ≤ 1) :
    ‖(L.map (fun ρ => scatNum ρ s)).prod‖ ≤ ‖(L.map (fun ρ => scatDen ρ s)).prod‖ := by
  induction L with
  | nil => simp
  | cons ρ L ih =>
    have hρ := hL ρ (by simp)
    have hL' : ∀ ρ' ∈ L, 0 ≤ ρ'.re ∧ ρ'.re ≤ 1 := fun ρ' h => hL ρ' (by simp [h])
    simp only [List.map_cons, List.prod_cons, norm_mul]
    exact mul_le_mul (scat_inner hs hρ.1 hρ.2) (ih hL') (norm_nonneg _) (norm_nonneg _)

/-- ...and unimodular on the unitary axis, for any configuration whatsoever. -/
theorem scat_unimodular_list (L : List ℂ) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖(L.map (fun ρ => scatNum ρ s)).prod‖ = ‖(L.map (fun ρ => scatDen ρ s)).prod‖ := by
  induction L with
  | nil => simp
  | cons ρ L ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    rw [scat_unimodular_on_line hs, ih]

/-! ## 3. Zero multisets with correct multiplicity, and the shifted (Hermite–Biehler) channel

A finite zero multiset is a list `Z` closed under `ι` as a multiset (`(Z.map iota).Perm Z`).
This is the right bookkeeping: a simple zero on the line is `[ρ, conj ρ]` (then `ι ρ = ρ`), not
the doubled quadruple.  For a shift `h`, the channel `Λ(u - h)/Λ(u + h)` of
`Λ(x) ∝ ∏_{w ∈ Z} (w - x)` is `chNum h Z u / chDen h Z u`.  The modular scattering matrix
`Λ(2s - 1)/Λ(2s)` is the `h = 1/2` channel at `u = 2s - 1/2` (`chNum_half`, `chDen_half`). -/

/-- Numerator of the `h`-channel: `∏_{w ∈ Z} (w - u + h)`, i.e. `Λ(u - h)` up to a constant. -/
def chNum (h : ℝ) (Z : List ℂ) (u : ℂ) : ℂ := (Z.map fun w => w - u + h).prod

/-- Denominator of the `h`-channel: `∏_{w ∈ Z} (w - u - h)`, i.e. `Λ(u + h)` up to a constant. -/
def chDen (h : ℝ) (Z : List ℂ) (u : ℂ) : ℂ := (Z.map fun w => w - u - h).prod

lemma list_norm_prod_le {α : Type*} (L : List α) (f g : α → ℂ) (h : ∀ x ∈ L, ‖f x‖ ≤ ‖g x‖) :
    ‖(L.map f).prod‖ ≤ ‖(L.map g).prod‖ := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    exact mul_le_mul (h a (by simp)) (ih fun x hx => h x (by simp [hx])) (norm_nonneg _)
      (norm_nonneg _)

lemma list_norm_prod_eq {α : Type*} (L : List α) (f g : α → ℂ) (h : ∀ x ∈ L, ‖f x‖ = ‖g x‖) :
    ‖(L.map f).prod‖ = ‖(L.map g).prod‖ := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

/-- Re-index the denominator along the involution `ι` (this is where `ι`-closure is used). -/
lemma chDen_perm {Z : List ℂ} (hZ : (Z.map iota).Perm Z) (h : ℝ) (u : ℂ) :
    chDen h Z u = (Z.map fun w => iota w - u - h).prod := by
  unfold chDen
  have := (hZ.map (fun w => w - u - h)).prod_eq
  rw [← this, List.map_map]
  rfl

/-- Termwise channel inequality. -/
lemma ch_factor_le {w u : ℂ} {h : ℝ} (hw : 1 / 2 - h ≤ w.re) (hu : 1 / 2 ≤ u.re) :
    ‖w - u + h‖ ≤ ‖iota w - u - h‖ := by
  have g := shifted_gap w u h
  have hnn : 0 ≤ (2 * w.re - 1 + 2 * h) * (2 * u.re - 1) := by
    apply mul_nonneg <;> linarith
  exact norm_le_of_normSq_le (by linarith)

lemma ch_factor_eq {w u : ℂ} {h : ℝ} (hu : u.re = 1 / 2) :
    ‖w - u + h‖ = ‖iota w - u - h‖ := by
  have g := shifted_gap w u h
  rw [hu] at g
  exact norm_eq_of_normSq_eq (by linarith)

/-- The `h`-channel is contractive on `Re u ≥ 1/2` when every zero has `Re w ≥ 1/2 - h`
(for an `ι`-closed multiset this is the strip `|Re w - 1/2| ≤ h`). -/
theorem ch_inner {Z : List ℂ} (hZ : (Z.map iota).Perm Z) {h : ℝ}
    (hw : ∀ w ∈ Z, 1 / 2 - h ≤ w.re) {u : ℂ} (hu : 1 / 2 ≤ u.re) :
    ‖chNum h Z u‖ ≤ ‖chDen h Z u‖ := by
  rw [chDen_perm hZ]
  exact list_norm_prod_le Z _ _ fun w hwZ => ch_factor_le (hw w hwZ) hu

/-- Every `h`-channel of an `ι`-closed multiset is unimodular on the unitary axis. -/
theorem ch_unimodular {Z : List ℂ} (hZ : (Z.map iota).Perm Z) (h : ℝ) {u : ℂ}
    (hu : u.re = 1 / 2) : ‖chNum h Z u‖ = ‖chDen h Z u‖ := by
  rw [chDen_perm hZ]
  exact list_norm_prod_eq Z _ _ fun w _ => ch_factor_eq hu

lemma mem_of_iota_closed {Z : List ℂ} (hZ : (Z.map iota).Perm Z) {w : ℂ} (hw : w ∈ Z) :
    iota w ∈ Z :=
  hZ.subset (List.mem_map_of_mem hw)

/-- THE DETECTION THRESHOLD.  The `h`-channel is analytic and contractive on the open half-plane
`Re u > 1/2` exactly when every zero lies in the strip `|Re w - 1/2| ≤ h`.  A zero at distance
`d = |Re w - 1/2|` from the line is seen by the `h`-channel iff `h < d`. -/
theorem ch_edge_iff {Z : List ℂ} (hZ : (Z.map iota).Perm Z) (h : ℝ) :
    (∀ u : ℂ, 1 / 2 < u.re → chDen h Z u ≠ 0 ∧ ‖chNum h Z u‖ ≤ ‖chDen h Z u‖)
      ↔ ∀ w ∈ Z, |w.re - 1 / 2| ≤ h := by
  constructor
  · intro H w hw
    by_contra hc
    rw [not_le] at hc
    -- some zero `w'` of the multiset has `Re w' > 1/2 + h`
    obtain ⟨w', hw'Z, hw're⟩ : ∃ w' ∈ Z, 1 / 2 + h < w'.re := by
      rcases lt_abs.mp hc with hpos | hneg
      · exact ⟨w, hw, by linarith⟩
      · exact ⟨iota w, mem_of_iota_closed hZ hw, by simp; linarith⟩
    have hre : 1 / 2 < (w' - h).re := by simp; linarith
    apply (H (w' - h) hre).1
    unfold chDen
    apply List.prod_eq_zero
    exact List.mem_map.mpr ⟨w', hw'Z, by ring⟩
  · intro H u hu
    refine ⟨?_, ch_inner hZ (fun w hw => by
      have := neg_abs_le (w.re - 1 / 2); have := H w hw; linarith) hu.le⟩
    unfold chDen
    intro h0
    obtain ⟨w, hwZ, hw0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    have hwre : w.re = u.re + h := by
      have := congrArg Complex.re hw0; simp at this; linarith
    have := le_abs_self (w.re - 1 / 2)
    have := H w hwZ
    linarith

/-- RH for a finite `ι`-closed zero multiset is equivalent to contractivity of EVERY shifted
channel `h > 0`.  (Finite form of the Hermite–Biehler exchange rate; a relabeling.) -/
theorem rh_finite_iff_all_channels {Z : List ℂ} (hZ : (Z.map iota).Perm Z) :
    (∀ w ∈ Z, w.re = 1 / 2) ↔
      ∀ h : ℝ, 0 < h → ∀ u : ℂ, 1 / 2 < u.re → chDen h Z u ≠ 0 ∧ ‖chNum h Z u‖ ≤ ‖chDen h Z u‖ := by
  constructor
  · intro H h hh
    refine (ch_edge_iff hZ h).mpr fun w hw => ?_
    rw [H w hw, sub_self, abs_zero]; exact hh.le
  · intro H w hw
    have key : ∀ h : ℝ, 0 < h → |w.re - 1 / 2| ≤ h := fun h hh => (ch_edge_iff hZ h).mp (H h hh) w hw
    have h0 : |w.re - 1 / 2| ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      have := key (|w.re - 1 / 2| / 2) (by linarith)
      linarith
    have := abs_nonpos_iff.mp h0
    linarith

/-- The unitary channel `h = 1/2` sees exactly the edge: contractive iff all zeros have
`0 ≤ Re w ≤ 1`.  An off-line zero strictly inside the strip is invisible to it. -/
theorem unitary_channel_iff {Z : List ℂ} (hZ : (Z.map iota).Perm Z) :
    (∀ u : ℂ, 1 / 2 < u.re → chDen (1 / 2) Z u ≠ 0 ∧ ‖chNum (1 / 2) Z u‖ ≤ ‖chDen (1 / 2) Z u‖)
      ↔ ∀ w ∈ Z, 0 ≤ w.re ∧ w.re ≤ 1 := by
  rw [ch_edge_iff hZ]
  refine forall₂_congr fun w _ => ?_
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- In the variable `u = 2s - 1/2` the unitary channel is the modular scattering matrix
`∏ (w + 1 - 2s) / ∏ (w - 2s) = Λ(2s - 1)/Λ(2s)`. -/
theorem chNum_half (Z : List ℂ) (s : ℂ) :
    chNum (1 / 2) Z (2 * s - 1 / 2) = (Z.map fun w => w + 1 - 2 * s).prod := by
  unfold chNum; congr 1; apply List.map_congr_left; intro w _; push_cast; ring

theorem chDen_half (Z : List ℂ) (s : ℂ) :
    chDen (1 / 2) Z (2 * s - 1 / 2) = (Z.map fun w => w - 2 * s).prod := by
  unfold chDen; congr 1; apply List.map_congr_left; intro w _; push_cast; ring

/-- The functional-equation quadruple as a zero multiset. -/
def quadList (ρ : ℂ) : List ℂ := [ρ, conj ρ, 1 - ρ, 1 - conj ρ]

theorem quadList_iota_closed (ρ : ℂ) : ((quadList ρ).map iota).Perm (quadList ρ) := by
  have e : (quadList ρ).map iota = (quadList ρ).reverse := by
    simp only [quadList, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, iota, map_sub, map_one, Complex.conj_conj]
    simp only [sub_sub_cancel]
  rw [e]
  exact List.reverse_perm _

/-- A simple zero ON the line is the pair `[ρ, conj ρ]`, fixed pointwise by `ι`. -/
def pairList (γ : ℝ) : List ℂ := [1 / 2 + γ * I, 1 / 2 - γ * I]

theorem pairList_iota_closed (γ : ℝ) : ((pairList γ).map iota).Perm (pairList γ) := by
  have e : (pairList γ).map iota = pairList γ := by
    simp only [pairList, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    constructor <;> apply Complex.ext <;> simp [iota] <;> norm_num
  rw [e]

/-- The cooked quadruple `ρ₀ = 3/4 + 20 i` against the `h`-channels: contractive iff `h ≥ 1/4`.
So the unitary channel (`h = 1/2`) is blind to it and every channel `h < 1/4` detects it. -/
theorem cooked_quadruple_threshold (h : ℝ) :
    (∀ u : ℂ, 1 / 2 < u.re →
        chDen h (quadList (3 / 4 + 20 * I)) u ≠ 0 ∧
          ‖chNum h (quadList (3 / 4 + 20 * I)) u‖ ≤ ‖chDen h (quadList (3 / 4 + 20 * I)) u‖)
      ↔ 1 / 4 ≤ h := by
  rw [ch_edge_iff (quadList_iota_closed _)]
  simp only [quadList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  have r1 : ((3 / 4 : ℂ) + 20 * I).re = 3 / 4 := by simp
  have r2 : (conj ((3 / 4 : ℂ) + 20 * I)).re = 3 / 4 := by rw [Complex.conj_re]; simp
  have r3 : (1 - ((3 / 4 : ℂ) + 20 * I)).re = 1 / 4 := by simp; norm_num
  have r4 : (1 - conj ((3 / 4 : ℂ) + 20 * I)).re = 1 / 4 := by
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; simp; norm_num
  rw [r1, r2, r3, r4]
  have a1 : |(3 / 4 : ℝ) - 1 / 2| = 1 / 4 := by norm_num [abs_of_pos]
  have a2 : |(1 / 4 : ℝ) - 1 / 2| = 1 / 4 := by norm_num [abs_of_neg]
  rw [a1, a2]
  tauto

/-! ## 4. The real `ξ`: the modular scattering matrix is contractive (kernel-checked, via the
upstream genus-one Hadamard factorization of LiCriterion) -/

section RealXi

open LiCriterion

/-- Gap identity behind the real-`ξ` edge theorem: reflecting `v` in the imaginary axis. -/
theorem axis_gap (a v : ℂ) :
    Complex.normSq (a + conj v) - Complex.normSq (a - v) = 4 * a.re * v.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

lemma axis_le {a v : ℂ} (ha : 0 ≤ a.re) (hv : 0 ≤ v.re) : ‖a - v‖ ≤ ‖a + conj v‖ := by
  have g := axis_gap a v
  have : 0 ≤ 4 * a.re * v.re := by positivity
  exact norm_le_of_normSq_le (by linarith)

lemma one_sub_div_le {a v : ℂ} (ha0 : a ≠ 0) (ha : 0 ≤ a.re) (hv : 0 ≤ v.re) :
    ‖1 - v / a‖ ≤ ‖1 - (-conj v) / a‖ := by
  have e1 : 1 - v / a = (a - v) / a := by field_simp
  have e2 : 1 - (-conj v) / a = (a + conj v) / a := by field_simp; ring
  rw [e1, e2, norm_div, norm_div]
  exact div_le_div_of_nonneg_right (axis_le ha hv) (norm_nonneg _)

/-- Termwise edge inequality for the paired linear factor `(1 - v/ρ)(1 - v/(1-ρ))` of the
upstream Hadamard product: for `Re v ≥ 0` it is dominated by its value at `-conj v`. -/
lemma pairedFactor_le (ρ : NontrivialZero) {v : ℂ} (hv : 0 ≤ v.re) :
    ‖xiPairedLinearFactor ρ v‖ ≤ ‖xiPairedLinearFactor ρ (-conj v)‖ := by
  unfold xiPairedLinearFactor
  rw [norm_mul, norm_mul]
  exact mul_le_mul (one_sub_div_le ρ.ne_zero ρ.property.2.1.le hv)
    (one_sub_div_le (pairedZero ρ).ne_zero (pairedZero ρ).property.2.1.le hv)
    (norm_nonneg _) (norm_nonneg _)

/-- Comparison of infinite products by the modulus of their factors. -/
lemma norm_tprod_le {ι : Type*} {f g : ι → ℂ} (hf : Multipliable f) (hg : Multipliable g)
    (h : ∀ i, ‖f i‖ ≤ ‖g i‖) : ‖∏' i, f i‖ ≤ ‖∏' i, g i‖ :=
  le_of_tendsto_of_tendsto' hf.hasProd.norm hg.hasProd.norm
    (fun _ => Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => h i))

/-- `ξ` does not vanish on the closed half-plane `Re w ≥ 1` (the edge; Mathlib's zero-free line,
routed through the upstream zero-set description). -/
theorem xi_ne_zero_of_one_le_re {w : ℂ} (hw : 1 ≤ w.re) : riemannXi w ≠ 0 := by
  intro h0
  obtain ⟨ρ, hρ⟩ := (xi_zeros_are_nontrivial_zeros w).1 h0
  have h1 : ρ.val.re < 1 := ρ.property.2.2
  have : w.re = ρ.val.re := by rw [hρ]
  linarith

lemma xi_norm_conj (w : ℂ) : ‖riemannXi (conj w)‖ = ‖riemannXi w‖ := by
  rw [riemannXi_conj, Complex.norm_conj]

/-- `‖ξ(2s)‖ = ‖ξ(-conj (2s - 1))‖`: functional equation plus reality. -/
lemma xi_two_mul_norm (s : ℂ) : ‖riemannXi (2 * s)‖ = ‖riemannXi (-conj (2 * s - 1))‖ := by
  have h1 : riemannXi (2 * s) = riemannXi (-(2 * s - 1)) := by
    rw [xi_functional_equation (2 * s)]; congr 1; ring
  rw [h1, ← xi_norm_conj (-(2 * s - 1)), map_neg]

/-- THE EDGE THEOREM FOR THE REAL `ξ` (kernel-checked).  The entire-`ξ` normalisation of the
modular scattering matrix, `φ_ξ(s) = ξ(2s - 1)/ξ(2s)`, is contractive on the closed half-plane:
`‖ξ(2s - 1)‖ ≤ ‖ξ(2s)‖` for `Re s ≥ 1/2`.
Proof: the upstream paired genus-one factorisation `ξ(s)^2 = e^{b} ∏ (1 - s/ρ)(1 - s/(1-ρ))`
(no exponential factor in `s`; this is where the functional equation enters), the reflection
`‖ξ(2s)‖ = ‖ξ(-conj v)‖` with `v = 2s - 1`, and the termwise gap
`|ρ + conj v|^2 - |ρ - v|^2 = 4 Re ρ Re v ≥ 0` for zeros in the strip. -/
theorem xi_inner {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖riemannXi (2 * s - 1)‖ ≤ ‖riemannXi (2 * s)‖ := by
  have hgenus := xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one
  have hhad := xi_factorization_prod_with_multiplicity_of_hadamard_order_one xi_hasFiniteOrder
    xi_order_le_one
  obtain ⟨b₂, hfac⟩ := xi_sq_factorization_pairedLinear_withMultiplicity_of_weighted_genus
    hgenus hhad
  have hg' := summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus hgenus
  have hv : 0 ≤ (2 * s - 1).re := by simp; linarith
  rw [xi_two_mul_norm s]
  have hsq : ‖riemannXi (2 * s - 1)‖ ^ 2 ≤ ‖riemannXi (-conj (2 * s - 1))‖ ^ 2 := by
    rw [← norm_pow, ← norm_pow, hfac, hfac, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_tprod_le (multipliable_xiPairedLinearFactor_withMultiplicity_of_genus_one _ hg')
        (multipliable_xiPairedLinearFactor_withMultiplicity_of_genus_one _ hg')
        (fun i => pairedFactor_le i.1 hv)) (norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Unitarity on the axis holds for EVERY function with the functional equation and reality. -/
theorem unitary_of_fe_real {Λ : ℂ → ℂ} (hfe : ∀ w, Λ (1 - w) = Λ w)
    (hre : ∀ w, Λ (conj w) = conj (Λ w)) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖Λ (2 * s - 1)‖ = ‖Λ (2 * s)‖ := by
  have e : 2 * s - 1 = conj (1 - 2 * s) := by
    apply Complex.ext <;> simp [hs]
  rw [e, hre, Complex.norm_conj, ← hfe (2 * s)]

theorem xi_unitary {s : ℂ} (hs : s.re = 1 / 2) : ‖riemannXi (2 * s - 1)‖ = ‖riemannXi (2 * s)‖ :=
  unitary_of_fe_real (fun w => (xi_functional_equation w).symm) riemannXi_conj hs

/-- The entire-`ξ` normalisation of the modular scattering matrix. -/
def scatXi (s : ℂ) : ℂ := riemannXi (2 * s - 1) / riemannXi (2 * s)

theorem scatXi_denom_ne_zero {s : ℂ} (hs : 1 / 2 ≤ s.re) : riemannXi (2 * s) ≠ 0 :=
  xi_ne_zero_of_one_le_re (by simp; linarith)

/-- `φ_ξ` is contractive on the closed half-plane `Re s ≥ 1/2`. -/
theorem scatXi_norm_le_one {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖scatXi s‖ ≤ 1 := by
  unfold scatXi
  rw [norm_div]
  exact div_le_one_of_le₀ (xi_inner hs) (norm_nonneg _)

/-- `φ_ξ` is unimodular on the unitary axis. -/
theorem scatXi_norm_eq_one {s : ℂ} (hs : s.re = 1 / 2) : ‖scatXi s‖ = 1 := by
  unfold scatXi
  rw [norm_div, xi_unitary hs]
  exact div_self (norm_ne_zero_iff.mpr (scatXi_denom_ne_zero hs.ge))

/-- `φ_ξ` is holomorphic at every point of the closed half-plane `Re s ≥ 1/2`. -/
theorem scatXi_differentiableAt {s : ℂ} (hs : 1 / 2 ≤ s.re) : DifferentiableAt ℂ scatXi s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => riemannXi (2 * s - 1)) s :=
    (xi_entire _).comp s (((differentiableAt_id.const_mul 2)).sub_const 1)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => riemannXi (2 * s)) s :=
    (xi_entire _).comp s (differentiableAt_id.const_mul 2)
  exact h1.div h2 (scatXi_denom_ne_zero hs)

/-- `ξ = (1/2) w (w - 1) Λ(w)` away from the poles of `Λ = completedRiemannZeta`. -/
lemma xi_eq_completed {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    riemannXi w = (1 / 2 : ℂ) * w * (w - 1) * completedRiemannZeta w := by
  have h1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : w - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold riemannXi
  rw [completedRiemannZeta_eq]
  field_simp
  ring

/-- CORRECTION (normalisation).  The Eisenstein scattering matrix of `PSL(2,ℤ)` is
`φ(s) = Λ(2s - 1)/Λ(2s)` with `Λ = completedRiemannZeta`; it equals `s/(s - 1) · φ_ξ(s)`.  So
`φ` itself has the pole of the residual spectrum at `s = 1` (the constants) and is not bounded on
`Re s > 1/2`; the contractive object is `φ(s) · (s - 1)/s = φ_ξ(s)`, i.e. `φ` with the Blaschke
factor of its residual pole divided out. -/
theorem modScat_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs2 : 2 * s - 1 ≠ 0) :
    completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s) * ((s - 1) / s)
      = scatXi s := by
  have a0 : 2 * s ≠ 0 := mul_ne_zero two_ne_zero hs0
  have a1 : 2 * s ≠ 1 := fun h => hs2 (by rw [h]; norm_num)
  have b1 : 2 * s - 1 ≠ 1 := fun h => hs1 (by linear_combination h / 2)
  unfold scatXi
  rw [xi_eq_completed hs2 b1, xi_eq_completed a0 a1]
  by_cases hΛ : completedRiemannZeta (2 * s) = 0
  · simp [hΛ]
  · have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    ring

/-- ...and `φ_ξ(1) = ξ(1)/ξ(2) ≠ 0`, so `φ = s/(s-1) · φ_ξ` has a genuine pole at `s = 1`. -/
theorem scatXi_one_ne_zero : scatXi 1 ≠ 0 := by
  unfold scatXi
  refine div_ne_zero ?_ (xi_ne_zero_of_one_le_re (by norm_num))
  norm_num
  unfold riemannXi
  norm_num

end RealXi

/-! ## 5. Birman–Krein positivity is forced by contractivity (general lemma) -/

section BirmanKrein

/-- Derivative form of the functional equation. -/
lemma deriv_fe {Λ : ℂ → ℂ} (hd : Differentiable ℂ Λ) (hfe : ∀ w, Λ (1 - w) = Λ w) (w : ℂ) :
    deriv Λ w = -deriv Λ (1 - w) := by
  have hin : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (1 : ℂ)
  have h1 : HasDerivAt (fun z => Λ (1 - z)) (deriv Λ (1 - w) * (-1)) w :=
    (hd (1 - w)).hasDerivAt.comp w hin
  have h2 : (fun z => Λ (1 - z)) = Λ := funext hfe
  rw [h2] at h1
  rw [h1.deriv]
  ring

/-- Derivative form of reality. -/
lemma deriv_real {Λ : ℂ → ℂ} (hd : Differentiable ℂ Λ) (hre : ∀ w, Λ (conj w) = conj (Λ w))
    (z : ℂ) : deriv Λ (conj z) = conj (deriv Λ z) := by
  have h1 := (hd z).hasDerivAt.conj_conj
  have h2 : (conj ∘ Λ ∘ conj) = Λ := by
    funext w; simp [Function.comp, hre]
  rw [h2] at h1
  exact h1.deriv

/-- A one-sided maximum at the left end forces a nonpositive derivative. -/
lemma deriv_nonpos_of_right_max {F : ℝ → ℝ} {F' x : ℝ} (hF : HasDerivAt F F' x)
    (hle : ∀ y, x < y → F y ≤ F x) : F' ≤ 0 := by
  have h := hF.hasDerivWithinAt (s := Set.Ioi x)
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi x) (by simp)] at h
  apply le_of_tendsto h
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [hle y hy]) (by linarith [Set.mem_Ioi.mp hy])

/-- WEAK BIRMAN–KREIN POSITIVITY FROM CONTRACTIVITY.  For any entire `Λ` with the functional
equation and reality, contractivity `‖Λ(2s-1)‖ ≤ ‖Λ(2s)‖` on `Re s ≥ 1/2` forces
`Re (conj Λ(1 + 2it) · Λ'(1 + 2it)) ≥ 0` for every real `t`, i.e. `Re Λ'/Λ ≥ 0` on the line
`Re w = 1` (the `σ = 1` slice of the rational face).  So Birman–Krein positivity carries no
information beyond contractivity. -/
theorem bk_of_inner {Λ : ℂ → ℂ} (hd : Differentiable ℂ Λ) (hfe : ∀ w, Λ (1 - w) = Λ w)
    (hre : ∀ w, Λ (conj w) = conj (Λ w))
    (hin : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖Λ (2 * s - 1)‖ ≤ ‖Λ (2 * s)‖) (t : ℝ) :
    0 ≤ (conj (Λ (1 + 2 * t * I)) * deriv Λ (1 + 2 * t * I)).re := by
  set a : ℂ := 1 + 2 * t * I with ha
  set b : ℂ := 2 * t * I with hb
  have hca : conj a = 1 - b := by
    rw [ha, hb]; apply Complex.ext <;> simp
  have hvalb : Λ b = conj (Λ a) := by
    rw [← hre, hca, hfe]
  have hderb : deriv Λ b = -conj (deriv Λ a) := by
    rw [deriv_fe hd hfe b, ← hca, deriv_real hd hre]
  have hinner : ∀ c : ℂ, ∀ z : ℂ, HasDerivAt (fun z : ℂ => 2 * (z + t * I) - c) 2 z := by
    intro c z
    simpa using (((hasDerivAt_id z).add_const (t * I)).const_mul (2 : ℂ)).sub_const c
  have hpt1 : 2 * (((1 / 2 : ℝ) : ℂ) + t * I) - 1 = b := by rw [hb]; push_cast; ring
  have hpt2 : 2 * (((1 / 2 : ℝ) : ℂ) + t * I) - 0 = a := by rw [ha]; push_cast; ring
  have hD1 : HasDerivAt (fun σ : ℝ => Λ (2 * ((σ : ℂ) + t * I) - 1)) (deriv Λ b * 2) (1 / 2) := by
    have h := (hd (2 * (((1 / 2 : ℝ) : ℂ) + t * I) - 1)).hasDerivAt.comp
      (((1 / 2 : ℝ) : ℂ)) (hinner 1 _)
    rw [hpt1] at h
    exact h.comp_ofReal
  have hD2 : HasDerivAt (fun σ : ℝ => Λ (2 * ((σ : ℂ) + t * I) - 0)) (deriv Λ a * 2) (1 / 2) := by
    have h := (hd (2 * (((1 / 2 : ℝ) : ℂ) + t * I) - 0)).hasDerivAt.comp
      (((1 / 2 : ℝ) : ℂ)) (hinner 0 _)
    rw [hpt2] at h
    exact h.comp_ofReal
  have hF := hD1.norm_sq.sub hD2.norm_sq
  set F : ℝ → ℝ := fun σ => ‖Λ (2 * ((σ : ℂ) + t * I) - 1)‖ ^ 2
    - ‖Λ (2 * ((σ : ℂ) + t * I) - 0)‖ ^ 2 with hFdef
  have hF0 : F (1 / 2) = 0 := by
    simp only [hFdef, hpt1, hpt2, hvalb, Complex.norm_conj, sub_self]
  have hle : ∀ y : ℝ, 1 / 2 < y → F y ≤ F (1 / 2) := by
    intro y hy
    rw [hF0]
    have h := hin ((y : ℂ) + t * I) (by simp; linarith)
    simp only [hFdef, sub_zero]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have e : (2 : ℂ) * ((y : ℂ) + t * I) - 1 = 2 * ((y : ℂ) + t * I) - 1 := rfl
    linarith
  have hneg := deriv_nonpos_of_right_max hF hle
  simp only [hpt1, hpt2, hvalb, hderb, Complex.inner] at hneg
  have key : ((-conj (deriv Λ a) * 2 * conj (conj (Λ a))).re)
      = -2 * (conj (Λ a) * deriv Λ a).re := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
      Complex.mul_im]
    norm_num
    ring
  have key2 : ((deriv Λ a * 2 * conj (Λ a)).re) = 2 * (conj (Λ a) * deriv Λ a).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    norm_num
    ring
  rw [key, key2] at hneg
  linarith

end BirmanKrein

/-! ## 6. The cooked control with the REAL `ξ`, and the channel no-go -/

section NoGo

open LiCriterion

/-- The functional-equation quadruple as a polynomial: `∏_{w' ∈ {ρ, conj ρ, 1-ρ, 1-conj ρ}} (w - w')`. -/
def quadPoly (ρ w : ℂ) : ℂ := (w - ρ) * (w - conj ρ) * (w - (1 - ρ)) * (w - (1 - conj ρ))

lemma quadPoly_one_sub (ρ w : ℂ) : quadPoly ρ (1 - w) = quadPoly ρ w := by
  unfold quadPoly; ring

lemma quadPoly_conj (ρ w : ℂ) : quadPoly ρ (conj w) = conj (quadPoly ρ w) := by
  unfold quadPoly; simp only [map_mul, map_sub, map_one, Complex.conj_conj]; ring

lemma quadPoly_scatNum (ρ s : ℂ) : quadPoly ρ (2 * s - 1) = scatNum ρ s := by
  unfold quadPoly scatNum; ring

lemma quadPoly_scatDen (ρ s : ℂ) : quadPoly ρ (2 * s) = scatDen ρ s := by
  unfold quadPoly scatDen; ring

lemma quadPoly_self (ρ : ℂ) : quadPoly ρ ρ = 0 := by
  unfold quadPoly; ring

lemma quadPoly_differentiable (ρ : ℂ) : Differentiable ℂ (quadPoly ρ) := by
  unfold quadPoly; fun_prop

lemma quadPoly_ne_zero {ρ w : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hw : 1 ≤ w.re) :
    quadPoly ρ w ≠ 0 := by
  unfold quadPoly
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
    (intro hz; have := congrArg Complex.re hz; simp at this; linarith)

/-- THE CHANNEL AXIOMS: everything the unitary scattering channel of the modular surface
records about `Λ` -- entire, functional equation, reality, the edge (no zero on `Re w ≥ 1`,
i.e. regular Eisenstein data on the unitary axis), contractivity of `φ_Λ(s) = Λ(2s-1)/Λ(2s)` on
`Re s ≥ 1/2`, unimodularity on the axis, and (weak) Birman–Krein positivity. -/
structure ChannelAxioms (Λ : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ Λ
  fe : ∀ w, Λ (1 - w) = Λ w
  real : ∀ w, Λ (conj w) = conj (Λ w)
  edge : ∀ w : ℂ, 1 ≤ w.re → Λ w ≠ 0
  inner : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖Λ (2 * s - 1)‖ ≤ ‖Λ (2 * s)‖
  unitary : ∀ s : ℂ, s.re = 1 / 2 → ‖Λ (2 * s - 1)‖ = ‖Λ (2 * s)‖
  bk : ∀ t : ℝ, 0 ≤ (conj (Λ (1 + 2 * t * I)) * deriv Λ (1 + 2 * t * I)).re

/-- The real `ξ` satisfies every channel axiom (kernel-checked; the contractivity field is
`xi_inner`, which rests on the upstream Hadamard factorisation). -/
theorem channelAxioms_xi : ChannelAxioms riemannXi where
  entire := xi_entire
  fe := fun w => (xi_functional_equation w).symm
  real := riemannXi_conj
  edge := fun _ hw => xi_ne_zero_of_one_le_re hw
  inner := fun _ hs => xi_inner hs
  unitary := fun _ hs => xi_unitary hs
  bk := bk_of_inner xi_entire (fun w => (xi_functional_equation w).symm) riemannXi_conj
    (fun _ hs => xi_inner hs)

/-- CLOSURE UNDER COOKED QUADRUPLES.  Multiplying by the quadruple of ANY `ρ` in the open strip
(on the line or not) preserves every channel axiom. -/
theorem channelAxioms_mul_quad {Λ : ℂ → ℂ} (hΛ : ChannelAxioms Λ) {ρ : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : ChannelAxioms (fun w => Λ w * quadPoly ρ w) := by
  have hent : Differentiable ℂ (fun w => Λ w * quadPoly ρ w) :=
    hΛ.entire.mul (quadPoly_differentiable ρ)
  have hfe : ∀ w, Λ (1 - w) * quadPoly ρ (1 - w) = Λ w * quadPoly ρ w := by
    intro w; rw [hΛ.fe, quadPoly_one_sub]
  have hre : ∀ w, Λ (conj w) * quadPoly ρ (conj w) = conj (Λ w * quadPoly ρ w) := by
    intro w; rw [hΛ.real, quadPoly_conj, map_mul]
  have hin : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖Λ (2 * s - 1) * quadPoly ρ (2 * s - 1)‖ ≤ ‖Λ (2 * s) * quadPoly ρ (2 * s)‖ := by
    intro s hs
    rw [norm_mul, norm_mul, quadPoly_scatNum, quadPoly_scatDen]
    exact mul_le_mul (hΛ.inner s hs) (scat_inner hs h0.le h1.le) (norm_nonneg _) (norm_nonneg _)
  refine ⟨hent, hfe, hre, ?_, hin, ?_, bk_of_inner hent hfe hre hin⟩
  · intro w hw
    exact mul_ne_zero (hΛ.edge w hw) (quadPoly_ne_zero h0 h1 hw)
  · intro s hs
    rw [norm_mul, norm_mul, hΛ.unitary s hs, quadPoly_scatNum, quadPoly_scatDen,
      scat_unimodular_on_line hs]

/-- The cooked point. -/
def rho0 : ℂ := 3 / 4 + 20 * I

lemma rho0_re : rho0.re = 3 / 4 := by simp [rho0]

/-- The fake `ξ`: the real `ξ` times the cooked quadruple of `ρ₀ = 3/4 + 20 i`. -/
def fakeXi (w : ℂ) : ℂ := riemannXi w * quadPoly rho0 w

/-- The fake passes every channel axiom... -/
theorem channelAxioms_fakeXi : ChannelAxioms fakeXi :=
  channelAxioms_mul_quad channelAxioms_xi (by rw [rho0_re]; norm_num) (by rw [rho0_re]; norm_num)

/-- ...and has a zero OFF the critical line, strictly inside the strip. -/
theorem fakeXi_offline_zero : fakeXi rho0 = 0 ∧ rho0.re ≠ 1 / 2 ∧ 0 < rho0.re ∧ rho0.re < 1 := by
  refine ⟨by simp [fakeXi, quadPoly_self], ?_, ?_, ?_⟩ <;> rw [rho0_re] <;> norm_num

/-- THE CHANNEL NO-GO (kernel-checked).  No argument that uses only the channel axioms can place
the zeros in the strip on the critical line: the axioms hold for the real `ξ` and for the fake
`ξ · Q_{ρ₀}`, which has the zero `ρ₀ = 3/4 + 20 i`. -/
theorem channel_axioms_do_not_imply_rh :
    ¬ ∀ Λ : ℂ → ℂ, ChannelAxioms Λ → ∀ w : ℂ, Λ w = 0 → 0 < w.re → w.re < 1 → w.re = 1 / 2 := by
  intro H
  obtain ⟨hz, hne, hpos, hlt⟩ := fakeXi_offline_zero
  exact hne (H fakeXi channelAxioms_fakeXi rho0 hz hpos hlt)

/-- General form: for every `ρ` in the open strip there is a channel-admissible `Λ` vanishing at
`ρ`, namely `ξ · Q_ρ`. -/
theorem channel_realizes_any_strip_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ Λ : ℂ → ℂ, ChannelAxioms Λ ∧ Λ ρ = 0 :=
  ⟨fun w => riemannXi w * quadPoly ρ w, channelAxioms_mul_quad channelAxioms_xi h0 h1,
    by simp [quadPoly_self]⟩

/-- The edge is exactly what the channel sees: a channel-admissible `Λ` has all its zeros in the
closed strip `0 ≤ Re w ≤ 1` (the `edge` field plus the functional equation). -/
theorem channel_zeros_in_closed_strip {Λ : ℂ → ℂ} (hΛ : ChannelAxioms Λ) {w : ℂ} (hw : Λ w = 0) :
    0 < w.re ∧ w.re < 1 := by
  constructor
  · by_contra hc
    rw [not_lt] at hc
    apply hΛ.edge (1 - w) (by simp; linarith)
    rw [hΛ.fe, hw]
  · by_contra hc
    rw [not_lt] at hc
    exact hΛ.edge w hc hw

end NoGo

/-! ## 7. The Hecke–wave identity (scalar core): Hecke operators on the Eisenstein channel are
functions of the Laplacian -/

section Hecke

/-- `T_p` on the unitary Eisenstein series `E(·, 1/2 + ir)`: `p^{ir} + p^{-ir} = 2 cos (r log p)`,
i.e. `T_p = 2 cos (log p · √(Δ - 1/4))` on the continuous spectrum. -/
theorem hecke_wave (p r : ℝ) (hp : 0 < p) :
    (p : ℂ) ^ ((r : ℂ) * I) + (p : ℂ) ^ (-((r : ℂ) * I)) = 2 * Real.cos (r * Real.log p) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp', Complex.cpow_def_of_ne_zero hp',
    ← Complex.ofReal_log hp.le]
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The normalised Hecke eigenvalue of `E(·, s)` under `T_n`:
`λ_n(s) = Σ_{ad = n} (a/d)^{s - 1/2} = n^{1/2 - s} σ_{2s-1}(n)`.  It is defined for every complex
`s`, so it covers the unitary states (`s = 1/2 + ir`) and the resonant states (`s = ρ/2`). -/
def heckeEig (n : ℕ) (s : ℂ) : ℂ :=
  ∑ x ∈ n.divisorsAntidiagonal, (((x.1 : ℝ) / (x.2 : ℝ) : ℝ) : ℂ) ^ (s - 1 / 2)

lemma ofReal_inv_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) : ((x⁻¹ : ℝ) : ℂ) ^ z = (x : ℂ) ^ (-z) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne), Complex.cpow_neg]

/-- `λ_n(1 - s) = λ_n(s)`: the Hecke eigenvalue is invariant under the functional-equation
involution of the spectral parameter (swap `a ↔ d`). -/
theorem heckeEig_one_sub (n : ℕ) (s : ℂ) : heckeEig n (1 - s) = heckeEig n s := by
  unfold heckeEig
  refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun x => ?_) (fun x hx => ?_)
  · simp [Nat.swap_mem_divisorsAntidiagonal]
  · have h1 : (0 : ℝ) < x.1 := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
    have h2 : (0 : ℝ) < x.2 := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [show ((x.2 : ℝ) / (x.1 : ℝ)) = ((x.1 : ℝ) / (x.2 : ℝ))⁻¹ by rw [inv_div],
      ofReal_inv_cpow (by positivity)]
    congr 1
    ring

/-- HECKE LOOPHOLE CLOSED (scalar core).  On every Eisenstein state `E(·, s)` -- unitary or
resonant -- the `T_n`-eigenvalue is a function of the Laplace eigenvalue `s(1 - s)` alone.  So
Hecke-equivariant statements on the scattering channel are statements about the functional
calculus of `Δ`. -/
theorem heckeEig_fun_of_laplace (n : ℕ) :
    ∃ G : ℂ → ℂ, ∀ s : ℂ, heckeEig n s = G (s * (1 - s)) := by
  refine ⟨fun lam => heckeEig n (1 / 2 + (1 / 4 - lam) ^ ((2 : ℂ)⁻¹)), fun s => ?_⟩
  set r : ℂ := (1 / 4 - s * (1 - s)) ^ ((2 : ℂ)⁻¹) with hr
  have hsq : r ^ 2 = (s - 1 / 2) ^ 2 := by
    rw [hr, Complex.cpow_ofNat_inv_pow]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · show heckeEig n s = heckeEig n (1 / 2 + r)
    rw [h]; congr 1; ring
  · show heckeEig n s = heckeEig n (1 / 2 + r)
    rw [h, show (1 / 2 : ℂ) + -(s - 1 / 2) = 1 - s by ring, heckeEig_one_sub]

/-- Conjugation of the spectral parameter. -/
theorem heckeEig_conj (n : ℕ) (s : ℂ) : conj (heckeEig n s) = heckeEig n (conj s) := by
  unfold heckeEig
  rw [map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h1 : (0 : ℝ) < x.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
  have h2 : (0 : ℝ) < x.2 := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)
  have hq : (0 : ℝ) < (x.1 : ℝ) / (x.2 : ℝ) := by positivity
  have harg : (((x.1 : ℝ) / (x.2 : ℝ) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hq.le]; exact Real.pi_pos.ne
  have := Complex.conj_cpow (((x.1 : ℝ) / (x.2 : ℝ) : ℝ) : ℂ) (conj s - 1 / 2) harg
  rw [Complex.conj_ofReal] at this
  rw [this]
  congr 2
  apply Complex.ext <;> simp

/-- On the unitary axis the Hecke eigenvalue is real. -/
theorem heckeEig_real_on_axis (n : ℕ) (r : ℝ) :
    conj (heckeEig n (1 / 2 + r * I)) = heckeEig n (1 / 2 + r * I) := by
  rw [heckeEig_conj, ← heckeEig_one_sub n (1 / 2 + r * I)]
  congr 1
  apply Complex.ext <;> norm_num

/-- For a prime `p`, `λ_p(1/2 + ir) = 2 cos (r log p)`. -/
theorem heckeEig_prime (p : ℕ) (hp : p.Prime) (r : ℝ) :
    heckeEig p (1 / 2 + r * I) = 2 * Real.cos (r * Real.log p) := by
  unfold heckeEig
  rw [Nat.sum_divisorsAntidiagonal (fun a d => (((a : ℝ) / (d : ℝ) : ℝ) : ℂ) ^ (1 / 2 + r * I - 1 / 2)),
    Nat.Prime.divisors hp, Finset.sum_pair (Ne.symm hp.one_lt.ne')]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Nat.div_one, Nat.div_self hp.pos]
  simp only [Nat.cast_one, one_div, div_one]
  rw [ofReal_inv_cpow hp0, show (2 : ℂ)⁻¹ + r * I - 2⁻¹ = (r : ℂ) * I by ring, add_comm]
  exact hecke_wave p r hp0

end Hecke

/-! ## 8. Emergent unitarity: no finite Euler truncation of `φ` is unimodular -/

section Emergent

open Filter Topology

/-- Local (Gindikin–Karpelevich) factor of the scattering matrix at a prime `p`. -/
def localC (p : ℕ) (s : ℂ) : ℂ := (1 - (p : ℂ) ^ (-2 * s)) / (1 - (p : ℂ) ^ (1 - 2 * s))

lemma localC_axis (p : ℕ) (t : ℝ) :
    localC p (1 / 2 + t * I) = (1 - (p : ℂ) ^ (-1 - 2 * (t : ℂ) * I)) /
      (1 - (p : ℂ) ^ (-(2 * (t : ℂ) * I))) := by
  unfold localC
  congr 3 <;> ring

/-- A local factor has its pole exactly where `p^{-2it} = 1`; near `t = 0` only at `t = 0`. -/
lemma local_den_ne_zero (p : ℕ) (hp : 2 ≤ p) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, 1 - (p : ℂ) ^ (-(2 * (t : ℂ) * I)) ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hball : Set.Ioo (-(Real.pi / Real.log p)) (Real.pi / Real.log p) ∈ 𝓝 (0 : ℝ) := by
    apply Ioo_mem_nhds <;> [linarith [div_pos Real.pi_pos hlog]; exact div_pos Real.pi_pos hlog]
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with t ht ht0
  intro h0
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have h1 : Complex.exp (Complex.log p * (-(2 * (t : ℂ) * I))) = 1 := by
    rw [← Complex.cpow_def_of_ne_zero hp0]; linear_combination -h0
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  have hlogp : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_log (by positivity)]
  rw [hlogp] at hk
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
    Complex.re_ofNat, Complex.im_ofNat] at him
  -- him : Real.log p * -(2 * t) = k * (2 * π)   (after normalisation)
  have him' : Real.log p * t = -(k * Real.pi) := by nlinarith [him]
  have ht0' : t ≠ 0 := ht0
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, neg_zero] at him'
    rcases mul_eq_zero.mp him' with h | h
    · linarith
    · exact ht0' h
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
  have hteq : t = -(k * Real.pi) / Real.log p := by
    field_simp; linarith
  have habs : Real.pi / Real.log p ≤ |t| := by
    rw [hteq, abs_div, abs_neg, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hlog.le
  rcases ht with ⟨hl, hr⟩
  rcases abs_cases t with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at habs <;> linarith

/-- EMERGENT UNITARITY.  For every nonempty finite set `S` of integers `≥ 2`, the truncated
Euler product `∏_{p ∈ S} c_p` blows up along the unitary axis at `s = 1/2`:
`‖∏ c_p(1/2 + it)‖ → ∞` as `t → 0`.  So no finite truncation is unimodular on `Re s = 1/2`;
`|φ| = 1` is a global (functional-equation) phenomenon. -/
theorem finite_euler_blowup_on_axis (S : Finset ℕ) (hS : S.Nonempty) (h2 : ∀ p ∈ S, 2 ≤ p) :
    Tendsto (fun t : ℝ => ‖∏ p ∈ S, localC p (1 / 2 + t * I)‖) (𝓝[≠] 0) atTop := by
  set N : ℝ → ℂ := fun t => ∏ p ∈ S, (1 - (p : ℂ) ^ (-1 - 2 * (t : ℂ) * I)) with hN
  set D : ℝ → ℂ := fun t => ∏ p ∈ S, (1 - (p : ℂ) ^ (-(2 * (t : ℂ) * I))) with hD
  have hsplit : ∀ t : ℝ, ∏ p ∈ S, localC p (1 / 2 + t * I) = N t / D t := by
    intro t; simp only [hN, hD, localC_axis]; rw [Finset.prod_div_distrib]
  simp only [hsplit, norm_div]
  have hpos : ∀ p ∈ S, (p : ℂ) ≠ 0 := fun p hp => by
    exact_mod_cast (show p ≠ 0 by have := h2 p hp; omega)
  have hNc : Continuous N := by
    refine continuous_finsetProd _ fun p hp => ?_
    exact continuous_const.sub (Continuous.const_cpow (by fun_prop) (Or.inl (hpos p hp)))
  have hDc : Continuous D := by
    refine continuous_finsetProd _ fun p hp => ?_
    exact continuous_const.sub (Continuous.const_cpow (by fun_prop) (Or.inl (hpos p hp)))
  have hN0 : N 0 ≠ 0 := by
    simp only [hN]
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hp2 := h2 p hp
    have e : (p : ℂ) ^ (-1 - 2 * ((0 : ℝ) : ℂ) * I) = ((p : ℂ))⁻¹ := by
      simp [Complex.cpow_neg_one]
    rw [e]
    intro h
    have : ((p : ℂ))⁻¹ = 1 := by linear_combination -h
    have hp1 : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) this
    have : (p : ℕ) = 1 := by exact_mod_cast hp1
    omega
  have hD0 : D 0 = 0 := by
    simp only [hD]
    obtain ⟨p, hp⟩ := hS
    exact Finset.prod_eq_zero hp (by simp)
  have hDne : ∀ᶠ t : ℝ in 𝓝[≠] 0, D t ≠ 0 := by
    have := (Filter.eventually_all_finset S).mpr fun p hp => local_den_ne_zero p (h2 p hp)
    filter_upwards [this] with t ht
    simp only [hD]
    exact Finset.prod_ne_zero_iff.mpr ht
  have hNlim : Tendsto (fun t => ‖N t‖) (𝓝[≠] 0) (𝓝 ‖N 0‖) :=
    ((hNc.norm.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hDlim : Tendsto (fun t => ‖D t‖) (𝓝[≠] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have := (hDc.norm.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      simpa [hD0] using this
    · filter_upwards [hDne] with t ht
      exact norm_pos_iff.mpr ht
  have hinv := hDlim.inv_tendsto_nhdsGT_zero
  have := Filter.Tendsto.pos_mul_atTop (norm_pos_iff.mpr hN0) hNlim hinv
  refine this.congr' ?_
  filter_upwards with t
  simp [div_eq_mul_inv]

end Emergent

/-! ## 9. Correction to the Hecke-orbit claim: the orbit of `i` contains a second class-number-one
point, `2i` -/

section HeckeOrbit

/-- The Hecke correspondence `T_n(z) = {(a z + b)/d : ad = n, 0 ≤ b < d}`. -/
def heckeSet (n : ℕ) (z : ℂ) : Set ℂ :=
  {w | ∃ a d b : ℕ, a * d = n ∧ b < d ∧ w = ((a : ℂ) * z + b) / d}

/-- `2i ∈ T_2(i)`.  The point `2i` has discriminant `-16` and class number `h(-16) = 1`. -/
theorem two_I_mem_T2 : 2 * I ∈ heckeSet 2 I :=
  ⟨2, 1, 0, by norm_num, by norm_num, by push_cast; ring⟩

/-- `21 i/20 ∈ T_420(i)` (the idea's Hecke-neighbour example). -/
theorem hecke_neighbour_mem : (21 / 20 : ℂ) * I ∈ heckeSet 420 I :=
  ⟨21, 20, 0, by norm_num, by norm_num, by push_cast; ring⟩

/-- `3i ∈ T_3(i)` and `4i ∈ T_4(i)`: class-number-two points of the orbit (discriminants `-36`,
`-64`), where off-line zeros are certified in the research directory (Arb, genus theory). -/
theorem three_I_mem_T3 : 3 * I ∈ heckeSet 3 I :=
  ⟨3, 1, 0, by norm_num, by norm_num, by push_cast; ring⟩

theorem four_I_mem_T4 : 4 * I ∈ heckeSet 4 I :=
  ⟨4, 1, 0, by norm_num, by norm_num, by push_cast; ring⟩

/-- At `3i`, `Z_{x²+9y²} = ζ(s) L(s, χ₋₄)(1 + 3^{1-2s}) + L(s, χ₋₃) L(s, χ₁₂)` (Dirichlet
coefficients checked exactly for `n ≤ 4000` in the research directory).
The local correction `1 + 3 · 9^{-s}` has all its zeros on `Re s = 1/2`: the certified off-line
zeros at `3i` come from the sum of two Euler products, not from a local factor. -/
theorem euler3_disc36_zeros_on_line {s : ℂ} (h : 1 + 3 * (9 : ℂ) ^ (-s) = 0) : s.re = 1 / 2 := by
  have hu : (9 : ℂ) ^ (-s) = -(1 / 3) := by linear_combination h / 3
  have hn : ‖(9 : ℂ) ^ (-s)‖ = 1 / 3 := by rw [hu]; norm_num
  have hnorm : ‖(9 : ℂ) ^ (-s)‖ = (9 : ℝ) ^ (-s).re := by
    rw [show (9 : ℂ) = ((9 : ℝ) : ℂ) by norm_num]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  rw [hnorm] at hn
  have hlog := congrArg Real.log hn
  rw [Real.log_rpow (by norm_num), show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv,
    show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow] at hlog
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  simp only [Complex.neg_re, Nat.cast_ofNat] at hlog
  nlinarith

/-- At `2i` the Epstein zeta function of `x² + 4y²` is `2 ζ(s) L(s, χ₋₄) (1 - 2^{-s} + 2^{1-2s})`
(Dirichlet coefficients checked exactly for `n ≤ 4000` in the research directory).  The extra
Euler factor has ALL its zeros on the unitary line `Re s = 1/2`, so RH at `2i` is equivalent to
RH at `i`: the Hecke orbit of `i` is not "`i` plus class-number `≥ 2` points". -/
theorem euler2_disc16_zeros_on_line {s : ℂ}
    (h : 1 - (2 : ℂ) ^ (-s) + 2 * (2 : ℂ) ^ (-2 * s) = 0) : s.re = 1 / 2 := by
  set u : ℂ := (2 : ℂ) ^ (-s) with hu
  have hsq : (2 : ℂ) ^ (-2 * s) = u ^ 2 := by
    rw [hu, ← Complex.cpow_nat_mul]; congr 1; push_cast; ring
  rw [hsq] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, pow_two,
    Complex.sub_im, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.zero_re,
    Complex.zero_im] at hre him
  norm_num at hre him
  -- him : -u.im + 2 * (u.re * u.im + u.im * u.re) = 0 ; hre : 1 - u.re + 2 * (u.re^2 - u.im^2) = 0
  have hy : u.im ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (u.re - 1 / 4)]
  have hx : u.re = 1 / 4 := by
    have : u.im * (4 * u.re - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hy
    · linarith
  have hn : ‖u‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hx] at hre ⊢
    nlinarith
  have hnorm : ‖u‖ = (2 : ℝ) ^ (-s).re := by
    rw [hu, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  rw [hnorm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at hn
  have hlog := congrArg Real.log hn
  rw [Real.log_rpow (by norm_num), show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at hlog
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Complex.neg_re, Nat.cast_ofNat] at hlog
  nlinarith

end HeckeOrbit

/-! ## 10. The exchange rate for the real `ξ` (kernel-checked relabelings), the phase identity,
edge cancellation, and finite cooked configurations -/

section ExchangeRate

open LiCriterion

/-- Shifted gap: reflecting `v` in the vertical line `Re = c`. -/
theorem shift_axis_gap (a v : ℂ) (c : ℝ) :
    Complex.normSq (a - 2 * c + conj v) - Complex.normSq (a - v)
      = 4 * (a.re - c) * (v.re - c) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

lemma shift_one_sub_div_le {a v : ℂ} {c : ℝ} (ha0 : a ≠ 0) (ha : c ≤ a.re) (hv : c ≤ v.re) :
    ‖1 - v / a‖ ≤ ‖1 - (2 * c - conj v) / a‖ := by
  have e1 : 1 - v / a = (a - v) / a := by field_simp
  have e2 : 1 - (2 * c - conj v) / a = (a - 2 * c + conj v) / a := by field_simp; ring
  rw [e1, e2, norm_div, norm_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  have g := shift_axis_gap a v c
  have : 0 ≤ 4 * (a.re - c) * (v.re - c) := by
    apply mul_nonneg; apply mul_nonneg; norm_num; linarith; linarith
  exact norm_le_of_normSq_le (by linarith)

/-- Shifted contractivity of the real `ξ` at shift `h`, GIVEN the zero-free strip
`|Re ρ - 1/2| ≤ h`: `‖ξ(u - h)‖ ≤ ‖ξ(u + h)‖` for `Re u ≥ 1/2`. -/
theorem xi_shift_inner {h : ℝ} (hstrip : ∀ ρ : NontrivialZero, |ρ.val.re - 1 / 2| ≤ h) {u : ℂ}
    (hu : 1 / 2 ≤ u.re) : ‖riemannXi (u - h)‖ ≤ ‖riemannXi (u + h)‖ := by
  have hgenus := xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one
  have hhad := xi_factorization_prod_with_multiplicity_of_hadamard_order_one xi_hasFiniteOrder
    xi_order_le_one
  obtain ⟨b₂, hfac⟩ := xi_sq_factorization_pairedLinear_withMultiplicity_of_weighted_genus
    hgenus hhad
  have hg' := summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus hgenus
  set c : ℝ := 1 / 2 - h with hc
  have hv : c ≤ (u - h).re := by simp [hc]; linarith
  have hrefl : ‖riemannXi (u + h)‖ = ‖riemannXi (2 * c - conj (u - h))‖ := by
    have e1 : riemannXi (u + h) = riemannXi (1 - (u + h)) := xi_functional_equation _
    have e2 : (2 * (c : ℂ) - conj (u - h)) = conj (1 - (u + h)) := by
      rw [hc]; simp only [map_sub, map_add, map_one, Complex.conj_ofReal]; push_cast; ring
    rw [e1, e2, xi_norm_conj]
  rw [hrefl]
  have hsq : ‖riemannXi (u - h)‖ ^ 2 ≤ ‖riemannXi (2 * c - conj (u - h))‖ ^ 2 := by
    rw [← norm_pow, ← norm_pow, hfac, hfac, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left
      (norm_tprod_le (multipliable_xiPairedLinearFactor_withMultiplicity_of_genus_one _ hg')
        (multipliable_xiPairedLinearFactor_withMultiplicity_of_genus_one _ hg')
        (fun i => ?_)) (norm_nonneg _)
    have hρ := hstrip i.1
    have hρ' := hstrip (pairedZero i.1)
    rw [pairedZero_val] at hρ'
    unfold xiPairedLinearFactor
    rw [norm_mul, norm_mul]
    refine mul_le_mul (shift_one_sub_div_le i.1.ne_zero ?_ hv)
      (shift_one_sub_div_le (pairedZero i.1).ne_zero ?_ hv) (norm_nonneg _) (norm_nonneg _)
    · have := neg_abs_le (i.1.val.re - 1 / 2); rw [hc]; linarith
    · have := neg_abs_le ((1 - i.1.val).re - 1 / 2); rw [hc, pairedZero_val]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Zeros force zeros under shifted contractivity: if `ξ(ρ) = 0` and the `h`-channel is contractive
at `u = ρ - h` (with `Re u ≥ 1/2`), then `ξ(ρ - 2h) = 0`. -/
lemma shift_partner {h : ℝ} (H : ∀ u : ℂ, 1 / 2 ≤ u.re → ‖riemannXi (u - h)‖ ≤ ‖riemannXi (u + h)‖)
    {ρ : ℂ} (hρ : riemannXi ρ = 0) (hre : 1 / 2 ≤ ρ.re - h) : riemannXi (ρ - 2 * h) = 0 := by
  have := H (ρ - h) (by simpa using hre)
  rw [show ρ - (h : ℂ) + h = ρ by ring, hρ, norm_zero,
    show ρ - (h : ℂ) - h = ρ - 2 * h by ring] at this
  exact norm_le_zero_iff.mp this

/-- THE EXCHANGE RATE FOR THE REAL `ξ` (kernel-checked; a relabeling, used only to price an
improvement).  For every `h₀ ≥ 0`: all nontrivial zeros lie in the strip `|Re ρ - 1/2| ≤ h₀`
iff every shifted channel `h > h₀` is contractive on `Re u ≥ 1/2`.  The unitary channel of the
modular surface is `h = 1/2` (unconditional: `xi_inner`); RH is `h₀ = 0`; a zero-free half-plane
`Re s > 1 - 2δ` is `h₀ = 1/2 - 2δ`. -/
theorem zero_free_strip_iff_shift_contractive (h₀ : ℝ) :
    (∀ ρ : NontrivialZero, |ρ.val.re - 1 / 2| ≤ h₀) ↔
      ∀ h : ℝ, h₀ < h → ∀ u : ℂ, 1 / 2 ≤ u.re → ‖riemannXi (u - h)‖ ≤ ‖riemannXi (u + h)‖ := by
  constructor
  · intro H h hh u hu
    exact xi_shift_inner (fun ρ => (H ρ).trans hh.le) hu
  · intro H
    -- a zero with `Re ρ > 1/2 + h₀` would force a continuum of zeros `ρ - 2h`
    have key : ∀ ρ : NontrivialZero, ρ.val.re ≤ 1 / 2 + h₀ := by
      intro ρ
      by_contra hc
      rw [not_le] at hc
      set ε : ℝ := ρ.val.re - 1 / 2 with hε
      have hρ0 : riemannXi ρ.val = 0 := (xi_zeros_are_nontrivial_zeros ρ.val).2 ⟨ρ, rfl⟩
      have hmaps : Set.MapsTo (fun h : ℝ => ρ.val - 2 * h) (Set.Ioo h₀ ε)
          (Set.range (fun z : NontrivialZero => z.val)) := by
        intro h hh
        have hz := shift_partner (H h hh.1) hρ0 (by rw [hε] at hh; linarith [hh.2])
        obtain ⟨z, hz'⟩ := (xi_zeros_are_nontrivial_zeros _).1 hz
        exact ⟨z, hz'.symm⟩
      have hinj : Set.InjOn (fun h : ℝ => ρ.val - 2 * h) (Set.Ioo h₀ ε) := by
        intro a _ b _ hab
        have := congrArg Complex.re hab
        simp at this
        linarith
      have hcount := hmaps.countable_of_injOn hinj (Set.countable_range _)
      rw [Cardinal.Real.Ioo_countable_iff] at hcount
      linarith
    intro ρ
    rw [abs_le]
    constructor
    · have := key (pairedZero ρ)
      rw [pairedZero_val, Complex.sub_re, Complex.one_re] at this
      linarith
    · linarith [key ρ]

/-- RH (Mathlib's `RiemannHypothesis`) iff every shifted channel `h > 0` of the real `ξ` is
contractive.  Relabeling (Hermite–Biehler / Lagarias form); nothing about RH is proved. -/
theorem rh_iff_all_shifts_contractive :
    RiemannHypothesis ↔
      ∀ h : ℝ, 0 < h → ∀ u : ℂ, 1 / 2 ≤ u.re → ‖riemannXi (u - h)‖ ≤ ‖riemannXi (u + h)‖ := by
  rw [← zero_free_strip_iff_shift_contractive 0, rh_equiv_mathlib]
  constructor
  · intro H ρ
    rw [H ρ.val ρ.property.1 ⟨ρ.property.2.1, ρ.property.2.2⟩, sub_self, abs_zero]
  · intro H s hs hstrip
    have := H ⟨s, hs, hstrip.1, hstrip.2⟩
    have h0 := abs_nonpos_iff.mp this
    simp only at h0
    linarith

/-- The unconditional end of the family: the unitary channel `h = 1/2` of the modular surface
(the strip `|Re ρ - 1/2| ≤ 1/2` is the trivial one). -/
theorem xi_unitary_channel_contractive {u : ℂ} (hu : 1 / 2 ≤ u.re) :
    ‖riemannXi (u - (1 / 2 : ℝ))‖ ≤ ‖riemannXi (u + (1 / 2 : ℝ))‖ :=
  xi_shift_inner (fun ρ => by
    rw [abs_le]; constructor <;> linarith [ρ.property.2.1, ρ.property.2.2]) hu

/-- LAX–PHILLIPS RELABELING.  The scattering resonances of the modular surface in the `ξ`
normalisation are the zeros of `ξ(2s)`, i.e. `s = ρ/2`; RH iff all of them lie on `Re s = 1/4`. -/
theorem rh_iff_resonances_on_quarter_line :
    RiemannHypothesis ↔ ∀ s : ℂ, riemannXi (2 * s) = 0 → s.re = 1 / 4 := by
  rw [rh_equiv_mathlib]
  constructor
  · intro H s hs
    obtain ⟨ρ, hρ⟩ := (xi_zeros_are_nontrivial_zeros _).1 hs
    have h2 := H ρ.val ρ.property.1 ⟨ρ.property.2.1, ρ.property.2.2⟩
    have : (2 * s).re = ρ.val.re := by rw [hρ]
    simp at this
    linarith
  · intro H s hs hstrip
    have hx : riemannXi s = 0 := (xi_zeros_are_nontrivial_zeros s).2 ⟨⟨s, hs, hstrip.1, hstrip.2⟩, rfl⟩
    have := H (s / 2) (by rw [show 2 * (s / 2) = s by ring]; exact hx)
    simp at this
    linarith

end ExchangeRate

section Extras

/-- The phase identity: for `Λ` with the functional equation and reality, the logarithmic
derivative of `φ_Λ(s) = Λ(2s-1)/Λ(2s)` on the unitary axis is `-4 Re (Λ'/Λ)(1 + 2it)`.  So the
Birman–Krein phase derivative is exactly the `σ = 1` slice of the rational face. -/
theorem bk_phase_identity {Λ : ℂ → ℂ} (hd : Differentiable ℂ Λ) (hfe : ∀ w, Λ (1 - w) = Λ w)
    (hre : ∀ w, Λ (conj w) = conj (Λ w)) (t : ℝ) (hL : Λ (1 + 2 * t * I) ≠ 0) :
    logDeriv (fun s => Λ (2 * s - 1) / Λ (2 * s)) (1 / 2 + t * I)
      = -4 * ((logDeriv Λ (1 + 2 * t * I)).re : ℂ) := by
  set a : ℂ := 1 + 2 * t * I with ha
  set b : ℂ := 2 * t * I with hb
  have hca : conj a = 1 - b := by rw [ha, hb]; apply Complex.ext <;> simp
  have hvalb : Λ b = conj (Λ a) := by rw [← hre, hca, hfe]
  have hderb : deriv Λ b = -conj (deriv Λ a) := by
    rw [deriv_fe hd hfe b, ← hca, deriv_real hd hre]
  have hb0 : Λ b ≠ 0 := by rw [hvalb]; exact (map_ne_zero _).mpr hL
  have p1 : 2 * (1 / 2 + (t : ℂ) * I) - 1 = b := by rw [hb]; ring
  have p2 : 2 * (1 / 2 + (t : ℂ) * I) = a := by rw [ha]; ring
  have hf : DifferentiableAt ℂ (fun s : ℂ => Λ (2 * s - 1)) (1 / 2 + t * I) :=
    (hd _).comp _ ((differentiableAt_id.const_mul 2).sub_const 1)
  have hg : DifferentiableAt ℂ (fun s : ℂ => Λ (2 * s)) (1 / 2 + t * I) :=
    (hd _).comp _ (differentiableAt_id.const_mul 2)
  rw [logDeriv_div _ (by simp only [p1]; exact hb0) (by simp only [p2]; exact hL) hf hg]
  have c1 : logDeriv (fun s : ℂ => Λ (2 * s - 1)) (1 / 2 + t * I) = logDeriv Λ b * 2 := by
    have := logDeriv_comp (f := Λ) (g := fun s : ℂ => 2 * s - 1) (x := 1 / 2 + t * I) (hd _)
      ((differentiableAt_id.const_mul 2).sub_const 1)
    simp only [Function.comp_def] at this
    rw [this, p1]
    congr 1
    have hh : HasDerivAt (fun s : ℂ => 2 * s - 1) 2 (1 / 2 + t * I) := by
      simpa using ((hasDerivAt_id (1 / 2 + t * I)).const_mul (2 : ℂ)).sub_const 1
    exact hh.deriv
  have c2 : logDeriv (fun s : ℂ => Λ (2 * s)) (1 / 2 + t * I) = logDeriv Λ a * 2 := by
    have := logDeriv_comp (f := Λ) (g := fun s : ℂ => 2 * s) (x := 1 / 2 + t * I) (hd _)
      (differentiableAt_id.const_mul 2)
    simp only [Function.comp_def] at this
    rw [this, p2]
    congr 1
    have hh : HasDerivAt (fun s : ℂ => 2 * s) 2 (1 / 2 + t * I) := by
      simpa using (hasDerivAt_id (1 / 2 + t * I)).const_mul (2 : ℂ)
    exact hh.deriv
  rw [c1, c2]
  simp only [logDeriv_apply, hvalb, hderb]
  have hz : ∀ z : ℂ, (-conj z / conj (Λ a)) * 2 - z / Λ a * 2 = -4 * (((z / Λ a).re : ℝ) : ℂ) := by
    intro z
    have e : -conj z / conj (Λ a) = -conj (z / Λ a) := by rw [map_div₀]; ring
    rw [e]
    generalize z / Λ a = w
    exact Complex.ext (by simp; ring) (by simp)
  exact hz _

/-- Contractivity is blind to zeros on the edge `Re w = 1` and forces every zero at or beyond it
to be cancelled: if `Λ(w₀) = 0` with `Re w₀ ≥ 1`, then `Λ(w₀ - 1) = 0`. -/
theorem inner_forces_partner {Λ : ℂ → ℂ}
    (hin : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖Λ (2 * s - 1)‖ ≤ ‖Λ (2 * s)‖) {w₀ : ℂ} (hw : Λ w₀ = 0)
    (hre : 1 ≤ w₀.re) : Λ (w₀ - 1) = 0 := by
  have := hin (w₀ / 2) (by simp; linarith)
  rw [show 2 * (w₀ / 2) - 1 = w₀ - 1 by ring, show 2 * (w₀ / 2) = w₀ by ring, hw,
    norm_zero] at this
  exact norm_le_zero_iff.mp this

/-- Finite cooked configurations: `ξ · ∏_{ρ ∈ L} Q_ρ` satisfies every channel axiom for ANY
finite list `L` of points of the open strip. -/
theorem channelAxioms_mul_quadList (L : List ℂ) (hL : ∀ ρ ∈ L, 0 < ρ.re ∧ ρ.re < 1) :
    ChannelAxioms (fun w => LiCriterion.riemannXi w * (L.map fun ρ => quadPoly ρ w).prod) := by
  induction L with
  | nil => simpa using channelAxioms_xi
  | cons ρ L ih =>
    have hρ := hL ρ (by simp)
    have h' := channelAxioms_mul_quad (ih fun ρ' h => hL ρ' (by simp [h])) hρ.1 hρ.2
    have e : (fun w => LiCriterion.riemannXi w * ((ρ :: L).map fun ρ => quadPoly ρ w).prod)
        = (fun w => LiCriterion.riemannXi w * (L.map fun ρ => quadPoly ρ w).prod * quadPoly ρ w) := by
      funext w; simp only [List.map_cons, List.prod_cons]; ring
    rw [e]
    exact h'

end Extras

end CruxDynamicsErgodic

/-! ## Axiom audit: every theorem and lemma of this file. -/

#print axioms CruxDynamicsErgodic.blaschke_gap
#print axioms CruxDynamicsErgodic.doubled_gap
#print axioms CruxDynamicsErgodic.shifted_gap
#print axioms CruxDynamicsErgodic.norm_le_of_normSq_le
#print axioms CruxDynamicsErgodic.norm_eq_of_normSq_eq
#print axioms CruxDynamicsErgodic.doubled_le
#print axioms CruxDynamicsErgodic.doubled_eq_on_line
#print axioms CruxDynamicsErgodic.scat_inner
#print axioms CruxDynamicsErgodic.scat_unimodular_on_line
#print axioms CruxDynamicsErgodic.scat_pole_of_re_gt_one
#print axioms CruxDynamicsErgodic.scat_edge_iff
#print axioms CruxDynamicsErgodic.fake_offline_quadruple_is_inner
#print axioms CruxDynamicsErgodic.scat_inner_list
#print axioms CruxDynamicsErgodic.scat_unimodular_list
#print axioms CruxDynamicsErgodic.list_norm_prod_le
#print axioms CruxDynamicsErgodic.list_norm_prod_eq
#print axioms CruxDynamicsErgodic.chDen_perm
#print axioms CruxDynamicsErgodic.ch_factor_le
#print axioms CruxDynamicsErgodic.ch_factor_eq
#print axioms CruxDynamicsErgodic.ch_inner
#print axioms CruxDynamicsErgodic.ch_unimodular
#print axioms CruxDynamicsErgodic.mem_of_iota_closed
#print axioms CruxDynamicsErgodic.ch_edge_iff
#print axioms CruxDynamicsErgodic.rh_finite_iff_all_channels
#print axioms CruxDynamicsErgodic.unitary_channel_iff
#print axioms CruxDynamicsErgodic.chNum_half
#print axioms CruxDynamicsErgodic.chDen_half
#print axioms CruxDynamicsErgodic.quadList_iota_closed
#print axioms CruxDynamicsErgodic.pairList_iota_closed
#print axioms CruxDynamicsErgodic.cooked_quadruple_threshold
#print axioms CruxDynamicsErgodic.axis_gap
#print axioms CruxDynamicsErgodic.axis_le
#print axioms CruxDynamicsErgodic.one_sub_div_le
#print axioms CruxDynamicsErgodic.pairedFactor_le
#print axioms CruxDynamicsErgodic.norm_tprod_le
#print axioms CruxDynamicsErgodic.xi_ne_zero_of_one_le_re
#print axioms CruxDynamicsErgodic.xi_norm_conj
#print axioms CruxDynamicsErgodic.xi_two_mul_norm
#print axioms CruxDynamicsErgodic.xi_inner
#print axioms CruxDynamicsErgodic.unitary_of_fe_real
#print axioms CruxDynamicsErgodic.xi_unitary
#print axioms CruxDynamicsErgodic.scatXi_denom_ne_zero
#print axioms CruxDynamicsErgodic.scatXi_norm_le_one
#print axioms CruxDynamicsErgodic.scatXi_norm_eq_one
#print axioms CruxDynamicsErgodic.scatXi_differentiableAt
#print axioms CruxDynamicsErgodic.xi_eq_completed
#print axioms CruxDynamicsErgodic.modScat_eq
#print axioms CruxDynamicsErgodic.scatXi_one_ne_zero
#print axioms CruxDynamicsErgodic.deriv_fe
#print axioms CruxDynamicsErgodic.deriv_real
#print axioms CruxDynamicsErgodic.deriv_nonpos_of_right_max
#print axioms CruxDynamicsErgodic.bk_of_inner
#print axioms CruxDynamicsErgodic.quadPoly_one_sub
#print axioms CruxDynamicsErgodic.quadPoly_conj
#print axioms CruxDynamicsErgodic.quadPoly_scatNum
#print axioms CruxDynamicsErgodic.quadPoly_scatDen
#print axioms CruxDynamicsErgodic.quadPoly_self
#print axioms CruxDynamicsErgodic.quadPoly_differentiable
#print axioms CruxDynamicsErgodic.quadPoly_ne_zero
#print axioms CruxDynamicsErgodic.channelAxioms_xi
#print axioms CruxDynamicsErgodic.channelAxioms_mul_quad
#print axioms CruxDynamicsErgodic.rho0_re
#print axioms CruxDynamicsErgodic.channelAxioms_fakeXi
#print axioms CruxDynamicsErgodic.fakeXi_offline_zero
#print axioms CruxDynamicsErgodic.channel_axioms_do_not_imply_rh
#print axioms CruxDynamicsErgodic.channel_realizes_any_strip_zero
#print axioms CruxDynamicsErgodic.channel_zeros_in_closed_strip
#print axioms CruxDynamicsErgodic.hecke_wave
#print axioms CruxDynamicsErgodic.ofReal_inv_cpow
#print axioms CruxDynamicsErgodic.heckeEig_one_sub
#print axioms CruxDynamicsErgodic.heckeEig_fun_of_laplace
#print axioms CruxDynamicsErgodic.heckeEig_conj
#print axioms CruxDynamicsErgodic.heckeEig_real_on_axis
#print axioms CruxDynamicsErgodic.heckeEig_prime
#print axioms CruxDynamicsErgodic.localC_axis
#print axioms CruxDynamicsErgodic.local_den_ne_zero
#print axioms CruxDynamicsErgodic.finite_euler_blowup_on_axis
#print axioms CruxDynamicsErgodic.two_I_mem_T2
#print axioms CruxDynamicsErgodic.hecke_neighbour_mem
#print axioms CruxDynamicsErgodic.three_I_mem_T3
#print axioms CruxDynamicsErgodic.four_I_mem_T4
#print axioms CruxDynamicsErgodic.euler3_disc36_zeros_on_line
#print axioms CruxDynamicsErgodic.euler2_disc16_zeros_on_line
#print axioms CruxDynamicsErgodic.shift_axis_gap
#print axioms CruxDynamicsErgodic.shift_one_sub_div_le
#print axioms CruxDynamicsErgodic.xi_shift_inner
#print axioms CruxDynamicsErgodic.shift_partner
#print axioms CruxDynamicsErgodic.zero_free_strip_iff_shift_contractive
#print axioms CruxDynamicsErgodic.rh_iff_all_shifts_contractive
#print axioms CruxDynamicsErgodic.xi_unitary_channel_contractive
#print axioms CruxDynamicsErgodic.rh_iff_resonances_on_quarter_line
#print axioms CruxDynamicsErgodic.bk_phase_identity
#print axioms CruxDynamicsErgodic.inner_forces_partner
#print axioms CruxDynamicsErgodic.channelAxioms_mul_quadList
