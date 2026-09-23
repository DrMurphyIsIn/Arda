/-
  Crux_spectral_operator.lean -- buildable core of "The Weil-Pontryagin window realization"
  (lens: spectral / Hilbert-Polya / de Branges).  Abstract Krein-space layer.

  conjecture1_proved = False.  Nothing in this file bears on where the zeros of zeta lie.  RH is
  equivalent (Weil) to kappa_zeta(x) = 0 for every window x, and nothing here says anything about
  kappa_zeta.  Every statement is linear algebra over C: no Euler product, no arithmetic.  All of
  it applies verbatim to the Davenport-Heilbronn function D (negative control), and that is
  consistent: these theorems bound zeros of EIGENVECTOR transforms by negative indices, and bound
  negative indices by numbers of off-line pairs; they never assert that an index vanishes.

  Checked by: cd telperion/examples/li_positivity/lean && lake env lean Crux/Crux_spectral_operator.lean
  (Lean v4.34.0-rc1, Mathlib de5ce8a9).  No `sorry`, no `native_decide`, no `opaque`, no new
  `axiom`.  The `#print axioms` block at the end reports only propext, Classical.choice,
  Quot.sound.

  SETTING.  V a complex vector space, B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ a Hermitian form (conjugate-linear in
  the first slot).  `NegIndexLE B K`: every family spanning a B-negative-definite subspace has at
  most K members, i.e. the Pontryagin index kappa(B) is at most K.

  WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked; abstract):
  A. The isotropy mechanism.  `chain_isotropic_line`: E in the radical of B (the eigen-equation
     (Q - λ)η = 0, E = η^), R the Jordan chains E/(z - α)^k of zeros α of E, encoded by
     z·R = P + α R (P the previous chain element or E).  If multiplication by z is B-symmetric on
     these vectors and conj α_i ≠ α_j (e.g. all α in one open half-plane), the span of all chains
     is totally B-isotropic.  `chain_isotropic_circle`: the same with B(zu, zv) = B(u, v) (Toeplitz
     shift invariance) and conj α_i · α_j ≠ 1 (all α inside, or all outside, the unit disk).
  B. Pontryagin inertia lemma, `card_le_of_isotropic` (via `exists_dual_family`,
     `exists_neg_gram`, `isNegFamily_of_gram`): an independent totally isotropic family whose span
     meets the radical only in 0 has at most kappa(B) members.
  C. A + B.  `pontryagin_cvs_line` (+ `_lower`, `_pos`): the number of zeros of E in the open upper
     (lower) half-plane, with multiplicity, is at most kappa(Q - λ), and at most its positive
     index.  `no_upper_zeros_of_psd` is the case kappa = 0 (with `pontryagin_cvs_line_lower` at
     K = 0 for the lower half-plane): the bottom eigenvector has no non-real zeros
     (Connes-van Suijlekom 2025, here without discretisation or Hurwitz).
     `iohvidov_krein_circle` (+ `_outside`): the finite Iohvidov-Krein bound for Hermitian
     Toeplitz eigenpolynomials.
  D. Galerkin matrices.  `matForm_diag_symm`: a displacement identity
     (Ω_i - Ω_j) Q_ij = ℓ_i conj g_j - g_i ℓ_j makes multiplication by Ω symmetric on ker ℓ.
     `galerkin_pontryagin_cvs`: for such a Hermitian Q, the upper-half-plane roots w of the
     secular equation Σ_k ℓ_k c_k/(Ω_k - w) = 0 of an eigenvector c number at most kappa(Q - λ).
     The Galerkin matrices of the window Weil form satisfy this identity with Ω = diag((kω)²)
     (measured residual 1e-40 in both parity sectors, for zeta and D;
     telperion/research/crux_spectral-operator/validate_forms.py), and the roots w are the squares
     of the zeros of the eigenvector's transform, so the theorem applies to those matrices exactly.
  E. The upper bound kappa <= #off-line pairs: `card_le_of_nonneg_on_ker`,
     `negIndexLE_of_nonneg_on_ker`, `zeroSide_negIndexLE` (a nonnegative on-line part plus k
     hyperbolic pair terms 2 Re(conj(a_j v) · b_j v) has kappa <= k; killing a_j alone kills the pair
     term).  The zeta instance, on the unconditional explicit formula, is on the rvm_bridge island
     (`weil_negIndex_le_offline`, file of the same name).
  F. The detection algebra: `detector_pair_term` (the pair value -Re(X²)/(2δ²) of the idea's
     detector), `exists_detector_phase` and `detector_pair_term_le` (a real a makes the pair value
     at most -|Ξ'(w₋)|²/2), `isNegFamily_of_diag_dominant` (Gershgorin form: almost-orthogonal
     detectors with negative diagonal give kappa >= m).

  PAPER GLUE (THEOREM-paper-proof, not kernel-checked here).  To apply C to the window form Q_x on
  L²[-L/2, L/2]: (i) Q_x is translation invariant, so multiplication by z is Q_x-symmetric on the
  Paley-Wiener transforms, and so is the L² product (Plancherel); the zeta instance
  B(f', g) + B(f, g') = 0 is kernel-checked on the rvm_bridge island (`weilSesq_deriv_symm`);
  (ii) for a zero α of E = η^ in PW_{L/2}, E/(z - α)^k lies in PW_{L/2} and in the form domain, and
  z·E/(z - α)^k = E/(z - α)^{k-1} + α E/(z - α)^k; (iii) distinct chain vectors are independent,
  and their span misses span(E) = ker(Q_x - λ) when λ is simple.
  CORRECTION to the idea's claim 2.  In the EVEN sector multiplication by z leaves the sector, so
  one must use w = z² there: the zeros of E in the open first quadrant number at most
  kappa_even(λ), while zeros on the imaginary axis are controlled only by the full-space index
  kappa_even(λ) + kappa_odd(λ).  The idea's even-sector statement ("at most kappa_even pairs of
  non-real zeros") FAILS for Galerkin truncations, which satisfy every hypothesis used here: at
  Davenport-Heilbronn x = 40, N = 60, the even ground state has kappa_even = 0 and a zero pair at
  ±27.5057 i, and the corrected bound 1 <= 0 + 1 holds with equality.  So it cannot be derived
  from this structure alone.  Those imaginary zeros vanish under refinement (N >= 70), so for the
  untruncated operator the even-sector statement is open (imag_zero.py and README section 6.2 in
  the research directory).

  DOES NOT ESTABLISH: anything about kappa_zeta (that is RH); the Locator conjecture (convergence of
  the (kappa+1)-th eigenvector transform to Ξ); the analytic half of the detection theorem (the
  truncation error estimates and the horizon X(ρ) ≈ γ/4 + logs); the annihilator lemma; the
  numerical Davenport-Heilbronn calibration (see the research README for those, with status
  tags); the identification of the Galerkin/eigenvalue counts with `NegIndexLE` (Courant-Fischer),
  which is used as a hypothesis.
-/
import Mathlib

namespace Crux.SpectralOperator

open scoped ComplexConjugate
open Finset

section Krein

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Hermitian symmetry of a sesquilinear form (conjugate-linear in the first slot). -/
def IsHermitian (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop := ∀ u v, conj (B u v) = B v u

/-- `w` spans a `B`-negative-definite subspace. -/
def IsNegFamily (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {ι : Type*} [Fintype ι] (w : ι → V) : Prop :=
  ∀ c : ι → ℂ, c ≠ 0 → (B (∑ i, c i • w i) (∑ i, c i • w i)).re < 0

/-- The negative (Pontryagin) index of `B` is at most `K`. -/
def NegIndexLE (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (K : ℕ) : Prop :=
  ∀ (n : ℕ) (w : Fin n → V), IsNegFamily B w → n ≤ K

lemma B_smul_left (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (a : ℂ) (u v : V) :
    B (a • u) v = conj a * B u v := by
  rw [LinearMap.map_smulₛₗ₂]; rfl

lemma B_smul_right (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (a : ℂ) (u v : V) :
    B u (a • v) = a * B u v := by
  rw [map_smul]; rfl

theorem chain_isotropic_line (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} (α : ι → ℂ) (R P : ι → V) (rk : ι → ℕ)
    (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i j, conj (α i) ≠ α j)
    (hZ : ∀ i j, B (P i + α i • R i) (R j) = B (R i) (P j + α j • R j)) :
    ∀ i j, B (R i) (R j) = 0 := by
  have hE' : ∀ v, B v E = 0 := fun v => by rw [← hB E v, hE v, map_zero]
  suffices H : ∀ N, ∀ i j, rk i + rk j ≤ N → B (R i) (R j) = 0 by
    intro i j; exact H _ i j le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i j hij
    have h1 : B (P i) (R j) = 0 := by
      rcases hP i with h | ⟨k, hk, hlt⟩
      · rw [h, hE]
      · rw [hk]; exact ih (rk k + rk j) (by omega) k j le_rfl
    have h2 : B (R i) (P j) = 0 := by
      rcases hP j with h | ⟨k, hk, hlt⟩
      · rw [h, hE']
      · rw [hk]; exact ih (rk i + rk k) (by omega) i k le_rfl
    have key := hZ i j
    rw [map_add, LinearMap.add_apply, B_smul_left, h1, map_add, B_smul_right, h2] at key
    have hne : conj (α i) - α j ≠ 0 := sub_ne_zero.mpr (hα i j)
    have : (conj (α i) - α j) * B (R i) (R j) = 0 := by linear_combination key
    exact (mul_eq_zero.mp this).resolve_left hne

theorem chain_isotropic_circle (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} (α : ι → ℂ) (R P : ι → V) (rk : ι → ℕ)
    (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i j, conj (α i) * α j ≠ 1)
    (hZ : ∀ i j, B (P i + α i • R i) (P j + α j • R j) = B (R i) (R j)) :
    ∀ i j, B (R i) (R j) = 0 := by
  have hE' : ∀ v, B v E = 0 := fun v => by rw [← hB E v, hE v, map_zero]
  suffices H : ∀ N, ∀ i j, rk i + rk j ≤ N → B (R i) (R j) = 0 by
    intro i j; exact H _ i j le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i j hij
    have h1 : B (P i) (R j) = 0 := by
      rcases hP i with h | ⟨k, hk, hlt⟩
      · rw [h, hE]
      · rw [hk]; exact ih (rk k + rk j) (by omega) k j le_rfl
    have h2 : B (R i) (P j) = 0 := by
      rcases hP j with h | ⟨k, hk, hlt⟩
      · rw [h, hE']
      · rw [hk]; exact ih (rk i + rk k) (by omega) i k le_rfl
    have h3 : B (P i) (P j) = 0 := by
      rcases hP i with h | ⟨k, hk, hlt⟩
      · rw [h, hE]
      · rcases hP j with h' | ⟨k', hk', hlt'⟩
        · rw [h', hE']
        · rw [hk, hk']; exact ih (rk k + rk k') (by omega) k k' le_rfl
    have key := hZ i j
    simp only [map_add, LinearMap.add_apply, B_smul_left, B_smul_right, h1, h2, h3] at key
    have hne : conj (α i) * α j - 1 ≠ 0 := sub_ne_zero.mpr (hα i j)
    have : (conj (α i) * α j - 1) * B (R i) (R j) = 0 := by linear_combination key
    exact (mul_eq_zero.mp this).resolve_left hne

/-- Upper half-plane: `conj α ≠ β` whenever `Im α, Im β > 0`. -/
lemma conj_ne_of_im_pos {ι : Type*} {α : ι → ℂ} (hα : ∀ i, 0 < (α i).im) :
    ∀ i j, conj (α i) ≠ α j := by
  intro i j h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith [hα i, hα j]

/-- Lower half-plane: `conj α ≠ β` whenever `Im α, Im β < 0`. -/
lemma conj_ne_of_im_neg {ι : Type*} {α : ι → ℂ} (hα : ∀ i, (α i).im < 0) :
    ∀ i j, conj (α i) ≠ α j := by
  intro i j h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith [hα i, hα j]

/-- Open unit disk: `conj α · β ≠ 1` whenever `‖α‖, ‖β‖ < 1`. -/
lemma conj_mul_ne_one_of_norm_lt {ι : Type*} {α : ι → ℂ} (hα : ∀ i, ‖α i‖ < 1) :
    ∀ i j, conj (α i) * α j ≠ 1 := by
  intro i j h
  have := congrArg (‖·‖) h
  simp only [norm_mul, Complex.norm_conj, norm_one] at this
  have hi := hα i
  have hj := hα j
  have : ‖α i‖ * ‖α j‖ < 1 := by
    calc ‖α i‖ * ‖α j‖ ≤ ‖α i‖ * 1 := by gcongr
      _ < 1 := by linarith
  linarith

/-- Outside the closed unit disk: `conj α · β ≠ 1` whenever `‖α‖, ‖β‖ > 1`. -/
lemma conj_mul_ne_one_of_one_lt_norm {ι : Type*} {α : ι → ℂ} (hα : ∀ i, 1 < ‖α i‖) :
    ∀ i j, conj (α i) * α j ≠ 1 := by
  intro i j h
  have := congrArg (‖·‖) h
  simp only [norm_mul, Complex.norm_conj, norm_one] at this
  have hi := hα i
  have hj := hα j
  have : 1 < ‖α i‖ * ‖α j‖ := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ < ‖α i‖ * ‖α j‖ := by gcongr
  linarith

/-- Dual family: if `u` is linearly independent and its span meets the radical of `B` only in `0`,
there are vectors `y j` with `B (u i) (y j) = δ i j`. -/
theorem exists_dual_family (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → V) (hind : LinearIndependent ℂ u)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • u i) v = 0) → ∑ i, c i • u i = 0) :
    ∃ y : ι → V, ∀ i j, B (u i) (y j) = if i = j then 1 else 0 := by
  let Ψ : V →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun i => B (u i))
  have hΨ : ∀ v i, Ψ v i = B (u i) v := fun v i => rfl
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    have hlt : LinearMap.range Ψ < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    have hfv : ∀ v, f (Ψ v) = 0 := by
      intro v
      have hmem : f (Ψ v) ∈ (LinearMap.range Ψ).map f :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self Ψ v)
      rw [hf] at hmem
      simpa using hmem
    set c : ι → ℂ := fun i => f (fun j => if i = j then 1 else 0) with hc_def
    have hsum : ∀ v, B (∑ i, conj (c i) • u i) v = 0 := by
      intro v
      have h := hfv v
      rw [LinearMap.pi_apply_eq_sum_univ f (Ψ v)] at h
      rw [LinearMap.map_sum₂]
      simp only [B_smul_left, Complex.conj_conj]
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΨ, smul_eq_mul, mul_comm]
    have h0 := hrad _ hsum
    have hc : ∀ i, conj (c i) = 0 := Fintype.linearIndependent_iff.mp hind _ h0
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : c i = 0 := by simpa using hc i
    simp only [smul_eq_mul]
    rw [show (f fun j => if i = j then 1 else 0) = c i from rfl, this, mul_zero]
  choose y hy using fun j => hsurj (fun i => if i = j then 1 else 0)
  exact ⟨y, fun i j => by rw [← hΨ, hy j]⟩

/-- Hyperbolic completion: an isotropic family with a dual family produces a family whose Gram
matrix is exactly `-2 · I`. -/
theorem exists_neg_gram (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u : ι → V) (hiso : ∀ i j, B (u i) (u j) = 0) (y : ι → V)
    (hy : ∀ i j, B (u i) (y j) = if i = j then 1 else 0) :
    ∃ w : ι → V, ∀ i j, B (w i) (w j) = if i = j then -2 else 0 := by
  have hy' : ∀ i j, B (y i) (u j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hB (u j) (y i), hy j i]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  set a : ι → ι → ℂ := fun k j => (1 / 2 : ℂ) * B (y k) (y j) with ha
  let y' : ι → V := fun j => y j - ∑ k, a k j • u k
  have h1 : ∀ i j, B (u i) (y' j) = if i = j then 1 else 0 := by
    intro i j
    simp only [y', map_sub, map_sum, B_smul_right, hiso, mul_zero, Finset.sum_const_zero,
      sub_zero, hy]
  have h1' : ∀ i j, B (y' i) (u j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hB (u j) (y' i), h1 j i]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have h2 : ∀ i j, B (y' i) (y' j) = 0 := by
    intro i j
    have e1 : ∀ z, B (y' i) z = B (y i) z - ∑ k, conj (a k i) * B (u k) z := by
      intro z
      show B (y i - ∑ k, a k i • u k) z = _
      rw [LinearMap.map_sub₂, LinearMap.map_sum₂]
      simp only [B_smul_left]
    have e2 : B (y i) (y' j) = B (y i) (y j) - a i j := by
      show B (y i) (y j - ∑ k, a k j • u k) = _
      rw [map_sub, map_sum]
      simp only [B_smul_right, hy', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    rw [e1 (y' j), e2]
    simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hconj : conj (a j i) = (1 / 2 : ℂ) * B (y i) (y j) := by
      rw [ha, map_mul, hB (y j) (y i), map_div₀, map_one, Complex.conj_ofNat]
    rw [hconj, ha]; ring
  refine ⟨fun j => u j - y' j, fun i j => ?_⟩
  simp only [map_sub, LinearMap.sub_apply, hiso, h1, h1', h2, sub_zero]
  by_cases h : i = j
  · subst h; simp; norm_num
  · simp [h]

/-- A family with Gram matrix `-2 · I` spans a negative-definite subspace. -/
theorem isNegFamily_of_gram (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (hw : ∀ i j, B (w i) (w j) = if i = j then -2 else 0) : IsNegFamily B w := by
  intro c hc
  have hexp : B (∑ i, c i • w i) (∑ j, c j • w j)
      = ∑ i, (((-2) * Complex.normSq (c i) : ℝ) : ℂ) := by
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [B_smul_left, map_sum, B_smul_right, hw, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    push_cast
    linear_combination (-2 : ℂ) * Complex.mul_conj (c i)
  rw [hexp, Complex.re_sum]
  simp only [Complex.ofReal_re]
  obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    exact hc (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have hpos : 0 < Complex.normSq (c i0) := Complex.normSq_pos.mpr hi0
  have hle : ∀ i ∈ Finset.univ, (-2) * Complex.normSq (c i) ≤ 0 := fun i _ => by
    nlinarith [Complex.normSq_nonneg (c i)]
  have := Finset.sum_lt_sum_of_nonempty ⟨i0, Finset.mem_univ _⟩ (s := Finset.univ)
    (f := fun _ => (0:ℝ)) (g := fun i => (-2) * Complex.normSq (c i))
  calc ∑ i, (-2) * Complex.normSq (c i) ≤ (-2) * Complex.normSq (c i0) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
        have : ∑ i ∈ Finset.univ.erase i0, (-2) * Complex.normSq (c i) ≤ 0 :=
          Finset.sum_nonpos fun i _ => by nlinarith [Complex.normSq_nonneg (c i)]
        linarith
    _ < 0 := by linarith

/-- Reindexing a negative family along an equivalence. -/
lemma isNegFamily_comp_equiv (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → V) (e : κ ≃ ι) (hw : IsNegFamily B w) : IsNegFamily B (w ∘ e) := by
  intro c hc
  have hc' : c ∘ e.symm ≠ 0 := by
    intro h
    apply hc
    funext k
    have := congrFun h (e k)
    simpa using this
  have hsum : ∑ k, c k • (w ∘ e) k = ∑ i, (c ∘ e.symm) i • w i := by
    rw [← Equiv.sum_comp e]
    simp
  rw [hsum]
  exact hw _ hc'

/-- **Pontryagin inertia lemma.** A totally `B`-isotropic, linearly independent family whose span
meets the radical of `B` only in `0` has at most `K` members when the negative index of `B` is at
most `K`. -/
theorem card_le_of_isotropic (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (u : ι → V) (hind : LinearIndependent ℂ u)
    (hiso : ∀ i j, B (u i) (u j) = 0)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • u i) v = 0) → ∑ i, c i • u i = 0)
    {K : ℕ} (hK : NegIndexLE B K) : Fintype.card ι ≤ K := by
  obtain ⟨y, hy⟩ := exists_dual_family B u hind hrad
  obtain ⟨w, hw⟩ := exists_neg_gram B hB u hiso y hy
  have hneg := isNegFamily_of_gram B w hw
  exact hK _ _ (isNegFamily_comp_equiv B w (Fintype.equivFin ι).symm hneg)

/-- The negative index of `-B` bounds the positive index of `B`. -/
lemma isHermitian_neg (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) : IsHermitian (-B) := by
  intro u v
  simp only [LinearMap.neg_apply, map_neg, hB u v]

/-- **Pontryagin--Caratheodory--Fejer, line form (abstract core).** Let `B` be Hermitian, `E` in
its radical (`B E · = 0`: the eigen-equation `(Q - λ) ξ = 0`), and let `R i` be the Jordan chains
`E / (z - α)^k` of the zeros `α` of `E` in the open upper half-plane, encoded by `z R = P + α R`
(`P` the previous chain element, or `E`).  If multiplication by `z` is `B`-symmetric on these
vectors, the chains are linearly independent and their span meets the radical only in `0`, then
the number of chain vectors (= the number of zeros in the upper half-plane, with multiplicity) is
at most every bound `K` for the negative index of `B`. -/
theorem pontryagin_cvs_line (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℂ) (R P : ι → V)
    (rk : ι → ℕ) (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i, 0 < (α i).im)
    (hZ : ∀ i j, B (P i + α i • R i) (R j) = B (R i) (P j + α j • R j))
    (hind : LinearIndependent ℂ R)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • R i) v = 0) → ∑ i, c i • R i = 0)
    {K : ℕ} (hK : NegIndexLE B K) : Fintype.card ι ≤ K :=
  card_le_of_isotropic B hB R hind
    (chain_isotropic_line B hB E hE α R P rk hP (conj_ne_of_im_pos hα) hZ) hrad hK

/-- The same count bounds the positive index (apply the line form to `-B`). -/
theorem pontryagin_cvs_line_pos (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℂ) (R P : ι → V)
    (rk : ι → ℕ) (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i, 0 < (α i).im)
    (hZ : ∀ i j, B (P i + α i • R i) (R j) = B (R i) (P j + α j • R j))
    (hind : LinearIndependent ℂ R)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • R i) v = 0) → ∑ i, c i • R i = 0)
    {K : ℕ} (hK : NegIndexLE (-B) K) : Fintype.card ι ≤ K := by
  refine pontryagin_cvs_line (-B) (isHermitian_neg B hB) E (fun v => by simp [hE v]) α R P rk
    hP hα (fun i j => by simp only [LinearMap.neg_apply, hZ i j]) hind
    (fun c hc => hrad c (fun v => by simpa using hc v)) hK

/-- **Caratheodory--Fejer / Connes--van Suijlekom case `K = 0`.** If `B ≥ 0` (negative index `0`),
the eigenfunction has no zero in the open upper half-plane. -/
theorem no_upper_zeros_of_psd (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℂ) (R P : ι → V)
    (rk : ι → ℕ) (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i, 0 < (α i).im)
    (hZ : ∀ i j, B (P i + α i • R i) (R j) = B (R i) (P j + α j • R j))
    (hind : LinearIndependent ℂ R)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • R i) v = 0) → ∑ i, c i • R i = 0)
    (hK : NegIndexLE B 0) : IsEmpty ι := by
  have := pontryagin_cvs_line B hB E hE α R P rk hP hα hZ hind hrad hK
  exact Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp this)

/-- **Iohvidov--Krein, circle form (abstract core).** Same as the line form with the unit circle in
place of the real line: `B (z u) (z v) = B u v` (shift invariance of a Toeplitz form) and the
zeros strictly inside the unit disk. -/
theorem iohvidov_krein_circle (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℂ) (R P : ι → V)
    (rk : ι → ℕ) (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i, ‖α i‖ < 1)
    (hZ : ∀ i j, B (P i + α i • R i) (P j + α j • R j) = B (R i) (R j))
    (hind : LinearIndependent ℂ R)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • R i) v = 0) → ∑ i, c i • R i = 0)
    {K : ℕ} (hK : NegIndexLE B K) : Fintype.card ι ≤ K :=
  card_le_of_isotropic B hB R hind
    (chain_isotropic_circle B hB E hE α R P rk hP (conj_mul_ne_one_of_norm_lt hα) hZ) hrad hK

/-- Lower half-plane version of `pontryagin_cvs_line`. -/
theorem pontryagin_cvs_line_lower (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℂ) (R P : ι → V)
    (rk : ι → ℕ) (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i, (α i).im < 0)
    (hZ : ∀ i j, B (P i + α i • R i) (R j) = B (R i) (P j + α j • R j))
    (hind : LinearIndependent ℂ R)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • R i) v = 0) → ∑ i, c i • R i = 0)
    {K : ℕ} (hK : NegIndexLE B K) : Fintype.card ι ≤ K :=
  card_le_of_isotropic B hB R hind
    (chain_isotropic_line B hB E hE α R P rk hP (conj_ne_of_im_neg hα) hZ) hrad hK

/-- Outside-the-disk version of `iohvidov_krein_circle`. -/
theorem iohvidov_krein_circle_outside (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℂ) (R P : ι → V)
    (rk : ι → ℕ) (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i, 1 < ‖α i‖)
    (hZ : ∀ i j, B (P i + α i • R i) (P j + α j • R j) = B (R i) (R j))
    (hind : LinearIndependent ℂ R)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • R i) v = 0) → ∑ i, c i • R i = 0)
    {K : ℕ} (hK : NegIndexLE B K) : Fintype.card ι ≤ K :=
  card_le_of_isotropic B hB R hind
    (chain_isotropic_circle B hB E hE α R P rk hP (conj_mul_ne_one_of_one_lt_norm hα) hZ) hrad hK

/-! ## Upper bound: each hyperbolic pair costs at most one negative square -/

/-- Coefficient-space form of the codimension bound: if `Q ≥ 0` on the kernel of a linear map
`ℓ : ℂ^n → ℂ^ι` and `Q < 0` off `0`, then `n ≤ |ι|`. -/
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

/-- If `Re B(v,v) ≥ 0` on the common kernel of `k` linear functionals, the negative index of `B`
is at most `k`. -/
theorem negIndexLE_of_nonneg_on_ker (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {κ : Type*} [Fintype κ]
    (ℓ : V →ₗ[ℂ] (κ → ℂ)) (hQ : ∀ v, ℓ v = 0 → 0 ≤ (B v v).re) :
    NegIndexLE B (Fintype.card κ) := by
  intro n w hw
  let L : (Fin n → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ w
  have hL : ∀ c, L c = ∑ i, c i • w i := fun c => by
    simp [L, Fintype.linearCombination_apply]
  refine card_le_of_nonneg_on_ker (fun c => (B (L c) (L c)).re) (ℓ.comp L) ?_ ?_
  · intro c hc
    exact hQ (L c) hc
  · intro c hc
    simp only [hL]
    exact hw c hc

/-- **Zero-side model of a Weil-type form.** Suppose the diagonal of a Hermitian form is a
nonnegative part `P` (the on-line zeros: `Σ m(γ) |F(γ)|²`, possibly an infinite sum) plus `k`
hyperbolic pair terms `2 Re(conj (a_j v) · b_j v)` (the off-line pairs
`2 Re(conj F(w₊) F(w₋))`).  Then the negative index is at most `k`: killing `a_j` alone kills the
pair term. -/
theorem zeroSide_negIndexLE (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (P : V → ℝ) (hP : ∀ v, 0 ≤ P v) {k : ℕ}
    (a b : Fin k → (V →ₗ[ℂ] ℂ))
    (hdiag : ∀ v, (B v v).re = P v + ∑ j, 2 * (conj (a j v) * b j v).re) :
    NegIndexLE B k := by
  have := negIndexLE_of_nonneg_on_ker B (LinearMap.pi a) (fun v hv => by
    rw [hdiag v]
    have hz : ∀ j, a j v = 0 := fun j => congrFun hv j
    simp only [hz, map_zero, zero_mul, Complex.zero_re, mul_zero, Finset.sum_const_zero,
      add_zero]
    exact hP v)
  simpa using this

/-! ## Lower bound: detection -/

/-- **The detector's pair value.** At an off-line pair `w₊ = γ + iδ`, `w₋ = γ - iδ`, the
detector `F = (Φ̂ - R)(z - a)/((z - w₊)(z - w₋))` takes the values `F(w₋) = X/(-2iδ)` and
`F(w₊) = conj X/(2iδ)` with `X = Ξ'(w₋)(w₋ - a)` (real `a`); the pair contributes
`2 Re(conj F(w₊) F(w₋)) = -Re(X²)/(2δ²)`. -/
theorem detector_pair_term (X : ℂ) {δ : ℝ} (hδ : δ ≠ 0) :
    2 * (conj (conj X / (2 * Complex.I * δ)) * (X / -(2 * Complex.I * δ))).re
      = -(X ^ 2).re / (2 * δ ^ 2) := by
  have hI : conj (conj X / (2 * Complex.I * δ)) = X / -(2 * Complex.I * δ) := by
    rw [map_div₀, Complex.conj_conj, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_ofNat]
    ring
  rw [hI]
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ
  have hprod : X / -(2 * Complex.I * δ) * (X / -(2 * Complex.I * δ))
      = -(X ^ 2) / ((4 * δ ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hprod, Complex.div_ofReal_re, Complex.neg_re]
  field_simp
  ring

/-- A real shift `s = γ - a` making the pair value at least `‖c‖² δ²`: take `s = pδ/q` when
`q = Im c ≠ 0` (then `c(s - iδ)` is real) and `s = 2δ` when `c` is real. -/
theorem exists_detector_phase (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℝ, ‖c‖ ^ 2 * δ ^ 2 ≤ ((c * ((s : ℂ) - (δ : ℂ) * Complex.I)) ^ 2).re := by
  have hre : ∀ s : ℝ, ((c * ((s : ℂ) - (δ : ℂ) * Complex.I)) ^ 2).re
      = (c.re * s + c.im * δ) ^ 2 - (c.im * s - c.re * δ) ^ 2 := by
    intro s
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hn : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  by_cases hq : c.im = 0
  · refine ⟨2 * δ, ?_⟩
    rw [hre, hn, hq]
    nlinarith [sq_nonneg (c.re * δ)]
  · refine ⟨c.re * δ / c.im, ?_⟩
    rw [hre, hn]
    have h1 : c.im * (c.re * δ / c.im) - c.re * δ = 0 := by field_simp; ring
    have h2 : c.re * (c.re * δ / c.im) + c.im * δ = δ * (c.re ^ 2 + c.im ^ 2) / c.im := by
      field_simp
    rw [h1, h2, div_pow]
    have hq2 : 0 < c.im ^ 2 := by positivity
    rw [le_sub_iff_add_le, le_div_iff₀ hq2]
    nlinarith [sq_nonneg c.re, sq_nonneg c.im, sq_nonneg δ, mul_pos hq2 (by positivity : (0:ℝ) < δ ^ 2),
      mul_nonneg (mul_nonneg (sq_nonneg c.re) (sq_nonneg δ)) (add_nonneg (sq_nonneg c.re) (sq_nonneg c.im))]

/-- **One off-line pair, one negative square.** For every value `c = Ξ'(w₋)` and every half-width
`δ > 0` there is a real `a` for which the detector's pair term is at most `-‖c‖²/2`. -/
theorem detector_pair_term_le (c : ℂ) (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℝ, 2 * (conj (conj (c * (((γ - a : ℝ) : ℂ) - (δ : ℂ) * Complex.I))
        / (2 * Complex.I * δ)) * ((c * (((γ - a : ℝ) : ℂ) - (δ : ℂ) * Complex.I))
        / -(2 * Complex.I * δ))).re ≤ -‖c‖ ^ 2 / 2 := by
  obtain ⟨s, hs⟩ := exists_detector_phase c hδ
  refine ⟨γ - s, ?_⟩
  have hsa : γ - (γ - s) = s := by ring
  rw [hsa, detector_pair_term _ hδ.ne']
  have hδ2 : 0 < 2 * δ ^ 2 := by positivity
  rw [div_le_iff₀ hδ2]
  nlinarith [hs]

/-- Swapping an off-diagonal double sum. -/
lemma sum_erase_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f i j = ∑ j, ∑ i ∈ Finset.univ.erase j, f i j := by
  have h1 : ∀ i, ∑ j ∈ Finset.univ.erase i, f i j = ∑ j, f i j - f i i := fun i =>
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  have h2 : ∀ j, ∑ i ∈ Finset.univ.erase j, f i j = ∑ i, f i j - f j j := fun j =>
    Finset.sum_erase_eq_sub (Finset.mem_univ j)
  simp only [h1, h2, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

/-- **Almost-orthogonal detectors give negative squares (Gershgorin form).** If `m` vectors have
`Re B(w_i,w_i) ≤ -η` and off-diagonal row sums `Σ_{j≠i} ‖B(w_i,w_j)‖ < η`, they span a
negative-definite subspace; so the negative index is at least `m`.  This is the step
"distinct off-line pairs give almost `QW`-orthogonal detectors, hence `κ(x) ≥ #pairs`". -/
theorem isNegFamily_of_diag_dominant (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (w : ι → V) {η : ℝ}
    (hdiag : ∀ i, (B (w i) (w i)).re ≤ -η)
    (hoff : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖B (w i) (w j)‖ < η) : IsNegFamily B w := by
  intro c hc
  set G : ι → ι → ℂ := fun i j => B (w i) (w j) with hG
  have hGsymm : ∀ i j, ‖G j i‖ = ‖G i j‖ := fun i j => by
    simp only [hG]; rw [← hB (w i) (w j), Complex.norm_conj]
  have hexp : B (∑ i, c i • w i) (∑ j, c j • w j) = ∑ i, ∑ j, conj (c i) * c j * G i j := by
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [B_smul_left, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [B_smul_right]; ring
  rw [hexp, Complex.re_sum]
  -- the diagonal term
  have hdiagterm : ∀ i, (conj (c i) * c i * G i i).re = ‖c i‖ ^ 2 * (G i i).re := by
    intro i
    have : conj (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, Complex.re_ofReal_mul]
  -- the off-diagonal terms
  have hoffterm : ∀ i j, (conj (c i) * c j * G i j).re
      ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖G i j‖ := by
    intro i j
    calc (conj (c i) * c j * G i j).re ≤ ‖conj (c i) * c j * G i j‖ := Complex.re_le_norm _
      _ = ‖c i‖ * ‖c j‖ * ‖G i j‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖G i j‖ := by
        gcongr
        nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
  have hrow : ∀ i, (∑ j, conj (c i) * c j * G i j).re
      ≤ ‖c i‖ ^ 2 * (G i i).re
        + ∑ j ∈ Finset.univ.erase i, (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖G i j‖ := by
    intro i
    rw [Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiagterm]
    gcongr with j hj
    exact hoffterm i j
  have hsum_le : ∑ i, (∑ j, conj (c i) * c j * G i j).re
      ≤ ∑ i, ‖c i‖ ^ 2 * ((G i i).re + ∑ j ∈ Finset.univ.erase i, ‖G i j‖) := by
    refine (Finset.sum_le_sum fun i _ => hrow i).trans (le_of_eq ?_)
    have hsplit : ∀ i, ∑ j ∈ Finset.univ.erase i, (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * ‖G i j‖
        = ∑ j ∈ Finset.univ.erase i, ‖c i‖ ^ 2 / 2 * ‖G i j‖
          + ∑ j ∈ Finset.univ.erase i, ‖c j‖ ^ 2 / 2 * ‖G i j‖ := by
      intro i
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hsplit, Finset.sum_add_distrib]
    have hswap : ∑ i, ∑ j ∈ Finset.univ.erase i, ‖c j‖ ^ 2 / 2 * ‖G i j‖
        = ∑ i, ∑ j ∈ Finset.univ.erase i, ‖c i‖ ^ 2 / 2 * ‖G i j‖ := by
      rw [sum_erase_swap]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hGsymm]
    rw [hswap]
    have hfac : ∀ i, ‖c i‖ ^ 2 * ((G i i).re + ∑ j ∈ Finset.univ.erase i, ‖G i j‖)
        = ‖c i‖ ^ 2 * (G i i).re + (∑ j ∈ Finset.univ.erase i, ‖c i‖ ^ 2 / 2 * ‖G i j‖
          + ∑ j ∈ Finset.univ.erase i, ‖c i‖ ^ 2 / 2 * ‖G i j‖) := by
      intro i
      rw [← Finset.sum_add_distrib, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hfac, Finset.sum_add_distrib]
  refine lt_of_le_of_lt hsum_le ?_
  obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    exact hc (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have hneg : ∀ i, (G i i).re + ∑ j ∈ Finset.univ.erase i, ‖G i j‖ < 0 := fun i => by
    have := hdiag i; have := hoff i; simp only [hG] at *; linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
  have h0 : ‖c i0‖ ^ 2 * ((G i0 i0).re + ∑ j ∈ Finset.univ.erase i0, ‖G i0 j‖) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (hneg i0)
  have h1 : ∑ i ∈ Finset.univ.erase i0,
      ‖c i‖ ^ 2 * ((G i i).re + ∑ j ∈ Finset.univ.erase i, ‖G i j‖) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (by positivity) (hneg i).le
  linarith

/-! ## Galerkin truncations: matrices with displacement structure -/

section Displacement

variable {n : Type*} [Fintype n]

/-- The sesquilinear form `(u, v) ↦ Σᵢ Σⱼ conj (u i) A i j v j` of a square matrix. -/
def matForm (A : Matrix n n ℂ) : (n → ℂ) →ₗ⋆[ℂ] (n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun u v => ∑ i, ∑ j, conj (u i) * A i j * v j)
    (fun u₁ u₂ v => by
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun a u v => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
    (fun u v₁ v₂ => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a u v => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

lemma matForm_apply (A : Matrix n n ℂ) (u v : n → ℂ) :
    matForm A u v = ∑ i, ∑ j, conj (u i) * A i j * v j := rfl

lemma matForm_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) : IsHermitian (matForm A) := by
  intro u v
  simp only [matForm_apply, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have h : conj (A i j) = A j i := by
    have := congrFun (congrFun hA j) i
    simpa [Matrix.conjTranspose_apply] using this
  rw [h]; ring

/-- **Displacement structure gives `z²`-symmetry.**  If the commutator of `A` with a real diagonal
`Ω` has the form `ℓ g* - g ℓ*` (`ℓ` real), then multiplication by `Ω` is `A`-symmetric on vectors
annihilated by `ℓ`.  For the Galerkin matrix of a translation-invariant form on
`L²[-L/2, L/2]`, `Ω = diag((kω)²)` is multiplication by `z²` on transforms and `ℓ` is the boundary
functional `f ↦ f(L/2)` (even sector) or `f ↦ f'(L/2)` (odd sector). -/
theorem matForm_diag_symm (A : Matrix n n ℂ) (Ω ℓ : n → ℝ) (g : n → ℂ)
    (hdisp : ∀ i j, ((Ω i : ℂ) - Ω j) * A i j = (ℓ i : ℂ) * conj (g j) - g i * (ℓ j : ℂ))
    (u v : n → ℂ) (hu : ∑ i, (ℓ i : ℂ) * u i = 0) (hv : ∑ i, (ℓ i : ℂ) * v i = 0) :
    matForm A (fun i => (Ω i : ℂ) * u i) v = matForm A u (fun j => (Ω j : ℂ) * v j) := by
  rw [← sub_eq_zero, matForm_apply, matForm_apply, ← Finset.sum_sub_distrib]
  have hterm : ∀ i j, conj ((Ω i : ℂ) * u i) * A i j * v j - conj (u i) * A i j * ((Ω j : ℂ) * v j)
      = conj (u i) * v j * ((ℓ i : ℂ) * conj (g j) - g i * (ℓ j : ℂ)) := by
    intro i j
    rw [← hdisp i j, map_mul, Complex.conj_ofReal]
    ring
  simp only [← Finset.sum_sub_distrib, hterm]
  have hu' : ∑ i, conj (u i) * (ℓ i : ℂ) = 0 := by
    have := congrArg conj hu
    simp only [map_sum, map_mul, Complex.conj_ofReal, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsplit : ∀ i, ∑ j, conj (u i) * v j * ((ℓ i : ℂ) * conj (g j) - g i * (ℓ j : ℂ))
      = conj (u i) * (ℓ i : ℂ) * (∑ j, conj (g j) * v j)
        - conj (u i) * g i * (∑ j, (ℓ j : ℂ) * v j) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [hsplit, hv, mul_zero, sub_zero]
  rw [← Finset.sum_mul, hu', zero_mul]

/-- **Pontryagin--Caratheodory--Fejer for Galerkin matrices (finite, concrete).**  Let `Q` be a
Hermitian matrix with displacement structure `(Ωᵢ - Ωⱼ) Qᵢⱼ = ℓᵢ conj gⱼ - gᵢ ℓⱼ` (`Ω, ℓ` real),
`c` an eigenvector, `(Q - λ) c = 0`, and `wᵢ` distinct points of the open upper half-plane solving
the secular equation `Σₖ ℓₖ cₖ/(Ωₖ - wᵢ) = 0` (for the window Weil form these are the squares of
the zeros of the eigenvector's transform in the open first quadrant, even sector).  If the vectors
`Rᵢ = (Ω - wᵢ)⁻¹ c` are independent and their span meets `ker (Q - λ)` only in `0`, then the number
of such `wᵢ` is at most every bound `K` for the negative index of `Q - λ`. -/
theorem galerkin_pontryagin_cvs [DecidableEq n] (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (lam : ℝ)
    (Ω ℓ : n → ℝ) (g : n → ℂ)
    (hdisp : ∀ i j, ((Ω i : ℂ) - Ω j) * Q i j = (ℓ i : ℂ) * conj (g j) - g i * (ℓ j : ℂ))
    (c : n → ℂ) (hc : (Q - (lam : ℂ) • (1 : Matrix n n ℂ)).mulVec c = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) (hw : ∀ i, 0 < (w i).im)
    (hsec : ∀ i, ∑ k, (ℓ k : ℂ) * (c k / ((Ω k : ℂ) - w i)) = 0)
    (hind : LinearIndependent ℂ (fun i k => c k / ((Ω k : ℂ) - w i)))
    (hrad : ∀ a : ι → ℂ, (∀ v, matForm (Q - (lam : ℂ) • (1 : Matrix n n ℂ))
        (∑ i, a i • (fun k => c k / ((Ω k : ℂ) - w i))) v = 0) →
        ∑ i, a i • (fun k => c k / ((Ω k : ℂ) - w i)) = 0)
    {K : ℕ} (hK : NegIndexLE (matForm (Q - (lam : ℂ) • (1 : Matrix n n ℂ))) K) :
    Fintype.card ι ≤ K := by
  set A : Matrix n n ℂ := Q - (lam : ℂ) • (1 : Matrix n n ℂ) with hAdef
  have hA : A.IsHermitian := by
    rw [hAdef]
    refine hQ.sub ?_
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hdispA : ∀ i j, ((Ω i : ℂ) - Ω j) * A i j = (ℓ i : ℂ) * conj (g j) - g i * (ℓ j : ℂ) := by
    intro i j
    rw [← hdisp i j, hAdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  set R : ι → n → ℂ := fun i k => c k / ((Ω k : ℂ) - w i) with hRdef
  have hden : ∀ i k, (Ω k : ℂ) - w i ≠ 0 := by
    intro i k h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
    linarith [hw i]
  have hΩR : ∀ i, (c + w i • R i) = fun k => (Ω k : ℂ) * R i k := by
    intro i
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hRdef]
    field_simp [hden i k]
    ring
  have hE : ∀ v, matForm A c v = 0 := by
    intro v
    rw [matForm_apply, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : ∑ i, conj (c i) * A i j = 0 := by
      have h1 : ∑ i, A j i * c i = 0 := by
        have := congrFun hc j
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 := congrArg conj h1
      simp only [map_sum, map_mul, map_zero] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : conj (A j i) = A i j := by
        have := congrFun (congrFun hA i) j
        simpa [Matrix.conjTranspose_apply] using this
      rw [this, mul_comm]
    rw [← Finset.sum_mul, hj, zero_mul]
  refine pontryagin_cvs_line (matForm A) (matForm_isHermitian hA) c hE w R (fun _ => c)
    (fun _ => 1) (fun _ => Or.inl rfl) hw ?_ hind hrad hK
  intro i j
  rw [hΩR i, hΩR j]
  exact matForm_diag_symm A Ω ℓ g hdispA (R i) (R j) (hsec i) (hsec j)

end Displacement

end Krein

end Crux.SpectralOperator

#print axioms Crux.SpectralOperator.B_smul_left
#print axioms Crux.SpectralOperator.B_smul_right
#print axioms Crux.SpectralOperator.chain_isotropic_line
#print axioms Crux.SpectralOperator.chain_isotropic_circle
#print axioms Crux.SpectralOperator.conj_ne_of_im_pos
#print axioms Crux.SpectralOperator.conj_ne_of_im_neg
#print axioms Crux.SpectralOperator.conj_mul_ne_one_of_norm_lt
#print axioms Crux.SpectralOperator.conj_mul_ne_one_of_one_lt_norm
#print axioms Crux.SpectralOperator.exists_dual_family
#print axioms Crux.SpectralOperator.exists_neg_gram
#print axioms Crux.SpectralOperator.isNegFamily_of_gram
#print axioms Crux.SpectralOperator.isNegFamily_comp_equiv
#print axioms Crux.SpectralOperator.card_le_of_isotropic
#print axioms Crux.SpectralOperator.isHermitian_neg
#print axioms Crux.SpectralOperator.pontryagin_cvs_line
#print axioms Crux.SpectralOperator.pontryagin_cvs_line_pos
#print axioms Crux.SpectralOperator.no_upper_zeros_of_psd
#print axioms Crux.SpectralOperator.iohvidov_krein_circle
#print axioms Crux.SpectralOperator.pontryagin_cvs_line_lower
#print axioms Crux.SpectralOperator.iohvidov_krein_circle_outside
#print axioms Crux.SpectralOperator.card_le_of_nonneg_on_ker
#print axioms Crux.SpectralOperator.negIndexLE_of_nonneg_on_ker
#print axioms Crux.SpectralOperator.zeroSide_negIndexLE
#print axioms Crux.SpectralOperator.detector_pair_term
#print axioms Crux.SpectralOperator.exists_detector_phase
#print axioms Crux.SpectralOperator.detector_pair_term_le
#print axioms Crux.SpectralOperator.sum_erase_swap
#print axioms Crux.SpectralOperator.isNegFamily_of_diag_dominant
#print axioms Crux.SpectralOperator.matForm_apply
#print axioms Crux.SpectralOperator.matForm_isHermitian
#print axioms Crux.SpectralOperator.matForm_diag_symm
#print axioms Crux.SpectralOperator.galerkin_pontryagin_cvs
