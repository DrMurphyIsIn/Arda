/-
  Crux2_semilocal_archimedean.lean (rvm_bridge island) -- the buildable core of "Semi-local Weil
  positivity is critical: the S-local horizon is the next prime q plus W0(sqrt q / 2)/(2 pi), and
  every prime is load-bearing at its own scale" (crux round 2, lens: semilocal-archimedean).

  conjecture1_proved = False.  Nothing here says where the zeros of zeta lie.  The file maps the
  semi-local (archimedean + finitely many primes) lens onto the wall and shows it carries no
  positivity reservoir; it proves no positivity statement about zeta.

  Checked by: cd telperion/examples/rvm_bridge/lean &&
    leanlock.sh lake env lean Crux/Crux2_semilocal_archimedean.lean
  (Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 @ fbdc36bb).  No `sorry`, `admit`, `native_decide`,
  `opaque` or new `axiom`; the `#print axioms` block at the end reports only propext,
  Classical.choice, Quot.sound for every declaration.

  OBJECTS.  Everything is stated for the REGISTRY functional of E6Bridge4/5 (`archSide`,
  `primeSide`, `weilForm`, `autocorr`, and the unconditional explicit formula), not for abstract
  reals.  `sLocalWeilForm q f := archSide f - (prime side over the prime powers p^k with p < q)`
  is the S_q-local Weil functional, S_q = {primes < q}: the Gamma_R term, both pole terms, and
  every power of every prime in S_q.  Windows are `[-L/2, L/2]`, L = log x (the autocorrelation
  lives on (1/x, x)).  `SLocalIndefinite q L`: some Weil test on the window has W_{S_q} < 0;
  x*_{S_q} is the threshold (monotone: `sLocalIndefinite_mono`).

  WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
  A. Deficit identity `sLocalWeilForm_eq`: W_{S_q}(f) = W(f) + deficit_q(f) for f of bounded
     support (finite sums; the deleted prime powers are exactly those with minFac >= q).
  B. The relabeling, labelled as such: `sLocal_eq_weil_of_window` (on L <= log q, W_{S_q} = W),
     `sLocalIndefinite_iff_of_window` (part (a) of the horizon theorem: x*_{S_q} >= q iff window
     Weil positivity at q), `rh_iff_semilocal_natural_windows` and
     `rh_iff_no_natural_window_indefinite` (RH iff no S_q is indefinite on its natural window, via
     the unconditional Weil criterion of E6Bridge9).  Weil's criterion restated; NOT progress.
  C. The no-go skeleton, on the registry functional:
     `prime_of_missing` (on q < x < q^2 the deleted prime powers <= x are the primes in [q, x]);
     the sign lemma `realAutocorr_neg_of_odd` (sharp probe G 1_W or smooth probe: h_g(a) < 0 for
     L/2 < a < L) and `realAutocorr_nonpos_of_odd`; `deficit_re_le` (the whole deficit is at most
     its first term 2 (log q/sqrt q) h_g(log q) < 0, `overlap_first_neg`); `sLocal_neg_of_probe`
     (Re W(g) <= U < 2 (log q/sqrt q)|h_g(log q)|  ==>  Re W_{S_q}(g) < 0); the zero-side forms
     `weilForm_autocorr_hasSum`, `weilForm_re_le_zero_majorant` (Re W(g * g~) <= sum_rho m(rho)
     |g^(gamma_rho)| |g^(conj gamma_rho)|, every zero on or off the line) and
     `sLocalIndefinite_of_zero_side`; the named obligation `ProbeInput q x` and
     `horizon_of_probeInput` (ProbeInput q x  ==>  x*_{S_q} <= x).
  D. The two-sided precision barrier, structural half: `precision_decrease_detected` (odd probe:
     Lambda(n0) -> (1 + delta) Lambda(n0), delta < 0, lowers W by a strictly positive amount) and
     `precision_increase_detected` (even positive probe, delta > 0), with `realAutocorr_pos_of_pos`.
  E. Surgery negative controls (F = zeta * (1 + c p0^{-s} + p0^{1-2s}), a = c/sqrt p0):
     `latticeForm_nonneg_iff` (the surgery term on N lattice points, coefficients
     c_m = C_m(-a) = (-1)^m (r^m + r^{-m}), is PSD for EVERY N iff |a| <= 2; fails at N = 2),
     `surgery_local_rh_iff` (all zeros of 2 cosh w + a lie on Re w = 0 iff |a| <= 2: local RH),
     `partial_shift_bound` + `surgery_term_ge` (on windows p0 < x < p0^2 the surgery term is
     >= log p0 (2 - |a|) ||g||^2), `pair_probe_identities` + `pair_probe_surgery_value` (the pair
     probe attains log p0 (2 - a) exactly: the plateau value), `golden_violates` (a = sqrt 5),
     `w1_violates` (a = 11/sqrt 29).
  F. Fourier envelope: `poisson_kernel_le`, `local_symbol_ge` (each prime's symbol
     log p (1 - P_{p^{-1/2}}(t log p)) >= -2 log p/(sqrt p - 1); sums to the envelope -2 A_P).

  DOES NOT ESTABLISH (and where it lives):
  * `ProbeInput q x` itself.  For the Polya-kernel probe g = Phi' chi it needs Phi^ = Xi
    (Riemann's theta identity; not in Mathlib or Zeta23), Phi' < 0 on (0, oo) (Csordas-Norfolk-
    Varga 1986), and zero counting for the tail sum.  THEOREM-paper-proof with sketched constants
    in the research README (section 3); numerically verified (verify_probe_law.py).
  * The onset law Delta(q) = W0(sqrt q/2)/(2 pi) (1 + o(1)): paper asymptotics + numerics.
  * Any lower bound x*_{S_q} >= q for q >= 5: that is window Weil positivity (RH-window).
  * The Galerkin horizons, the pole-free archimedean horizon ~3.27, the non-monotonicity in S,
    the precision onsets: COMPUTED (research README; negative Galerkin eigenvalues re-derived
    independently from the zero side).
  * The fooling identity Q_F = Q_zeta + Z for the surgery fakes (paper; E proves only the
    algebra of Z and its link to local RH).
  NEGATIVE CONTROL.  A-D use no property of zeta beyond the explicit-formula bookkeeping; the
  Davenport-Heilbronn function satisfies the same statements for coefficient truncations (its
  probe uses Xi_D).  That is the correct behaviour of a no-go/relabeling result: it asserts no
  positivity, so D, Epstein and the surgery fakes cannot contradict it, and E shows the fakes are
  separated only by the local failure |a| > 2 at their own prime.

  Supersedes the idea-stage scratch SemilocalHorizonCore.lean (li_positivity, abstract reals):
  its sign lemma, assembly and deficit bound now live on the registry functional, and its
  lattice / violation lemmas are strengthened to all N and to local RH.

  CONSUMED (all unconditional on this island): RvMBridge4.limit_explicit_formula,
  RvMBridge4.weilKernel_eq_paperFT_gammaOf, RvMBridge5.autocorr_eq_weilTest,
  RvMBridge5.isWeilTest_autocorr, RvMBridge5.rh_implies_weil_positivity,
  RvMBridge9.weil_positivity_implies_rh, Zeta23.EF.paperFT_weilTest.
-/
import E6Bridge9
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open WeilExplicit ArithmeticFunction MeasureTheory Zeta23
open scoped ComplexConjugate

noncomputable section

namespace Crux2SemilocalArchimedean

/-! ## 1. The `S_q`-local Weil functional, on the registry objects -/

/-- The `n`-th term of the registry prime side `WeilExplicit.primeSide`. -/
def primeTerm (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (f (Real.log n) + f (-Real.log n))

lemma primeSide_eq (f : ℝ → ℂ) : primeSide f = ∑' n : ℕ, primeTerm f n := rfl

/-- The `S_q`-local prime side, `S_q = {p prime : p < q}`: only the prime powers `p^k` with
`p < q` are kept (on the support of `Λ`, `n.minFac` is the prime `p`). -/
def sLocalPrimeSide (q : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, if n.minFac < q then primeTerm f n else 0

/-- The `S_q`-local Weil functional: the registry archimedean side (the Gamma_R term and the two
pole terms) minus the `S_q`-local prime side. -/
def sLocalWeilForm (q : ℕ) (f : ℝ → ℂ) : ℂ := archSide f - sLocalPrimeSide q f

/-- The deficit: the prime powers whose prime is at least `q` (the ones `S_q` deletes). -/
def deficit (q : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, if q ≤ n.minFac then primeTerm f n else 0

lemma primeTerm_eq_zero_of_exp_lt {f : ℝ → ℂ} {M : ℝ} (hf : ∀ u, M < |u| → f u = 0) {n : ℕ}
    (hn : Real.exp M < n) : primeTerm f n = 0 := by
  have hpos : (0 : ℝ) < n := lt_trans (Real.exp_pos M) hn
  have hlog : M < Real.log n := (Real.lt_log_iff_exp_lt hpos).mpr hn
  have hM : M < |Real.log n| := lt_of_lt_of_le hlog (le_abs_self _)
  have hM' : M < |-Real.log n| := by rwa [abs_neg]
  simp [primeTerm, hf _ hM, hf _ hM']

lemma support_subset_range {f : ℝ → ℂ} {M : ℝ} (hf : ∀ u, M < |u| → f u = 0) (P : ℕ → Prop)
    [DecidablePred P] :
    ∀ n ∉ Finset.range (⌈Real.exp M⌉₊ + 1), (if P n then primeTerm f n else 0) = 0 := by
  intro n hn
  have hn' : ⌈Real.exp M⌉₊ + 1 ≤ n := by simpa using hn
  have hlt : Real.exp M < n := by
    have h1 : Real.exp M ≤ ⌈Real.exp M⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp M⌉₊ : ℕ) : ℝ) < n := by exact_mod_cast (by omega : ⌈Real.exp M⌉₊ < n)
    linarith
  split_ifs <;> simp [primeTerm_eq_zero_of_exp_lt hf hlt]

/-- **Deficit identity** (definitional, on the registry objects): for `f` vanishing outside a
bounded window, `W_{S_q}(f) = W(f) + deficit_q(f)`. -/
theorem sLocalWeilForm_eq {f : ℝ → ℂ} {M : ℝ} (hf : ∀ u, M < |u| → f u = 0) (q : ℕ) :
    sLocalWeilForm q f = weilForm f + deficit q f := by
  set s := Finset.range (⌈Real.exp M⌉₊ + 1)
  have h1 : primeSide f = ∑ n ∈ s, primeTerm f n := by
    rw [primeSide_eq]
    refine tsum_eq_sum ?_
    intro n hn
    have := support_subset_range hf (fun _ => True) n hn
    simpa using this
  have h2 : sLocalPrimeSide q f = ∑ n ∈ s, (if n.minFac < q then primeTerm f n else 0) :=
    tsum_eq_sum (support_subset_range hf _)
  have h3 : deficit q f = ∑ n ∈ s, (if q ≤ n.minFac then primeTerm f n else 0) :=
    tsum_eq_sum (support_subset_range hf _)
  have hsplit : ∑ n ∈ s, primeTerm f n = ∑ n ∈ s, (if n.minFac < q then primeTerm f n else 0)
      + ∑ n ∈ s, (if q ≤ n.minFac then primeTerm f n else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n.minFac < q
    · simp [h, not_le.mpr h]
    · simp [h, le_of_not_gt h]
  unfold sLocalWeilForm weilForm
  rw [h1, h2, h3, hsplit]
  ring

/-- If `f` vanishes on `|u| ≥ log q`, the deficit of `S_q` is zero. -/
theorem deficit_eq_zero_of_window {f : ℝ → ℂ} {q : ℕ} (hq : 1 ≤ q)
    (hf : ∀ u, Real.log q ≤ |u| → f u = 0) : deficit q f = 0 := by
  unfold deficit
  have : ∀ n : ℕ, (if q ≤ n.minFac then primeTerm f n else 0) = 0 := by
    intro n
    split_ifs with h
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [primeTerm]
      · have hle : q ≤ n := h.trans (Nat.minFac_le hpos)
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
        have hlog : Real.log q ≤ Real.log n :=
          Real.log_le_log hq0 (by exact_mod_cast hle)
        have ha : Real.log q ≤ |Real.log n| := hlog.trans (le_abs_self _)
        have hb : Real.log q ≤ |-Real.log n| := by rwa [abs_neg]
        simp [primeTerm, hf _ ha, hf _ hb]
    · rfl
  simp [this]

/-! ## 2. Windows, the natural-window identity, and the relabeling -/

lemma vanish_of_tsupport {g : ℝ → ℂ} {L : ℝ} (h : tsupport g ⊆ Set.Icc (-(L / 2)) (L / 2)) :
    ∀ v, L / 2 < |v| → g v = 0 := by
  intro v hv
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h' := h hmem
  rw [Set.mem_Icc] at h'
  have : |v| ≤ L / 2 := abs_le.mpr h'
  linarith

lemma tsupport_subset_of_vanish {g : ℝ → ℂ} {b : ℝ} (hs : ∀ v, b < |v| → g v = 0) :
    tsupport g ⊆ Set.Icc (-b) b := by
  refine closure_minimal ?_ isClosed_Icc
  intro v hv
  have hv' : g v ≠ 0 := hv
  have : |v| ≤ b := not_lt.mp fun h => hv' (hs v h)
  exact abs_le.mp this

/-- The autocorrelation of a function supported in `[-L/2, L/2]` vanishes on `|u| ≥ L` (at
`|u| = L` the overlap is the single point `u/2`). -/
lemma autocorr_eq_zero_of_le {g : ℝ → ℂ} {L : ℝ} (hs : ∀ v, L / 2 < |v| → g v = 0) {u : ℝ}
    (hu : L ≤ |u|) : autocorr g u = 0 := by
  unfold autocorr
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (t := {u / 2}) ?_ (measure_singleton _)
  intro v hv
  have hv' : ¬ (g v * conj (g (v - u)) = 0) := hv
  have h1 : g v ≠ 0 := fun h => hv' (by simp [h])
  have h2 : g (v - u) ≠ 0 := fun h => hv' (by simp [h])
  have a1 : |v| ≤ L / 2 := not_lt.mp (fun h => h1 (hs v h))
  have a2 : |v - u| ≤ L / 2 := not_lt.mp (fun h => h2 (hs _ h))
  rw [abs_le] at a1 a2
  simp only [Set.mem_singleton_iff]
  rcases le_abs.mp hu with h | h <;> linarith

/-- **Natural-window identity** (a relabeling, flagged as such): on `L ≤ log q` the `S_q`-local
functional IS the full Weil functional. -/
theorem sLocal_eq_weil_of_window {g : ℝ → ℂ} {L : ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hsupp : tsupport g ⊆ Set.Icc (-(L / 2)) (L / 2)) (hL : L ≤ Real.log q) :
    sLocalWeilForm q (autocorr g) = weilForm (autocorr g) := by
  have hs := vanish_of_tsupport hsupp
  have hf : ∀ u, L < |u| → autocorr g u = 0 := fun u hu => autocorr_eq_zero_of_le hs hu.le
  rw [sLocalWeilForm_eq hf,
    deficit_eq_zero_of_window hq (fun u hu => autocorr_eq_zero_of_le hs (hL.trans hu)), add_zero]

/-- `W_{S_q}` is indefinite on the window `[-L/2, L/2]`: some Weil test supported there has a
strictly negative `S_q`-local value.  (`x*_{S_q} = sup {e^L : ¬ SLocalIndefinite q L}`.) -/
def SLocalIndefinite (q : ℕ) (L : ℝ) : Prop :=
  ∃ g : ℝ → ℂ, IsWeilTest g ∧ tsupport g ⊆ Set.Icc (-(L / 2)) (L / 2) ∧
    (sLocalWeilForm q (autocorr g)).re < 0

/-- The full Weil form is indefinite on the window `[-L/2, L/2]`. -/
def WeilIndefinite (L : ℝ) : Prop :=
  ∃ g : ℝ → ℂ, IsWeilTest g ∧ tsupport g ⊆ Set.Icc (-(L / 2)) (L / 2) ∧
    (weilForm (autocorr g)).re < 0

/-- Indefiniteness propagates to every larger window (so the horizon `x*_{S_q}` is a threshold). -/
theorem sLocalIndefinite_mono {q : ℕ} {L L' : ℝ} (hLL : L ≤ L') (h : SLocalIndefinite q L) :
    SLocalIndefinite q L' := by
  obtain ⟨g, hg, hsupp, hneg⟩ := h
  refine ⟨g, hg, hsupp.trans ?_, hneg⟩
  intro u hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- Part (a) of the horizon theorem, as an identity: on the natural window `L ≤ log q`,
`S_q`-local indefiniteness is window Weil indefiniteness. -/
theorem sLocalIndefinite_iff_of_window {q : ℕ} (hq : 1 ≤ q) {L : ℝ} (hL : L ≤ Real.log q) :
    SLocalIndefinite q L ↔ WeilIndefinite L := by
  constructor
  · rintro ⟨g, hg, hsupp, hneg⟩
    exact ⟨g, hg, hsupp, by rwa [← sLocal_eq_weil_of_window hq hsupp hL]⟩
  · rintro ⟨g, hg, hsupp, hneg⟩
    exact ⟨g, hg, hsupp, by rwa [sLocal_eq_weil_of_window hq hsupp hL]⟩

/-- **The relabeling, kernel-checked** (Weil's criterion restated; NOT progress on RH): RH holds
iff for every prime `q` the `S_q`-local Weil functional is positive on its natural window. -/
theorem rh_iff_semilocal_natural_windows :
    RiemannHypothesis ↔ ∀ q : ℕ, q.Prime → ∀ L : ℝ, L ≤ Real.log q → ∀ g : ℝ → ℂ,
      IsWeilTest g → tsupport g ⊆ Set.Icc (-(L / 2)) (L / 2) →
        0 ≤ (sLocalWeilForm q (autocorr g)).re := by
  constructor
  · intro hRH q hq L hL g hg hsupp
    rw [sLocal_eq_weil_of_window hq.one_lt.le hsupp hL]
    exact RvMBridge5.rh_implies_weil_positivity hRH g hg
  · intro h
    apply RvMBridge9.weil_positivity_implies_rh
    intro g hg
    obtain ⟨r, hr⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hg.2.isCompact.isBounded
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hr
    set L : ℝ := 2 * |r| with hLdef
    have hsupp : tsupport g ⊆ Set.Icc (-(L / 2)) (L / 2) := by
      intro v hv
      have := hr hv
      rw [Set.mem_Icc] at this ⊢
      have hr' : r ≤ |r| := le_abs_self r
      constructor <;> linarith [this.1, this.2]
    obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (⌈Real.exp L⌉₊ + 1)
    have hqL : L ≤ Real.log q := by
      have h1 : Real.exp L ≤ ⌈Real.exp L⌉₊ := Nat.le_ceil _
      have h2 : ((⌈Real.exp L⌉₊ : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast hqge
      have hqpos : (0 : ℝ) < q := by linarith [Real.exp_pos L]
      exact ((Real.lt_log_iff_exp_lt hqpos).mpr (by linarith)).le
    have := h q hq L hqL g hg hsupp
    rwa [sLocal_eq_weil_of_window hq.one_lt.le hsupp hqL] at this

/-- The same relabeling in indefiniteness form: RH iff no `S_q` is indefinite on its natural
window. -/
theorem rh_iff_no_natural_window_indefinite :
    RiemannHypothesis ↔ ∀ q : ℕ, q.Prime → ¬ SLocalIndefinite q (Real.log q) := by
  rw [rh_iff_semilocal_natural_windows]
  constructor
  · rintro h q hq ⟨g, hg, hsupp, hneg⟩
    exact absurd (h q hq _ le_rfl g hg hsupp) (not_le.mpr hneg)
  · intro h q hq L hL g hg hsupp
    by_contra hneg
    refine h q hq ⟨g, hg, hsupp.trans ?_, lt_of_not_ge hneg⟩
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-! ## 3. The missing prime powers beyond the natural window -/

/-- On `x < q^2` a prime power `n ≤ x` whose prime is `≥ q` is itself prime: the deficit of
`S_q` on windows `q < x < q^2` consists of the primes in `[q, x]` only. -/
theorem prime_of_missing {q n : ℕ} {x : ℝ} (hn : IsPrimePow n) (hq : q ≤ n.minFac)
    (hnx : (n : ℝ) ≤ x) (hx : x < (q : ℝ) ^ 2) : n.Prime := by
  have hfac := hn.minFac_pow_factorization_eq
  have hn1 : n ≠ 1 := hn.ne_one
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  by_contra hnp
  rcases (by omega : n.factorization n.minFac = 0 ∨ n.factorization n.minFac = 1 ∨
      2 ≤ n.factorization n.minFac) with hk | hk | hk
  · rw [hk, pow_zero] at hfac
    exact hn1 hfac.symm
  · rw [hk, pow_one] at hfac
    exact hnp (hfac ▸ hp)
  · have hle : n.minFac ^ 2 ≤ n :=
      (Nat.pow_le_pow_right hp.pos hk).trans hfac.le
    have hq2 : q ^ 2 ≤ n := (Nat.pow_le_pow_left hq 2).trans hle
    have : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hq2
    linarith

/-! ## 4. The sign lemma, on the registry autocorrelation (sharp or smooth windows) -/

/-- The real autocorrelation `h_g(a) = ∫ g(v) g(v - a) dv`. -/
def realAutocorr (g : ℝ → ℝ) (a : ℝ) : ℝ := ∫ v, g v * g (v - a)

/-- For real `g` the registry autocorrelation is the real one. -/
lemma autocorr_ofReal (g : ℝ → ℝ) (a : ℝ) :
    autocorr (fun u => (g u : ℂ)) a = (realAutocorr g a : ℂ) := by
  unfold autocorr realAutocorr
  rw [← integral_complex_ofReal]
  congr 1
  funext v
  simp [Complex.conj_ofReal]

/-- `h_g` is even. -/
lemma realAutocorr_neg (g : ℝ → ℝ) (a : ℝ) : realAutocorr g (-a) = realAutocorr g a := by
  unfold realAutocorr
  have h := integral_sub_right_eq_self (μ := volume) (fun v => g v * g (v + a)) a
  simp only [sub_add_cancel] at h
  simp only [sub_neg_eq_add]
  rw [← h]
  congr 1
  funext v
  ring

/-- Overlap reduction.  `g` vanishes off `[-b, b]` and agrees with `G` on the open window
(`g = G · 1_W` for the sharp probe `G = Φ'`, or `g = G` for a smooth one).  For `b ≤ a ≤ 2b` the
autocorrelation at `a` is the overlap integral of `G` over `[a - b, b]`. -/
lemma realAutocorr_eq_overlap {g G : ℝ → ℝ} {a b : ℝ} (hs : ∀ v, b < |v| → g v = 0)
    (hin : ∀ v, |v| < b → g v = G v) (ha : 0 ≤ a) (hab : a - b ≤ b) :
    realAutocorr g a = ∫ v in (a - b)..b, G v * G (v - a) := by
  unfold realAutocorr
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (a - b) b),
    integral_Icc_eq_integral_Ioo]
  · refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
    have h1 : |v| < b := abs_lt.mpr ⟨by linarith [hv.1], hv.2⟩
    have h2 : |v - a| < b := abs_lt.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    rw [hin v h1, hin (v - a) h2]
  · intro v hv
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
    rcases hv with hv | hv
    · have : b < |v - a| := lt_of_lt_of_le (by linarith) (neg_le_abs (v - a))
      rw [hs _ this, mul_zero]
    · rw [hs v (lt_of_lt_of_le hv (le_abs_self v)), zero_mul]

/-- SIGN LEMMA.  `G` continuous, odd, strictly negative on `(0, b)`: for `b < a < 2b` the overlap
integral is strictly negative. -/
theorem overlap_neg_of_odd {G : ℝ → ℝ} {a b : ℝ} (hG : Continuous G)
    (hodd : ∀ v, G (-v) = -G v) (hneg : ∀ v, 0 < v → v < b → G v < 0)
    (hab : b < a) (ha2 : a < 2 * b) :
    ∫ v in (a - b)..b, G v * G (v - a) < 0 := by
  have hlt : a - b < b := by linarith
  have hcont : Continuous (fun v => -(G v * G (v - a))) :=
    (hG.mul (hG.comp (continuous_id.sub continuous_const))).neg
  have hpos : ∀ v ∈ Set.Ioo (a - b) b, 0 < -(G v * G (v - a)) := by
    intro v hv
    have h1 : G v < 0 := hneg v (by linarith [hv.1]) hv.2
    have h2 : G (a - v) < 0 := hneg (a - v) (by linarith [hv.2]) (by linarith [hv.1])
    have h3 : G (v - a) = -G (a - v) := by
      have := hodd (a - v)
      rwa [neg_sub] at this
    rw [h3]
    nlinarith
  have hI : 0 < ∫ v in (a - b)..b, -(G v * G (v - a)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) hpos hlt
  rw [intervalIntegral.integral_neg] at hI
  linarith

/-- The sign lemma on the genuine autocorrelation: `h_g(a) < 0` for `b < a < 2b`. -/
theorem realAutocorr_neg_of_odd {g G : ℝ → ℝ} {a b : ℝ} (hG : Continuous G)
    (hodd : ∀ v, G (-v) = -G v) (hneg : ∀ v, 0 < v → v < b → G v < 0)
    (hs : ∀ v, b < |v| → g v = 0) (hin : ∀ v, |v| < b → g v = G v)
    (hab : b < a) (ha2 : a < 2 * b) : realAutocorr g a < 0 := by
  rw [realAutocorr_eq_overlap hs hin (by linarith) (by linarith)]
  exact overlap_neg_of_odd hG hodd hneg hab ha2

/-- `h_g(a) ≤ 0` for every `a > b` (it vanishes for `a ≥ 2b`). -/
theorem realAutocorr_nonpos_of_odd {g G : ℝ → ℝ} {a b : ℝ} (hG : Continuous G)
    (hodd : ∀ v, G (-v) = -G v) (hneg : ∀ v, 0 < v → v < b → G v < 0)
    (hs : ∀ v, b < |v| → g v = 0) (hin : ∀ v, |v| < b → g v = G v) (hab : b < a) :
    realAutocorr g a ≤ 0 := by
  rcases lt_or_ge a (2 * b) with ha2 | ha2
  · exact (realAutocorr_neg_of_odd hG hodd hneg hs hin hab ha2).le
  · have hsC : ∀ v, (2 * b) / 2 < |v| → (fun u => (g u : ℂ)) v = 0 := by
      intro v hv
      simp only [Complex.ofReal_eq_zero]
      exact hs v (by linarith)
    have h0 := autocorr_eq_zero_of_le hsC (u := a) (ha2.trans (le_abs_self a))
    rw [autocorr_ofReal, Complex.ofReal_eq_zero] at h0
    rw [h0]

/-- Even-probe sign lemma: `G` continuous and strictly positive on `(-b, b)` (e.g. the Polya
kernel `Φ` itself): `h_g(a) > 0` for `0 ≤ a < 2b`. -/
theorem realAutocorr_pos_of_pos {g G : ℝ → ℝ} {a b : ℝ} (hG : Continuous G)
    (hpos : ∀ v, |v| < b → 0 < G v) (hs : ∀ v, b < |v| → g v = 0)
    (hin : ∀ v, |v| < b → g v = G v) (ha : 0 ≤ a) (ha2 : a < 2 * b) : 0 < realAutocorr g a := by
  rw [realAutocorr_eq_overlap hs hin ha (by linarith)]
  have hlt : a - b < b := by linarith
  have hcont : Continuous (fun v => G v * G (v - a)) :=
    hG.mul (hG.comp (continuous_id.sub continuous_const))
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) ?_ hlt
  intro v hv
  have h1 : 0 < G v := hpos v (abs_lt.mpr ⟨by linarith [hv.1], hv.2⟩)
  have h2 : 0 < G (v - a) := hpos (v - a) (abs_lt.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩)
  exact mul_pos h1 h2

/-! ## 5. The deficit is negative; the horizon assembly on the registry functional -/

/-- The prime term of `autocorr g` for real `g` is `(Λ(n)/√n) · 2 h_g(log n)`. -/
lemma primeTerm_autocorr_ofReal (g : ℝ → ℝ) (n : ℕ) :
    primeTerm (autocorr (fun u => (g u : ℂ))) n
      = ((vonMangoldt n / Real.sqrt n * (2 * realAutocorr g (Real.log n)) : ℝ) : ℂ) := by
  unfold primeTerm
  rw [autocorr_ofReal, autocorr_ofReal, realAutocorr_neg]
  push_cast
  ring

lemma autocorr_vanish_of_window {g : ℝ → ℝ} {x : ℝ} (hs : ∀ v, Real.log x / 2 < |v| → g v = 0) :
    ∀ u, Real.log x < |u| → autocorr (fun u => (g u : ℂ)) u = 0 := by
  intro u hu
  refine autocorr_eq_zero_of_le (L := Real.log x) (fun v hv => ?_) hu.le
  simp only [Complex.ofReal_eq_zero]
  exact hs v hv

/-- **Deficit bound.**  `q` prime, `q < x < q^2`, `L = log x`; `g` real, vanishing off
`[-L/2, L/2]`, equal on the open window to a continuous odd `G` that is negative on `(0, L/2)`.
Every deleted prime power contributes a nonpositive amount, so the deficit is at most the single
term of `q`, which is strictly negative. -/
theorem deficit_re_le {q : ℕ} (hq : q.Prime) {x : ℝ} (hqx : (q : ℝ) < x) (hxq : x < (q : ℝ) ^ 2)
    {g G : ℝ → ℝ} (hG : Continuous G) (hodd : ∀ v, G (-v) = -G v)
    (hneg : ∀ v, 0 < v → v < Real.log x / 2 → G v < 0)
    (hs : ∀ v, Real.log x / 2 < |v| → g v = 0) (hin : ∀ v, |v| < Real.log x / 2 → g v = G v) :
    (deficit q (autocorr (fun u => (g u : ℂ)))).re
      ≤ 2 * (Real.log q / Real.sqrt q) * realAutocorr g (Real.log q) := by
  set b := Real.log x / 2 with hbdef
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hx0 : 0 < x := by linarith
  have hlogq : b < Real.log q := by
    have : Real.log x < Real.log ((q : ℝ) ^ 2) := Real.log_lt_log hx0 hxq
    rw [Real.log_pow] at this
    push_cast at this
    rw [hbdef]
    linarith
  have hsC := autocorr_vanish_of_window hs
  set F : ℕ → ℝ := fun n => if q ≤ n.minFac then
      vonMangoldt n / Real.sqrt n * (2 * realAutocorr g (Real.log n)) else 0 with hFdef
  set s := Finset.range (⌈Real.exp (Real.log x)⌉₊ + 1)
  have hdef : deficit q (autocorr (fun u => (g u : ℂ))) = ((∑ n ∈ s, F n : ℝ) : ℂ) := by
    unfold deficit
    rw [tsum_eq_sum (support_subset_range hsC _)]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hFdef]
    split_ifs
    · rw [primeTerm_autocorr_ofReal]
    · simp
  rw [hdef, Complex.ofReal_re]
  have hqs : q ∈ s := by
    rw [Finset.mem_range, Real.exp_log hx0]
    have : (q : ℝ) ≤ ⌈x⌉₊ := hqx.le.trans (Nat.le_ceil x)
    have : q ≤ ⌈x⌉₊ := by exact_mod_cast this
    omega
  have hFq : F q = 2 * (Real.log q / Real.sqrt q) * realAutocorr g (Real.log q) := by
    simp only [hFdef, hq.minFac_eq, le_refl, if_true, vonMangoldt_apply_prime hq]
    ring
  have hFn : ∀ n ∈ s.erase q, F n ≤ 0 := by
    intro n _
    simp only [hFdef]
    split_ifs with hmin
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · have hle : q ≤ n := hmin.trans (Nat.minFac_le hpos)
        have hlog : Real.log q ≤ Real.log n := Real.log_le_log hq0 (by exact_mod_cast hle)
        have hh := realAutocorr_nonpos_of_odd hG hodd hneg hs hin (lt_of_lt_of_le hlogq hlog)
        have hw : 0 ≤ vonMangoldt n / Real.sqrt n :=
          div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
        nlinarith
    · exact le_refl 0
  rw [← Finset.add_sum_erase s F hqs, hFq]
  have := Finset.sum_nonpos hFn
  linarith

/-- The overlap of the first deleted prime is strictly negative. -/
theorem overlap_first_neg {q : ℕ} (hq : q.Prime) {x : ℝ} (hqx : (q : ℝ) < x)
    (hxq : x < (q : ℝ) ^ 2) {g G : ℝ → ℝ} (hG : Continuous G) (hodd : ∀ v, G (-v) = -G v)
    (hneg : ∀ v, 0 < v → v < Real.log x / 2 → G v < 0)
    (hs : ∀ v, Real.log x / 2 < |v| → g v = 0) (hin : ∀ v, |v| < Real.log x / 2 → g v = G v) :
    realAutocorr g (Real.log q) < 0 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hx0 : 0 < x := by linarith
  have h1 : Real.log x / 2 < Real.log q := by
    have : Real.log x < Real.log ((q : ℝ) ^ 2) := Real.log_lt_log hx0 hxq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h2 : Real.log q < 2 * (Real.log x / 2) := by
    have := Real.log_lt_log hq0 hqx
    linarith
  exact realAutocorr_neg_of_odd hG hodd hneg hs hin h1 h2

/-- **The semi-local horizon, assembled on the registry functional.**  If the full Weil
functional of the probe is at most `U` and `U` is below the overlap of the first deleted prime,
`2 (log q/√q) |h_g(log q)|`, then the `S_q`-local functional is strictly negative.  Covers the
sharp-window probe `g = Φ' · 1_W` (take `G = Φ'`).  The analytic input -- a small full value `U`
-- is a hypothesis. -/
theorem sLocal_neg_of_probe {q : ℕ} (hq : q.Prime) {x : ℝ} (hqx : (q : ℝ) < x)
    (hxq : x < (q : ℝ) ^ 2) {g G : ℝ → ℝ} (hG : Continuous G) (hodd : ∀ v, G (-v) = -G v)
    (hneg : ∀ v, 0 < v → v < Real.log x / 2 → G v < 0)
    (hs : ∀ v, Real.log x / 2 < |v| → g v = 0) (hin : ∀ v, |v| < Real.log x / 2 → g v = G v)
    {U : ℝ} (hU : (weilForm (autocorr (fun u => (g u : ℂ)))).re ≤ U)
    (hUD : U < 2 * (Real.log q / Real.sqrt q) * -(realAutocorr g (Real.log q))) :
    (sLocalWeilForm q (autocorr (fun u => (g u : ℂ)))).re < 0 := by
  rw [sLocalWeilForm_eq (autocorr_vanish_of_window hs), Complex.add_re]
  have hD := deficit_re_le hq hqx hxq hG hodd hneg hs hin
  linarith

/-! ### The analytic input in zero-side form -/

/-- Zero-side representation of the Weil functional of an autocorrelation (the E8 explicit
formula composed with the transform factorisation): `W(g ⋆ g~) = Σ_ρ m(ρ) ĝ(γ_ρ) conj ĝ(conj γ_ρ)`. -/
theorem weilForm_autocorr_hasSum {g : ℝ → ℂ} (hg : IsWeilTest g) :
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ)
        * (paperFT g (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ)))))
      (weilForm (autocorr g)) := by
  have h := (RvMBridge4.limit_explicit_formula _ (RvMBridge5.isWeilTest_autocorr hg)).2
  have hk : ∀ ρ, weilKernel (autocorr g) ρ
      = paperFT g (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ))) := fun ρ => by
    rw [RvMBridge4.weilKernel_eq_paperFT_gammaOf, RvMBridge5.autocorr_eq_weilTest,
      Zeta23.EF.paperFT_weilTest hg.1.continuous hg.1.continuous hg.2 hg.2]
  simp only [hk] at h
  exact h

/-- Unconditional zero-side majorant: `Re W(g ⋆ g~) ≤ Σ_ρ m(ρ) |ĝ(γ_ρ)| |ĝ(conj γ_ρ)|` (every
zero, on or off the line). -/
theorem weilForm_re_le_zero_majorant {g : ℝ → ℂ} (hg : IsWeilTest g)
    (hsum : Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℝ)
        * (‖paperFT g (gammaOf ρ)‖ * ‖paperFT g (conj (gammaOf ρ))‖))) :
    (weilForm (autocorr g)).re ≤ ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ)
        * (‖paperFT g (gammaOf ρ)‖ * ‖paperFT g (conj (gammaOf ρ))‖) := by
  have h := Complex.hasSum_re (weilForm_autocorr_hasSum hg)
  refine hasSum_le (fun ρ => ?_) h hsum.hasSum
  refine (Complex.re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast]

/-- **Horizon theorem, zero-side form.**  For a smooth real probe `g` on the window
`[-L/2, L/2]`, `L = log x`, `q < x < q^2`: if the absolute zero sum
`Σ_ρ m(ρ) |ĝ(γ_ρ)| |ĝ(conj γ_ρ)|` is below the first overlap `2 (log q/√q) |h_g(log q)|`, then
`W_{S_q}` is indefinite on every window `L' ≥ log x`.  The hypothesis `hZ` is exactly what the
Pólya-kernel probe supplies (`ĝ(γ_ρ) = -tail^(γ_ρ)` from `Ξ(γ_ρ) = 0`); it is not proved here. -/
theorem sLocalIndefinite_of_zero_side {q : ℕ} (hq : q.Prime) {x : ℝ} (hqx : (q : ℝ) < x)
    (hxq : x < (q : ℝ) ^ 2) {g : ℝ → ℝ} (hW : IsWeilTest (fun u => (g u : ℂ)))
    (hodd : ∀ v, g (-v) = -g v) (hs : ∀ v, Real.log x / 2 < |v| → g v = 0)
    (hneg : ∀ v, 0 < v → v < Real.log x / 2 → g v < 0)
    (hsum : Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℝ) * (‖paperFT (fun u => (g u : ℂ)) (gammaOf ρ)‖
        * ‖paperFT (fun u => (g u : ℂ)) (conj (gammaOf ρ))‖)))
    (hZ : ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ) * (‖paperFT (fun u => (g u : ℂ)) (gammaOf ρ)‖
        * ‖paperFT (fun u => (g u : ℂ)) (conj (gammaOf ρ))‖)
        < 2 * (Real.log q / Real.sqrt q) * -(realAutocorr g (Real.log q)))
    {L' : ℝ} (hL' : Real.log x ≤ L') : SLocalIndefinite q L' := by
  have hc : Continuous g :=
    (Complex.continuous_re.comp hW.1.continuous).congr (fun u => by simp)
  have hneg' := sLocal_neg_of_probe hq hqx hxq hc hodd hneg hs (fun v _ => rfl)
    (weilForm_re_le_zero_majorant hW hsum) hZ
  refine sLocalIndefinite_mono hL' ⟨fun u => (g u : ℂ), hW, ?_, hneg'⟩
  refine tsupport_subset_of_vanish (b := Real.log x / 2) (fun v hv => ?_)
  simp only [Complex.ofReal_eq_zero]
  exact hs v hv

/-- **The named analytic obligation of the horizon theorem.**  At prime `q` and window `x`
(`q < x < q^2`) there is a smooth real probe, odd, supported in `[-L/2, L/2]` (`L = log x`),
negative on `(0, L/2)`, whose absolute zero sum is below the first overlap.  For the Pólya-kernel
probe `g = Φ' χ` this is the near-annihilation `ĝ(γ_ρ) = -tail^(γ_ρ)` (from `Φ^ = Ξ`) plus zero
counting; claimed (THEOREM-paper-proof, research README) for `x ≥ q + (1/2π) log q + O(log log q)`
unconditionally and for `x ≥ q + W0(√q/2)/(2π) (1 + o(1))` when the zeros that matter are on the
line.  NOT proved here. -/
def ProbeInput (q : ℕ) (x : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, IsWeilTest (fun u => (g u : ℂ)) ∧ (∀ v, g (-v) = -g v) ∧
    (∀ v, Real.log x / 2 < |v| → g v = 0) ∧ (∀ v, 0 < v → v < Real.log x / 2 → g v < 0) ∧
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℝ) * (‖paperFT (fun u => (g u : ℂ)) (gammaOf ρ)‖
        * ‖paperFT (fun u => (g u : ℂ)) (conj (gammaOf ρ))‖)) ∧
    ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ) * (‖paperFT (fun u => (g u : ℂ)) (gammaOf ρ)‖
        * ‖paperFT (fun u => (g u : ℂ)) (conj (gammaOf ρ))‖)
      < 2 * (Real.log q / Real.sqrt q) * -(realAutocorr g (Real.log q))

/-- **Semi-local horizon theorem, upper half, modulo `ProbeInput`**: `ProbeInput q x` makes
`W_{S_q}` indefinite on every window `L' ≥ log x`, i.e. `x*_{S_q} ≤ x`.  (The lower half
`x*_{S_q} ≥ q` is window Weil positivity, `sLocalIndefinite_iff_of_window`: RH-window.) -/
theorem horizon_of_probeInput {q : ℕ} (hq : q.Prime) {x : ℝ} (hqx : (q : ℝ) < x)
    (hxq : x < (q : ℝ) ^ 2) (h : ProbeInput q x) {L' : ℝ} (hL' : Real.log x ≤ L') :
    SLocalIndefinite q L' := by
  obtain ⟨g, hW, hodd, hs, hneg, hsum, hZ⟩ := h
  exact sLocalIndefinite_of_zero_side hq hqx hxq hW hodd hs hneg hsum hZ hL'

/-! ## 6. Negative controls: the one-prime surgery algebra -/

/-- The lattice coefficients `c_m = (-1)^m (r^m + r^{-m})`, `r + 1/r = a = c/√p0`, of the surgery
term `Z = log p0 · Σ_m c_m τ_{m log p0}` of `F = ζ · (1 + c p0^{-s} + p0^{1-2s})`, written as the
Dickson/Chebyshev value `C_m(-a)` (`C_m(t + 1/t) = t^m + t^{-m}`, `t = -r`).  `c_0 = 2` is the
conductor term. -/
def surgeryCoeff (a : ℝ) (m : ℤ) : ℝ := (Polynomial.Chebyshev.C ℝ m).eval (-a)

/-- The surgery form on `N` lattice points: `Σ_{j,k} c_{j-k} y_j y_k`. -/
def latticeForm (a : ℝ) {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N, surgeryCoeff a ((j.val : ℤ) - (k.val : ℤ)) * y j * y k

theorem latticeForm_two (a y0 y1 : ℝ) :
    latticeForm a ![y0, y1] = 2 * y0 ^ 2 + 2 * y1 ^ 2 - 2 * a * y0 * y1 := by
  unfold latticeForm surgeryCoeff
  simp [Fin.sum_univ_two, Polynomial.Chebyshev.C_zero, Polynomial.Chebyshev.C_one]
  ring

/-- Local RH (`|a| ≤ 2`) makes the surgery form PSD on every lattice configuration: with
`-a = 2 cos ψ`, `c_{j-k} = 2 cos((j-k) ψ)` and the form is `2 (Σ y_j cos jψ)^2 + 2 (Σ y_j sin jψ)^2`. -/
theorem latticeForm_nonneg_of_abs_le {a : ℝ} (ha : |a| ≤ 2) {N : ℕ} (y : Fin N → ℝ) :
    0 ≤ latticeForm a y := by
  set ψ := Real.arccos (-a / 2)
  have hab := abs_le.mp ha
  have hcos : 2 * Real.cos ψ = -a := by
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring
  set u : Fin N → ℝ := fun j => y j * Real.cos ((j.val : ℝ) * ψ)
  set w : Fin N → ℝ := fun j => y j * Real.sin ((j.val : ℝ) * ψ)
  have key : latticeForm a y = 2 * ((∑ j, u j) ^ 2 + (∑ j, w j) ^ 2) := by
    unfold latticeForm surgeryCoeff
    rw [← hcos]
    simp only [Polynomial.Chebyshev.C_two_mul_real_cos]
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [sub_mul, Real.cos_sub]
    simp only [u, w]
    ring
  rw [key]
  positivity

/-- **Lattice Toeplitz theorem.**  The surgery term is PSD on every lattice configuration (every
number `N` of points) iff `|a| ≤ 2`; failure is already visible at `N = 2`. -/
theorem latticeForm_nonneg_iff (a : ℝ) :
    (∀ (N : ℕ) (y : Fin N → ℝ), 0 ≤ latticeForm a y) ↔ |a| ≤ 2 := by
  constructor
  · intro h
    have h1 := h 2 ![1, 1]
    have h2 := h 2 ![1, -1]
    rw [latticeForm_two] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith
  · intro ha N y
    exact latticeForm_nonneg_of_abs_le ha y

/-- **Local RH for the surgered factor.**  With `w = (s - 1/2) log p0`,
`p0^{s-1/2} (1 + c p0^{-s} + p0^{1-2s}) = 2 cosh w + a` (`a = c/√p0`).  All its zeros lie on
`Re w = 0` (i.e. `Re s = 1/2`) iff `|a| ≤ 2`.  With `latticeForm_nonneg_iff`: the fake's lattice
block is PSD for every `N` iff its extra Euler factor satisfies local RH. -/
theorem surgery_local_rh_iff (a : ℝ) :
    (∀ w : ℂ, 2 * Complex.cosh w + a = 0 → w.re = 0) ↔ |a| ≤ 2 := by
  constructor
  · intro h
    by_contra hc'
    have hc : 2 < |a| := not_le.mp hc'
    have ha2 : 4 < a ^ 2 := by
      have := sq_abs a
      nlinarith [abs_nonneg a]
    set t := Real.sqrt (a ^ 2 - 4) with htdef
    have ht0 : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have ht2 : t ^ 2 = a ^ 2 - 4 := Real.sq_sqrt (by linarith)
    set r := (|a| + t) / 2 with hrdef
    have hr1 : 1 < r := by rw [hrdef]; linarith
    have hr0 : 0 < r := by linarith
    have hrinv : r⁻¹ = (|a| - t) / 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      have h1 : (|a| + t) / 2 * ((|a| - t) / 2) = (|a| ^ 2 - t ^ 2) / 4 := by ring
      rw [hrdef, h1, sq_abs, ht2]
      ring
    have hch : Real.cosh (Real.log r) = |a| / 2 := by
      rw [Real.cosh_log hr0, hrinv, hrdef]
      ring
    have hlogpos : 0 < Real.log r := Real.log_pos hr1
    rcases le_or_gt 0 a with ha | ha
    · -- a > 2 : w = log r + π i
      have habs : |a| = a := abs_of_nonneg ha
      have hz : 2 * Complex.cosh ((Real.log r : ℂ) + (Real.pi : ℂ) * Complex.I) + (a : ℂ) = 0 := by
        rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi, ← Complex.ofReal_cosh, hch, habs]
        push_cast
        ring
      have hre : ((Real.log r : ℂ) + (Real.pi : ℂ) * Complex.I).re = Real.log r := by simp
      have := h _ hz
      rw [hre] at this
      linarith
    · -- a < -2 : w = log r
      have habs : |a| = -a := abs_of_neg ha
      have hz : 2 * Complex.cosh ((Real.log r : ℂ)) + (a : ℂ) = 0 := by
        rw [← Complex.ofReal_cosh, hch, habs]
        push_cast
        ring
      have := h _ hz
      rw [Complex.ofReal_re] at this
      linarith
  · intro ha w hw
    have hw' : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    rw [hw', Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hw
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hre him
    norm_num at hre him
    by_contra hu
    have hsin : Real.sin w.im = 0 := by
      rcases him with h1 | h1
      · exact absurd h1 hu
      · exact h1
    have hcosh : 1 < Real.cosh w.re := Real.one_lt_cosh.mpr hu
    have hab := abs_le.mp ha
    rcases Real.sin_eq_zero_iff_cos_eq.mp hsin with hc | hc <;> rw [hc] at hre <;> nlinarith

/-- PARTIAL-SHIFT BOUND.  If `g` vanishes off `[-b, b]` and the shift `l > b` (only one lattice
translate overlaps: windows `x < p0^2`), then `|h_g(l)| ≤ ‖g‖² / 2`. -/
theorem partial_shift_bound {g : ℝ → ℝ} (hc : Continuous g) {b l : ℝ} (hb : 0 ≤ b) (hbl : b < l)
    (hs : ∀ v, b < |v| → g v = 0) :
    |realAutocorr g l| ≤ (1 / 2) * ∫ v, g v ^ 2 := by
  have hl : 0 < l := by linarith
  have hred : realAutocorr g l = ∫ v in (0 : ℝ)..l, g v * g (v - l) := by
    unfold realAutocorr
    rw [intervalIntegral.integral_of_le hl.le, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro v hv
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
    rcases hv with hv | hv
    · have : b < |v - l| := lt_of_lt_of_le (by linarith) (neg_le_abs (v - l))
      rw [hs _ this, mul_zero]
    · rw [hs v (lt_of_lt_of_le (by linarith) (le_abs_self v)), zero_mul]
  have hsq : ∫ v, g v ^ 2 = ∫ v in (-l)..l, g v ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro v hv
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
    have : b < |v| := by
      rcases hv with hv | hv
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs v)
      · exact lt_of_lt_of_le (by linarith) (le_abs_self v)
    rw [hs v this]
    ring
  have hc1 : Continuous (fun v => g v * g (v - l)) :=
    hc.mul (hc.comp (continuous_id.sub continuous_const))
  have hc2 : Continuous (fun v => (g v ^ 2 + g (v - l) ^ 2) / 2) := by
    have := hc.comp (continuous_id.sub (continuous_const (y := l)))
    fun_prop
  have habs : |∫ v in (0 : ℝ)..l, g v * g (v - l)|
      ≤ ∫ v in (0 : ℝ)..l, (g v ^ 2 + g (v - l) ^ 2) / 2 := by
    refine (intervalIntegral.abs_integral_le_integral_abs hl.le).trans ?_
    refine intervalIntegral.integral_mono_on hl.le (hc1.abs.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) ?_
    intro v _
    rw [abs_mul]
    nlinarith [sq_abs (g v), sq_abs (g (v - l)), sq_nonneg (|g v| - |g (v - l)|)]
  have hgi : ∀ a c : ℝ, IntervalIntegrable (fun v => g v ^ 2) volume a c :=
    fun a c => (hc.pow 2).intervalIntegrable _ _
  have hshift : ∫ v in (0 : ℝ)..l, g (v - l) ^ 2 = ∫ v in (-l)..0, g v ^ 2 := by
    have := intervalIntegral.integral_comp_sub_right (fun v => g v ^ 2) l (a := 0) (b := l)
    simp only [zero_sub, sub_self] at this
    exact this
  have hgl : Continuous (fun v => g (v - l) ^ 2) :=
    (hc.comp (continuous_id.sub continuous_const)).pow 2
  have hsplit : ∫ v in (0 : ℝ)..l, (g v ^ 2 + g (v - l) ^ 2) / 2
      = (1 / 2) * ∫ v in (-l)..l, g v ^ 2 := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add (hgi 0 l) (hgl.intervalIntegrable 0 l),
      hshift, add_comm, intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)]
    ring
  rw [hred, hsq, ← hsplit]
  exact habs

/-- **Plateau lower bound** (abstract).  On windows where only the first lattice shift
`l = log p0` fits (`b < l`, i.e. `x < p0^2`), the one-prime surgery term
`ℓ (2 ‖g‖² + 2 c_1 h_g(l))`, `c_1 = -a`, `ℓ = log p0`, is at least `ℓ (2 - |a|) ‖g‖²`.  So
`λ_min(Q_F) ≥ λ_min(Q_ζ) + log p0 (2 - |a|)` there; the pair probe (`pair_probe_rayleigh`)
attains `log p0 (2 - a)`. -/
theorem surgery_term_ge {g : ℝ → ℝ} (hc : Continuous g) {b l : ℝ} (hb : 0 ≤ b) (hbl : b < l)
    (hs : ∀ v, b < |v| → g v = 0) (a ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ℓ * (2 - |a|) * (∫ v, g v ^ 2)
      ≤ ℓ * (2 * (∫ v, g v ^ 2) - 2 * a * realAutocorr g l) := by
  have h := partial_shift_bound hc hb hbl hs
  set I := ∫ v, g v ^ 2 with hI
  set H := realAutocorr g l with hH
  have h2 : a * H ≤ |a| * ((1 / 2) * I) := by
    calc a * H ≤ |a * H| := le_abs_self _
      _ = |a| * |H| := abs_mul _ _
      _ ≤ |a| * ((1 / 2) * I) := mul_le_mul_of_nonneg_left h (abs_nonneg a)
  have h3 : (2 - |a|) * I ≤ 2 * I - 2 * a * H := by nlinarith
  calc ℓ * (2 - |a|) * I = ℓ * ((2 - |a|) * I) := by ring
    _ ≤ ℓ * (2 * I - 2 * a * H) := mul_le_mul_of_nonneg_left h3 hℓ

/-- The pair probe `φ(· - l/2) + φ(· + l/2)` has `‖g‖² = 2‖φ‖²` and `h_g(l) = ‖φ‖²`, so the
surgery block has Rayleigh quotient exactly `2 - a` (times `log p0`), negative iff `a > 2`. -/
theorem pair_probe_rayleigh (a : ℝ) :
    (2 * 1 ^ 2 + 2 * 1 ^ 2 - 2 * a * 1 * 1) / (1 ^ 2 + 1 ^ 2 : ℝ) = 2 - a := by
  ring

/-- The golden fake `(p0, c) = (5, 5)`: `a = √5 > 2`, local RH fails. -/
theorem golden_violates : ¬ |Real.sqrt 5| ≤ 2 := by
  intro h
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h4]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [abs_of_nonneg (Real.sqrt_nonneg 5)] at h
  linarith

/-- W1(29, 11): `a = 11/√29 > 2` because `121 > 4 · 29`. -/
theorem w1_violates : ¬ |11 / Real.sqrt 29| ≤ 2 := by
  intro h
  have hs : 0 < Real.sqrt 29 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 29 ^ 2 = 29 := Real.sq_sqrt (by norm_num)
  rw [abs_of_nonneg (div_nonneg (by norm_num) hs.le), div_le_iff₀ hs] at h
  nlinarith

/-- The pair probe `g = φ(· - l/2) + φ(· + l/2)`, `φ` vanishing off `[-c, c]`, `2c < l`:
`‖g‖² = 2 ‖φ‖²` and `h_g(l) = ‖φ‖²`. -/
theorem pair_probe_identities {φ : ℝ → ℝ} (hint : Integrable (fun v => φ v ^ 2))
    {c l : ℝ} (hcl : 2 * c < l) (hs : ∀ v, c < |v| → φ v = 0) :
    (∫ v, (φ (v - l / 2) + φ (v + l / 2)) ^ 2) = 2 * ∫ v, φ v ^ 2 ∧
      realAutocorr (fun v => φ (v - l / 2) + φ (v + l / 2)) l = ∫ v, φ v ^ 2 := by
  have hdisj : ∀ u w : ℝ, l ≤ |u - w| → φ u * φ w = 0 := by
    intro u w huw
    by_contra hne
    have h1 : φ u ≠ 0 := left_ne_zero_of_mul hne
    have h2 : φ w ≠ 0 := right_ne_zero_of_mul hne
    have a1 : |u| ≤ c := not_lt.mp fun h => h1 (hs u h)
    have a2 : |w| ≤ c := not_lt.mp fun h => h2 (hs w h)
    have : |u - w| ≤ |u| + |w| := abs_sub _ _
    linarith
  have hpt1 : ∀ v, (φ (v - l / 2) + φ (v + l / 2)) ^ 2 = φ (v - l / 2) ^ 2 + φ (v + l / 2) ^ 2 := by
    intro v
    have h0 : φ (v - l / 2) * φ (v + l / 2) = 0 :=
      hdisj _ _ (by rw [show v - l / 2 - (v + l / 2) = -l by ring, abs_neg]; exact le_abs_self l)
    nlinarith [h0]
  have hpt2 : ∀ v, (φ (v - l / 2) + φ (v + l / 2)) * (φ (v - l - l / 2) + φ (v - l + l / 2))
      = φ (v - l / 2) ^ 2 := by
    intro v
    have e1 : φ (v - l / 2) * φ (v - l - l / 2) = 0 :=
      hdisj _ _ (by rw [show v - l / 2 - (v - l - l / 2) = l by ring]; exact le_abs_self l)
    have e2 : φ (v + l / 2) * φ (v - l - l / 2) = 0 :=
      hdisj _ _ (by
        rw [show v + l / 2 - (v - l - l / 2) = 2 * l by ring, abs_mul, abs_two]
        linarith [abs_nonneg l, le_abs_self l])
    have e3 : φ (v + l / 2) * φ (v - l + l / 2) = 0 :=
      hdisj _ _ (by rw [show v + l / 2 - (v - l + l / 2) = l by ring]; exact le_abs_self l)
    have e4 : v - l + l / 2 = v - l / 2 := by ring
    rw [e4] at e3 ⊢
    nlinarith [e1, e2, e3]
  have hA : Integrable (fun v => φ (v - l / 2) ^ 2) := hint.comp_sub_right (l / 2)
  have hB : Integrable (fun v => φ (v + l / 2) ^ 2) := hint.comp_add_right (l / 2)
  have htA : ∫ v, φ (v - l / 2) ^ 2 = ∫ v, φ v ^ 2 :=
    integral_sub_right_eq_self (fun v => φ v ^ 2) (l / 2)
  have htB : ∫ v, φ (v + l / 2) ^ 2 = ∫ v, φ v ^ 2 :=
    integral_add_right_eq_self (fun v => φ v ^ 2) (l / 2)
  constructor
  · simp_rw [hpt1]
    rw [integral_add hA hB, htA, htB]
    ring
  · unfold realAutocorr
    simp only
    simp_rw [hpt2]
    exact htA

/-- **Exact plateau of the surgery term.**  On the pair probe the surgery term equals
`ℓ (2 - a) ‖g‖²` exactly; with `surgery_term_ge` (for `a ≥ 0`), the infimum of the surgery
Rayleigh quotient over a window `l < L < 2l` is exactly `log p0 (2 - a)`. -/
theorem pair_probe_surgery_value {φ : ℝ → ℝ} (hint : Integrable (fun v => φ v ^ 2)) {c l : ℝ} (hcl : 2 * c < l)
    (hs : ∀ v, c < |v| → φ v = 0) (a ℓ : ℝ) :
    ℓ * (2 * (∫ v, (φ (v - l / 2) + φ (v + l / 2)) ^ 2)
        - 2 * a * realAutocorr (fun v => φ (v - l / 2) + φ (v + l / 2)) l)
      = ℓ * (2 - a) * (∫ v, (φ (v - l / 2) + φ (v + l / 2)) ^ 2) := by
  obtain ⟨h1, h2⟩ := pair_probe_identities hint hcl hs
  rw [h1, h2]
  ring

/-! ## 6b. The two-sided precision barrier (structural half) -/

/-- The Weil functional with the single coefficient `Λ(n0)` replaced by `(1 + δ) Λ(n0)`. -/
def perturbedWeilForm (n0 : ℕ) (δ : ℝ) (f : ℝ → ℂ) : ℂ := weilForm f - (δ : ℂ) * primeTerm f n0

lemma perturbed_re_eq (n0 : ℕ) (δ : ℝ) (g : ℝ → ℝ) :
    (perturbedWeilForm n0 δ (autocorr (fun u => (g u : ℂ)))).re
      = (weilForm (autocorr (fun u => (g u : ℂ)))).re
        - δ * (vonMangoldt n0 / Real.sqrt n0 * (2 * realAutocorr g (Real.log n0))) := by
  unfold perturbedWeilForm
  rw [primeTerm_autocorr_ofReal, Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Decreases are seen by the odd probe.**  `n0` a prime power, `√x < n0 < x`, `δ < 0`, and an
odd probe negative on `(0, L/2)`: the perturbed functional is the full one minus the strictly
positive amount `2 |δ| (Λ(n0)/√n0) |h_g(log n0)|`. -/
theorem precision_decrease_detected {n0 : ℕ} (hn0 : IsPrimePow n0) {x : ℝ}
    (hlo : x < (n0 : ℝ) ^ 2) (hhi : (n0 : ℝ) < x) {δ : ℝ} (hδ : δ < 0)
    {g G : ℝ → ℝ} (hG : Continuous G) (hodd : ∀ v, G (-v) = -G v)
    (hneg : ∀ v, 0 < v → v < Real.log x / 2 → G v < 0)
    (hs : ∀ v, Real.log x / 2 < |v| → g v = 0) (hin : ∀ v, |v| < Real.log x / 2 → g v = G v) :
    (perturbedWeilForm n0 δ (autocorr (fun u => (g u : ℂ)))).re
      < (weilForm (autocorr (fun u => (g u : ℂ)))).re := by
  rw [perturbed_re_eq]
  have hn1 : (1 : ℝ) < n0 := by exact_mod_cast hn0.one_lt
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hx0 : 0 < x := by linarith
  have h1 : Real.log x / 2 < Real.log n0 := by
    have : Real.log x < Real.log ((n0 : ℝ) ^ 2) := Real.log_lt_log hx0 hlo
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h2 : Real.log n0 < 2 * (Real.log x / 2) := by
    have := Real.log_lt_log hn00 hhi
    linarith
  have hh := realAutocorr_neg_of_odd hG hodd hneg hs hin h1 h2
  have hΛ : 0 < vonMangoldt n0 := lt_of_le_of_ne vonMangoldt_nonneg
    (Ne.symm (vonMangoldt_ne_zero_iff.mpr hn0))
  have hw : 0 < vonMangoldt n0 / Real.sqrt n0 := div_pos hΛ (Real.sqrt_pos.mpr hn00)
  have : 0 < δ * (vonMangoldt n0 / Real.sqrt n0 * (2 * realAutocorr g (Real.log n0))) := by
    have : vonMangoldt n0 / Real.sqrt n0 * (2 * realAutocorr g (Real.log n0)) < 0 := by
      nlinarith
    nlinarith
  linarith

/-- **Increases are seen by the even probe.**  `n0` a prime power, `n0 < x`, `δ > 0`, and a probe
strictly positive on the open window (e.g. `Φ · 1_W`): the perturbed functional is the full one
minus the strictly positive amount `2 δ (Λ(n0)/√n0) h_g(log n0)`. -/
theorem precision_increase_detected {n0 : ℕ} (hn0 : IsPrimePow n0) {x : ℝ}
    (hhi : (n0 : ℝ) < x) {δ : ℝ} (hδ : 0 < δ) {g G : ℝ → ℝ} (hG : Continuous G)
    (hpos : ∀ v, |v| < Real.log x / 2 → 0 < G v)
    (hs : ∀ v, Real.log x / 2 < |v| → g v = 0) (hin : ∀ v, |v| < Real.log x / 2 → g v = G v) :
    (perturbedWeilForm n0 δ (autocorr (fun u => (g u : ℂ)))).re
      < (weilForm (autocorr (fun u => (g u : ℂ)))).re := by
  rw [perturbed_re_eq]
  have hn1 : (1 : ℝ) < n0 := by exact_mod_cast hn0.one_lt
  have hn00 : (0 : ℝ) < n0 := by linarith
  have h0 : 0 ≤ Real.log n0 := (Real.log_pos hn1).le
  have h2 : Real.log n0 < 2 * (Real.log x / 2) := by
    have := Real.log_lt_log hn00 hhi
    linarith
  have hh := realAutocorr_pos_of_pos hG hpos hs hin h0 h2
  have hΛ : 0 < vonMangoldt n0 := lt_of_le_of_ne vonMangoldt_nonneg
    (Ne.symm (vonMangoldt_ne_zero_iff.mpr hn0))
  have hw : 0 < vonMangoldt n0 / Real.sqrt n0 := div_pos hΛ (Real.sqrt_pos.mpr hn00)
  have : 0 < δ * (vonMangoldt n0 / Real.sqrt n0 * (2 * realAutocorr g (Real.log n0))) := by
    positivity
  linarith

/-! ## 7. The Fourier-side envelope of the `S`-local symbol -/

/-- The Poisson kernel `P_r(θ) = (1 - r²)/(1 - 2 r cos θ + r²)` is at most `(1 + r)/(1 - r)`. -/
theorem poisson_kernel_le {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2) ≤ (1 + r) / (1 - r) := by
  have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hD : (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos θ + r ^ 2 := by nlinarith
  have hpos : 0 < (1 - r) ^ 2 := by
    have : 0 < 1 - r := by linarith
    positivity
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Each prime's contribution `log p (1 - P_{p^{-1/2}}(t log p))` to the `S`-local symbol is at
least `-2 log p/(√p - 1)`; summed over `p ≤ P` this is the envelope `-2 A_P`. -/
theorem local_symbol_ge {p : ℝ} (hp : 1 < p) (θ : ℝ) :
    -(2 * Real.log p / (Real.sqrt p - 1)) ≤
      Real.log p * (1 - (1 - (1 / Real.sqrt p) ^ 2)
        / (1 - 2 * (1 / Real.sqrt p) * Real.cos θ + (1 / Real.sqrt p) ^ 2)) := by
  have hs1 : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hp
  set r := 1 / Real.sqrt p with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one (by linarith)]; exact hs1
  have hP := poisson_kernel_le (θ := θ) hr0 hr1
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hs0 : Real.sqrt p ≠ 0 := by positivity
  have hne : Real.sqrt p - 1 ≠ 0 := by linarith
  have h1r : 1 - r ≠ 0 := by linarith
  have hfrac : (1 + r) / (1 - r) = (Real.sqrt p + 1) / (Real.sqrt p - 1) := by
    rw [div_eq_div_iff h1r hne, hrdef]
    field_simp
  have hid : 1 - (1 + r) / (1 - r) = -(2 / (Real.sqrt p - 1)) := by
    rw [hfrac]
    field_simp
    ring
  have : -(2 / (Real.sqrt p - 1)) ≤
      1 - (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2) := by
    rw [← hid]
    linarith
  calc -(2 * Real.log p / (Real.sqrt p - 1)) = Real.log p * -(2 / (Real.sqrt p - 1)) := by ring
    _ ≤ Real.log p * (1 - (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2)) :=
      mul_le_mul_of_nonneg_left this hlog.le

end Crux2SemilocalArchimedean

#print axioms Crux2SemilocalArchimedean.primeSide_eq
#print axioms Crux2SemilocalArchimedean.primeTerm_eq_zero_of_exp_lt
#print axioms Crux2SemilocalArchimedean.support_subset_range
#print axioms Crux2SemilocalArchimedean.sLocalWeilForm_eq
#print axioms Crux2SemilocalArchimedean.deficit_eq_zero_of_window
#print axioms Crux2SemilocalArchimedean.vanish_of_tsupport
#print axioms Crux2SemilocalArchimedean.tsupport_subset_of_vanish
#print axioms Crux2SemilocalArchimedean.autocorr_eq_zero_of_le
#print axioms Crux2SemilocalArchimedean.sLocal_eq_weil_of_window
#print axioms Crux2SemilocalArchimedean.sLocalIndefinite_mono
#print axioms Crux2SemilocalArchimedean.sLocalIndefinite_iff_of_window
#print axioms Crux2SemilocalArchimedean.rh_iff_semilocal_natural_windows
#print axioms Crux2SemilocalArchimedean.rh_iff_no_natural_window_indefinite
#print axioms Crux2SemilocalArchimedean.prime_of_missing
#print axioms Crux2SemilocalArchimedean.autocorr_ofReal
#print axioms Crux2SemilocalArchimedean.realAutocorr_neg
#print axioms Crux2SemilocalArchimedean.realAutocorr_eq_overlap
#print axioms Crux2SemilocalArchimedean.overlap_neg_of_odd
#print axioms Crux2SemilocalArchimedean.realAutocorr_neg_of_odd
#print axioms Crux2SemilocalArchimedean.realAutocorr_nonpos_of_odd
#print axioms Crux2SemilocalArchimedean.realAutocorr_pos_of_pos
#print axioms Crux2SemilocalArchimedean.primeTerm_autocorr_ofReal
#print axioms Crux2SemilocalArchimedean.autocorr_vanish_of_window
#print axioms Crux2SemilocalArchimedean.deficit_re_le
#print axioms Crux2SemilocalArchimedean.overlap_first_neg
#print axioms Crux2SemilocalArchimedean.sLocal_neg_of_probe
#print axioms Crux2SemilocalArchimedean.weilForm_autocorr_hasSum
#print axioms Crux2SemilocalArchimedean.weilForm_re_le_zero_majorant
#print axioms Crux2SemilocalArchimedean.sLocalIndefinite_of_zero_side
#print axioms Crux2SemilocalArchimedean.horizon_of_probeInput
#print axioms Crux2SemilocalArchimedean.latticeForm_two
#print axioms Crux2SemilocalArchimedean.latticeForm_nonneg_of_abs_le
#print axioms Crux2SemilocalArchimedean.latticeForm_nonneg_iff
#print axioms Crux2SemilocalArchimedean.surgery_local_rh_iff
#print axioms Crux2SemilocalArchimedean.partial_shift_bound
#print axioms Crux2SemilocalArchimedean.surgery_term_ge
#print axioms Crux2SemilocalArchimedean.pair_probe_rayleigh
#print axioms Crux2SemilocalArchimedean.golden_violates
#print axioms Crux2SemilocalArchimedean.w1_violates
#print axioms Crux2SemilocalArchimedean.pair_probe_identities
#print axioms Crux2SemilocalArchimedean.pair_probe_surgery_value
#print axioms Crux2SemilocalArchimedean.perturbed_re_eq
#print axioms Crux2SemilocalArchimedean.precision_decrease_detected
#print axioms Crux2SemilocalArchimedean.precision_increase_detected
#print axioms Crux2SemilocalArchimedean.poisson_kernel_le
#print axioms Crux2SemilocalArchimedean.local_symbol_ge
