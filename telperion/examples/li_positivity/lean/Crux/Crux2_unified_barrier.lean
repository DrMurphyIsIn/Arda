/-
  Crux2_unified_barrier (li_positivity island) -- SEMI-LOCALITY IS THE RELATIVIZATION BARRIER.
  One Euler-product family W_{p,c} defeats every semi-local argument, and every global input that
  defeats it collapses class-level RH to RH for zeta.

  conjecture1_proved = False.  Nothing in this file says where the zeros of the Riemann zeta
  function lie.  It is a META-result about a class of arguments, with explicit witness models.
  Every theorem is kernel-checked; the audit block at the end prints the axiom closure of every
  theorem and lemma, and each is a subset of [propext, Classical.choice, Quot.sound].  The file has
  no proof holes, uses no kernel-bypassing evaluation, and declares no new postulates or sealed
  constants.

  PREREQUISITE.  This file imports three round-1 research modules (Crux_meta_barriers = Build B,
  Crux_dynamics_ergodic = Build C, Crux_axiso_theorem = the class-P collapse), so that the
  unification theorems speak about the LITERAL round-1 objects (XiA, XiH, ChannelAxioms,
  classP_eq_zeta), not copies.  Those modules are not lean_lib targets of this island; run
  `telperion/research/crux2_unified-barrier/build_deps.sh` once (it compiles them with the island
  toolchain into the island's untracked `.lake/build/lib/lean/Crux/`), then check this file with
  `lake env lean Crux/Crux2_unified_barrier.lean`.

  THE WITNESS FAMILY.  For a prime p and an integer c,
      W_{p,c}(s) = zeta(s) (1 + c p^{-s} + p p^{-2s}),
  a multiplicative Dirichlet series with integer coefficients: a surgery of zeta at ONE prime.
  Its completion is riemannXi(s) * surg p c s, where
      surg p c s = 2 cosh((s - 1/2) log p) + c / sqrt p = p^{s-1/2} (1 + c p^{-s} + p p^{-2s}).

  ESTABLISHES (kernel):
  1. The witness (sections 1, 7, 8, 12, 13).  `LSeries_aW`: L(a_W, s) = zeta(s)(1 + c p^-s + p p^-2s)
     on Re s > 1; `W_completion`, `W_completion_LSeries`: its completion is xi * surg, with the exact
     Gamma_R shape and conductor p^2 (`surg_one_sub`).  `aW_isMultiplicative` (Euler product),
     `W_isDirExp` (a_W = exp*(b_W), b_W = Lambda/log + b_loc, via the local Newton identity
     `Ploc_isDirExp`), `bW_pow`: b_W(p^m) = (1 - t_m)/m with t the Lucas power sums.  P2 below p^2
     (`bW_nonneg_below`), failure at p^2 (`bW_sq`), signs at all powers (`bW_odd_pos`,
     `bW_even_neg`).  Periodicity mod p^2 and the FE top coefficient (`aW_periodic`, `aW_top`).
  2. Local Hasse bound versus local trivial bound (sections 2-4, 12, 14).  All zeros of surg lie on
     Re s = 1/2 iff c^2 <= 4p (`surg_rh_iff`); for 4p < c^2 and |c| < p + 1 there is a zero with
     1/2 < Re s < 1 and |Im s| <= pi / log p (`surg_offline_zero`).  With x = (2 Re s - 1) L, a = L/2,
     phi = 2 Im s L: |Xi(2s)|^2 - |Xi(2s-1)|^2 = 4(2 sinh x sinh a)(2 cosh x cosh a - c cos phi)
     (`Xi_contractive`).  xi * surg satisfies all seven ChannelAxioms of Build C IFF |c| < p + 1
     (`channelAxioms_W_iff`), and the de la Vallee Poussin defect B = sum_n Lambda_W^-(n)/n is finite
     IFF |c| < p + 1 (`robust_positivity_iff`).  Both see the trivial bound, never the Hasse bound.
  3. THE SUPPORT-PRIME DUALITY (section 13, `surg_explicit_formula`).  For c^2 != 4p the zeros of
     surg are exactly 1/2 + i gamma, gamma = (+-alpha + 2 pi k)/log p (2 cos alpha = -c/sqrt p), all
     simple, the two branches disjoint; for every smooth test g supported in (-log p, log p) the sum
     over these zeros of h(gamma) = int g(x) e^{i x gamma} dx equals 2 log p * g(0), independent of c;
     for support in (-2 log p, 2 log p) it equals 2 log p (g(0) - (c/(2 sqrt p))(g(log p) + g(-log p))).
     Proof: Poisson summation (`lattice_poisson`, via Mathlib's `SchwartzMap.tsum_eq_tsum_fourier`).
  4. THE SEMI-LOCAL BARRIER (sections 10, 16: `semilocal_barrier`, `semilocal_barrier_full`).  For
     every N0, every finite set S and every L0 there are a prime p notin S with p^2 > N0 and
     log p > L0 and c with 4p < c^2, c < p + 1, such that W_{p,c} is a multiplicative Dirichlet
     exponential agreeing with zeta away from p (X1); has the Gamma_R-shape completion of conductor
     p^2, periodic coefficients and the FE top coefficient (X2); has P2 on [0, p^2) (X3); satisfies
     the channel axioms (X4); satisfies the support-prime duality, so every Weil-positivity statement
     for zeta on tests supported in [-L0, L0] transfers verbatim, margin + 2 log p g(0) (X5); has
     finite robust-positivity defect (X6); and its completion vanishes at a point with
     1/2 < Re s < 1.
  5. UNIFICATION (sections 5, 11, 16).  Build B's golden fake is `surg 5 5` (`XiA_eq_surg`), so its
     hybrid XiH is the completion of the Dirichlet series of the Euler product W_{5,5}
     (`XiH_eq_W55`, `golden_unified`, `golden_unified_full`).  For every prime p and every integer c,
     W_{p,c} meets every hypothesis of the class-P collapse `classP_eq_zeta` except positivity
     (`classP_sharp`).
  6. SHARPNESS OF THE CLASS (section 6: `lowHeightBox_nonrelativizing`,
     `W41_semilocal_violates_box1`).  W_{41,13} satisfies the semi-local interface, but its
     completion vanishes at a point with 1/2 < Re s < 1 and |Im s| < sqrt 3 / 2, while every zeta
     zero in the strip has |Im| >= sqrt 3 / 2 (LowHeightBox).  So LowHeightBox is NOT semi-local.
  7. EXHAUSTION (sections 9, 12, 15, 16: `exhaustion`, `prime_square_surgery`).  P2 at p^2 alone,
     P2 at all powers of p, or no off-line surgery zero below height pi / log 2 each force
     c^2 <= 4p; the Selberg-class Euler axiom b(n) << n^theta (theta < 1/2), which zeta satisfies
     with theta = 0, fails for EVERY surgery, on-line ones included (`surgery_not_selberg`).  After
     the Hasse bound, RH for xi * surg is exactly RH for xi (`rh_W_iff`).  An incomplete global
     input is still fooled: the prime-square surgery zeta(s)(1 + A p^{-2s} + p^2 p^{-4s}),
     A = 2p + 1, is an Euler product with P2 at EVERY prime square and on [0, p^4), the channel
     axioms, and an off-line zero in the strip (`prime_square_surgery`, via the general local Newton
     identity `locE_isDirExp`).

  DOES NOT ESTABLISH.  Anything about the zeros of zeta.  That a global argument can succeed
  (relativization is silent there, not permissive).  The bookkeeping Z_W = Z_zeta + Z_surg (the
  zeros of a product, with multiplicity) is used only at the level of the zero set
  (`mul_eq_zero`); the Weil functional of zeta itself is not defined on this island.  Membership of
  the classical arguments (de la Vallee Poussin with defect B, PNT, small-support positivity) in the
  semi-local class is paper-level.  The degree-one completeness of the surgery family rests on
  Kaczorowski-Perelli 1999 and is not formalized.  Novelty against the literature is not verified.
-/
import Mathlib
import Crux.Crux_meta_barriers
import Crux.Crux_dynamics_ergodic
import Crux.Crux_axiso_theorem

open Complex

namespace Crux2UnifiedBarrier

open CruxMetaBarriers

/-! ## 1. The surgery factor -/

/-- The completed local surgery factor at `p` with trace parameter `c`:
`surg p c s = 2 cosh((s - 1/2) log p) + c / sqrt p`. -/
noncomputable def surg (p c : ℝ) (s : ℂ) : ℂ := Xi (Real.log p) (-(c / Real.sqrt p)) s

lemma surg_eq (p c : ℝ) (s : ℂ) :
    surg p c s = 2 * Complex.cosh ((s - 1 / 2) * (Real.log p : ℝ)) + ((c / Real.sqrt p : ℝ) : ℂ) := by
  unfold surg Xi; push_cast; ring

theorem surg_one_sub (p c : ℝ) (s : ℂ) : surg p c (1 - s) = surg p c s := Xi_symm _ _ s

theorem surg_conj (p c : ℝ) (s : ℂ) : surg p c (starRingEnd ℂ s) = starRingEnd ℂ (surg p c s) := by
  rw [surg_eq, surg_eq, map_add, map_mul, ← Complex.cosh_conj]
  simp [map_sub, Complex.conj_ofReal, map_ofNat]

theorem surg_differentiable (p c : ℝ) : Differentiable ℂ (surg p c) := by
  have : surg p c = fun s => 2 * Complex.cosh ((s - 1 / 2) * (Real.log p : ℝ))
      + ((c / Real.sqrt p : ℝ) : ℂ) := funext (surg_eq p c)
  rw [this]
  fun_prop

/-- The completed factor is `p^{s-1/2} (1 + c p^{-s} + p p^{-2s})` (with `p^z = exp(z log p)`). -/
theorem surg_eq_localPoly (p c : ℝ) (hp : 0 < p) (s : ℂ) :
    Complex.exp ((s - 1 / 2) * (Real.log p : ℝ)) *
        (1 + c * Complex.exp (-s * (Real.log p : ℝ))
          + (p : ℂ) * Complex.exp (-s * (Real.log p : ℝ)) ^ 2)
      = surg p c s := by
  have h := Xi_eq_P (Real.log p) (-c) s
  have hexp : Complex.exp ((Real.log p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hp]
  have he : Real.exp (Real.log p / 2) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]; ring_nf
  have hsq : Real.exp (-Real.log p / 2) = 1 / Real.sqrt p := by
    rw [one_div, ← he, ← Real.exp_neg]; ring_nf
  have hc' : -c * Real.exp (-Real.log p / 2) = -(c / Real.sqrt p) := by rw [hsq]; ring
  rw [hexp, hc'] at h
  unfold surg
  rw [← h]
  push_cast
  ring

/-! ## 2. Channel admissibility is the local TRIVIAL bound -/

/-- Real decomposition of `‖Xi L c (X + Y i)‖^2`. -/
lemma normSq_Xi_decomp (L c X Y : ℝ) (s : ℂ) (hs : (s - 1 / 2) * (L : ℂ) = (X : ℂ) + Y * I) :
    ‖Xi L c s‖ ^ 2 = (2 * Real.cosh X * Real.cos Y - c) ^ 2 + (2 * Real.sinh X * Real.sin Y) ^ 2 := by
  unfold Xi
  rw [hs, cosh_decomp, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **Contractivity identity and inequality.**  For `L ≥ 0`, `|c| ≤ 2 cosh(L/2)` and `Re s ≥ 1/2`,
`‖Xi L c (2s - 1)‖ ≤ ‖Xi L c (2s)‖`.  (The difference of squares is
`4 (cosh(x+a) - cosh(x-a)) (cosh(x+a) + cosh(x-a) - c cos φ)`, `x = (2 Re s - 1) L`, `a = L/2`.) -/
theorem Xi_contractive (L c : ℝ) (hL : 0 ≤ L) (hc : |c| ≤ 2 * Real.cosh (L / 2)) (s : ℂ)
    (hs : 1 / 2 ≤ s.re) : ‖Xi L c (2 * s - 1)‖ ≤ ‖Xi L c (2 * s)‖ := by
  set x : ℝ := (2 * s.re - 1) * L with hx
  set a : ℝ := L / 2 with ha
  set φ : ℝ := 2 * s.im * L with hφ
  have h1 : (2 * s - 1 - 1 / 2) * (L : ℂ) = ((x - a : ℝ) : ℂ) + (φ : ℂ) * I := by
    apply Complex.ext <;> simp [hx, ha, hφ] <;> ring
  have h2 : (2 * s - 1 / 2) * (L : ℂ) = ((x + a : ℝ) : ℂ) + (φ : ℂ) * I := by
    apply Complex.ext <;> simp [hx, ha, hφ] <;> ring
  have e1 := normSq_Xi_decomp L c (x - a) φ (2 * s - 1) h1
  have e2 := normSq_Xi_decomp L c (x + a) φ (2 * s) h2
  have hx0 : 0 ≤ x := by rw [hx]; apply mul_nonneg <;> linarith
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hsx : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
  have hsa : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.mpr ha0
  have hcx : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hca : 0 < Real.cosh a := Real.cosh_pos a
  have hcos : c * Real.cos φ ≤ |c| := by
    calc c * Real.cos φ ≤ |c * Real.cos φ| := le_abs_self _
      _ = |c| * |Real.cos φ| := abs_mul _ _
      _ ≤ |c| * 1 := by gcongr; exact Real.abs_cos_le_one φ
      _ = |c| := mul_one _
  have hpyth := Real.sin_sq_add_cos_sq φ
  have hcp := Real.cosh_add x a
  have hcm := Real.cosh_sub x a
  have hsp := Real.sinh_add x a
  have hsm := Real.sinh_sub x a
  have hq1 := Real.cosh_sq (x + a)
  have hq2 := Real.cosh_sq (x - a)
  -- the difference of squares
  have hdiff : ‖Xi L c (2 * s)‖ ^ 2 - ‖Xi L c (2 * s - 1)‖ ^ 2
      = 4 * (2 * Real.sinh x * Real.sinh a) * (2 * Real.cosh x * Real.cosh a - c * Real.cos φ) := by
    rw [e1, e2]
    have hs2p : Real.sinh (x + a) ^ 2 = Real.cosh (x + a) ^ 2 - 1 := by linarith
    have hs2m : Real.sinh (x - a) ^ 2 = Real.cosh (x - a) ^ 2 - 1 := by linarith
    have hsin2 : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by linarith
    have expand : (2 * Real.cosh (x + a) * Real.cos φ - c) ^ 2 + (2 * Real.sinh (x + a) * Real.sin φ) ^ 2
        - ((2 * Real.cosh (x - a) * Real.cos φ - c) ^ 2 + (2 * Real.sinh (x - a) * Real.sin φ) ^ 2)
        = 4 * Real.cos φ ^ 2 * (Real.cosh (x + a) ^ 2 - Real.cosh (x - a) ^ 2)
          - 4 * c * Real.cos φ * (Real.cosh (x + a) - Real.cosh (x - a))
          + 4 * Real.sin φ ^ 2 * (Real.sinh (x + a) ^ 2 - Real.sinh (x - a) ^ 2) := by ring
    rw [expand, hs2p, hs2m, hsin2, hcp, hcm]
    ring
  have hbr : 0 ≤ 2 * Real.cosh x * Real.cosh a - c * Real.cos φ := by
    have : 2 * Real.cosh a ≤ 2 * Real.cosh x * Real.cosh a := by nlinarith
    have hc' : |c| ≤ 2 * Real.cosh a := by rw [ha]; exact hc
    linarith
  have hprod : 0 ≤ 4 * (2 * Real.sinh x * Real.sinh a) * (2 * Real.cosh x * Real.cosh a - c * Real.cos φ) := by
    have : 0 ≤ 2 * Real.sinh x * Real.sinh a := by positivity
    positivity
  have hsq : ‖Xi L c (2 * s - 1)‖ ^ 2 ≤ ‖Xi L c (2 * s)‖ ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- **Edge.**  If `|c| < 2 cosh(L/2)` and `L > 0`, `Xi L c` has no zero on `Re w ≥ 1`. -/
theorem Xi_edge (L c : ℝ) (hL : 0 < L) (hc : |c| < 2 * Real.cosh (L / 2)) (w : ℂ) (hw : 1 ≤ w.re) :
    Xi L c w ≠ 0 := by
  intro h0
  set X : ℝ := (w.re - 1 / 2) * L with hX
  set Y : ℝ := w.im * L with hY
  have hw' : (w - 1 / 2) * (L : ℂ) = (X : ℂ) + Y * I := by
    apply Complex.ext <;> simp [hX, hY]
  have hn := normSq_Xi_decomp L c X Y w hw'
  rw [h0, norm_zero] at hn
  have hX0 : L / 2 ≤ X := by rw [hX]; nlinarith
  have hXpos : 0 < X := by linarith
  have hsinh : 0 < Real.sinh X := Real.sinh_pos_iff.mpr hXpos
  -- both squares vanish
  have hA : 2 * Real.cosh X * Real.cos Y - c = 0 := by nlinarith [sq_nonneg (2 * Real.cosh X * Real.cos Y - c), sq_nonneg (2 * Real.sinh X * Real.sin Y)]
  have hB : 2 * Real.sinh X * Real.sin Y = 0 := by nlinarith [sq_nonneg (2 * Real.cosh X * Real.cos Y - c), sq_nonneg (2 * Real.sinh X * Real.sin Y)]
  have hsin : Real.sin Y = 0 := by
    rcases mul_eq_zero.mp hB with h | h
    · exact absurd h (by positivity)
    · exact h
  have hcos2 : Real.cos Y ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq Y]
  have hcabs : |Real.cos Y| = 1 := by
    have := sq_abs (Real.cos Y); nlinarith [abs_nonneg (Real.cos Y)]
  have hmono : Real.cosh (L / 2) ≤ Real.cosh X := by
    rw [Real.cosh_le_cosh]; rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; exact hX0
  have hcX : |c| = 2 * Real.cosh X := by
    have : c = 2 * Real.cosh X * Real.cos Y := by linarith
    rw [this, abs_mul, abs_mul, hcabs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (Real.cosh_pos X)]; ring
  linarith

/-- `2 cosh((log p)/2) = sqrt p + 1/sqrt p`. -/
lemma two_cosh_half_log (p : ℝ) (hp : 0 < p) :
    2 * Real.cosh (Real.log p / 2) = Real.sqrt p + 1 / Real.sqrt p := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have he : Real.exp (Real.log p / 2) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]; ring_nf
  rw [Real.cosh_eq, he, Real.exp_neg, he]
  field_simp

/-- The surgery bound in `c`: `|c / sqrt p| < 2 cosh(log p / 2)` iff `|c| < p + 1`. -/
lemma surg_trivial_bound_iff (p c : ℝ) (hp : 0 < p) :
    |c / Real.sqrt p| < 2 * Real.cosh (Real.log p / 2) ↔ |c| < p + 1 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  rw [two_cosh_half_log p hp, abs_div, abs_of_pos hs, div_lt_iff₀ hs]
  have : (Real.sqrt p + 1 / Real.sqrt p) * Real.sqrt p = p + 1 := by
    field_simp; rw [hsq]
  rw [this]

lemma surg_trivial_bound_iff_le (p c : ℝ) (hp : 0 < p) :
    |c / Real.sqrt p| ≤ 2 * Real.cosh (Real.log p / 2) ↔ |c| ≤ p + 1 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  rw [two_cosh_half_log p hp, abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have : (Real.sqrt p + 1 / Real.sqrt p) * Real.sqrt p = p + 1 := by
    field_simp; rw [hsq]
  rw [this]

theorem surg_contractive (p c : ℝ) (hp : 1 ≤ p) (hc : |c| ≤ p + 1) (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖surg p c (2 * s - 1)‖ ≤ ‖surg p c (2 * s)‖ := by
  have hp0 : 0 < p := by linarith
  apply Xi_contractive _ _ (Real.log_nonneg hp) _ s hs
  rw [abs_neg]; exact (surg_trivial_bound_iff_le p c hp0).mpr hc

theorem surg_edge (p c : ℝ) (hp : 1 < p) (hc : |c| < p + 1) (w : ℂ) (hw : 1 ≤ w.re) :
    surg p c w ≠ 0 := by
  have hp0 : 0 < p := by linarith
  apply Xi_edge _ _ (Real.log_pos hp) _ w hw
  rw [abs_neg]; exact (surg_trivial_bound_iff p c hp0).mpr hc

theorem surg_unitary (p c : ℝ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖surg p c (2 * s - 1)‖ = ‖surg p c (2 * s)‖ := by
  have : surg p c (2 * s) = starRingEnd ℂ (surg p c (2 * s - 1)) := by
    rw [← surg_conj, ← surg_one_sub]
    congr 1
    apply Complex.ext <;> simp [hs]
  rw [this, Complex.norm_conj]


/-! ## 3. The witness completion `xi * surg` satisfies every channel axiom (Build C) -/

section Channel

open CruxDynamicsErgodic ComplexConjugate

/-- Closure of Build C's channel axioms under multiplication by a surgery factor obeying the local
TRIVIAL bound `|c| < p + 1`. -/
theorem channelAxioms_mul_surg {Λ : ℂ → ℂ} (hΛ : ChannelAxioms Λ) (p c : ℝ) (hp : 1 < p)
    (hc : |c| < p + 1) : ChannelAxioms (fun w => Λ w * surg p c w) := by
  have hent : Differentiable ℂ (fun w => Λ w * surg p c w) :=
    hΛ.entire.mul (surg_differentiable p c)
  have hfe : ∀ w, Λ (1 - w) * surg p c (1 - w) = Λ w * surg p c w := by
    intro w; rw [hΛ.fe, surg_one_sub]
  have hre : ∀ w, Λ (conj w) * surg p c (conj w) = conj (Λ w * surg p c w) := by
    intro w; rw [hΛ.real, surg_conj, map_mul]
  have hin : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖Λ (2 * s - 1) * surg p c (2 * s - 1)‖ ≤ ‖Λ (2 * s) * surg p c (2 * s)‖ := by
    intro s hs
    rw [norm_mul, norm_mul]
    exact mul_le_mul (hΛ.inner s hs) (surg_contractive p c hp.le hc.le s hs) (norm_nonneg _)
      (norm_nonneg _)
  refine ⟨hent, hfe, hre, ?_, hin, ?_, bk_of_inner hent hfe hre hin⟩
  · intro w hw
    exact mul_ne_zero (hΛ.edge w hw) (surg_edge p c hp hc w hw)
  · intro s hs
    rw [norm_mul, norm_mul, hΛ.unitary s hs, surg_unitary p c s hs]

/-- **The witness passes the dynamics channel.**  For every `p > 1` and `|c| < p + 1`, the
completion `riemannXi * surg p c` satisfies all seven channel axioms. -/
theorem channelAxioms_W (p c : ℝ) (hp : 1 < p) (hc : |c| < p + 1) :
    ChannelAxioms (fun w => LiCriterion.riemannXi w * surg p c w) :=
  channelAxioms_mul_surg channelAxioms_xi p c hp hc

end Channel

/-! ## 4. Off-line zeros: the local Hasse bound, the trivial bound, low height -/

/-- `|c / sqrt p| > 2` iff `c^2 > 4 p`. -/
lemma two_lt_abs_div_sqrt_iff (p c : ℝ) (hp : 0 < p) :
    2 < |c / Real.sqrt p| ↔ 4 * p < c ^ 2 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  rw [abs_div, abs_of_pos hs, lt_div_iff₀ hs]
  constructor
  · intro h
    have h2 : (2 * Real.sqrt p) ^ 2 < |c| ^ 2 := by
      have h0 : 0 ≤ 2 * Real.sqrt p := by positivity
      exact pow_lt_pow_left₀ h h0 two_ne_zero
    rw [sq_abs] at h2; nlinarith
  · intro h
    have h0 : 0 ≤ 2 * Real.sqrt p := by positivity
    have h2 : (2 * Real.sqrt p) ^ 2 < |c| ^ 2 := by rw [sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg c) h2

/-- **Local RH for the surgery factor is the local Hasse bound**: all zeros of `surg p c` lie on
`Re s = 1/2` iff `c^2 ≤ 4p`. -/
theorem surg_rh_iff (p c : ℝ) (hp : 1 < p) :
    (∀ s : ℂ, surg p c s = 0 → s.re = 1 / 2) ↔ c ^ 2 ≤ 4 * p := by
  have hp0 : 0 < p := by linarith
  unfold surg
  rw [rh_iff _ _ (Real.log_pos hp), abs_neg, ← not_lt, ← not_lt,
    two_lt_abs_div_sqrt_iff p c hp0]

/-- **Beyond the Hasse bound, below the trivial bound: an explicit off-line zero in the open strip
at height at most `pi / log p`.** -/
theorem surg_offline_zero (p c : ℝ) (hp : 1 < p) (hD : 4 * p < c ^ 2) (hc : |c| < p + 1) :
    ∃ s : ℂ, surg p c s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1 ∧ |s.im| ≤ Real.pi / Real.log p := by
  have hp0 : 0 < p := by linarith
  have hL : 0 < Real.log p := Real.log_pos hp
  have h2 : 2 < |-(c / Real.sqrt p)| := by rw [abs_neg]; exact (two_lt_abs_div_sqrt_iff p c hp0).mpr hD
  obtain ⟨x, hx0, hcx, s, hs, hre, him⟩ := offline_zero_explicit (Real.log p) _ hL h2
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · rw [hre]; have : 0 < x / Real.log p := div_pos hx0 hL; linarith
  · rw [hre]
    have hb : |-(c / Real.sqrt p)| < 2 * Real.cosh (Real.log p / 2) := by
      rw [abs_neg]; exact (surg_trivial_bound_iff p c hp0).mpr hc
    have hlt : Real.cosh x < Real.cosh (Real.log p / 2) := by rw [hcx]; linarith
    rw [Real.cosh_lt_cosh, abs_of_pos hx0, abs_of_pos (by linarith)] at hlt
    have : x / Real.log p < 1 / 2 := by rw [div_lt_iff₀ hL]; linarith
    linarith
  · rcases him with h | h
    · rw [h, abs_zero]; positivity
    · rw [h, abs_of_pos (by positivity)]

/-- **No intermediate class (single surgery).**  RH for the completion of `W_{p,c}` is exactly RH
for `xi` together with the local Hasse bound. -/
theorem rh_W_iff (p c : ℝ) (hp : 1 < p) :
    (∀ s : ℂ, LiCriterion.riemannXi s * surg p c s = 0 → s.re = 1 / 2) ↔
      (∀ s : ℂ, LiCriterion.riemannXi s = 0 → s.re = 1 / 2) ∧ c ^ 2 ≤ 4 * p := by
  rw [← surg_rh_iff p c hp]
  constructor
  · intro h
    exact ⟨fun s hs => h s (by rw [hs, zero_mul]), fun s hs => h s (by rw [hs, mul_zero])⟩
  · rintro ⟨h1, h2⟩ s hs
    rcases mul_eq_zero.mp hs with h | h
    · exact h1 s h
    · exact h2 s h

/-- **Global input 1: low-height certification kills every off-line surgery.**  If the surgery
factor has no off-line zero below height `pi / log 2` (a finite certificate zeta passes: its first
zero is at height 14.13), the local Hasse bound holds.  No `|c| < p + 1` needed. -/
theorem lowcert_kills (p c : ℝ) (hp : 2 ≤ p)
    (hcert : ∀ s : ℂ, surg p c s = 0 → |s.im| ≤ Real.pi / Real.log 2 → s.re = 1 / 2) :
    c ^ 2 ≤ 4 * p := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hL : 0 < Real.log p := Real.log_pos hp1
  by_contra hD
  rw [not_le] at hD
  have h2 : 2 < |-(c / Real.sqrt p)| := by rw [abs_neg]; exact (two_lt_abs_div_sqrt_iff p c hp0).mpr hD
  obtain ⟨x, hx0, _, s, hs, hre, him⟩ := offline_zero_explicit (Real.log p) _ hL h2
  have hlow : |s.im| ≤ Real.pi / Real.log 2 := by
    have hmono : Real.pi / Real.log p ≤ Real.pi / Real.log 2 :=
      div_le_div_of_nonneg_left Real.pi_pos.le (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) hp)
    rcases him with h | h
    · rw [h, abs_zero]; positivity
    · rw [h, abs_of_pos (by positivity)]; exact hmono
  have := hcert s hs hlow
  rw [hre] at this
  have : 0 < x / Real.log p := div_pos hx0 hL
  linarith

/-! ## 5. Unification: the golden fake and the barrier core are members of the family -/

/-- **The golden fake of Build B is the surgery factor of `W_{5,5}`**: `XiA = surg 5 5`. -/
theorem XiA_eq_surg : XiA = surg 5 5 := by
  funext s
  unfold XiA surg
  congr 2
  rw [Real.div_sqrt]

/-- So the golden hybrid `XiH = xi * XiA` IS the completion of the honest Euler product
`W_{5,5} = zeta(s) (1 + 5 * 5^{-s} + 5 * 5^{-2s})` (exact Gamma_R-shape FE, conductor 25). -/
theorem XiH_eq_W55 : XiH = fun s => LiCriterion.riemannXi s * surg 5 5 s := by
  funext s
  unfold XiH
  rw [XiA_eq_surg]

/-! ## 6. Sharpness: LowHeightBox is NOT semi-locally provable -/

lemma log41_gt : 3.659 < Real.log 41 := by
  have h2 := Real.log_two_gt_d9
  have h5 := log5_bounds.1
  have h40 : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    rw [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have hlt : Real.log 40 < Real.log 41 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

lemma pi_div_log41_lt : Real.pi / Real.log 41 < Real.sqrt 3 / 2 := by
  have h41 := log41_gt
  have hpi := Real.pi_lt_d4
  have hs3 : (1.732 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **`W_{41,13}` has an off-line zero in the open strip below height `sqrt 3 / 2`**, so the zero
set of its completion violates Box 1 of the corpus's pointwise layer (`|Im ρ| ≥ sqrt 3/2`), which
zeta satisfies (`zeta_pointwiseLayer`, from LowHeightBox).  Since `W_{41,13}` is a model of the
semi-local interface (`semilocal_barrier`-type data at `p = 41`, `c = 13`: channel axioms, P2 below
`41^2`, all class-P hypotheses but P2 at `41^2`), LowHeightBox's proof is necessarily
non-relativizing: it must use the conductor-1 normalization. -/
theorem lowHeightBox_nonrelativizing :
    (∀ ρ : ℂ, ZetaStripZero ρ → Real.sqrt 3 / 2 ≤ |ρ.im|) ∧
    (∃ s : ℂ, LiCriterion.riemannXi s * surg 41 13 s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1 ∧
      |s.im| < Real.sqrt 3 / 2) := by
  refine ⟨zeta_pointwiseLayer.box1, ?_⟩
  obtain ⟨s, hs, h1, h2, h3⟩ := surg_offline_zero 41 13 (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 13)]; norm_num)
  exact ⟨s, by rw [hs, mul_zero], h1, h2, lt_of_le_of_lt h3 pi_div_log41_lt⟩


/-! ## 7. Coefficient level: `W = exp*(b_W)`, P2 below `p^2`, and the class-P hypotheses -/

section Arith

open ArithmeticFunction Crux.AxisoTheorem

/-- The local polynomial `1 + c T + p T^2` (at `T = p^{-s}`) as an arithmetic function supported
on `{1, p, p^2}`. -/
noncomputable def Ploc (p : ℕ) (c : ℤ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else if n = 1 then 1 else if n = p then (c : ℝ)
    else if n = p ^ 2 then (p : ℝ) else 0, by simp⟩

lemma Ploc_apply (p : ℕ) (c : ℤ) (n : ℕ) :
    Ploc p c n = if n = 0 then 0 else if n = 1 then 1 else if n = p then (c : ℝ)
      else if n = p ^ 2 then (p : ℝ) else 0 := rfl

/-- Lucas power sums `t_m` of the roots of `x^2 + c x + p`. -/
def tLoc (p : ℕ) (c : ℤ) (m : ℕ) : ℤ := CruxMetaBarriers.tr p (-c) m

lemma tLoc_one (p : ℕ) (c : ℤ) : tLoc p c 1 = -c := rfl

lemma tLoc_two (p : ℕ) (c : ℤ) : tLoc p c 2 = c ^ 2 - 2 * p := by
  unfold tLoc; rw [CruxMetaBarriers.tr_succ_succ]; simp [CruxMetaBarriers.tr]; ring

lemma tLoc_rec (p : ℕ) (c : ℤ) (m : ℕ) :
    tLoc p c (m + 2) = -c * tLoc p c (m + 1) - p * tLoc p c m := by
  unfold tLoc; rw [CruxMetaBarriers.tr_succ_succ]

/-- The local log-coefficients: `b_loc(p^m) = -t_m / m` (`m ≥ 1`), zero off the powers of `p`. -/
noncomputable def bLoc (p : ℕ) (c : ℤ) : ArithmeticFunction ℝ :=
  ⟨fun n => if 1 ≤ padicValNat p n ∧ p ^ padicValNat p n = n then
      -(tLoc p c (padicValNat p n) : ℝ) / (padicValNat p n : ℝ) else 0, by simp⟩

lemma bLoc_apply (p : ℕ) (c : ℤ) (n : ℕ) :
    bLoc p c n = if 1 ≤ padicValNat p n ∧ p ^ padicValNat p n = n then
      -(tLoc p c (padicValNat p n) : ℝ) / (padicValNat p n : ℝ) else 0 := rfl

section Prime

variable {p : ℕ} (hp : p.Prime) (c : ℤ)
include hp

lemma p_two_le : 2 ≤ p := hp.two_le

lemma Ploc_one : Ploc p c 1 = 1 := by simp [Ploc_apply]

lemma Ploc_p : Ploc p c p = c := by
  have h1 : p ≠ 1 := hp.one_lt.ne'
  simp [Ploc_apply, hp.ne_zero, h1]

lemma Ploc_sq : Ploc p c (p ^ 2) = p := by
  have h0 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have h1 : p ^ 2 ≠ 1 := by
    intro h; have := (Nat.pow_eq_one.mp h); rcases this with h | h
    · exact hp.one_lt.ne' h
    · omega
  have h2 : p ^ 2 ≠ p := by
    intro h
    have : p ^ 2 = p ^ 1 := by rw [h, pow_one]
    have := Nat.pow_right_injective hp.two_le this
    omega
  simp [Ploc_apply, h0, h1, h2, hp.ne_zero, hp.one_lt.ne']

/-- `Ploc` vanishes at every `n` outside `{1, p, p^2}`. -/
lemma Ploc_eq_zero {n : ℕ} (h1 : n ≠ 1) (h2 : n ≠ p) (h3 : n ≠ p ^ 2) : Ploc p c n = 0 := by
  simp [Ploc_apply, h1, h2, h3]

lemma Ploc_pow_eq_zero {k : ℕ} (hk : 3 ≤ k) : Ploc p c (p ^ k) = 0 := by
  have inj := Nat.pow_right_injective hp.two_le
  apply Ploc_eq_zero hp c
  · intro h; have : p ^ k = p ^ 0 := by rw [h, pow_zero]
    have := inj this; omega
  · intro h; have : p ^ k = p ^ 1 := by rw [h, pow_one]
    have := inj this; omega
  · intro h; have := inj h; omega

lemma bLoc_pow {m : ℕ} (hm : 1 ≤ m) : bLoc p c (p ^ m) = -(tLoc p c m : ℝ) / m := by
  haveI := Fact.mk hp
  rw [bLoc_apply, padicValNat.prime_pow]
  simp [hm]

lemma bLoc_one : bLoc p c 1 = 0 := by simp [bLoc_apply]

lemma bLoc_eq_zero_of {n : ℕ} (hn : ¬ ∃ m, 1 ≤ m ∧ n = p ^ m) : bLoc p c n = 0 := by
  rw [bLoc_apply, if_neg]
  rintro ⟨h1, h2⟩
  exact hn ⟨_, h1, h2.symm⟩

/-- `b_loc(p^j) log(p^j) = -t_j log p` for `j ≥ 1`. -/
lemma bLoc_mul_log_pow {j : ℕ} (hj : 1 ≤ j) :
    bLoc p c (p ^ j) * Real.log ((p ^ j : ℕ) : ℝ) = -(tLoc p c j : ℝ) * Real.log p := by
  rw [bLoc_pow hp c hj]
  push_cast
  rw [Real.log_pow]
  have : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  field_simp

/-- **The local Newton identity** `P · log = (b_loc · log) ⋆ P`, i.e. `P = exp⋆(b_loc)`. -/
theorem Ploc_isDirExp : IsDirExp (Ploc p c) (bLoc p c) := by
  refine ⟨Ploc_one hp c, ?_⟩
  ext n
  rw [pmul_apply, mul_apply, log_apply]
  by_cases hn0 : n = 0
  · subst hn0; simp
  by_cases hpow : ∃ k, n = p ^ k
  · obtain ⟨k, rfl⟩ := hpow
    rw [Nat.sum_divisorsAntidiagonal (fun x y => (bLoc p c).pmul log x * Ploc p c y),
      Nat.sum_divisors_prime_pow hp]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (bLoc p c).pmul log (p ^ j) * Ploc p c (p ^ k / p ^ j)
          = if j = 0 then 0 else -(tLoc p c j : ℝ) * Real.log p * Ploc p c (p ^ (k - j)) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Nat.pow_div hjk hp.pos, pmul_apply, log_apply]
      split_ifs with h0
      · subst h0; simp [bLoc_one hp c]
      · rw [bLoc_mul_log_pow hp c (by omega)]
    rw [Finset.sum_congr rfl hterm]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with hk | hk | hk | hk
    · subst hk; simp [Ploc_one hp c]
    · subst hk
      simp [Finset.sum_range_succ, Ploc_one hp c, Ploc_p hp c, tLoc_one]
    · subst hk
      simp [Finset.sum_range_succ, Ploc_one hp c, Ploc_p hp c, Ploc_sq hp c, tLoc_one, tLoc_two]
      ring
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      rw [Ploc_pow_eq_zero hp c hk, zero_mul]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have hzero : ∑ x ∈ Finset.range (m + 1),
          (if x = 0 then (0 : ℝ) else -(tLoc p c x : ℝ) * Real.log p * Ploc p c (p ^ (m + 3 - x)))
          = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hx' : x < m + 1 := Finset.mem_range.mp hx
        split_ifs
        · rfl
        · rw [Ploc_pow_eq_zero hp c (by omega), mul_zero]
      rw [hzero]
      have e1 : m + 3 - (m + 1) = 2 := by omega
      have e2 : m + 3 - (m + 2) = 1 := by omega
      have e3 : m + 3 - (m + 3) = 0 := by omega
      simp only [e1, e2, e3, pow_one, pow_zero, Ploc_one hp c, Ploc_p hp c, Ploc_sq hp c,
        show m + 1 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 3 ≠ 0 by omega, if_false]
      have hr := tLoc_rec p c (m + 1)
      have hr' : (tLoc p c (m + 3) : ℝ) = -c * tLoc p c (m + 2) - p * tLoc p c (m + 1) := by
        exact_mod_cast hr
      rw [hr']; ring
  · -- `n` is not a power of `p`: both sides vanish
    have hl : Ploc p c n = 0 := by
      apply Ploc_eq_zero hp c
      · intro h; exact hpow ⟨0, by rw [h, pow_zero]⟩
      · intro h; exact hpow ⟨1, by rw [h, pow_one]⟩
      · intro h; exact hpow ⟨2, h⟩
    rw [hl, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    rw [pmul_apply]
    by_cases hb : ∃ m, 1 ≤ m ∧ x.1 = p ^ m
    · obtain ⟨m, _, hm⟩ := hb
      by_cases hP : Ploc p c x.2 = 0
      · rw [hP, mul_zero]
      · exfalso
        have h123 : x.2 = 1 ∨ x.2 = p ∨ x.2 = p ^ 2 := by
          by_contra hc
          push Not at hc
          exact hP (Ploc_eq_zero hp c hc.1 hc.2.1 hc.2.2)
        apply hpow
        rcases h123 with h | h | h
        · exact ⟨m, by rw [← hx'.1, hm, h, mul_one]⟩
        · exact ⟨m + 1, by rw [← hx'.1, hm, h, pow_succ]⟩
        · exact ⟨m + 2, by rw [← hx'.1, hm, h, pow_add]⟩
    · rw [bLoc_eq_zero_of hp c hb, zero_mul, zero_mul]

end Prime

/-- Products of Dirichlet exponentials: `exp⋆(b₁) ⋆ exp⋆(b₂) = exp⋆(b₁ + b₂)`. -/
theorem isDirExp_mul {a₁ b₁ a₂ b₂ : ArithmeticFunction ℝ} (h₁ : IsDirExp a₁ b₁)
    (h₂ : IsDirExp a₂ b₂) : IsDirExp (a₁ * a₂) (b₁ + b₂) := by
  refine ⟨?_, ?_⟩
  · rw [mul_apply_one, h₁.1, h₂.1, mul_one]
  · rw [pmul_mul_of_additive isAdditiveWeight_log, h₁.2, h₂.2]
    have : (b₁ + b₂).pmul log = b₁.pmul log + b₂.pmul log := by
      ext n; simp only [pmul_apply, ArithmeticFunction.add_apply]; ring
    rw [this]; ring

/-- The Dirichlet coefficients of `W_{p,c} = zeta * (1 + c p^{-s} + p p^{-2s})`. -/
noncomputable def aW (p : ℕ) (c : ℤ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * Ploc p c

/-- Its log-coefficients `b_W = Λ/log + b_loc`. -/
noncomputable def bW (p : ℕ) (c : ℤ) : ArithmeticFunction ℝ := zetaLogCoeff + bLoc p c

/-- **`W_{p,c}` is a Dirichlet exponential with the explicit log-coefficients `b_W`.** -/
theorem W_isDirExp {p : ℕ} (hp : p.Prime) (c : ℤ) : IsDirExp (aW p c) (bW p c) :=
  isDirExp_mul zeta_isDirExp (Ploc_isDirExp hp c)

section PrimeW

variable {p : ℕ} (hp : p.Prime) (c : ℤ)
include hp

lemma zetaLogCoeff_pow {m : ℕ} (hm : 1 ≤ m) : zetaLogCoeff (p ^ m) = 1 / m := by
  rw [zetaLogCoeff_apply, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  push_cast
  rw [Real.log_pow]
  have hl : Real.log p ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact (Real.log_pos this).ne'
  have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

/-- `b_W(p^m) = (1 - t_m)/m`: the von Mangoldt weight of `W` at `p^m` is `log p (1 - t_m)`. -/
theorem bW_pow {m : ℕ} (hm : 1 ≤ m) : bW p c (p ^ m) = (1 - (tLoc p c m : ℝ)) / m := by
  rw [bW, ArithmeticFunction.add_apply, zetaLogCoeff_pow hp hm, bLoc_pow hp c hm]
  ring

theorem bW_eq_zeta_off {n : ℕ} (hn : ¬ ∃ m, 1 ≤ m ∧ n = p ^ m) : bW p c n = zetaLogCoeff n := by
  rw [bW, ArithmeticFunction.add_apply, bLoc_eq_zero_of hp c hn, add_zero]

/-- **P2 below `p^2`.**  If `c ≥ -1`, every log-coefficient of `W_{p,c}` at `n < p^2` is `≥ 0`. -/
theorem bW_nonneg_below (hc : -1 ≤ c) {n : ℕ} (hn : n < p ^ 2) : 0 ≤ bW p c n := by
  by_cases h : ∃ m, 1 ≤ m ∧ n = p ^ m
  · obtain ⟨m, hm, rfl⟩ := h
    have hm1 : m = 1 := by
      have : m < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hn
      omega
    subst hm1
    rw [bW_pow hp c le_rfl, tLoc_one]
    push_cast
    have : (-1 : ℝ) ≤ c := by exact_mod_cast hc
    have : (0 : ℝ) ≤ 1 - -(c : ℝ) := by linarith
    positivity
  · rw [bW_eq_zeta_off hp c h]; exact zetaLogCoeff_nonneg n

/-- **P2 fails at `p^2` as soon as `c^2 > 2p + 1`** (in particular for every off-line surgery,
`c^2 > 4p`): `b_W(p^2) = (1 + 2p - c^2)/2`. -/
theorem bW_sq (hD : 2 * (p : ℤ) + 1 < c ^ 2) : bW p c (p ^ 2) < 0 := by
  rw [bW_pow hp c (by norm_num), tLoc_two]
  have : (2 * (p : ℝ) + 1 : ℝ) < (c : ℝ) ^ 2 := by exact_mod_cast hD
  push_cast
  have : (1 - ((c : ℝ) ^ 2 - 2 * p)) < 0 := by linarith
  exact div_neg_of_neg_of_pos this (by norm_num)

/-- Positivity of the power sums of the (positive, real) roots of `x^2 - c x + p`. -/
lemma tr_pos (hc : 0 < c) (hD : 4 * (p : ℤ) < c ^ 2) (m : ℕ) : 0 < CruxMetaBarriers.tr p c m := by
  obtain ⟨α, β, hs, hpr, -, -⟩ := CruxMetaBarriers.real_roots p c hD
  have hrep := (CruxMetaBarriers.tr_real_rep p c α β hs hpr m).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hαβ : 0 < α * β := by rw [hpr]; exact_mod_cast hp.pos
  have hα : 0 < α := by
    by_contra h; push Not at h
    have : β < 0 := by
      rcases lt_or_eq_of_le h with h' | h'
      · exact (neg_of_mul_pos_right hαβ h'.le)
      · rw [h', zero_mul] at hαβ; exact absurd hαβ (lt_irrefl 0)
    push_cast at hs; linarith
  have hβ : 0 < β := pos_of_mul_pos_right hαβ hα.le
  have : (0 : ℝ) < α ^ m + β ^ m := by positivity
  rw [← hrep] at this
  exact_mod_cast this

/-- For `c > 0`, `c^2 > 4p`: `W` has POSITIVE weights at the odd powers of `p` ... -/
theorem bW_odd_pos (hc : 0 < c) (hD : 4 * (p : ℤ) < c ^ 2) (j : ℕ) :
    0 < bW p c (p ^ (2 * j + 1)) := by
  rw [bW_pow hp c (by omega)]
  have ht : tLoc p c (2 * j + 1) = -CruxMetaBarriers.tr p c (2 * j + 1) := by
    unfold tLoc; rw [CruxMetaBarriers.tr_neg, pow_succ, pow_mul]; norm_num
  have hpos := tr_pos hp c hc hD (2 * j + 1)
  rw [ht]; push_cast
  have : (0 : ℝ) < CruxMetaBarriers.tr p c (2 * j + 1) := by exact_mod_cast hpos
  apply div_pos (by linarith); positivity

/-- ... and NEGATIVE weights at every even power `p^(2j)`, `j ≥ 1`. -/
theorem bW_even_neg (hD : 4 * (p : ℤ) < c ^ 2) {j : ℕ} (hj : 1 ≤ j) :
    bW p c (p ^ (2 * j)) < 0 := by
  rw [bW_pow hp c (by omega)]
  have ht : tLoc p c (2 * j) = CruxMetaBarriers.tr p c (2 * j) := by
    unfold tLoc; rw [CruxMetaBarriers.tr_neg, pow_mul]; norm_num
  have hq2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hge := CruxMetaBarriers.tr_even_ge p c hD j
  have hbig := (CruxMetaBarriers.bigRoot_gt p c hq2 hD).2
  have hpow : 1 < CruxMetaBarriers.bigRoot p c ^ (2 * j) := one_lt_pow₀ hbig (by omega)
  rw [ht]
  have : 1 < (CruxMetaBarriers.tr p c (2 * j) : ℝ) := by push_cast at hge ⊢; linarith
  apply div_neg_of_neg_of_pos (by linarith); positivity

/-- `a_W(n) = 1 + c [p ∣ n] + p [p^2 ∣ n]` for `n ≥ 1`. -/
theorem aW_apply {n : ℕ} (hn : 0 < n) :
    aW p c n = 1 + (if p ∣ n then (c : ℝ) else 0) + (if p ^ 2 ∣ n then (p : ℝ) else 0) := by
  have hn0 : n ≠ 0 := by omega
  rw [aW, coe_zeta_mul_apply]
  have hsplit : ∀ i ∈ n.divisors, Ploc p c i
      = (if i = 1 then (1 : ℝ) else 0) + (if i = p then (c : ℝ) else 0)
        + (if i = p ^ 2 then (p : ℝ) else 0) := by
    intro i hi
    have hi0 : i ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hi)
    have hp1 : p ≠ 1 := hp.one_lt.ne'
    have hsq1 : p ^ 2 ≠ 1 := by
      intro h; rcases Nat.pow_eq_one.mp h with h | h
      · exact hp1 h
      · omega
    have hsqp : p ^ 2 ≠ p := by
      intro h
      have : p ^ 2 = p ^ 1 := by rw [h, pow_one]
      have := Nat.pow_right_injective hp.two_le this; omega
    rw [Ploc_apply]
    by_cases h1 : i = 1
    · subst h1; simp [hp1.symm, hsq1.symm]
    by_cases h2 : i = p
    · subst h2; simp [h1, hsqp.symm, hp.ne_zero]
    by_cases h3 : i = p ^ 2
    · subst h3; simp [h1, hsqp, pow_ne_zero 2 hp.ne_zero, hp.ne_zero, hp1]
    simp [h1, h2, h3, hi0]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Nat.mem_divisors, hn0]

/-- **`W` agrees with `zeta` away from `p`**: `a_W(n) = 1` whenever `p ∤ n`. -/
theorem aW_coprime {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) : aW p c n = 1 := by
  rw [aW_apply hp c hn, if_neg hpn, if_neg]
  · ring
  · intro h; exact hpn (dvd_trans (dvd_pow_self p two_ne_zero) h)

/-- **Periodicity mod the conductor `p^2`** (the KP99-type input of `classP_eq_zeta`). -/
theorem aW_periodic : ∃ A : ZMod (p ^ 2) → ℝ, ∀ n : ℕ, 0 < n → aW p c n = A n := by
  refine ⟨fun r => 1 + (if p ∣ r.val then (c : ℝ) else 0) + (if p ^ 2 ∣ r.val then (p : ℝ) else 0),
    fun n hn => ?_⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [aW_apply hp c hn]
  show _ = 1 + (if p ∣ ((n : ZMod (p ^ 2))).val then (c : ℝ) else 0)
    + (if p ^ 2 ∣ ((n : ZMod (p ^ 2))).val then (p : ℝ) else 0)
  rw [ZMod.val_natCast]
  have e1 : p ∣ n % p ^ 2 ↔ p ∣ n := Nat.dvd_mod_iff (dvd_pow_self p two_ne_zero)
  have e2 : p ^ 2 ∣ n % p ^ 2 ↔ p ^ 2 ∣ n := Nat.dvd_mod_iff dvd_rfl
  simp only [e1, e2]

/-- **The FE top coefficient**: `(a_W ⋆ μ)(p^2) = p`, so `|(a_W ⋆ μ)(q)| = sqrt q` at `q = p^2`. -/
theorem aW_top : |(aW p c * (moebius : ArithmeticFunction ℝ)) (p ^ 2)| = √(((p ^ 2 : ℕ)) : ℝ) := by
  have h : aW p c * (moebius : ArithmeticFunction ℝ) = Ploc p c := by
    rw [aW, mul_comm (ArithmeticFunction.zeta : ArithmeticFunction ℝ), mul_assoc,
      coe_zeta_mul_coe_moebius, mul_one]
  rw [h, Ploc_sq hp c]
  push_cast
  rw [Real.sqrt_sq (by positivity), abs_of_nonneg (by positivity)]

/-- **THE CLASS-P COLLAPSE IS SHARP AT ITS POSITIVITY HYPOTHESIS.**  For every prime `p` and every
integer `c`, the data of `W_{p,c}` satisfy every hypothesis of `classP_eq_zeta` (Dirichlet
exponential, periodicity mod `q = p^2`, the FE top coefficient `|P(q)| = sqrt q`) except
positivity; so the collapse theorem itself certifies that some log-coefficient is negative. -/
theorem classP_sharp :
    IsDirExp (aW p c) (bW p c) ∧ (∃ A : ZMod (p ^ 2) → ℝ, ∀ n : ℕ, 0 < n → aW p c n = A n) ∧
      |(aW p c * (moebius : ArithmeticFunction ℝ)) (p ^ 2)| = √(((p ^ 2 : ℕ)) : ℝ) ∧
      p ^ 2 ≠ 1 ∧ ¬ (∀ n, 0 ≤ bW p c n) := by
  have hq1 : p ^ 2 ≠ 1 := by
    intro h; rcases Nat.pow_eq_one.mp h with h | h
    · exact hp.one_lt.ne' h
    · omega
  refine ⟨W_isDirExp hp c, aW_periodic hp c, aW_top hp c, hq1, fun hb => ?_⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  obtain ⟨A, hA⟩ := aW_periodic hp c
  exact hq1 (classP_eq_zeta (W_isDirExp hp c) hb A hA (aW_top hp c)).1

end PrimeW

end Arith


/-! ## 8. The completion has the exact Gamma_R shape (conductor `p^2`) -/

/-- **Completion identity.**  For `Re s > 0`, `s ≠ 1`:
`xi(s) * surg p c s = (1/2) s (s-1) Gamma_R(s) p^{s - 1/2} zeta(s) (1 + c p^{-s} + p p^{-2s})`,
i.e. the completion of `W_{p,c}` is the Gamma_R completion with the extra factor `p^{s}` of a
conductor-`p^2` functional equation (and it is symmetric under `s ↦ 1 - s`: `surg_one_sub`). -/
theorem W_completion (p c : ℝ) (hp : 0 < p) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    LiCriterion.riemannXi s * surg p c s
      = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s * Complex.exp ((s - 1 / 2) * (Real.log p : ℝ)) *
        (riemannZeta s * (1 + c * Complex.exp (-s * (Real.log p : ℝ))
          + (p : ℂ) * Complex.exp (-s * (Real.log p : ℝ)) ^ 2)) := by
  have h0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  rw [CruxDynamicsErgodic.xi_eq_completed h0 hs1, ← surg_eq_localPoly p c hp s,
    riemannZeta_def_of_ne_zero h0]
  field_simp

/-! ## 9. Exhaustion: each GLOBAL input kills every off-line surgery -/

/-- **Global input 2: positivity at every power of `p` forces the local Hasse bound.** -/
theorem positivity_at_powers_kills {p : ℕ} (hp : p.Prime) (c : ℤ)
    (hpos : ∀ m : ℕ, 1 ≤ m → 0 ≤ bW p c (p ^ m)) : c ^ 2 ≤ 4 * (p : ℤ) := by
  have hq2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have h := CruxMetaBarriers.local_rh_of_positivity p (-c) hq2 (k := 0) (fun _ => 0)
    (fun j => j.elim0) 1 (by
      intro n hn
      have := hpos n hn
      rw [bW_pow hp c hn] at this
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : 0 ≤ 1 - (tLoc p c n : ℝ) := by
        by_contra hneg; push Not at hneg
        have : (1 - (tLoc p c n : ℝ)) / n < 0 := div_neg_of_neg_of_pos hneg hn'
        linarith
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re, add_zero]
      unfold tLoc at h1
      exact h1)
  simpa using h

/-- **Global input 3: positivity at `p^2` alone kills every off-line quadratic surgery.** -/
theorem positivity_at_sq_kills {p : ℕ} (hp : p.Prime) (c : ℤ) (h : 0 ≤ bW p c (p ^ 2)) :
    c ^ 2 ≤ 4 * (p : ℤ) := by
  by_contra hD; push Not at hD
  have : 2 * (p : ℤ) + 1 < c ^ 2 := by
    have : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  exact absurd h (not_le.mpr (bW_sq hp c this))

/-! ## 10. THE SEMI-LOCAL BARRIER -/

open CruxDynamicsErgodic in
/-- **THE SEMI-LOCAL RELATIVIZATION BARRIER.**  For every bound `N0` and every finite set `S` of
primes there is a prime `p ∉ S` with `p^2 > N0` and an integer `c` such that the Euler product
`W_{p,c} = zeta(s)(1 + c p^{-s} + p p^{-2s})`:
* is a Dirichlet exponential `a_W = exp⋆(b_W)` with `b_W(n) ≥ 0` for every `n < p^2` (P2 on
  every finite range one fixes in advance) but `b_W(p^2) < 0`;
* agrees with zeta at every prime other than `p` (`a_W(n) = 1` for `p ∤ n`);
* is periodic modulo its conductor `p^2` and has the FE top coefficient `|(a_W ⋆ μ)(p^2)| = p`,
  i.e. satisfies every hypothesis of the class-P collapse `classP_eq_zeta` except P2 at `p^2`;
* has a completion `xi * surg p c` that satisfies all seven channel axioms of Build C;
* and has an off-line zero in the open strip `1/2 < Re s < 1`.
So no argument whose every step is valid for all such data can prove RH. -/
theorem semilocal_barrier (N0 : ℕ) (S : Finset ℕ) :
    ∃ p c : ℕ, p.Prime ∧ p ∉ S ∧ N0 < p ^ 2 ∧ 4 * p < c ^ 2 ∧ c < p + 1 ∧
      Crux.AxisoTheorem.IsDirExp (aW p c) (bW p c) ∧
      (∀ n : ℕ, n < p ^ 2 → 0 ≤ bW p c n) ∧ bW p c (p ^ 2) < 0 ∧
      (∀ n : ℕ, 0 < n → ¬ p ∣ n → aW p c n = 1) ∧
      (∃ A : ZMod (p ^ 2) → ℝ, ∀ n : ℕ, 0 < n → aW p c n = A n) ∧
      |(aW p c * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (p ^ 2)| = √(((p ^ 2 : ℕ)) : ℝ) ∧
      ChannelAxioms (fun w => LiCriterion.riemannXi w * surg p c w) ∧
      (∃ s : ℂ, LiCriterion.riemannXi s * surg p c s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1) := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (N0 + S.sup id + 5)
  set c : ℕ := Nat.sqrt (4 * p) + 1 with hcdef
  have hp5 : 5 ≤ p := by omega
  have hpS : p ∉ S := by
    intro hmem
    have : p ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  have hN0 : N0 < p ^ 2 := by nlinarith
  have hD : 4 * p < c ^ 2 := by rw [hcdef]; exact Nat.lt_succ_sqrt' (4 * p)
  have hcp : c < p + 1 := by
    have : Nat.sqrt (4 * p) < p := Nat.sqrt_lt'.mpr (by nlinarith)
    omega
  have hDz : 4 * (p : ℤ) < ((c : ℤ)) ^ 2 := by exact_mod_cast hD
  have hDz' : 2 * (p : ℤ) + 1 < ((c : ℤ)) ^ 2 := by
    have : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  have hcR : |((c : ℕ) : ℝ)| < (p : ℝ) + 1 := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hcp
  have hDR : 4 * (p : ℝ) < ((c : ℕ) : ℝ) ^ 2 := by exact_mod_cast hD
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨p, c, hp, hpS, hN0, hD, hcp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast W_isDirExp hp (c : ℤ)
  · intro n hn; exact_mod_cast bW_nonneg_below hp (c : ℤ) (by omega) hn
  · exact_mod_cast bW_sq hp (c : ℤ) hDz'
  · intro n hn hpn; exact_mod_cast aW_coprime hp (c : ℤ) hn hpn
  · exact_mod_cast aW_periodic hp (c : ℤ)
  · exact_mod_cast aW_top hp (c : ℤ)
  · have := channelAxioms_W (p : ℝ) ((c : ℕ) : ℝ) hp1 hcR
    exact_mod_cast this
  · obtain ⟨s, hs, h1, h2, -⟩ := surg_offline_zero (p : ℝ) ((c : ℕ) : ℝ) hp1 hDR hcR
    exact ⟨s, by rw [hs, mul_zero], h1, h2⟩

/-! ## 11. One witness, four barriers -/

open CruxDynamicsErgodic in
/-- **The golden fake, unified.**  The golden hybrid `XiH = xi * XiA` of Build B is the completion
of the honest Euler product `W_{5,5} = zeta(s)(1 + 5 * 5^{-s} + 5 * 5^{-2s})`, and that single
object simultaneously (a) passes the corpus's pointwise layer (Build B), (b) passes all seven
channel axioms (Build C's dynamics no-go), (c) satisfies every hypothesis of the class-P collapse
(the axiom-isolation run) except positivity, with P2 holding on `[0, 25)` and failing at `25`,
and (d) has an off-line zero.  (Its Gaussian-layer passage is Build B's rvm_bridge theorem
`gaussian_layer_barrier`, about the same function on the other island.) -/
theorem golden_unified :
    PointwiseLayer (fun ρ => XiH ρ = 0) ∧ ChannelAxioms XiH ∧
      Crux.AxisoTheorem.IsDirExp (aW 5 5) (bW 5 5) ∧ (∀ n : ℕ, n < 5 ^ 2 → 0 ≤ bW 5 5 n) ∧
      bW 5 5 (5 ^ 2) < 0 ∧ (∃ A : ZMod (5 ^ 2) → ℝ, ∀ n : ℕ, 0 < n → aW 5 5 n = A n) ∧
      |(aW 5 5 * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (5 ^ 2)| = √(((5 ^ 2 : ℕ)) : ℝ) ∧
      (∃ ρ : ℂ, XiH ρ = 0 ∧ ρ.re ≠ 1 / 2) := by
  have hp : Nat.Prime 5 := by norm_num
  refine ⟨hybrid_pointwiseLayer, ?_, W_isDirExp hp 5, fun n hn => bW_nonneg_below hp 5 (by norm_num) hn,
    bW_sq hp 5 (by norm_num), aW_periodic hp 5, aW_top hp 5, ⟨_, XiH_offline_zero⟩⟩
  rw [XiH_eq_W55]
  exact_mod_cast channelAxioms_W 5 5 (by norm_num)
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)]; norm_num)

open CruxDynamicsErgodic in
/-- **LowHeightBox is non-relativizing, with the full semi-local certificate.**  `W_{41,13}`
satisfies the semi-local interface (Dirichlet exponential, P2 on `[0, 41^2)`, agreement with zeta
away from 41, periodicity mod `41^2` and the FE top coefficient, all channel axioms), yet its
completion has an off-line zero in the open strip below height `sqrt 3/2`, while every zeta zero in
the strip has height `≥ sqrt 3/2` (LowHeightBox).  So no semi-local argument proves Box 1. -/
theorem W41_semilocal_violates_box1 :
    Crux.AxisoTheorem.IsDirExp (aW 41 13) (bW 41 13) ∧ (∀ n : ℕ, n < 41 ^ 2 → 0 ≤ bW 41 13 n) ∧
      (∀ n : ℕ, 0 < n → ¬ 41 ∣ n → aW 41 13 n = 1) ∧
      (∃ A : ZMod (41 ^ 2) → ℝ, ∀ n : ℕ, 0 < n → aW 41 13 n = A n) ∧
      |(aW 41 13 * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (41 ^ 2)|
        = √(((41 ^ 2 : ℕ)) : ℝ) ∧
      ChannelAxioms (fun w => LiCriterion.riemannXi w * surg 41 13 w) ∧
      (∀ ρ : ℂ, ZetaStripZero ρ → Real.sqrt 3 / 2 ≤ |ρ.im|) ∧
      (∃ s : ℂ, LiCriterion.riemannXi s * surg 41 13 s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1 ∧
        |s.im| < Real.sqrt 3 / 2) := by
  have hp : Nat.Prime 41 := by norm_num
  refine ⟨W_isDirExp hp 13, fun n hn => bW_nonneg_below hp 13 (by norm_num) hn,
    fun n hn h => aW_coprime hp 13 hn h, aW_periodic hp 13, aW_top hp 13, ?_,
    lowHeightBox_nonrelativizing.1, lowHeightBox_nonrelativizing.2⟩
  exact_mod_cast channelAxioms_W 41 13 (by norm_num)
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 13)]; norm_num)


/-! ## 12. (X6) Robust positivity is the trivial bound; the Selberg-class killer; (X1) Euler product -/

section RobustSelberg

open ArithmeticFunction Crux.AxisoTheorem

/-- `Λ_W^-(n)/n`: the negative part of the von Mangoldt weight `Λ_W(n) = b_W(n) log n` of
`W_{p,c}`, divided by `n`.  Its sum is the additive defect `B` of the conductor-uniform
de la Vallee Poussin argument. -/
noncomputable def defect (p : ℕ) (c : ℤ) (n : ℕ) : ℝ :=
  max 0 (-(bW p c n)) * Real.log n / n

section Robust

variable {p : ℕ} (hp : p.Prime) (c : ℤ)
include hp

lemma defect_nonneg (n : ℕ) : 0 ≤ defect p c n := by
  unfold defect
  have h1 : 0 ≤ max 0 (-(bW p c n)) := le_max_left _ _
  have h2 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  positivity

lemma defect_eq_zero_off {n : ℕ} (hn : ¬ ∃ m, 1 ≤ m ∧ n = p ^ m) : defect p c n = 0 := by
  unfold defect
  rw [bW_eq_zeta_off hp c hn]
  have := zetaLogCoeff_nonneg n
  rw [max_eq_left (by linarith)]
  simp

lemma defect_pow {m : ℕ} (hm : 1 ≤ m) :
    defect p c (p ^ m) = max 0 ((tLoc p c m : ℝ) - 1) * Real.log p / (p : ℝ) ^ m := by
  unfold defect
  rw [bW_pow hp c hm]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : -((1 - (tLoc p c m : ℝ)) / m) = ((tLoc p c m : ℝ) - 1) / m := by ring
  have e2 : max 0 (((tLoc p c m : ℝ) - 1) / m) = max 0 ((tLoc p c m : ℝ) - 1) / m := by
    rcases le_total 0 ((tLoc p c m : ℝ) - 1) with h | h
    · rw [max_eq_right (div_nonneg h hm0.le), max_eq_right h]
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg h hm0.le), max_eq_left h, zero_div]
  rw [e1, e2]
  push_cast
  rw [Real.log_pow]
  field_simp

/-- Complex-root (on-line) case: `|t_m| ≤ 2 (sqrt p)^m`, from the Lucas identity. -/
lemma tLoc_abs_le_sqrt (hD : c ^ 2 ≤ 4 * (p : ℤ)) (m : ℕ) :
    |(tLoc p c m : ℝ)| ≤ 2 * Real.sqrt p ^ m := by
  have hL := CruxMetaBarriers.lucas_identity (p : ℤ) (-c) m
  have hneg : (-c) ^ 2 = c ^ 2 := neg_sq c
  have hsq : (tLoc p c m) ^ 2 ≤ 4 * (p : ℤ) ^ m := by
    unfold tLoc
    have : 0 ≤ (4 * (p : ℤ) - (-c) ^ 2) * CruxMetaBarriers.lu p (-c) m ^ 2 :=
      mul_nonneg (by rw [hneg]; linarith) (sq_nonneg _)
    nlinarith
  have hsqR : ((tLoc p c m : ℝ)) ^ 2 ≤ (2 * Real.sqrt p ^ m) ^ 2 := by
    have h1 : ((tLoc p c m : ℝ)) ^ 2 ≤ 4 * (p : ℝ) ^ m := by exact_mod_cast hsq
    have h2 : (2 * Real.sqrt p ^ m) ^ 2 = 4 * (p : ℝ) ^ m := by
      rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]
      norm_num
    linarith
  have h3 := sq_le_sq.mp hsqR
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt p ^ m)] at h3

/-- Real-root case: `|t_m| ≤ 2 R^m`, `R` the larger root modulus. -/
lemma tLoc_abs_le_big (hD : 4 * (p : ℤ) < c ^ 2) (m : ℕ) :
    |(tLoc p c m : ℝ)| ≤ 2 * CruxMetaBarriers.bigRoot p (-c) ^ m := by
  have hDa : 4 * (p : ℤ) < |c| ^ 2 := by rw [sq_abs]; exact hD
  obtain ⟨α, β, hs, hpr, hα, hβ⟩ := CruxMetaBarriers.real_roots (p : ℤ) |c| hDa
  have hrep := (CruxMetaBarriers.tr_real_rep (p : ℤ) |c| α β hs hpr m).1
  have htr : |(tLoc p c m : ℝ)| = |(CruxMetaBarriers.tr (p : ℤ) |c| m : ℝ)| := by
    unfold tLoc
    rcases abs_choice c with h | h
    · rw [h, CruxMetaBarriers.tr_neg]
      push_cast
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    · rw [h]
  have hαeq : α = CruxMetaBarriers.bigRoot p (-c) := by
    rw [hα, CruxMetaBarriers.bigRoot]
    push_cast
    rw [abs_neg, sq_abs, neg_sq]
  have hc0 : (0 : ℝ) ≤ |(c : ℝ)| := abs_nonneg _
  have hDR : 4 * (p : ℝ) < (c : ℝ) ^ 2 := by exact_mod_cast hD
  have hsqrt_le : Real.sqrt ((c : ℝ) ^ 2 - 4 * p) ≤ |(c : ℝ)| := by
    rw [Real.sqrt_le_left hc0]
    rw [sq_abs]
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have hβ0 : 0 ≤ β := by
    rw [hβ]; push_cast; rw [sq_abs]; linarith
  have hβα : β ≤ α := by
    rw [hα, hβ]
    have : 0 ≤ Real.sqrt (((|c| : ℤ) : ℝ) ^ 2 - 4 * ((p : ℤ) : ℝ)) := Real.sqrt_nonneg _
    linarith
  rw [htr, hrep, ← hαeq]
  have hb : β ^ m ≤ α ^ m := pow_le_pow_left₀ hβ0 hβα m
  have hb0 : 0 ≤ β ^ m := pow_nonneg hβ0 m
  rw [abs_of_nonneg (by linarith)]
  linarith

lemma bigRoot_eq (c : ℤ) :
    CruxMetaBarriers.bigRoot p (-c) = (|(c : ℝ)| + Real.sqrt ((c : ℝ) ^ 2 - 4 * p)) / 2 := by
  rw [CruxMetaBarriers.bigRoot]
  push_cast
  rw [abs_neg, neg_sq]

/-- Below the trivial bound the larger root modulus is `< p`. -/
lemma bigRoot_lt_p (hc : |c| < (p : ℤ) + 1) : CruxMetaBarriers.bigRoot p (-c) < p := by
  rw [bigRoot_eq hp c]
  have hc' : |c| ≤ (p : ℤ) := by omega
  have hcR : |(c : ℝ)| ≤ p := by
    have : ((|c| : ℤ) : ℝ) ≤ ((p : ℤ) : ℝ) := by exact_mod_cast hc'
    simpa using this
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hy : 0 < 2 * (p : ℝ) - |(c : ℝ)| := by linarith
  have hcl : |(c : ℝ)| < p + 1 := by
    have : ((|c| : ℤ) : ℝ) < ((p : ℤ) : ℝ) + 1 := by exact_mod_cast hc
    simpa using this
  have hs : Real.sqrt ((c : ℝ) ^ 2 - 4 * p) < 2 * p - |(c : ℝ)| := by
    rw [Real.sqrt_lt' hy]
    rw [← sq_abs (c : ℝ)]
    nlinarith [abs_nonneg (c : ℝ)]
  linarith

/-- At or beyond the trivial bound the larger root modulus is `≥ p`. -/
lemma p_le_bigRoot (hc : (p : ℤ) + 1 ≤ |c|) : (p : ℝ) ≤ CruxMetaBarriers.bigRoot p (-c) := by
  rw [bigRoot_eq hp c]
  have hcR : (p : ℝ) + 1 ≤ |(c : ℝ)| := by
    have : ((p : ℤ) : ℝ) + 1 ≤ ((|c| : ℤ) : ℝ) := by exact_mod_cast hc
    simpa using this
  rcases le_or_gt (2 * (p : ℝ) - |(c : ℝ)|) 0 with h | h
  · have : 0 ≤ Real.sqrt ((c : ℝ) ^ 2 - 4 * p) := Real.sqrt_nonneg _
    linarith
  · have hs : 2 * (p : ℝ) - |(c : ℝ)| ≤ Real.sqrt ((c : ℝ) ^ 2 - 4 * p) := by
      rw [Real.le_sqrt' h]
      rw [← sq_abs (c : ℝ)]
      nlinarith [abs_nonneg (c : ℝ)]
    linarith

/-- **(X6) Robust positivity below the trivial bound.**  If `|c| < p + 1`, the negative part of
the von Mangoldt function of `W_{p,c}` is summable against `1/n`: the additive defect
`B = Σ_n Λ_W^-(n)/n` of the conductor-uniform de la Vallee Poussin argument is finite. -/
theorem robust_positivity (hc : |c| < (p : ℤ) + 1) : Summable (defect p c) := by
  obtain ⟨R, hR0, hRp, hbound⟩ : ∃ R : ℝ, 0 ≤ R ∧ R < p ∧
      ∀ m, |(tLoc p c m : ℝ)| ≤ 2 * R ^ m := by
    rcases le_or_gt (c ^ 2) (4 * (p : ℤ)) with hD | hD
    · refine ⟨Real.sqrt p, Real.sqrt_nonneg _, ?_, tLoc_abs_le_sqrt hp c hD⟩
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      rw [Real.sqrt_lt' (by linarith)]
      nlinarith
    · refine ⟨CruxMetaBarriers.bigRoot p (-c), ?_, bigRoot_lt_p hp c hc, tLoc_abs_le_big hp c hD⟩
      rw [bigRoot_eq hp c]
      positivity
  have hinj : Function.Injective (fun m : ℕ => p ^ (m + 1)) := by
    intro a b h
    have := Nat.pow_right_injective hp.two_le h
    simpa using this
  have hoff : ∀ x ∉ Set.range (fun m : ℕ => p ^ (m + 1)), defect p c x = 0 := by
    intro x hx
    apply defect_eq_zero_off hp c
    rintro ⟨m, hm, rfl⟩
    exact hx ⟨m - 1, by simp only; congr 1; omega⟩
  rw [← hinj.summable_iff hoff]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hgeo : Summable (fun m : ℕ => 2 * Real.log p * (R / p) ^ (m + 1)) := by
    have h1 : Summable (fun m : ℕ => (R / p) ^ m) :=
      summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one hp0]; exact hRp)
    have h2 : Summable (fun m : ℕ => (R / p) ^ (m + 1)) := (summable_nat_add_iff 1).mpr h1
    exact h2.mul_left (2 * Real.log p)
  refine Summable.of_nonneg_of_le (fun m => defect_nonneg hp c _) (fun m => ?_) hgeo
  simp only [Function.comp]
  rw [defect_pow hp c (by omega : 1 ≤ m + 1)]
  have ht := hbound (m + 1)
  have hmax : max 0 ((tLoc p c (m + 1) : ℝ) - 1) ≤ 2 * R ^ (m + 1) := by
    apply max_le (by positivity)
    have := le_abs_self (tLoc p c (m + 1) : ℝ)
    linarith
  have hpm : (0 : ℝ) < (p : ℝ) ^ (m + 1) := by positivity
  calc max 0 ((tLoc p c (m + 1) : ℝ) - 1) * Real.log p / (p : ℝ) ^ (m + 1)
      ≤ 2 * R ^ (m + 1) * Real.log p / (p : ℝ) ^ (m + 1) := by gcongr
    _ = 2 * Real.log p * (R / p) ^ (m + 1) := by rw [div_pow]; field_simp

/-- **(X6) fails at and beyond the trivial bound**: for `|c| ≥ p + 1` the defect terms at the
even powers of `p` stay above `(1/2) log 2`, so the defect diverges. -/
theorem robust_positivity_fails (hc : (p : ℤ) + 1 ≤ |c|) : ¬ Summable (defect p c) := by
  intro hs
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hD : 4 * (p : ℤ) < (-c) ^ 2 := by
    have h1 : ((p : ℤ) + 1) ^ 2 ≤ |c| ^ 2 := by
      have : (0 : ℤ) ≤ (p : ℤ) + 1 := by omega
      exact pow_le_pow_left₀ this hc 2
    rw [sq_abs] at h1
    rw [neg_sq]
    nlinarith
  have hinj : Function.Injective (fun j : ℕ => p ^ (2 * (j + 1))) := by
    intro a b h
    have := Nat.pow_right_injective hp.two_le h
    omega
  have ht := (hs.comp_injective hinj).tendsto_atTop_zero
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : ∀ j : ℕ, (1 / 2) * Real.log 2 ≤ defect p c (p ^ (2 * (j + 1))) := by
    intro j
    rw [defect_pow hp c (by omega)]
    have hge := CruxMetaBarriers.tr_even_ge (p : ℤ) (-c) hD (j + 1)
    have hbig := p_le_bigRoot hp c hc
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hpow : (p : ℝ) ^ (2 * (j + 1)) ≤ CruxMetaBarriers.bigRoot p (-c) ^ (2 * (j + 1)) :=
      pow_le_pow_left₀ hp0 hbig _
    have htp : (p : ℝ) ^ (2 * (j + 1)) ≤ (tLoc p c (2 * (j + 1)) : ℝ) := by
      unfold tLoc
      have : (((p : ℤ) : ℝ)) = (p : ℝ) := by push_cast; rfl
      linarith
    have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hP4 : (4 : ℝ) ≤ (p : ℝ) ^ (2 * (j + 1)) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hp1 2
        _ ≤ (p : ℝ) ^ (2 * (j + 1)) :=
            pow_le_pow_right₀ (by linarith) (by omega)
    have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp1
    set P : ℝ := (p : ℝ) ^ (2 * (j + 1)) with hP
    have hmax : P - 1 ≤ max 0 ((tLoc p c (2 * (j + 1)) : ℝ) - 1) := by
      apply le_max_of_le_right; linarith
    have hPpos : 0 < P := by linarith
    rw [le_div_iff₀ hPpos]
    have hlp : 0 ≤ Real.log p := by linarith
    calc 1 / 2 * Real.log 2 * P ≤ (P - 1) * Real.log p := by nlinarith
      _ ≤ max 0 ((tLoc p c (2 * (j + 1)) : ℝ) - 1) * Real.log p := by gcongr
  have hev := ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (1 / 2) * Real.log 2))
  obtain ⟨j, hj⟩ := hev.exists
  have := hlow j
  simp only [Function.comp] at hj
  linarith

/-- **(X6) = the local TRIVIAL bound**: the defect `B` is finite iff `|c| < p + 1`, exactly the
condition for the channel edge condition (`surg_edge`).  So robust positivity, like the channel
conditions, sees only the trivial bound, never the Hasse bound `c^2 ≤ 4p`. -/
theorem robust_positivity_iff : Summable (defect p c) ↔ |c| < (p : ℤ) + 1 := by
  constructor
  · intro hs
    by_contra h
    exact robust_positivity_fails hp c (by omega) hs
  · exact robust_positivity hp c

end Robust

/-! ## The Selberg-class Euler axiom kills every surgery (on-line ones included) -/

/-- Power sums in `ℂ` through two complex roots with the right sum and product. -/
lemma tr_complex_rep (q m : ℤ) (α β : ℂ) (hs : α + β = m) (hp : α * β = q) :
    ∀ n : ℕ, (CruxMetaBarriers.tr q m n : ℂ) = α ^ n + β ^ n ∧
      (CruxMetaBarriers.tr q m (n + 1) : ℂ) = α ^ (n + 1) + β ^ (n + 1)
  | 0 => by
      refine ⟨by simp [CruxMetaBarriers.tr]; norm_num, ?_⟩
      simp [CruxMetaBarriers.tr, hs]
  | (n + 1) => by
      obtain ⟨h0, h1⟩ := tr_complex_rep q m α β hs hp n
      refine ⟨h1, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl, CruxMetaBarriers.tr_succ_succ]
      push_cast
      rw [h0, h1, ← hs, ← hp]
      ring

lemma exists_complex_roots (q m : ℤ) : ∃ α β : ℂ, α + β = m ∧ α * β = q := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq ((m : ℂ) ^ 2 - 4 * q) (by norm_num : 0 < 2)
  refine ⟨(m + d) / 2, (m - d) / 2, by ring, ?_⟩
  have : ((m : ℂ) + d) / 2 * (((m : ℂ) - d) / 2) = ((m : ℂ) ^ 2 - d ^ 2) / 4 := by ring
  rw [this, hd]
  ring

/-- **Doubling formula** `t_{2n} = t_n^2 - 2 q^n`. -/
lemma tr_double (q m : ℤ) (n : ℕ) :
    CruxMetaBarriers.tr q m (2 * n) = CruxMetaBarriers.tr q m n ^ 2 - 2 * q ^ n := by
  obtain ⟨α, β, hs, hp⟩ := exists_complex_roots q m
  have h1 := (tr_complex_rep q m α β hs hp (2 * n)).1
  have h2 := (tr_complex_rep q m α β hs hp n).1
  have : (CruxMetaBarriers.tr q m (2 * n) : ℂ)
      = ((CruxMetaBarriers.tr q m n ^ 2 - 2 * q ^ n : ℤ) : ℂ) := by
    push_cast
    rw [h1, h2, ← hp]
    ring
  exact_mod_cast this

section Selberg

variable {p : ℕ} (hp : p.Prime) (c : ℤ)
include hp

/-- **The local roots of every surgery have modulus at least `sqrt p`**: for every `m`,
`t_m^2 > p^m` or `|t_{2m}| ≥ p^m`. -/
lemma tLoc_large (m : ℕ) : (p : ℤ) ^ m < tLoc p c m ^ 2 ∨ (p : ℤ) ^ m ≤ |tLoc p c (2 * m)| := by
  rcases lt_or_ge ((p : ℤ) ^ m) (tLoc p c m ^ 2) with h | h
  · exact Or.inl h
  · right
    have hd := tr_double (p : ℤ) (-c) m
    have hpm : (0 : ℤ) ≤ (p : ℤ) ^ m := by positivity
    unfold tLoc at h ⊢
    rw [hd, abs_of_nonpos (by nlinarith)]
    linarith

/-- Hence `|t_k| ≥ (sqrt p)^k` for arbitrarily large `k`. -/
lemma tLoc_large_frequently (M : ℕ) :
    ∃ k : ℕ, M ≤ k ∧ 1 ≤ k ∧ Real.sqrt p ^ k ≤ |(tLoc p c k : ℝ)| := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  rcases tLoc_large hp c (M + 1) with h | h
  · refine ⟨M + 1, by omega, by omega, ?_⟩
    have e : (Real.sqrt p ^ (M + 1)) ^ 2 = (p : ℝ) ^ (M + 1) := by
      rw [← pow_mul, mul_comm, pow_mul, hsq]
    have hR : (Real.sqrt p ^ (M + 1)) ^ 2 < ((tLoc p c (M + 1) : ℝ)) ^ 2 := by
      rw [e]
      exact_mod_cast h
    have h2 := sq_lt_sq.mp hR
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt p ^ (M + 1))] at h2
    exact h2.le
  · refine ⟨2 * (M + 1), by omega, by omega, ?_⟩
    have hR : ((p : ℤ) : ℝ) ^ (M + 1) ≤ ((|tLoc p c (2 * (M + 1))| : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    rw [pow_mul, hsq]
    exact hR


/-- **Every surgery violates the Selberg-class Euler-product axiom** `b(n) ≪ n^θ`, `θ < 1/2`,
on-line surgeries (`c^2 ≤ 4p`) included: the local roots have modulus `≥ sqrt p`. -/
theorem surgery_not_selberg {θ : ℝ} (hθ : θ < 1 / 2) (C : ℝ) :
    ¬ (∀ n : ℕ, 1 ≤ n → |bW p c n| ≤ C * (n : ℝ) ^ θ) := by
  intro H
  set θ' : ℝ := max θ 0 with hθ'def
  have hθ' : θ' < 1 / 2 := max_lt hθ (by norm_num)
  have hθ0 : 0 ≤ θ' := le_max_right _ _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have H' : ∀ k : ℕ, 1 ≤ k → |bW p c (p ^ k)| ≤ |C| * ((p : ℝ) ^ θ') ^ k := by
    intro k hk
    have hn : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
    have h1 : (1 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hn
    have e : ((p ^ k : ℕ) : ℝ) ^ θ' = ((p : ℝ) ^ θ') ^ k := by
      push_cast
      rw [← Real.rpow_natCast_mul hp0.le, mul_comm, Real.rpow_mul_natCast hp0.le]
    calc |bW p c (p ^ k)| ≤ C * ((p ^ k : ℕ) : ℝ) ^ θ := H (p ^ k) hn
      _ ≤ |C| * ((p ^ k : ℕ) : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((p ^ k : ℕ) : ℝ) ^ θ' :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)) (abs_nonneg C)
      _ = |C| * ((p : ℝ) ^ θ') ^ k := by rw [e]
  set b : ℝ := (p : ℝ) ^ θ' with hb
  have hb1 : 1 ≤ b := Real.one_le_rpow hp1.le hθ0
  have hbpos : 0 < b := by linarith
  have hsb : b < Real.sqrt p := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 hθ'
  set a : ℝ := Real.sqrt p / b with ha
  have ha1 : 1 < a := by rw [ha, one_lt_div hbpos]; exact hsb
  have hev : ∀ᶠ k : ℕ in Filter.atTop, 1 + |C| * k < a ^ k := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 ha1).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * (|C| + 1))))
    have h2 := (tendsto_pow_atTop_atTop_of_one_lt ha1).eventually_gt_atTop 2
    filter_upwards [h1, h2] with k hk1 hk2
    have hak : 0 < a ^ k := by positivity
    rw [pow_one, div_lt_iff₀ hak] at hk1
    have hpos : 0 < 2 * (|C| + 1) := by positivity
    have h3 : 2 * (|C| + 1) * k < a ^ k := by
      calc 2 * (|C| + 1) * k < 2 * (|C| + 1) * (1 / (2 * (|C| + 1)) * a ^ k) := by gcongr
        _ = a ^ k := by field_simp
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [abs_nonneg C]
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨k, hkK, hk1, hlarge⟩ := tLoc_large_frequently hp c K
  have hbound := H' k hk1
  rw [bW_pow hp c hk1] at hbound
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  rw [abs_div, abs_of_pos hk0, div_le_iff₀ hk0] at hbound
  have htri : |(tLoc p c k : ℝ)| - 1 ≤ |1 - (tLoc p c k : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (tLoc p c k : ℝ) 1
    rw [abs_one] at this
    rw [abs_sub_comm]
    exact this
  have hsk : Real.sqrt p ^ k = a ^ k * b ^ k := by
    rw [ha, div_pow]
    field_simp
  have hbk : 1 ≤ b ^ k := one_le_pow₀ hb1
  have hbk0 : 0 < b ^ k := by positivity
  have hmain : a ^ k * b ^ k ≤ (1 + |C| * k) * b ^ k := by
    have : Real.sqrt p ^ k - 1 ≤ |C| * b ^ k * k := by linarith
    rw [hsk] at this
    nlinarith [abs_nonneg C]
  have hle : a ^ k ≤ 1 + |C| * k := le_of_mul_le_mul_right hmain hbk0
  have := hK k hkK
  linarith

/-- The same finite surgery changes only the factor at `p`: the Dirichlet coefficients
`1 + c p^{-s} + p p^{-2s}` form a multiplicative arithmetic function. -/
lemma Ploc_isMultiplicative : IsMultiplicative (Ploc p c) := by
  refine ⟨Ploc_one hp c, fun {m n} hmn => ?_⟩
  by_cases hm1 : m = 1
  · subst hm1; rw [one_mul, Ploc_one hp c, one_mul]
  by_cases hn1 : n = 1
  · subst hn1; rw [mul_one, Ploc_one hp c, mul_one]
  have hsupp : ∀ k, Ploc p c k ≠ 0 → k = 1 ∨ k = p ∨ k = p ^ 2 := by
    intro k hk
    by_contra hc
    push Not at hc
    exact hk (Ploc_eq_zero hp c hc.1 hc.2.1 hc.2.2)
  have hdvd : ∀ k, Ploc p c k ≠ 0 → k ≠ 1 → p ∣ k := by
    intro k hk hk1
    rcases hsupp k hk with h | h | h
    · exact absurd h hk1
    · rw [h]
    · rw [h]; exact dvd_pow_self p two_ne_zero
  have hL : Ploc p c (m * n) = 0 := by
    by_contra hne
    rcases hsupp _ hne with h | h | h
    · exact hm1 (Nat.eq_one_of_mul_eq_one_right h)
    · have hpr : (m * n).Prime := h ▸ hp
      rcases Nat.prime_mul_iff.mp hpr with ⟨_, hn⟩ | ⟨_, hm⟩
      · exact hn1 hn
      · exact hm1 hm
    · have hm : m ∣ p ^ 2 := ⟨n, h.symm⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
      interval_cases i
      · exact hm1 (pow_zero p)
      · have hn' : n = p := by
          have : p * n = p * p := by rw [pow_one] at h; rw [h]; ring
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        rw [pow_one, hn'] at hmn
        exact hp.one_lt.ne' ((Nat.coprime_self p).mp hmn)
      · have : p ^ 2 * n = p ^ 2 * 1 := by rw [h, mul_one]
        exact hn1 (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) this)
  rw [hL]
  by_contra hne
  have hm0 : Ploc p c m ≠ 0 := left_ne_zero_of_mul (Ne.symm hne)
  have hn0 : Ploc p c n ≠ 0 := right_ne_zero_of_mul (Ne.symm hne)
  have hg := Nat.dvd_gcd (hdvd m hm0 hm1) (hdvd n hn0 hn1)
  rw [Nat.Coprime.gcd_eq_one hmn, Nat.dvd_one] at hg
  exact hp.one_lt.ne' hg

/-- **(X1) `W_{p,c}` is an Euler product**: its coefficients are multiplicative. -/
theorem aW_isMultiplicative : IsMultiplicative (aW p c) :=
  isMultiplicative_zeta.natCast.mul (Ploc_isMultiplicative hp c)

end Selberg

/-- ... while `zeta` satisfies the Selberg-class Euler axiom with `θ = 0`: `0 ≤ b_ζ(n) ≤ 1`. -/
theorem zetaLogCoeff_le_one (n : ℕ) : zetaLogCoeff n ≤ 1 := by
  rw [zetaLogCoeff_apply]
  rcases le_or_gt n 1 with h | h
  · interval_cases n <;> simp
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast h)
    rw [div_le_one hlog]
    exact ArithmeticFunction.vonMangoldt_le_log


end RobustSelberg

/-! ## 13. (X5) The support-prime duality in the kernel; (X2) the L-series of the witness -/

section SupportPrime

open MeasureTheory
open scoped FourierTransform ContDiff

/-- Weil's transform of a test function, `h(z) = ∫ g(x) e^{i x z} dx`, at a complex point. -/
noncomputable def weilHat (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp (I * x * z)

/-- The rescaled, twisted test `F(u) = g(L u) e^{i u α}`. -/
noncomputable def twistScale (g : ℝ → ℂ) (L : ℝ) (α : ℂ) (u : ℝ) : ℂ :=
  g (L * u) * Complex.exp (I * u * α)

lemma twistScale_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (L : ℝ) (α : ℂ) :
    ContDiff ℝ ∞ (twistScale g L α) := by
  unfold twistScale
  apply ContDiff.mul
  · exact hg.comp (contDiff_const.mul contDiff_id)
  · apply ContDiff.cexp
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const

lemma twistScale_hasCompactSupport {g : ℝ → ℂ} (hgc : HasCompactSupport g) {L : ℝ} (hL : L ≠ 0)
    (α : ℂ) : HasCompactSupport (twistScale g L α) := by
  have h1 : HasCompactSupport (fun u : ℝ => g (L * u)) :=
    hgc.comp_homeomorph (Homeomorph.mulLeft₀ L hL)
  exact h1.mul_right

lemma twistScale_pointwise (g : ℝ → ℂ) {L : ℝ} (hL : L ≠ 0) (α : ℂ) (k : ℤ) (u : ℝ) :
    g (L * u) * Complex.exp (I * ((L * u : ℝ) : ℂ) * ((α + 2 * Real.pi * k) / L))
      = Complex.exp (((-2 * Real.pi * u * ((-k : ℤ) : ℝ) : ℝ) : ℂ) * I) • twistScale g L α u := by
  unfold twistScale
  rw [smul_eq_mul]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have e : I * ((L * u : ℝ) : ℂ) * ((α + 2 * Real.pi * k) / L)
      = ((-2 * Real.pi * u * ((-k : ℤ) : ℝ) : ℝ) : ℂ) * I + I * u * α := by
    push_cast
    field_simp
    ring
  rw [e, Complex.exp_add]
  ring

/-- **Poisson summation over one branch of a zero lattice.**  For a smooth compactly supported
test `g`, any `L > 0` and any complex `α`,
`Σ_{k ∈ ℤ} h((α + 2πk)/L) = L Σ_{n ∈ ℤ} g(nL) e^{i n α}` (with `h` = `weilHat g`). -/
theorem lattice_poisson {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) {L : ℝ}
    (hL : 0 < L) (α : ℂ) :
    HasSum (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / L))
      (L * ∑' n : ℤ, g (L * n) * Complex.exp (I * n * α)) := by
  set F : ℝ → ℂ := twistScale g L α with hFdef
  have hFs := twistScale_contDiff hg L α
  have hFc := twistScale_hasCompactSupport hgc hL.ne' α
  set Fs : SchwartzMap ℝ ℂ := hFc.toSchwartzMap hFs with hFsdef
  have hP := SchwartzMap.tsum_eq_tsum_fourier Fs 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  have hsum : Summable (fun n : ℤ => 𝓕 F (n : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 Fs).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have hkey : ∀ k : ℤ, weilHat g ((α + 2 * Real.pi * k) / L) = L * 𝓕 F ((-k : ℤ) : ℝ) := by
    intro k
    set G : ℝ → ℂ := fun x => g x * Complex.exp (I * x * ((α + 2 * Real.pi * k) / L)) with hG
    have hsub : ∫ u : ℝ, G (L * u) = |L⁻¹| • ∫ x : ℝ, G x :=
      MeasureTheory.Measure.integral_comp_mul_left G L
    have hint : ∫ x : ℝ, G x = (L : ℂ) * ∫ u : ℝ, G (L * u) := by
      rw [hsub, abs_of_pos (inv_pos.mpr hL), Complex.real_smul, ← mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ hL.ne', Complex.ofReal_one, one_mul]
    show ∫ x : ℝ, G x = _
    rw [hint, Real.fourier_real_eq_integral_exp_smul]
    congr 1
    congr 1
    funext u
    exact twistScale_pointwise g hL.ne' α k u
  have hneg : HasSum (fun k : ℤ => 𝓕 F ((-k : ℤ) : ℝ)) (∑' n : ℤ, 𝓕 F n) :=
    (Equiv.neg ℤ).hasSum_iff.mpr hsum.hasSum
  have hP' : ∑' n : ℤ, 𝓕 F n = ∑' n : ℤ, g (L * n) * Complex.exp (I * n * α) := by
    have e1 : ∑' n : ℤ, 𝓕 F (n : ℝ) = ∑' n : ℤ, (𝓕 Fs) (n : ℝ) := rfl
    rw [e1, ← hP]
    rfl
  have h := hneg.mul_left (L : ℂ)
  rw [hP'] at h
  have hfun : (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / L))
      = (fun k : ℤ => (L : ℂ) * 𝓕 F ((-k : ℤ) : ℝ)) := funext hkey
  rw [hfun]
  exact h

/-- **Support below `L`: the lattice sum is `L g(0)`, independent of `α`.** -/
theorem lattice_poisson_small {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ x : ℝ, L ≤ |x| → g x = 0) (α : ℂ) :
    HasSum (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / L)) (L * g 0) := by
  have h := lattice_poisson hg hgc hL α
  have hs : ∑' n : ℤ, g (L * n) * Complex.exp (I * n * α) = g 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
        exact_mod_cast this
      have : L ≤ |L * n| := by
        rw [abs_mul, abs_of_pos hL]
        nlinarith
      rw [hsupp _ this, zero_mul]
  rwa [hs] at h

/-- **Support below `2L`: exactly the three lattice points `0, ±L` are seen.** -/
theorem lattice_poisson_two {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ x : ℝ, 2 * L ≤ |x| → g x = 0) (α : ℂ) :
    HasSum (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / L))
      (L * (g 0 + g L * Complex.exp (I * α) + g (-L) * Complex.exp (-(I * α)))) := by
  have h := lattice_poisson hg hgc hL α
  have hs : ∑' n : ℤ, g (L * n) * Complex.exp (I * n * α)
      = g 0 + g L * Complex.exp (I * α) + g (-L) * Complex.exp (-(I * α)) := by
    rw [tsum_eq_sum (s := {0, 1, -1})]
    · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [Int.cast_zero, mul_zero, Int.cast_one, mul_one, Int.cast_neg, mul_neg,
        zero_mul, Complex.exp_zero]
      ring_nf
    · intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have h2 : (2 : ℝ) ≤ |(n : ℝ)| := by
        have : (2 : ℤ) ≤ |n| := by
          rcases le_or_gt 0 n with h0 | h0
          · rw [abs_of_nonneg h0]; omega
          · rw [abs_of_neg h0]; omega
        exact_mod_cast this
      have : 2 * L ≤ |L * n| := by
        rw [abs_mul, abs_of_pos hL]
        nlinarith
      rw [hsupp _ this, zero_mul]
  rwa [hs] at h

/-! ### The zero lattice of the completed local factor -/

/-- The zeros of `Xi L c` (Build B's completed genus-one factor) form two arithmetic progressions:
if `2 cos α = c`, then `Xi L c (1/2 + i γ) = 0` iff `γ = (±α + 2πk)/L` for some `k ∈ ℤ`. -/
theorem Xi_zero_iff_lattice (L c : ℝ) (hL : L ≠ 0) (α : ℂ) (hα : 2 * Complex.cos α = c)
    (γ : ℂ) :
    CruxMetaBarriers.Xi L c (1 / 2 + I * γ) = 0 ↔
      ∃ k : ℤ, γ = (α + 2 * Real.pi * k) / L ∨ γ = (-α + 2 * Real.pi * k) / L := by
  unfold CruxMetaBarriers.Xi
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have e : (1 / 2 + I * γ - 1 / 2) * (L : ℂ) = (γ * L) * I := by ring
  rw [e, Complex.cosh_mul_I, sub_eq_zero, ← hα, mul_right_inj' two_ne_zero, eq_comm,
    Complex.cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [eq_div_iff hL', h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [eq_div_iff hL', h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; field_simp; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; field_simp; ring)⟩

/-- Every point is `1/2 + i γ` for `γ = -i (s - 1/2)`. -/
lemma half_add_I_mul (s : ℂ) : s = 1 / 2 + I * (-I * (s - 1 / 2)) := by
  have : I * (-I * (s - 1 / 2)) = -(I * I) * (s - 1 / 2) := by ring
  rw [this, Complex.I_mul_I]
  ring

/-- The two branches are disjoint when `c^2 ≠ 4` (then `α ∉ π ℤ`). -/
theorem lattice_branches_disjoint (L c : ℝ) (hL : L ≠ 0) (α : ℂ) (hα : 2 * Complex.cos α = c)
    (hc : c ^ 2 ≠ 4) (k k' : ℤ) :
    (α + 2 * Real.pi * k) / L ≠ (-α + 2 * Real.pi * k') / L := by
  intro h
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [div_left_inj' hL'] at h
  have hα' : α = ((k' - k : ℤ) : ℂ) * Real.pi := by
    push_cast
    linear_combination h / 2
  have hs : Complex.sin α = 0 := by rw [hα']; exact Complex.sin_int_mul_pi _
  have hcos : Complex.cos α ^ 2 = 1 := by
    have := Complex.sin_sq_add_cos_sq α
    rw [hs] at this
    linear_combination this
  apply hc
  have : ((c : ℂ)) ^ 2 = 4 := by
    rw [← hα]
    linear_combination 4 * hcos
  exact_mod_cast this

/-- Within one branch the parametrisation is injective. -/
theorem lattice_branch_injective (L : ℝ) (hL : L ≠ 0) (α : ℂ) (ε : ℂ) (k k' : ℤ)
    (h : (ε * α + 2 * Real.pi * k) / L = (ε * α + 2 * Real.pi * k') / L) : k = k' := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [div_left_inj' hL'] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : ((k : ℂ)) = k' := by
    have h2 : 2 * (Real.pi : ℂ) * k = 2 * Real.pi * k' := by linear_combination h
    have h3 : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi
    exact mul_left_cancel₀ h3 h2
  exact_mod_cast this

/-- `Xi L c` has derivative `2 L sinh((s - 1/2) L)`. -/
lemma Xi_hasDerivAt (L c : ℝ) (s : ℂ) :
    HasDerivAt (CruxMetaBarriers.Xi L c) (2 * (L * Complex.sinh ((s - 1 / 2) * L))) s := by
  unfold CruxMetaBarriers.Xi
  have h1 : HasDerivAt (fun s : ℂ => (s - 1 / 2) * (L : ℂ)) (L : ℂ) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (L : ℂ)
  have h2 := (Complex.hasDerivAt_cosh ((s - 1 / 2) * L)).comp s h1
  have h3 := (h2.const_mul (2 : ℂ)).sub_const (c : ℂ)
  exact h3.congr_deriv (by ring)

/-- **All zeros are simple when `c^2 ≠ 4`.** -/
theorem Xi_zero_simple (L c : ℝ) (hL : L ≠ 0) (hc : c ^ 2 ≠ 4) (s : ℂ)
    (hs : CruxMetaBarriers.Xi L c s = 0) : deriv (CruxMetaBarriers.Xi L c) s ≠ 0 := by
  rw [(Xi_hasDerivAt L c s).deriv]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  intro h0
  have hsinh : Complex.sinh ((s - 1 / 2) * L) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h two_ne_zero
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hL'
      · exact h'
  unfold CruxMetaBarriers.Xi at hs
  have hcosh : 2 * Complex.cosh ((s - 1 / 2) * L) = c := by linear_combination hs
  have hpy := Complex.cosh_sq_sub_sinh_sq ((s - 1 / 2) * L)
  rw [hsinh] at hpy
  apply hc
  have : ((c : ℂ)) ^ 2 = 4 := by
    rw [← hcosh]
    linear_combination 4 * hpy
  exact_mod_cast this

/-! ### (X5) The support-prime duality for the surgery factor, in the kernel -/

/-- **THE SUPPORT-PRIME DUALITY (kernel form).**  Let `p > 1` and `c^2 ≠ 4p`, and put
`L = log p`.  There is `α ∈ ℂ` with `2 cos α = -c/sqrt p` such that
* the zeros of the completed surgery factor `surg p c` are exactly the points `1/2 + i γ` with
  `γ = (±α + 2πk)/L`, `k ∈ ℤ`; the two branches are disjoint and every zero is simple;
* for every smooth test `g` supported in `(-L, L)`, the sum of Weil's transform
  `h(γ) = ∫ g(x) e^{i x γ} dx` over this zero set is `2 L g(0)`: it does not depend on `c`;
* for every smooth test `g` supported in `(-2L, 2L)`, the sum is
  `2 L (g(0) - (c / (2 sqrt p)) (g(L) + g(-L)))`: at support `L` the surgery becomes visible.
Since the zeros of `xi * surg p c` are those of `xi` together with these (orders add), the Weil
functional of `W_{p,c}` is `Z_W(g) = Z_ζ(g) + 2 log p · g(0)` for every test supported in
`(-log p, log p)`: every bounded-support positivity certificate for `ζ` holds verbatim for
`W_{p,c}`, with margin increased by `2 log p · g(0) ≥ 0` for positive-type `g`. -/
theorem surg_explicit_formula (p c : ℝ) (hp : 1 < p) (hc : c ^ 2 ≠ 4 * p) :
    ∃ α : ℂ, 2 * Complex.cos α = -(c / Real.sqrt p) ∧
      (∀ γ : ℂ, surg p c (1 / 2 + I * γ) = 0 ↔
        ∃ k : ℤ, γ = (α + 2 * Real.pi * k) / Real.log p ∨
          γ = (-α + 2 * Real.pi * k) / Real.log p) ∧
      (∀ k k' : ℤ, (α + 2 * Real.pi * k) / Real.log p ≠ (-α + 2 * Real.pi * k') / Real.log p) ∧
      (∀ s : ℂ, surg p c s = 0 → deriv (surg p c) s ≠ 0) ∧
      (∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
        (∀ x : ℝ, Real.log p ≤ |x| → g x = 0) →
        HasSum (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / Real.log p)
          + weilHat g ((-α + 2 * Real.pi * k) / Real.log p)) (2 * Real.log p * g 0)) ∧
      (∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
        (∀ x : ℝ, 2 * Real.log p ≤ |x| → g x = 0) →
        HasSum (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / Real.log p)
          + weilHat g ((-α + 2 * Real.pi * k) / Real.log p))
          (2 * Real.log p * (g 0 - (c / (2 * Real.sqrt p)) * (g (Real.log p) + g (-Real.log p))))) := by
  have hp0 : 0 < p := by linarith
  have hL : 0 < Real.log p := Real.log_pos hp
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  obtain ⟨α, hα⟩ := Complex.cos_surjective (-((c / Real.sqrt p : ℝ) : ℂ) / 2)
  have hα2 : 2 * Complex.cos α = ((-(c / Real.sqrt p) : ℝ) : ℂ) := by
    rw [hα]; push_cast; ring
  have hc' : (-(c / Real.sqrt p)) ^ 2 ≠ 4 := by
    rw [neg_sq, div_pow, hsq]
    intro h
    apply hc
    field_simp at h
    linarith
  have hsurg : surg p c = CruxMetaBarriers.Xi (Real.log p) (-(c / Real.sqrt p)) := rfl
  refine ⟨α, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hα2]; push_cast; ring
  · intro γ
    rw [hsurg]
    exact Xi_zero_iff_lattice _ _ hL.ne' α hα2 γ
  · exact lattice_branches_disjoint _ _ hL.ne' α hα2 hc'
  · intro s hs
    rw [hsurg] at hs ⊢
    exact Xi_zero_simple _ _ hL.ne' hc' s hs
  · intro g hg hgc hsupp
    have h1 := lattice_poisson_small hg hgc hL hsupp α
    have h2 := lattice_poisson_small hg hgc hL hsupp (-α)
    have h := h1.add h2
    convert h using 1
    ring
  · intro g hg hgc hsupp
    have h1 := lattice_poisson_two hg hgc hL hsupp α
    have h2 := lattice_poisson_two hg hgc hL hsupp (-α)
    simp only [mul_neg, neg_neg] at h2
    have h := h1.add h2
    convert h using 1
    have hcos : Complex.exp (I * α) + Complex.exp (-(I * α)) = -((c / Real.sqrt p : ℝ) : ℂ) := by
      have := Complex.two_cos α
      rw [hα] at this
      rw [mul_comm I α, ← neg_mul]
      linear_combination -this
    have e : (((c / (2 * Real.sqrt p)) : ℝ) : ℂ) = ((c / Real.sqrt p : ℝ) : ℂ) / 2 := by
      push_cast; ring
    push_cast at hcos e ⊢
    rw [e]
    linear_combination (-(Real.log p : ℂ) * (g (Real.log p) + g (-Real.log p))) * hcos

/-- **Positivity transfer below support `log p`.**  For a test whose value at `0` is real and
nonnegative (every positive-type test `g = f ⋆ f̃` has `g(0) = ‖f‖^2`), the surgery's zeros add
`2 log p · g(0) ≥ 0` to the Weil functional. -/
theorem surg_zero_sum_nonneg (p c : ℝ) (hp : 1 < p) (hc : c ^ 2 ≠ 4 * p) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hsupp : ∀ x : ℝ, Real.log p ≤ |x| → g x = 0)
    (hg0 : 0 ≤ (g 0).re) (hg0' : (g 0).im = 0) :
    ∃ α : ℂ, (∀ γ : ℂ, surg p c (1 / 2 + I * γ) = 0 ↔
        ∃ k : ℤ, γ = (α + 2 * Real.pi * k) / Real.log p ∨
          γ = (-α + 2 * Real.pi * k) / Real.log p) ∧
      ∃ S : ℂ, HasSum (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / Real.log p)
          + weilHat g ((-α + 2 * Real.pi * k) / Real.log p)) S ∧ 0 ≤ S.re ∧ S.im = 0 := by
  obtain ⟨α, -, hz, -, -, hsmall, -⟩ := surg_explicit_formula p c hp hc
  refine ⟨α, hz, _, hsmall g hg hgc hsupp, ?_, ?_⟩
  · have hL : 0 ≤ Real.log p := (Real.log_pos hp).le
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
      Complex.ofReal_im, mul_zero, sub_zero, zero_mul, hg0']
    positivity
  · simp [hg0']

/-! ### The L-series of `W_{p,c}` -/

section LSeriesW

open ArithmeticFunction

variable {p : ℕ} (hp : p.Prime) (c : ℤ)
include hp

/-- The local factor's coefficients as a complex arithmetic function. -/
noncomputable def PlocC (p : ℕ) (c : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun n => ((Ploc p c n : ℝ) : ℂ), by simp [Ploc_apply]⟩

omit hp in
lemma PlocC_apply (n : ℕ) : PlocC p c n = ((Ploc p c n : ℝ) : ℂ) := rfl

lemma aW_coe_eq : (fun n => ((aW p c n : ℝ) : ℂ))
    = ⇑((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * PlocC p c) := by
  funext n
  rw [aW, coe_zeta_mul_apply, coe_zeta_mul_apply]
  push_cast
  rfl

lemma PlocC_support {n : ℕ} (hn : n ∉ ({1, p, p ^ 2} : Finset ℕ)) : PlocC p c n = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rw [PlocC_apply, Ploc_eq_zero hp c hn.1 hn.2.1 hn.2.2, Complex.ofReal_zero]

lemma LSeries_PlocC (s : ℂ) :
    LSeries ⇑(PlocC p c) s = 1 + c * (p : ℂ) ^ (-s) + p * ((p : ℂ) ^ (-s)) ^ 2 := by
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hsq1 : p ^ 2 ≠ 1 := by
    intro h; rcases Nat.pow_eq_one.mp h with h | h
    · exact hp1 h
    · omega
  have hsqp : p ^ 2 ≠ p := by
    intro h
    have : p ^ 2 = p ^ 1 := by rw [h, pow_one]
    have := Nat.pow_right_injective hp.two_le this; omega
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold LSeries
  rw [tsum_eq_sum (s := {1, p, p ^ 2})]
  · rw [Finset.sum_insert (by simp [hp1.symm, hsq1.symm]),
      Finset.sum_insert (by simp [hsqp.symm]), Finset.sum_singleton]
    rw [LSeries.term_of_ne_zero one_ne_zero, LSeries.term_of_ne_zero hp.ne_zero,
      LSeries.term_of_ne_zero (pow_ne_zero 2 hp.ne_zero)]
    rw [PlocC_apply, PlocC_apply, PlocC_apply, Ploc_one hp c, Ploc_p hp c, Ploc_sq hp c]
    push_cast
    rw [Complex.one_cpow, div_one, Complex.cpow_neg]
    have e : ((p : ℂ) ^ 2) ^ s = ((p : ℂ) ^ s) ^ 2 := by
      rw [sq, sq, Complex.natCast_mul_natCast_cpow]
    rw [e]
    have hps : (p : ℂ) ^ s ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hpC]; exact Complex.exp_ne_zero _
    field_simp
    ring
  · intro n hn
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · rw [PlocC_support hp c hn, zero_div]

/-- **The Dirichlet series of the coefficient-level witness is `ζ(s) (1 + c p^{-s} + p p^{-2s})`**
on `Re s > 1`, closing the chain from `aW` (Euler product, P2 below `p^2`, class-P data) to the
completion `xi * surg p c` (`W_completion`). -/
theorem LSeries_aW {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((aW p c n : ℝ) : ℂ)) s
      = riemannZeta s * (1 + c * (p : ℂ) ^ (-s) + p * ((p : ℂ) ^ (-s)) ^ 2) := by
  have hζ : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    have h := LSeriesSummable_zeta_iff.mpr hs
    refine (LSeriesSummable_congr s (fun {n} _ => ?_)).mp h
    simp [natCoe_apply]
  have hP : LSeriesSummable ⇑(PlocC p c) s := by
    unfold LSeriesSummable
    apply summable_of_ne_finset_zero (s := {1, p, p ^ 2})
    intro n hn
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · rw [PlocC_support hp c hn, zero_div]
  rw [aW_coe_eq hp c, LSeries_mul' hζ hP, LSeries_PlocC hp c s]
  congr 1
  rw [← LSeries_zeta_eq_riemannZeta hs]
  congr 1

/-- `p^{-s} = e^{-s log p}` for a prime `p`. -/
lemma natCast_cpow_neg_eq_exp (s : ℂ) :
    (p : ℂ) ^ (-s) = Complex.exp (-s * (Real.log p : ℝ)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Complex.cpow_def_of_ne_zero hpC, Complex.ofReal_log (Nat.cast_nonneg p),
    Complex.ofReal_natCast, mul_comm]

/-- **The completion of the Dirichlet series `L(a_W, s)`**: for `Re s > 1`,
`xi(s) surg(s) = (1/2) s (s-1) Γ_ℝ(s) p^{s-1/2} L(a_W, s)`. -/
theorem W_completion_LSeries {s : ℂ} (hs : 1 < s.re) :
    LiCriterion.riemannXi s * surg p c s
      = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s * Complex.exp ((s - 1 / 2) * (Real.log p : ℝ)) *
        LSeries (fun n => ((aW p c n : ℝ) : ℂ)) s := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  rw [W_completion (p : ℝ) (c : ℝ) (by exact_mod_cast hp.pos) s hs0 hs1, LSeries_aW hp c hs,
    natCast_cpow_neg_eq_exp hp s]
  push_cast
  ring

end LSeriesW

end SupportPrime


/-! ## 14. The channel axioms and robust positivity are EXACTLY the local trivial bound -/

/-- **Edge = trivial bound.**  The surgery factor has no zero on `Re w ≥ 1` iff `|c| < p + 1`
(beyond it, the off-line zero `1/2 + x/log p`, `cosh x = |c|/(2 sqrt p)`, has real part `≥ 1`). -/
theorem surg_edge_iff (p c : ℝ) (hp : 1 < p) :
    (∀ w : ℂ, 1 ≤ w.re → surg p c w ≠ 0) ↔ |c| < p + 1 := by
  constructor
  · intro h
    by_contra hc
    have hp0 : 0 < p := by linarith
    have hL : 0 < Real.log p := Real.log_pos hp
    have hb : 2 * Real.cosh (Real.log p / 2) ≤ |-(c / Real.sqrt p)| := by
      rw [abs_neg]
      exact not_lt.mp (fun h' => hc ((surg_trivial_bound_iff p c hp0).mp h'))
    have hcosh : 1 < Real.cosh (Real.log p / 2) := Real.one_lt_cosh.mpr (by positivity)
    have h2 : 2 < |-(c / Real.sqrt p)| := by linarith
    obtain ⟨x, hx0, hcx, s, hs, hre, -⟩ := offline_zero_explicit (Real.log p) _ hL h2
    have hmono : Real.cosh (Real.log p / 2) ≤ Real.cosh x := by rw [hcx]; linarith
    rw [Real.cosh_le_cosh, abs_of_pos (by positivity), abs_of_pos hx0] at hmono
    have hre1 : 1 ≤ s.re := by
      rw [hre]
      have : 1 / 2 ≤ x / Real.log p := by rw [le_div_iff₀ hL]; linarith
      linarith
    exact h s hre1 hs
  · exact fun hc w hw => surg_edge p c hp hc w hw

open CruxDynamicsErgodic in
/-- **(X4) = the local TRIVIAL bound.**  The completion `xi * surg p c` satisfies Build C's seven
channel axioms iff `|c| < p + 1`.  The Hasse bound `c^2 ≤ 4p` (RH at `p`) is invisible to them. -/
theorem channelAxioms_W_iff (p c : ℝ) (hp : 1 < p) :
    ChannelAxioms (fun w => LiCriterion.riemannXi w * surg p c w) ↔ |c| < p + 1 := by
  constructor
  · intro h
    rw [← surg_edge_iff p c hp]
    intro w hw h0
    exact h.edge w hw (by simp [h0])
  · exact channelAxioms_W p c hp

/-! ## 15. A global-but-incomplete positivity input is still fooled: the prime-square surgery -/

section PrimeSquareSurgery

open ArithmeticFunction Crux.AxisoTheorem

/-- A local factor at `p` with coefficient sequence `e`: `n ↦ e_k` if `n = p^k`, else `0`. -/
noncomputable def locE (p : ℕ) (e : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ p ^ padicValNat p n = n then e (padicValNat p n) else 0, by simp⟩

/-- Its log-coefficients from power sums `s`: `-s_k / k` at `p^k` (`k ≥ 1`). -/
noncomputable def locS (p : ℕ) (s : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if 1 ≤ padicValNat p n ∧ p ^ padicValNat p n = n then
      -s (padicValNat p n) / (padicValNat p n : ℝ) else 0, by simp⟩

section LocalGeneral

variable {p : ℕ} (hp : p.Prime)
include hp

lemma locE_pow (e : ℕ → ℝ) (k : ℕ) : locE p e (p ^ k) = e k := by
  have : Fact p.Prime := ⟨hp⟩
  show (if p ^ k ≠ 0 ∧ p ^ padicValNat p (p ^ k) = p ^ k then e (padicValNat p (p ^ k))
    else 0) = e k
  rw [padicValNat.prime_pow]
  simp [hp.ne_zero]

lemma locE_eq_zero (e : ℕ → ℝ) {n : ℕ} (hn : ¬ ∃ k, n = p ^ k) : locE p e n = 0 := by
  show (if n ≠ 0 ∧ p ^ padicValNat p n = n then e (padicValNat p n) else 0) = 0
  rw [if_neg]
  rintro ⟨_, h⟩
  exact hn ⟨_, h.symm⟩

lemma locS_pow (s : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) : locS p s (p ^ k) = -s k / k := by
  have : Fact p.Prime := ⟨hp⟩
  show (if 1 ≤ padicValNat p (p ^ k) ∧ p ^ padicValNat p (p ^ k) = p ^ k then
      -s (padicValNat p (p ^ k)) / (padicValNat p (p ^ k) : ℝ) else 0) = -s k / k
  rw [padicValNat.prime_pow]
  simp [hk]

omit hp in
lemma locS_one (s : ℕ → ℝ) : locS p s 1 = 0 := by
  show (if 1 ≤ padicValNat p 1 ∧ p ^ padicValNat p 1 = 1 then
      -s (padicValNat p 1) / (padicValNat p 1 : ℝ) else 0) = 0
  simp

omit hp in
lemma locS_eq_zero (s : ℕ → ℝ) {n : ℕ} (hn : ¬ ∃ k, 1 ≤ k ∧ n = p ^ k) : locS p s n = 0 := by
  show (if 1 ≤ padicValNat p n ∧ p ^ padicValNat p n = n then
      -s (padicValNat p n) / (padicValNat p n : ℝ) else 0) = 0
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hn ⟨_, h1, h2.symm⟩

/-- **The local Newton identity, general form.**  If `e_0 = 1` and `(e, s)` satisfy Newton's
identities `k e_k = -Σ_{i<k} s_{k-i} e_i` for `k ≥ 1`, then the local factor `Σ_k e_k p^{-ks}` is
the Dirichlet exponential of `Σ_{k≥1} (-s_k/k) p^{-ks}`. -/
theorem locE_isDirExp (e s : ℕ → ℝ) (he0 : e 0 = 1)
    (hN : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * e k = -∑ i ∈ Finset.range k, s (k - i) * e i) :
    IsDirExp (locE p e) (locS p s) := by
  refine ⟨by rw [show (1 : ℕ) = p ^ 0 from (pow_zero p).symm, locE_pow hp, he0], ?_⟩
  ext n
  rw [pmul_apply, mul_apply, log_apply]
  by_cases hn0 : n = 0
  · subst hn0; simp
  by_cases hpow : ∃ k, n = p ^ k
  · obtain ⟨k, rfl⟩ := hpow
    rw [Nat.sum_divisorsAntidiagonal (fun x y => (locS p s).pmul log x * locE p e y),
      Nat.sum_divisors_prime_pow hp, locE_pow hp]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (locS p s).pmul log (p ^ j) * locE p e (p ^ k / p ^ j)
          = if j = 0 then 0 else -s j * Real.log p * e (k - j) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Nat.pow_div hjk hp.pos, pmul_apply, log_apply, locE_pow hp]
      split_ifs with h0
      · subst h0; simp [locS_one]
      · rw [locS_pow hp s (by omega)]
        push_cast
        rw [Real.log_pow]
        have : (j : ℝ) ≠ 0 := by exact_mod_cast h0
        field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, if_true, add_zero]
    have hre : ∑ j ∈ Finset.range k, -s (j + 1) * Real.log p * e (k - (j + 1))
        = -Real.log p * ∑ i ∈ Finset.range k, s (k - i) * e i := by
      rw [Finset.mul_sum]
      conv_rhs => rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have e1 : k - (k - 1 - j) = j + 1 := by omega
      have e2 : k - (j + 1) = k - 1 - j := by omega
      rw [e1, e2]
      ring
    rw [hre]
    push_cast
    rw [Real.log_pow]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have hNk := hN k hk
      linear_combination Real.log p * hNk
  · rw [locE_eq_zero hp e hpow, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    rw [pmul_apply]
    by_cases hb : ∃ k, 1 ≤ k ∧ x.1 = p ^ k
    · obtain ⟨k, -, hk⟩ := hb
      by_cases hy : ∃ j, x.2 = p ^ j
      · obtain ⟨j, hj⟩ := hy
        exfalso
        exact hpow ⟨k + j, by rw [← hx'.1, hk, hj, pow_add]⟩
      · rw [locE_eq_zero hp e hy, mul_zero]
    · rw [locS_eq_zero s hb, zero_mul, zero_mul]

/-- A function supported on the powers of one prime, with value `1` at `1`, is multiplicative. -/
theorem isMultiplicative_of_primePow_support {f : ArithmeticFunction ℝ} (hf1 : f 1 = 1)
    (hsupp : ∀ n, f n ≠ 0 → ∃ k, n = p ^ k) : IsMultiplicative f := by
  refine ⟨hf1, fun {m n} hmn => ?_⟩
  by_cases hm1 : m = 1
  · subst hm1; rw [one_mul, hf1, one_mul]
  by_cases hn1 : n = 1
  · subst hn1; rw [mul_one, hf1, mul_one]
  have hnot : ∀ k, m * n ≠ p ^ k := by
    intro k hk
    have hm : m ∣ p ^ k := ⟨n, hk.symm⟩
    have hn : n ∣ p ^ k := ⟨m, by rw [← hk, mul_comm]⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hn
    have hi : i ≠ 0 := by rintro rfl; exact hm1 (pow_zero p)
    have hj : j ≠ 0 := by rintro rfl; exact hn1 (pow_zero p)
    have h1 : p ∣ p ^ i := dvd_pow_self p hi
    have h2 : p ∣ p ^ j := dvd_pow_self p hj
    have hg := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hmn, Nat.dvd_one] at hg
    exact hp.one_lt.ne' hg
  have hL : f (m * n) = 0 := by
    by_contra h
    obtain ⟨k, hk⟩ := hsupp _ h
    exact hnot k hk
  rw [hL]
  by_contra hne
  have hm0 : f m ≠ 0 := left_ne_zero_of_mul (Ne.symm hne)
  have hn0 : f n ≠ 0 := right_ne_zero_of_mul (Ne.symm hne)
  obtain ⟨i, rfl⟩ := hsupp m hm0
  obtain ⟨j, rfl⟩ := hsupp n hn0
  exact hnot (i + j) (by rw [pow_add])

lemma locE_isMultiplicative (e : ℕ → ℝ) (he0 : e 0 = 1) : IsMultiplicative (locE p e) := by
  refine isMultiplicative_of_primePow_support hp ?_ ?_
  · rw [show (1 : ℕ) = p ^ 0 from (pow_zero p).symm, locE_pow hp, he0]
  · intro n hn
    by_contra h
    exact hn (locE_eq_zero hp e h)

end LocalGeneral

/-! ### The prime-square surgery `zeta(s) (1 + A p^{-2s} + p^2 p^{-4s})` -/

/-- Coefficients of the local factor `1 + A T^2 + p^2 T^4`. -/
noncomputable def e4 (p : ℕ) (A : ℤ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 2 then (A : ℝ) else if k = 4 then (p : ℝ) ^ 2 else 0

/-- Its power sums: `0` at odd `k`, `2 t_{k/2}` at even `k`, where `t` are the power sums of the
roots of `y^2 + A y + p^2`. -/
noncomputable def s4 (p : ℕ) (A : ℤ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then 2 * (CruxMetaBarriers.tr ((p : ℤ) ^ 2) (-A) (k / 2) : ℝ) else 0

lemma e4_eq_zero (p : ℕ) (A : ℤ) {k : ℕ} (h0 : k ≠ 0) (h2 : k ≠ 2) (h4 : k ≠ 4) :
    e4 p A k = 0 := by
  simp [e4, h0, h2, h4]

lemma newton4 (p : ℕ) (A : ℤ) :
    ∀ k : ℕ, 1 ≤ k → (k : ℝ) * e4 p A k = -∑ i ∈ Finset.range k, s4 p A (k - i) * e4 p A i := by
  intro k hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k by omega) with h | h | h | h | h
  · subst h; simp [e4, s4]
  · subst h
    simp [e4, s4, Finset.sum_range_succ]
  · subst h
    simp [e4, s4, Finset.sum_range_succ]
  · subst h
    simp [e4, s4, Finset.sum_range_succ, CruxMetaBarriers.tr]
    ring
  · have hsub : ({0, 2, 4} : Finset ℕ) ⊆ Finset.range k := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      omega
    rw [← Finset.sum_subset hsub (fun i _ hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [e4_eq_zero p A hi.1 hi.2.1 hi.2.2, mul_zero])]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [e4_eq_zero p A (by omega) (by omega) (by omega)]
    simp only [e4, if_true, show (2 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 0 by decide,
      show (4 : ℕ) ≠ 2 by decide, if_false, mul_zero, Nat.sub_zero, mul_one]
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- k = m + m even, m ≥ 3
      have hk2 : (k - 2) % 2 = 0 := by omega
      have hk4 : (k - 4) % 2 = 0 := by omega
      have hk0 : k % 2 = 0 := by omega
      simp only [s4, hk0, hk2, hk4, if_true]
      have e0 : k / 2 = (m - 2) + 2 := by omega
      have e2 : (k - 2) / 2 = (m - 2) + 1 := by omega
      have e4' : (k - 4) / 2 = m - 2 := by omega
      rw [e0, e2, e4', CruxMetaBarriers.tr_succ_succ]
      push_cast
      ring
    · have hk2 : (k - 2) % 2 = 1 := by omega
      have hk4 : (k - 4) % 2 = 1 := by omega
      have hk0 : k % 2 = 1 := by omega
      simp [s4, hk0, hk2, hk4]

/-- The coefficient-level prime-square surgery `W^{(2)}_{p,A} = zeta * (1 + A p^{-2s} + p^2 p^{-4s})`. -/
noncomputable def aW4 (p : ℕ) (A : ℤ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * locE p (e4 p A)

/-- Its log-coefficients. -/
noncomputable def bW4 (p : ℕ) (A : ℤ) : ArithmeticFunction ℝ := zetaLogCoeff + locS p (s4 p A)

section PrimeSquare

variable {p : ℕ} (hp : p.Prime) (A : ℤ)
include hp

theorem W4_isDirExp : IsDirExp (aW4 p A) (bW4 p A) :=
  isDirExp_mul zeta_isDirExp (locE_isDirExp hp _ _ (by simp [e4]) (newton4 p A))

theorem aW4_isMultiplicative : IsMultiplicative (aW4 p A) :=
  isMultiplicative_zeta.natCast.mul (locE_isMultiplicative hp _ (by simp [e4]))

lemma bW4_pow {k : ℕ} (hk : 1 ≤ k) : bW4 p A (p ^ k) = (1 - s4 p A k) / k := by
  rw [bW4, ArithmeticFunction.add_apply, zetaLogCoeff_pow hp hk, locS_pow hp _ hk]
  ring

lemma bW4_eq_zeta_off {n : ℕ} (hn : ¬ ∃ k, 1 ≤ k ∧ n = p ^ k) : bW4 p A n = zetaLogCoeff n := by
  rw [bW4, ArithmeticFunction.add_apply, locS_eq_zero _ hn, add_zero]

/-- **P2 on `[0, p^4)`**: for `A ≥ 0` every log-coefficient below `p^4` is nonnegative. -/
theorem bW4_nonneg_below (hA : 0 ≤ A) {n : ℕ} (hn : n < p ^ 4) : 0 ≤ bW4 p A n := by
  by_cases h : ∃ k, 1 ≤ k ∧ n = p ^ k
  · obtain ⟨k, hk, rfl⟩ := h
    have hk4 : k < 4 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hn
    rw [bW4_pow hp A hk]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl
    · simp [s4]
    · simp only [s4, show 2 % 2 = 0 by rfl, if_true, show 2 / 2 = 1 by rfl,
        CruxMetaBarriers.tr_one]
      push_cast
      have : (0 : ℝ) ≤ A := by exact_mod_cast hA
      apply div_nonneg _ (by norm_num)
      linarith
    · simp [s4]
  · rw [bW4_eq_zeta_off hp A h]
    exact zetaLogCoeff_nonneg n

/-- **P2 at every prime square.** -/
theorem bW4_prime_sq (hA : 0 ≤ A) {q : ℕ} (hq : q.Prime) : 0 ≤ bW4 p A (q ^ 2) := by
  by_cases hqp : q = p
  · subst hqp
    apply bW4_nonneg_below hp A hA
    exact Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  · rw [bW4_eq_zeta_off hp A]
    · exact zetaLogCoeff_nonneg _
    · rintro ⟨k, hk, hqk⟩
      have hdvd : q ∣ p ^ k := ⟨q, by rw [← hqk]; ring⟩
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd))

/-- **P2 fails at `p^4`** as soon as `A^2 > 4 p^2` (the off-line case). -/
theorem bW4_p4 (hA : 4 * (p : ℤ) ^ 2 < A ^ 2) : bW4 p A (p ^ 4) < 0 := by
  rw [bW4_pow hp A (by norm_num)]
  simp only [s4, show 4 % 2 = 0 by rfl, if_true, show 4 / 2 = 2 by rfl]
  simp only [CruxMetaBarriers.tr_succ_succ, zero_add, CruxMetaBarriers.tr_one,
    CruxMetaBarriers.tr_zero]
  have hAR : 4 * (p : ℝ) ^ 2 < (A : ℝ) ^ 2 := by exact_mod_cast hA
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  push_cast
  apply div_neg_of_neg_of_pos _ (by norm_num)
  nlinarith

end PrimeSquare

section PrimeSquareLSeries

variable {p : ℕ} (hp : p.Prime) (A : ℤ)
include hp

/-- The prime-square local factor as a complex arithmetic function. -/
noncomputable def loc4C (p : ℕ) (A : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun n => ((locE p (e4 p A) n : ℝ) : ℂ), by simp⟩

omit hp in
lemma loc4C_apply (n : ℕ) : loc4C p A n = ((locE p (e4 p A) n : ℝ) : ℂ) := rfl

lemma aW4_coe_eq : (fun n => ((aW4 p A n : ℝ) : ℂ))
    = ⇑((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * loc4C p A) := by
  funext n
  rw [aW4, coe_zeta_mul_apply, coe_zeta_mul_apply]
  push_cast
  rfl

lemma loc4C_support {n : ℕ} (hn : n ∉ ({1, p ^ 2, p ^ 4} : Finset ℕ)) : loc4C p A n = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rw [loc4C_apply]
  by_cases h : ∃ k, n = p ^ k
  · obtain ⟨k, rfl⟩ := h
    rw [locE_pow hp, e4_eq_zero p A]
    · simp
    · rintro rfl; exact hn.1 (pow_zero p)
    · rintro rfl; exact hn.2.1 rfl
    · rintro rfl; exact hn.2.2 rfl
  · rw [locE_eq_zero hp _ h, Complex.ofReal_zero]

lemma LSeries_loc4C (s : ℂ) :
    LSeries ⇑(loc4C p A) s = 1 + A * ((p : ℂ) ^ (-s)) ^ 2 + p ^ 2 * ((p : ℂ) ^ (-s)) ^ 4 := by
  have inj := Nat.pow_right_injective hp.two_le
  have h1 : (1 : ℕ) ≠ p ^ 2 := by
    intro h; have : p ^ 0 = p ^ 2 := by rw [pow_zero]; exact h
    exact absurd (inj this) (by norm_num)
  have h2 : (1 : ℕ) ≠ p ^ 4 := by
    intro h; have : p ^ 0 = p ^ 4 := by rw [pow_zero]; exact h
    exact absurd (inj this) (by norm_num)
  have h3 : p ^ 2 ≠ p ^ 4 := by
    intro h; exact absurd (inj h) (by norm_num)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hps : (p : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpC]; exact Complex.exp_ne_zero _
  unfold LSeries
  rw [tsum_eq_sum (s := {1, p ^ 2, p ^ 4})]
  · rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_insert (by simp [h3]),
      Finset.sum_singleton]
    rw [LSeries.term_of_ne_zero one_ne_zero, LSeries.term_of_ne_zero (pow_ne_zero 2 hp.ne_zero),
      LSeries.term_of_ne_zero (pow_ne_zero 4 hp.ne_zero)]
    rw [loc4C_apply, loc4C_apply, loc4C_apply, show (1 : ℕ) = p ^ 0 from (pow_zero p).symm,
      locE_pow hp, locE_pow hp, locE_pow hp]
    simp only [e4, if_true, show (2 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 0 by decide,
      show (4 : ℕ) ≠ 2 by decide, if_false]
    push_cast
    rw [pow_zero, Complex.one_cpow, div_one, Complex.cpow_neg]
    have e2 : ((p : ℂ) ^ 2) ^ s = ((p : ℂ) ^ s) ^ 2 := by
      rw [sq, sq, Complex.natCast_mul_natCast_cpow]
    have e4' : ((p : ℂ) ^ 4) ^ s = ((p : ℂ) ^ s) ^ 4 := by
      have : ((p : ℂ) ^ 4) = ((p ^ 2 : ℕ) : ℂ) * ((p ^ 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.natCast_mul_natCast_cpow]
      push_cast
      rw [e2]
      ring
    rw [e2, e4']
    field_simp
    ring
  · intro n hn
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · rw [loc4C_support hp A hn, zero_div]

/-- **The Dirichlet series of the prime-square surgery**: `ζ(s) (1 + A p^{-2s} + p^2 p^{-4s})`. -/
theorem LSeries_aW4 {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((aW4 p A n : ℝ) : ℂ)) s
      = riemannZeta s * (1 + A * ((p : ℂ) ^ (-s)) ^ 2 + p ^ 2 * ((p : ℂ) ^ (-s)) ^ 4) := by
  have hζ : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    have h := LSeriesSummable_zeta_iff.mpr hs
    refine (LSeriesSummable_congr s (fun {n} _ => ?_)).mp h
    simp [natCoe_apply]
  have hP : LSeriesSummable ⇑(loc4C p A) s := by
    unfold LSeriesSummable
    apply summable_of_ne_finset_zero (s := {1, p ^ 2, p ^ 4})
    intro n hn
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · rw [loc4C_support hp A hn, zero_div]
  rw [aW4_coe_eq hp A, LSeries_mul' hζ hP, LSeries_loc4C hp A s]
  congr 1
  rw [← LSeries_zeta_eq_riemannZeta hs]
  congr 1

/-- **Its completion**: for `Re s > 1`,
`xi(s) surg(p^2, A)(s) = (1/2) s (s-1) Γ_ℝ(s) (p^2)^{s-1/2} L(a_{W^{(2)}}, s)`: the Gamma_R-shape
completion with conductor `p^4`. -/
theorem W4_completion_LSeries {s : ℂ} (hs : 1 < s.re) :
    LiCriterion.riemannXi s * surg ((p : ℝ) ^ 2) A s
      = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s *
        Complex.exp ((s - 1 / 2) * (Real.log ((p : ℝ) ^ 2) : ℝ)) *
        LSeries (fun n => ((aW4 p A n : ℝ) : ℂ)) s := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by have := hp.pos; positivity
  rw [W_completion ((p : ℝ) ^ 2) (A : ℝ) hp2 s hs0 hs1, LSeries_aW4 hp A hs]
  have hexp : Complex.exp (-s * (Real.log ((p : ℝ) ^ 2) : ℝ)) = ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [Real.log_pow, natCast_cpow_neg_eq_exp hp s, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  push_cast
  ring

end PrimeSquareLSeries

open CruxDynamicsErgodic in
/-- **A GLOBAL-BUT-INCOMPLETE POSITIVITY INPUT IS STILL FOOLED.**  For every prime `p ≥ 3` the
prime-square surgery `W = zeta(s) (1 + A p^{-2s} + p^2 p^{-4s})`, `A = 2p + 1`, is an Euler product
and a Dirichlet exponential; it satisfies P2 at EVERY prime square and on all of `[0, p^4)`, fails
it only at `p^4`; the completion `xi * surg (p^2) A` of its Dirichlet series (Gamma_R shape,
conductor `p^4`) satisfies all seven channel axioms; and it vanishes at a point with
`1/2 < Re s < 1`.  So "P2 at all prime squares" (which kills every off-line quadratic surgery,
`positivity_at_sq_kills`) does not pin zeta; for Euler products the complete positivity input is
P2 at ALL prime powers, i.e. the hypothesis of the class-P collapse `classP_eq_zeta`. -/
theorem prime_square_surgery {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∃ A : ℤ, 2 * (p : ℤ) < A ∧ A < (p : ℤ) ^ 2 + 1 ∧
      IsMultiplicative (aW4 p A) ∧ IsDirExp (aW4 p A) (bW4 p A) ∧
      (∀ q : ℕ, q.Prime → 0 ≤ bW4 p A (q ^ 2)) ∧
      (∀ n : ℕ, n < p ^ 4 → 0 ≤ bW4 p A n) ∧ bW4 p A (p ^ 4) < 0 ∧
      (∀ s : ℂ, 1 < s.re → LiCriterion.riemannXi s * surg ((p : ℝ) ^ 2) A s
        = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s *
          Complex.exp ((s - 1 / 2) * (Real.log ((p : ℝ) ^ 2) : ℝ)) *
          LSeries (fun n => ((aW4 p A n : ℝ) : ℂ)) s) ∧
      ChannelAxioms (fun w => LiCriterion.riemannXi w * surg ((p : ℝ) ^ 2) A w) ∧
      (∃ s : ℂ, LiCriterion.riemannXi s * surg ((p : ℝ) ^ 2) A s = 0 ∧ 1 / 2 < s.re ∧
        s.re < 1) := by
  refine ⟨2 * p + 1, by omega, ?_, aW4_isMultiplicative hp _, W4_isDirExp hp _,
    fun q hq => bW4_prime_sq hp _ (by positivity) hq, fun n hn => bW4_nonneg_below hp _
    (by positivity) hn, bW4_p4 hp _ (by nlinarith), fun s hs => W4_completion_LSeries hp _ hs,
    ?_, ?_⟩
  · nlinarith
  · have hp1 : (1 : ℝ) < (p : ℝ) ^ 2 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      nlinarith
    apply channelAxioms_W _ _ hp1
    have h : ((2 * (p : ℤ) + 1 : ℤ) : ℝ) < (p : ℝ) ^ 2 + 1 := by
      have : (2 * (p : ℤ) + 1 : ℤ) < (p : ℤ) ^ 2 + 1 := by nlinarith
      exact_mod_cast this
    rw [abs_of_pos (by positivity)]
    exact h
  · have hp1 : (1 : ℝ) < (p : ℝ) ^ 2 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      nlinarith
    have hlt : ((2 * (p : ℤ) + 1 : ℤ) : ℝ) < (p : ℝ) ^ 2 + 1 := by
      have : (2 * (p : ℤ) + 1 : ℤ) < (p : ℤ) ^ 2 + 1 := by nlinarith
      exact_mod_cast this
    have hD : 4 * (p : ℝ) ^ 2 < ((2 * (p : ℤ) + 1 : ℤ) : ℝ) ^ 2 := by
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      push_cast
      nlinarith
    obtain ⟨s, hs, h1, h2, -⟩ := surg_offline_zero _ _ hp1 hD
      (by rw [abs_of_pos (by positivity)]; exact hlt)
    exact ⟨s, by rw [hs, mul_zero], h1, h2⟩

end PrimeSquareSurgery

/-! ## 16. Capstones -/

section Capstones

open CruxDynamicsErgodic ArithmeticFunction Crux.AxisoTheorem
open scoped ContDiff

/-- **THE SEMI-LOCAL BARRIER, FULL FORM (X1-X6).**  For every bound `N0`, every finite set `S` of
primes and every support radius `L0` there are a prime `p ∉ S` with `p^2 > N0` and `log p > L0`,
and an integer `c` with `4p < c^2 < (p + 1)^2`, such that `W_{p,c} = zeta(s)(1 + c p^{-s} + p p^{-2s})`
* (X1) is an Euler product and a Dirichlet exponential `a_W = exp⋆(b_W)` agreeing with zeta at
  every prime other than `p`;
* (X2) has `L(a_W, s) = zeta(s)(1 + c p^{-s} + p p^{-2s})`, whose completion `xi * surg p c` has the
  exact Gamma_R shape with conductor `p^2` and root number `+1`, periodic coefficients mod `p^2`
  and the FE top coefficient `|(a_W ⋆ μ)(p^2)| = sqrt(p^2)`;
* (X3) has P2 on `[0, p^2)` (and fails it at `p^2`);
* (X4) satisfies all seven channel axioms;
* (X5) satisfies the support-prime duality: the zeros of the surgery factor are an explicit simple
  lattice whose Weil sum is `2 log p · g(0)` for every smooth test supported in `(-log p, log p)`,
  in particular for every test supported in `[-L0, L0]`; so every Weil-positivity statement for
  zeta on such tests transfers verbatim to `W_{p,c}`;
* (X6) has finite robust-positivity defect `Σ Λ_W^-(n)/n`;
and yet its completion vanishes at a point with `1/2 < Re s < 1`.  So no argument valid on every
datum with these properties proves RH. -/
theorem semilocal_barrier_full (N0 : ℕ) (S : Finset ℕ) (L0 : ℝ) :
    ∃ p c : ℕ, p.Prime ∧ p ∉ S ∧ N0 < p ^ 2 ∧ L0 < Real.log p ∧ 4 * p < c ^ 2 ∧ c < p + 1 ∧
      IsMultiplicative (aW p c) ∧ IsDirExp (aW p c) (bW p c) ∧
      (∀ n : ℕ, 0 < n → ¬ p ∣ n → aW p c n = 1) ∧
      (∀ s : ℂ, 1 < s.re → LSeries (fun n => ((aW p c n : ℝ) : ℂ)) s
          = riemannZeta s * (1 + (c : ℂ) * (p : ℂ) ^ (-s) + p * ((p : ℂ) ^ (-s)) ^ 2)) ∧
      (∀ s : ℂ, 1 < s.re → LiCriterion.riemannXi s * surg p c s
          = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s * Complex.exp ((s - 1 / 2) * (Real.log p : ℝ)) *
            LSeries (fun n => ((aW p c n : ℝ) : ℂ)) s) ∧
      (∀ s : ℂ, surg p c (1 - s) = surg p c s) ∧
      (∃ A : ZMod (p ^ 2) → ℝ, ∀ n : ℕ, 0 < n → aW p c n = A n) ∧
      |(aW p c * (moebius : ArithmeticFunction ℝ)) (p ^ 2)| = √(((p ^ 2 : ℕ)) : ℝ) ∧
      (∀ n : ℕ, n < p ^ 2 → 0 ≤ bW p c n) ∧ bW p c (p ^ 2) < 0 ∧
      ChannelAxioms (fun w => LiCriterion.riemannXi w * surg p c w) ∧
      (∃ α : ℂ,
        (∀ γ : ℂ, surg p c (1 / 2 + I * γ) = 0 ↔ ∃ k : ℤ,
          γ = (α + 2 * Real.pi * k) / Real.log p ∨ γ = (-α + 2 * Real.pi * k) / Real.log p) ∧
        (∀ k k' : ℤ, (α + 2 * Real.pi * k) / Real.log p ≠ (-α + 2 * Real.pi * k') / Real.log p) ∧
        (∀ s : ℂ, surg p c s = 0 → deriv (surg p c) s ≠ 0) ∧
        (∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
          (∀ x : ℝ, Real.log p ≤ |x| → g x = 0) →
          HasSum (fun k : ℤ => weilHat g ((α + 2 * Real.pi * k) / Real.log p)
            + weilHat g ((-α + 2 * Real.pi * k) / Real.log p)) (2 * Real.log p * g 0))) ∧
      Summable (defect p c) ∧
      (∃ s : ℂ, LiCriterion.riemannXi s * surg p c s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1) := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (N0 + S.sup id + ⌈Real.exp L0⌉₊ + 5)
  set c : ℕ := Nat.sqrt (4 * p) + 1 with hcdef
  have hp5 : 5 ≤ p := by omega
  have hpS : p ∉ S := by
    intro hmem
    have : p ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  have hN0 : N0 < p ^ 2 := by nlinarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL0 : L0 < Real.log p := by
    rw [Real.lt_log_iff_exp_lt hp0]
    have h1 : Real.exp L0 ≤ ⌈Real.exp L0⌉₊ := Nat.le_ceil _
    have h2 : (⌈Real.exp L0⌉₊ : ℝ) < p := by
      have : ⌈Real.exp L0⌉₊ < p := by omega
      exact_mod_cast this
    linarith
  have hD : 4 * p < c ^ 2 := by rw [hcdef]; exact Nat.lt_succ_sqrt' (4 * p)
  have hcp : c < p + 1 := by
    have : Nat.sqrt (4 * p) < p := Nat.sqrt_lt'.mpr (by nlinarith)
    omega
  have hDz' : 2 * (p : ℤ) + 1 < ((c : ℤ)) ^ 2 := by
    have hDz : 4 * (p : ℤ) < ((c : ℤ)) ^ 2 := by exact_mod_cast hD
    have : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  have hcR : |((c : ℕ) : ℝ)| < (p : ℝ) + 1 := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hcp
  have hDR : 4 * (p : ℝ) < ((c : ℕ) : ℝ) ^ 2 := by exact_mod_cast hD
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcZ : |((c : ℕ) : ℤ)| < (p : ℤ) + 1 := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hcp
  have hc4 : ((c : ℕ) : ℝ) ^ 2 ≠ 4 * (p : ℝ) := ne_of_gt hDR
  obtain ⟨α, -, hz, hdisj, hsimple, hsmall, -⟩ :=
    surg_explicit_formula (p : ℝ) ((c : ℕ) : ℝ) hp1 hc4
  refine ⟨p, c, hp, hpS, hN0, hL0, hD, hcp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact aW_isMultiplicative hp (c : ℤ)
  · exact W_isDirExp hp (c : ℤ)
  · intro n hn hpn; exact aW_coprime hp (c : ℤ) hn hpn
  · intro s hs
    have := LSeries_aW hp (c : ℤ) hs
    push_cast at this ⊢
    exact this
  · intro s hs
    have := W_completion_LSeries hp (c : ℤ) hs
    push_cast at this ⊢
    exact this
  · intro s; exact surg_one_sub _ _ s
  · exact aW_periodic hp (c : ℤ)
  · exact aW_top hp (c : ℤ)
  · intro n hn; exact bW_nonneg_below hp (c : ℤ) (by omega) hn
  · exact bW_sq hp (c : ℤ) hDz'
  · exact channelAxioms_W (p : ℝ) ((c : ℕ) : ℝ) hp1 hcR
  · exact ⟨α, hz, hdisj, hsimple, hsmall⟩
  · exact robust_positivity hp (c : ℤ) hcZ
  · obtain ⟨s, hs, h1, h2, -⟩ := surg_offline_zero (p : ℝ) ((c : ℕ) : ℝ) hp1 hDR hcR
    exact ⟨s, by rw [hs, mul_zero], h1, h2⟩

/-- **EXHAUSTION: every global input kills the surgery, and then no intermediate class remains.**
For every prime `p` and every integer `c`:
* P2 at `p^2` alone, P2 at all powers of `p`, or low-height certification of the surgery factor
  (no off-line zero below height `pi / log 2`, a finite certificate zeta passes) each force the
  local Hasse bound `c^2 ≤ 4p`;
* the Selberg-class Euler axiom `b(n) = O(n^θ)`, `θ < 1/2`, fails for `W_{p,c}` whatever `c`
  (on-line surgeries included), while zeta satisfies it with `θ = 0` (`0 ≤ b_ζ ≤ 1`);
* and RH for the completion of `W_{p,c}` is EXACTLY RH for `xi` together with `c^2 ≤ 4p`.
A global input that is not complete is still fooled: P2 at every prime square does not pin zeta
(`prime_square_surgery`). -/
theorem exhaustion {p : ℕ} (hp : p.Prime) (c : ℤ) :
    (0 ≤ bW p c (p ^ 2) → c ^ 2 ≤ 4 * (p : ℤ)) ∧
    ((∀ m : ℕ, 1 ≤ m → 0 ≤ bW p c (p ^ m)) → c ^ 2 ≤ 4 * (p : ℤ)) ∧
    ((∀ s : ℂ, surg p c s = 0 → |s.im| ≤ Real.pi / Real.log 2 → s.re = 1 / 2) →
      (c : ℝ) ^ 2 ≤ 4 * p) ∧
    (∀ θ : ℝ, θ < 1 / 2 → ∀ C : ℝ, ¬ ∀ n : ℕ, 1 ≤ n → |bW p c n| ≤ C * (n : ℝ) ^ θ) ∧
    (∀ n : ℕ, |zetaLogCoeff n| ≤ 1) ∧
    ((∀ s : ℂ, LiCriterion.riemannXi s * surg p c s = 0 → s.re = 1 / 2) ↔
      (∀ s : ℂ, LiCriterion.riemannXi s = 0 → s.re = 1 / 2) ∧ (c : ℝ) ^ 2 ≤ 4 * p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < p := by linarith
  refine ⟨positivity_at_sq_kills hp c, positivity_at_powers_kills hp c, lowcert_kills _ _ hp2,
    fun θ hθ C => surgery_not_selberg hp c hθ C, fun n => ?_, rh_W_iff _ _ hp1⟩
  rw [abs_of_nonneg (zetaLogCoeff_nonneg n)]
  exact zetaLogCoeff_le_one n

/-- **The golden fake, fully unified.**  Build B's golden hybrid `XiH` is the completion of the
Dirichlet series `L(a_{W_{5,5}}, s)` of an Euler product, and that one object carries the pointwise
layer, the channel axioms, the class-P data with P2 on `[0, 25)` and failure at `25`, a finite
robust-positivity defect, and an off-line zero. -/
theorem golden_unified_full :
    PointwiseLayer (fun ρ => XiH ρ = 0) ∧ ChannelAxioms XiH ∧ IsMultiplicative (aW 5 5) ∧
      IsDirExp (aW 5 5) (bW 5 5) ∧ (∀ n : ℕ, n < 5 ^ 2 → 0 ≤ bW 5 5 n) ∧ bW 5 5 (5 ^ 2) < 0 ∧
      Summable (defect 5 5) ∧
      (∀ s : ℂ, 1 < s.re → XiH s = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s *
        Complex.exp ((s - 1 / 2) * (Real.log 5 : ℝ)) * LSeries (fun n => ((aW 5 5 n : ℝ) : ℂ)) s) ∧
      (∃ ρ : ℂ, XiH ρ = 0 ∧ ρ.re ≠ 1 / 2) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8⟩ := golden_unified
  have hp : Nat.Prime 5 := by norm_num
  refine ⟨h1, h2, aW_isMultiplicative hp 5, h3, h4, h5, robust_positivity hp 5 (by norm_num), ?_,
    h8⟩
  intro s hs
  rw [XiH_eq_W55]
  have := W_completion_LSeries hp 5 hs
  push_cast at this
  exact this

end Capstones

end Crux2UnifiedBarrier
/-! ## Axiom audit: every theorem and lemma of this file -/
#print axioms Crux2UnifiedBarrier.surg_eq
#print axioms Crux2UnifiedBarrier.surg_one_sub
#print axioms Crux2UnifiedBarrier.surg_conj
#print axioms Crux2UnifiedBarrier.surg_differentiable
#print axioms Crux2UnifiedBarrier.surg_eq_localPoly
#print axioms Crux2UnifiedBarrier.normSq_Xi_decomp
#print axioms Crux2UnifiedBarrier.Xi_contractive
#print axioms Crux2UnifiedBarrier.Xi_edge
#print axioms Crux2UnifiedBarrier.two_cosh_half_log
#print axioms Crux2UnifiedBarrier.surg_trivial_bound_iff
#print axioms Crux2UnifiedBarrier.surg_trivial_bound_iff_le
#print axioms Crux2UnifiedBarrier.surg_contractive
#print axioms Crux2UnifiedBarrier.surg_edge
#print axioms Crux2UnifiedBarrier.surg_unitary
#print axioms Crux2UnifiedBarrier.channelAxioms_mul_surg
#print axioms Crux2UnifiedBarrier.channelAxioms_W
#print axioms Crux2UnifiedBarrier.two_lt_abs_div_sqrt_iff
#print axioms Crux2UnifiedBarrier.surg_rh_iff
#print axioms Crux2UnifiedBarrier.surg_offline_zero
#print axioms Crux2UnifiedBarrier.rh_W_iff
#print axioms Crux2UnifiedBarrier.lowcert_kills
#print axioms Crux2UnifiedBarrier.XiA_eq_surg
#print axioms Crux2UnifiedBarrier.XiH_eq_W55
#print axioms Crux2UnifiedBarrier.log41_gt
#print axioms Crux2UnifiedBarrier.pi_div_log41_lt
#print axioms Crux2UnifiedBarrier.lowHeightBox_nonrelativizing
#print axioms Crux2UnifiedBarrier.Ploc_apply
#print axioms Crux2UnifiedBarrier.tLoc_one
#print axioms Crux2UnifiedBarrier.tLoc_two
#print axioms Crux2UnifiedBarrier.tLoc_rec
#print axioms Crux2UnifiedBarrier.bLoc_apply
#print axioms Crux2UnifiedBarrier.p_two_le
#print axioms Crux2UnifiedBarrier.Ploc_one
#print axioms Crux2UnifiedBarrier.Ploc_p
#print axioms Crux2UnifiedBarrier.Ploc_sq
#print axioms Crux2UnifiedBarrier.Ploc_eq_zero
#print axioms Crux2UnifiedBarrier.Ploc_pow_eq_zero
#print axioms Crux2UnifiedBarrier.bLoc_pow
#print axioms Crux2UnifiedBarrier.bLoc_one
#print axioms Crux2UnifiedBarrier.bLoc_eq_zero_of
#print axioms Crux2UnifiedBarrier.bLoc_mul_log_pow
#print axioms Crux2UnifiedBarrier.Ploc_isDirExp
#print axioms Crux2UnifiedBarrier.isDirExp_mul
#print axioms Crux2UnifiedBarrier.W_isDirExp
#print axioms Crux2UnifiedBarrier.zetaLogCoeff_pow
#print axioms Crux2UnifiedBarrier.bW_pow
#print axioms Crux2UnifiedBarrier.bW_eq_zeta_off
#print axioms Crux2UnifiedBarrier.bW_nonneg_below
#print axioms Crux2UnifiedBarrier.bW_sq
#print axioms Crux2UnifiedBarrier.tr_pos
#print axioms Crux2UnifiedBarrier.bW_odd_pos
#print axioms Crux2UnifiedBarrier.bW_even_neg
#print axioms Crux2UnifiedBarrier.aW_apply
#print axioms Crux2UnifiedBarrier.aW_coprime
#print axioms Crux2UnifiedBarrier.aW_periodic
#print axioms Crux2UnifiedBarrier.aW_top
#print axioms Crux2UnifiedBarrier.classP_sharp
#print axioms Crux2UnifiedBarrier.W_completion
#print axioms Crux2UnifiedBarrier.positivity_at_powers_kills
#print axioms Crux2UnifiedBarrier.positivity_at_sq_kills
#print axioms Crux2UnifiedBarrier.semilocal_barrier
#print axioms Crux2UnifiedBarrier.golden_unified
#print axioms Crux2UnifiedBarrier.W41_semilocal_violates_box1
#print axioms Crux2UnifiedBarrier.defect_nonneg
#print axioms Crux2UnifiedBarrier.defect_eq_zero_off
#print axioms Crux2UnifiedBarrier.defect_pow
#print axioms Crux2UnifiedBarrier.tLoc_abs_le_sqrt
#print axioms Crux2UnifiedBarrier.tLoc_abs_le_big
#print axioms Crux2UnifiedBarrier.bigRoot_eq
#print axioms Crux2UnifiedBarrier.bigRoot_lt_p
#print axioms Crux2UnifiedBarrier.p_le_bigRoot
#print axioms Crux2UnifiedBarrier.robust_positivity
#print axioms Crux2UnifiedBarrier.robust_positivity_fails
#print axioms Crux2UnifiedBarrier.robust_positivity_iff
#print axioms Crux2UnifiedBarrier.tr_complex_rep
#print axioms Crux2UnifiedBarrier.exists_complex_roots
#print axioms Crux2UnifiedBarrier.tr_double
#print axioms Crux2UnifiedBarrier.tLoc_large
#print axioms Crux2UnifiedBarrier.tLoc_large_frequently
#print axioms Crux2UnifiedBarrier.surgery_not_selberg
#print axioms Crux2UnifiedBarrier.Ploc_isMultiplicative
#print axioms Crux2UnifiedBarrier.aW_isMultiplicative
#print axioms Crux2UnifiedBarrier.zetaLogCoeff_le_one
#print axioms Crux2UnifiedBarrier.twistScale_contDiff
#print axioms Crux2UnifiedBarrier.twistScale_hasCompactSupport
#print axioms Crux2UnifiedBarrier.twistScale_pointwise
#print axioms Crux2UnifiedBarrier.lattice_poisson
#print axioms Crux2UnifiedBarrier.lattice_poisson_small
#print axioms Crux2UnifiedBarrier.lattice_poisson_two
#print axioms Crux2UnifiedBarrier.Xi_zero_iff_lattice
#print axioms Crux2UnifiedBarrier.half_add_I_mul
#print axioms Crux2UnifiedBarrier.lattice_branches_disjoint
#print axioms Crux2UnifiedBarrier.lattice_branch_injective
#print axioms Crux2UnifiedBarrier.Xi_hasDerivAt
#print axioms Crux2UnifiedBarrier.Xi_zero_simple
#print axioms Crux2UnifiedBarrier.surg_explicit_formula
#print axioms Crux2UnifiedBarrier.surg_zero_sum_nonneg
#print axioms Crux2UnifiedBarrier.PlocC_apply
#print axioms Crux2UnifiedBarrier.aW_coe_eq
#print axioms Crux2UnifiedBarrier.PlocC_support
#print axioms Crux2UnifiedBarrier.LSeries_PlocC
#print axioms Crux2UnifiedBarrier.LSeries_aW
#print axioms Crux2UnifiedBarrier.natCast_cpow_neg_eq_exp
#print axioms Crux2UnifiedBarrier.W_completion_LSeries
#print axioms Crux2UnifiedBarrier.surg_edge_iff
#print axioms Crux2UnifiedBarrier.channelAxioms_W_iff
#print axioms Crux2UnifiedBarrier.locE_pow
#print axioms Crux2UnifiedBarrier.locE_eq_zero
#print axioms Crux2UnifiedBarrier.locS_pow
#print axioms Crux2UnifiedBarrier.locS_one
#print axioms Crux2UnifiedBarrier.locS_eq_zero
#print axioms Crux2UnifiedBarrier.locE_isDirExp
#print axioms Crux2UnifiedBarrier.isMultiplicative_of_primePow_support
#print axioms Crux2UnifiedBarrier.locE_isMultiplicative
#print axioms Crux2UnifiedBarrier.e4_eq_zero
#print axioms Crux2UnifiedBarrier.newton4
#print axioms Crux2UnifiedBarrier.W4_isDirExp
#print axioms Crux2UnifiedBarrier.aW4_isMultiplicative
#print axioms Crux2UnifiedBarrier.bW4_pow
#print axioms Crux2UnifiedBarrier.bW4_eq_zeta_off
#print axioms Crux2UnifiedBarrier.bW4_nonneg_below
#print axioms Crux2UnifiedBarrier.bW4_prime_sq
#print axioms Crux2UnifiedBarrier.bW4_p4
#print axioms Crux2UnifiedBarrier.loc4C_apply
#print axioms Crux2UnifiedBarrier.aW4_coe_eq
#print axioms Crux2UnifiedBarrier.loc4C_support
#print axioms Crux2UnifiedBarrier.LSeries_loc4C
#print axioms Crux2UnifiedBarrier.LSeries_aW4
#print axioms Crux2UnifiedBarrier.W4_completion_LSeries
#print axioms Crux2UnifiedBarrier.prime_square_surgery
#print axioms Crux2UnifiedBarrier.semilocal_barrier_full
#print axioms Crux2UnifiedBarrier.exhaustion
#print axioms Crux2UnifiedBarrier.golden_unified_full
