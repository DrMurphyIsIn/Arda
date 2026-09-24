/-  RS_B3.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 2: the exact
    saddle-point reduction.  Mathlib-only (imports `RS_C0`).

    ## Vocabulary (height t > 0)

        a = rsAlpha t = sqrt(t / 2 pi),  N = rsNn t = floor a,  p = rsFrac t = a - N,
        rsThetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8   (verbatim the corpus thetaMain),
        rsPsi p = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)            (Gabcke's C0 = Riemann's Psi),
        rsRem t = -lineUp (N + 1/2) (x |-> rsG x x^(-(1/2 + i t)))    (the exact RS remainder, B2).

    By B2 (`completed_re_eq_rs_cos`), on the critical line
        Re completedRiemannZeta(1/2+it) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} rsRem t) ).

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms)

      * `rsRem_factor` : moving the remainder line to the saddle point a and factoring out the
        stationary phase,
            rsRem t = (-1)^(N+1) e^{i pi a^2} a^(-s) (rsJ p + rsE1 a p),
        where rsJ is the tau = 2 Mordell integral (RS_C0) and rsE1 the error integral of the amplitude
        rsPhi a w - 1,  rsPhi a w = e^{2 pi i a w - pi i w^2} (1 + w/a)^(-s).
      * `rs_phase` : e^{i phi} e^{i pi a^2} a^(-s) = a^(-1/2) e^{i (phi - rsThetaMain t - pi/8)}.
      * `rs_remainder_exact` : the EXACT identity
            2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
              = (-1)^(N+1) a^(-1/2) [ 2 Re(e^{-i pi/8}(e^{i delta} - 1) rsJ p)
                                      + 2 Re(e^{i (delta - pi/8)} rsE1 a p) ],   delta = phi - thetaMain t,
        so the C0-corrected remainder is controlled by |delta| |rsJ p| and |rsE1 a p| alone.

    conjecture1_proved = False.
-/
import RS_C0

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 0. Vocabulary -/

/-- `a = sqrt(t / 2 pi)`, the saddle point of the Riemann-Siegel integral. -/
def rsAlpha (t : ℝ) : ℝ := Real.sqrt (t / (2 * π))

/-- `N = floor(sqrt(t / 2 pi))`, the length of the Riemann-Siegel main sum. -/
def rsNn (t : ℝ) : ℕ := ⌊rsAlpha t⌋₊

/-- `p = sqrt(t / 2 pi) - N ∈ [0, 1)`. -/
def rsFrac (t : ℝ) : ℝ := rsAlpha t - rsNn t

/-- The Stirling main term of the Riemann-Siegel theta (verbatim `ZeroFreeBridge.thetaMain`). -/
def rsThetaMain (t : ℝ) : ℝ :=
  t / 2 * Real.log t - t / 2 * Real.log (2 * Real.pi) - t / 2 - Real.pi / 8

/-- Riemann's Psi (Gabcke's C0): `cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)`. -/
def rsPsi (p : ℝ) : ℝ := Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p)

/-- The exact Riemann-Siegel remainder integral at height `t` (B2, line through `N + 1/2`). -/
def rsRem (t : ℝ) : ℂ :=
  -lineUp ((rsNn t : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I)))

/-- The saddle-point amplitude `e^{2 pi i a w - pi i w^2} (1 + w/a)^(-(1/2 + 2 pi a^2 i))`. -/
def rsPhi (a : ℝ) (w : ℂ) : ℂ :=
  cexp (2 * ↑π * I * a * w - ↑π * I * w ^ 2) * (1 + w / a) ^ (-((1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I))

/-- The error integral of the saddle-point expansion. -/
def rsE1 (a p : ℝ) : ℂ :=
  lineUp 0 (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * (rsPhi a w - 1))

theorem rsAlpha_pos {t : ℝ} (ht : 0 < t) : 0 < rsAlpha t := Real.sqrt_pos.mpr (by positivity)

theorem rsAlpha_sq {t : ℝ} (ht : 0 ≤ t) : rsAlpha t ^ 2 = t / (2 * π) :=
  Real.sq_sqrt (by positivity)

theorem t_eq_rsAlpha {t : ℝ} (ht : 0 ≤ t) : t = 2 * π * rsAlpha t ^ 2 := by
  rw [rsAlpha_sq ht]; field_simp

theorem rsNn_le (t : ℝ) : (rsNn t : ℝ) ≤ rsAlpha t :=
  Nat.floor_le (Real.sqrt_nonneg _)

theorem rsAlpha_lt {t : ℝ} : rsAlpha t < rsNn t + 1 := Nat.lt_floor_add_one _

theorem rsFrac_lt_one {t : ℝ} : rsFrac t < 1 := by
  unfold rsFrac; linarith [rsAlpha_lt (t := t)]

theorem rsAlpha_eq {t : ℝ} : rsAlpha t = rsNn t + rsFrac t := by unfold rsFrac; ring

/-! ## 1. Shifting the denominator by an integer -/

theorem rsD_add_nat (z : ℂ) (n : ℕ) : rsD (z + n) = (-1) ^ n * rsD z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, rsD_add_one, ih, pow_succ]; ring

/-! ## 2. The factorization at the saddle point -/

theorem upLine_ne_zero {a : ℝ} (ha : 0 < a) (v : ℝ) : (a : ℂ) + v * (1 + I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rw [him] at hre; linarith

/-- The pointwise factorization of Riemann's integrand at `x = a + w`. -/
theorem rsG_cpow_factor {a p : ℝ} (ha : 0 < a) {N : ℕ} (hN : a = N + p) (w : ℂ)
    (hw : (a : ℂ) + w ≠ 0) :
    rsG (a + w) * (a + w) ^ (-((1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I)) =
      (-1) ^ N * cexp (↑π * I * a ^ 2) * (a : ℂ) ^ (-((1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I)) *
        (cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * rsPhi a w) := by
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have h1w : 1 + w / a ≠ 0 := by
    intro h; apply hw
    have : (a : ℂ) * (1 + w / a) = a + w := by field_simp
    rw [← this, h, mul_zero]
  have hsplit : ((a : ℂ) + w) = (a : ℂ) * (1 + w / a) := by field_simp
  have hD : rsD (a + w) = (-1) ^ N * rsD (p + w) := by
    rw [show (a : ℂ) + w = (p + w) + (N : ℂ) by rw [hN]; push_cast; ring, rsD_add_nat]
  unfold rsG rsPhi
  rw [hD, hsplit, ofReal_mul_cpow ha h1w, ← hsplit]
  have hexp : cexp (↑π * I * ((a : ℂ) + w) ^ 2) =
      cexp (↑π * I * a ^ 2) * cexp (2 * ↑π * I * w ^ 2) * cexp (2 * ↑π * I * a * w - ↑π * I * w ^ 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [hexp]
  have hm1 : ((-1 : ℂ) ^ N)⁻¹ = (-1) ^ N := by
    rw [← inv_pow, inv_neg, inv_one]
  rcases eq_or_ne (rsD (p + w)) 0 with h0 | h0
  · rw [h0]; simp
  · field_simp
    rw [show ((-1 : ℂ) ^ N) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; simp]
    ring

theorem integrable_upLine_cpow {c : ℝ} (hc : 0 < c) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) (s : ℂ) :
    Integrable (fun v : ℝ => rsG ((c : ℂ) + v * (1 + I)) * ((c : ℂ) + v * (1 + I)) ^ (-s)) := by
  refine integrable_lineUp_rsG_mul (φ := fun x => x ^ (-s)) (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcl
    (fun x hx => continuousAt_cpow_const (slit_of_upStrip hc hx))
    (A := ((c / 2) ^ (-s).re + 1) * Real.exp (π * |(-s).im|)) (B := |(-s).re|)
    (fun x hx => norm_cpow_le_of_ge (by positivity) (norm_ge_of_upStrip hx hc))

theorem integrable_J2_integrand {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun v : ℝ => cexp (2 * ↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I)))) := by
  refine integrable_of_continuous_of_tail ?_ (a := 4 * π) (b := 0) (C := 1) (R := 1)
    (by positivity) (fun v hv => ?_)
  · rw [continuous_iff_continuousAt]
    intro v
    have hD : rsD (p + ((0 : ℝ) + v * (1 + I))) ≠ 0 := rsD_ne_zero_of_ne (pt_ne_int hp hp1 v)
    exact ((by fun_prop : Continuous (fun v : ℝ =>
      cexp (2 * ↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2))).continuousAt).div
      ((differentiable_rsD.continuous.comp (by fun_prop :
        Continuous (fun v : ℝ => (p : ℂ) + ((0 : ℝ) + v * (1 + I))))).continuousAt) hD
  · have h1 : 1 ≤ |((p : ℂ) + ((0 : ℝ) + v * (1 + I))).im| := by simpa using hv
    rw [norm_div, Complex.norm_exp]
    have hD := one_le_norm_rsD h1
    have hre : (2 * (π : ℂ) * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2).re =
        -(4 * π) * v ^ 2 + 0 * |v| := by
      simp [pow_two, mul_re, mul_im]; ring
    rw [hre, one_mul]
    exact div_le_self (Real.exp_pos _).le hD

/-- **The factorization.**  For `t > 0` with `p = rsFrac t > 0`:
    `rsRem t = (-1)^(N+1) e^{i pi a^2} a^(-s) (rsJ p + rsE1 a p)`. -/
theorem rsRem_factor {t : ℝ} (ht : 0 < t) (hp : 0 < rsFrac t) :
    rsRem t = (-1) ^ (rsNn t + 1) * cexp (↑π * I * (rsAlpha t) ^ 2) *
      ((rsAlpha t : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) *
        (rsJ (rsFrac t) + rsE1 (rsAlpha t) (rsFrac t)) := by
  set a := rsAlpha t with hadef
  set N := rsNn t with hNdef
  set p := rsFrac t with hpdef
  have ha : 0 < a := rsAlpha_pos ht
  have hN : a = N + p := rsAlpha_eq
  have hp1 : p < 1 := rsFrac_lt_one
  have hst : ((1 / 2 : ℂ) + t * I) = (1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I := by
    rw [t_eq_rsAlpha ht.le]; push_cast; ring
  set s : ℂ := (1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I with hs
  -- move the line to the saddle point
  have hmove : lineUp ((N : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))) =
      lineUp a (fun x => rsG x * x ^ (-s)) := by
    rw [hst]
    exact lineUp_cpow_same_gap s (n := N) (by linarith) (by linarith) (by linarith)
      (by linarith [rsAlpha_lt (t := t)])
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ a := notInt_of_Ioo (n := N) (by push_cast; linarith)
    (by push_cast; linarith [rsAlpha_lt (t := t)])
  set C : ℂ := (-1) ^ N * cexp (↑π * I * a ^ 2) * (a : ℂ) ^ (-s) with hC
  have hC0 : C ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _)) ?_
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => (ofReal_ne_zero.mpr ha.ne') h.1
  set G : ℂ → ℂ := fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * rsPhi a w with hG
  have hpt : ∀ v : ℝ, rsG ((a : ℂ) + ((0 : ℝ) + v * (1 + I))) *
      ((a : ℂ) + ((0 : ℝ) + v * (1 + I))) ^ (-s) = C * G ((0 : ℝ) + v * (1 + I)) := by
    intro v
    have hw : (a : ℂ) + ((0 : ℝ) + v * (1 + I)) ≠ 0 := by
      have := upLine_ne_zero ha v; simpa using this
    rw [rsG_cpow_factor ha hN _ hw]
  have hshift : lineUp a (fun x => rsG x * x ^ (-s)) = C * lineUp 0 G := by
    rw [← lineUp_shift a, ← lineUp_const_mul]
    exact lineUp_congr fun v => hpt v
  -- integrability of G along the line through 0
  have hFint := integrable_upLine_cpow (c := a) ha hcl s
  have hGint : Integrable (fun v : ℝ => G ((0 : ℝ) + v * (1 + I))) := by
    have := hFint.const_mul C⁻¹
    refine this.congr (Eventually.of_forall fun v => ?_)
    have h := hpt v
    simp only at h ⊢
    rw [show ((a : ℂ) + ((0 : ℝ) + v * (1 + I))) = (a : ℂ) + v * (1 + I) by push_cast; ring] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
  have hJint := integrable_J2_integrand hp hp1
  have hE1 : rsE1 a p = lineUp 0 G - 1 * rsJ p := by
    unfold rsE1 rsJ
    rw [← lineUp_sub_mul 1 hGint hJint]
    refine lineUp_congr fun v => ?_
    simp only [hG]; ring
  unfold rsRem
  rw [hmove, hshift, hE1, hC, hst]
  ring

/-! ## 3. The phase -/

theorem rs_phase {t : ℝ} (ht : 0 < t) (φ : ℝ) :
    cexp (I * φ) * (cexp (↑π * I * (rsAlpha t) ^ 2) * ((rsAlpha t : ℂ) ^ (-((1 / 2 : ℂ) + t * I)))) =
      (((rsAlpha t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (I * (φ - rsThetaMain t - π / 8)) := by
  set a := rsAlpha t with hadef
  have ha : 0 < a := rsAlpha_pos ht
  have ha2 : a ^ 2 = t / (2 * π) := rsAlpha_sq ht.le
  have hlog : Real.log a = (Real.log t - Real.log (2 * π)) / 2 := by
    have h1 : Real.log (a ^ 2) = Real.log t - Real.log (2 * π) := by
      rw [ha2, Real.log_div ht.ne' (by positivity)]
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have hcpow : (a : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
      ((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(I * (t * Real.log a))) := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'), ← Complex.ofReal_log ha.le,
      Complex.ofReal_cpow ha.le, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'),
      ← Complex.ofReal_log ha.le, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hcpow]
  have hphase : cexp (I * φ) * (cexp (↑π * I * a ^ 2) * cexp (-(I * (t * Real.log a)))) =
      cexp (I * (φ - rsThetaMain t - π / 8)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold rsThetaMain
    have hpa : (π : ℝ) * a ^ 2 = t / 2 := by rw [ha2]; field_simp
    have hta : t * Real.log a = t / 2 * Real.log t - t / 2 * Real.log (2 * π) := by rw [hlog]; ring
    have hc1 : (↑π * I * (a : ℂ) ^ 2 : ℂ) = I * ((π * a ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc1, hpa]
    push_cast
    rw [show (t : ℂ) * (Real.log a : ℂ) = ((t * Real.log a : ℝ) : ℂ) by push_cast; ring, hta]
    push_cast; ring
  calc cexp (I * φ) * (cexp (↑π * I * a ^ 2) * (((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (-(I * (t * Real.log a)))))
      = ((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (cexp (I * φ) * (cexp (↑π * I * a ^ 2) * cexp (-(I * (t * Real.log a))))) := by ring
    _ = _ := by rw [hphase]

/-! ## 4. The exact C0-corrected remainder -/

/-- **The exact reduction.**  For `t > 0`, `0 < p = rsFrac t`, `cos(2 pi p) ≠ 0` and any real `phi`,
    with `delta = phi - rsThetaMain t`:
        2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
          = (-1)^(N+1) a^(-1/2) [ 2 Re(e^{-i pi/8} (e^{i delta} - 1) rsJ p)
                                  + 2 Re(e^{i (delta - pi/8)} rsE1 a p) ]. -/
theorem rs_remainder_exact {t : ℝ} (ht : 0 < t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) (φ : ℝ) :
    2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t) =
      (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) *
        (2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) * rsJ (rsFrac t)).re +
          2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 (rsAlpha t) (rsFrac t)).re) := by
  have hC0 := rsJ_C0 hp rsFrac_lt_one hcos
  rw [rsRem_factor ht hp]
  set a := rsAlpha t
  set p := rsFrac t
  set J := rsJ p
  set E := rsE1 a p
  set q : ℝ := (-1 : ℝ) ^ (rsNn t + 1) * a ^ (-(1 / 2 : ℝ)) with hq
  have hmain : cexp (I * φ) * ((-1) ^ (rsNn t + 1) * cexp (↑π * I * a ^ 2) *
      ((a : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) * (J + E)) =
      (q : ℂ) * (cexp (I * (φ - rsThetaMain t - π / 8)) * (J + E)) := by
    have hph := rs_phase ht φ
    rw [hq]
    push_cast
    calc cexp (I * φ) * ((-1) ^ (rsNn t + 1) * cexp (↑π * I * a ^ 2) *
          ((a : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) * (J + E))
        = (-1) ^ (rsNn t + 1) * (cexp (I * φ) * (cexp (↑π * I * a ^ 2) *
            ((a : ℂ) ^ (-((1 / 2 : ℂ) + t * I))))) * (J + E) := by ring
      _ = (-1) ^ (rsNn t + 1) * ((((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
            cexp (I * (φ - rsThetaMain t - π / 8))) * (J + E) := by rw [hph]
      _ = _ := by ring
  rw [hmain, Complex.re_ofReal_mul]
  have hsplitexp : cexp (I * (φ - rsThetaMain t - π / 8)) =
      cexp (-(↑π / 8 * I)) * cexp (I * (φ - rsThetaMain t)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hXJ : cexp (I * (φ - rsThetaMain t - π / 8)) * J = cexp (-(↑π / 8 * I)) * J +
      cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) * J := by
    rw [hsplitexp]; ring
  have hre : (cexp (I * (φ - rsThetaMain t - π / 8)) * (J + E)).re =
      (cexp (-(↑π / 8 * I)) * J).re +
        (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) * J).re +
        (cexp (I * (φ - rsThetaMain t - π / 8)) * E).re := by
    rw [mul_add, Complex.add_re, hXJ, Complex.add_re]
  rw [hre]
  unfold rsPsi
  rw [← hC0]
  ring

end RSInt
