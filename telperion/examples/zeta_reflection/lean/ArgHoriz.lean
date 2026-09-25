/-  ArgHoriz.lean -- brick K6c of the ANDURIL Arb discharge: piecewise half-plane tracking of the
    horizontal argument change (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row
    H2e, brick K6c).

    THE BINDERS IT REDUCES.  Conjuncts 6 and 7 of the `hArbT` binder of every emitted Turing band
    (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) are

        hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2,
        hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3,

    the argument change of ζ along the horizontal edges `[2, -1] + i T` of the RvM rectangle
    (20,758 binders at h280000, 13,235 distinct heights).  Unlike K6a/K6b these are NOT generic:
    they need values of ζ off the line.  This file proves the reduction theorem that turns them
    into a finite, kernel-checkable certificate, so that only ENCLOSURES remain.

    THE CERTIFICATE (`OctCert`).  Breakpoints `2 = p 0, p 1, ..., p m = -1` and one integer label
    `k j` per piece `[p j, p (j+1)]`, the octant direction `k j · π/4`.  It is valid when
      * `StepOK`   : consecutive labels differ by at most 3 (a decidable check on integers);
      * `NoCross`  : on piece `j`, ζ never crosses the line through 0 orthogonal to the octant
                     direction: `0 < α Re ζ(x + i T) + β Im ζ(x + i T)` for all `x` in the piece,
                     `(α, β) ∈ {(1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1)}` the integer
                     octant vector (`octX`).  One strict sign condition per piece: a range
                     enclosure of ζ over the piece that avoids the octant boundary discharges it
                     (`octX_pos_of_box`, bundled per certificate as `OctCert.noCross_of_boxes`).
    Then (`argChangeHoriz_eq_of_octCert`, EXACT, no approximation):

        argChangeHoriz ζ T 2 (-1) = octAngle (k (m-1)) ζ(-1 + i T) - octAngle (k 0) ζ(2 + i T),
        octAngle k w = k π/4 + arctan ((α Im w - β Re w)/(α Re w + β Im w)).

    Every interior breakpoint cancels exactly: the chart angles of the two pieces meeting there
    agree (`chartAngle_eq`), because both charts contain the point and their directions differ by
    less than π.  So the only numerics left are TWO POINT ENCLOSURES, of ζ(2 + i T) and ζ(-1 + i T),
    turned into an arctan interval by `octAngle_mem_of_box` and the rational arctan brackets
    `atanLo ≤ arctan ≤ atanHi` (the emitter may use the sharper `ArctanTaylor.arctan_bracket`).
    `hAH_of_octCert_boxes` is the end-to-end binder-form statement.

    THE GENERAL THEOREM behind it (`argChangeHoriz_chain`): for any `f` analytic along the segment
    and any real chart directions `θ j` with `|θ (j+1) - θ j| < π` and `0 < Re (e^{-i θ j} f)` on
    piece `j`, the horizontal argument change is `chartAngle (θ (m-1)) f(end) - chartAngle (θ 0)
    f(start)`, `chartAngle θ w = θ + arg (e^{-i θ} w)` (FTC for `log (e^{-i θ} f)` on each piece).

    WHAT IS NOT HERE.  The off-line ζ evaluator (memo brick B6) that produces the `NoCross` range
    enclosures and the two endpoint point enclosures, and the functional-equation fold K6d.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  A reduction of one edge of a finite zero count to finitely many
    enclosures; nothing here bears on the Riemann Hypothesis. -/
import Mathlib
import DiffractionCore
import ThetaValue
import ArctanTaylor

open Complex

namespace ArgHoriz

/-! ## 1. Charts: rotated principal arguments -/

/-- The value `w` seen in the chart of direction `θ`: `e^{-iθ} w`. -/
noncomputable def rot (θ : ℝ) (w : ℂ) : ℂ := Complex.exp (((-θ : ℝ) : ℂ) * I) * w

/-- The chart angle of `w` in direction `θ`: `θ + arg (e^{-iθ} w)`, an argument of `w`. -/
noncomputable def chartAngle (θ : ℝ) (w : ℂ) : ℝ := θ + Complex.arg (rot θ w)

theorem rot_re (θ : ℝ) (w : ℂ) : (rot θ w).re = Real.cos θ * w.re + Real.sin θ * w.im := by
  unfold rot
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  ring

theorem rot_im (θ : ℝ) (w : ℂ) : (rot θ w).im = Real.cos θ * w.im - Real.sin θ * w.re := by
  unfold rot
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  ring

theorem norm_rot (θ : ℝ) (w : ℂ) : ‖rot θ w‖ = ‖w‖ := by
  unfold rot
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `w = ‖w‖ · exp (i · chartAngle θ w)`: the chart angle is an argument of `w`. -/
theorem norm_mul_exp_chartAngle (θ : ℝ) (w : ℂ) :
    (‖w‖ : ℂ) * Complex.exp ((chartAngle θ w : ℂ) * I) = w := by
  have h := Complex.norm_mul_exp_arg_mul_I (rot θ w)
  rw [norm_rot] at h
  unfold chartAngle
  push_cast
  rw [add_mul, Complex.exp_add, ← mul_assoc, mul_comm (‖w‖ : ℂ), mul_assoc, h]
  unfold rot
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

/-- **Chart agreement.**  If `w` lies in the open half-planes of two chart directions `θ`, `θ'`
    with `|θ - θ'| < π`, its two chart angles coincide. -/
theorem chartAngle_eq {θ θ' : ℝ} {w : ℂ} (hw : 0 < (rot θ w).re) (hw' : 0 < (rot θ' w).re)
    (hθ : |θ - θ'| < Real.pi) : chartAngle θ w = chartAngle θ' w := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp [rot] at hw
  have hn0 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hw0)
  have h1 := norm_mul_exp_chartAngle θ w
  have h2 := norm_mul_exp_chartAngle θ' w
  have hexp : Complex.exp ((chartAngle θ w : ℂ) * I) = Complex.exp ((chartAngle θ' w : ℂ) * I) := by
    have := h1.trans h2.symm
    exact mul_left_cancel₀ hn0 this
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hn' : ((chartAngle θ w : ℝ) : ℂ) * I
      = ((chartAngle θ' w + n * (2 * Real.pi) : ℝ) : ℂ) * I := by
    rw [hn]; push_cast; ring
  have hA : chartAngle θ w = chartAngle θ' w + n * (2 * Real.pi) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hn'
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have ha' := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw')
  have hdiff : |chartAngle θ w - chartAngle θ' w| < 2 * Real.pi := by
    unfold chartAngle
    have e : θ + Complex.arg (rot θ w) - (θ' + Complex.arg (rot θ' w))
        = (θ - θ') + (Complex.arg (rot θ w) - Complex.arg (rot θ' w)) := by ring
    rw [e]
    refine lt_of_le_of_lt (abs_add_le _ _) ?_
    have := abs_sub (Complex.arg (rot θ w)) (Complex.arg (rot θ' w))
    linarith
  rw [hA, show chartAngle θ' w + n * (2 * Real.pi) - chartAngle θ' w = n * (2 * Real.pi) by ring,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hdiff
  have hn1 : |(n : ℝ)| < 1 := by
    have hpi := Real.pi_pos
    nlinarith
  have hn0' : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hn1
    exact Int.abs_lt_one_iff.mp this
  rw [hA, hn0']
  simp

/-! ## 2. One piece: FTC for `log (e^{-iθ} f)` -/

/-- **One piece.**  If `f` is analytic along `[a, b] + i T` and stays in the open half-plane of
    direction `θ` there, the horizontal argument change over the piece is the difference of chart
    angles, and the integrand is interval integrable. -/
theorem piece_eq (f : ℂ → ℂ) (T a b θ : ℝ)
    (han : ∀ x ∈ Set.uIcc a b, AnalyticAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hin : ∀ x ∈ Set.uIcc a b, 0 < (rot θ (f ((x : ℂ) + (T : ℂ) * I))).re) :
    IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) MeasureTheory.volume a b ∧
      (∫ x in a..b, logDeriv f ((x : ℂ) + (T : ℂ) * I)).im
        = chartAngle θ (f ((b : ℂ) + (T : ℂ) * I)) - chartAngle θ (f ((a : ℂ) + (T : ℂ) * I)) := by
  set γ : ℝ → ℂ := fun x => (x : ℂ) + (T : ℂ) * I with hγdef
  set c : ℂ := Complex.exp (((-θ : ℝ) : ℂ) * I) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hγ : ∀ x : ℝ, HasDerivAt γ 1 x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    simpa [hγdef] using h1.add_const ((T : ℂ) * I)
  have hfne : ∀ x ∈ Set.uIcc a b, f (γ x) ≠ 0 := by
    intro x hx h
    have := hin x hx
    rw [show ((x : ℂ) + (T : ℂ) * I) = γ x from rfl, h] at this
    simp [rot] at this
  -- derivative of G x = log (c * f (γ x))
  have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => Complex.log (c * f (γ x)))
      (logDeriv f (γ x)) x := by
    intro x hx
    have hf : HasDerivAt (fun x => f (γ x)) (deriv f (γ x) * 1) x :=
      ((han x hx).differentiableAt.hasDerivAt).comp x (hγ x)
    have hcf : HasDerivAt (fun x => c * f (γ x)) (c * (deriv f (γ x) * 1)) x := hf.const_mul c
    have hslit : c * f (γ x) ∈ slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hin x hx))
    refine (hcf.clog_real hslit).congr_deriv ?_
    rw [logDeriv_apply]
    field_simp [hfne x hx]
  -- continuity of the integrand on the piece
  have hcont : ContinuousOn (fun x : ℝ => logDeriv f (γ x)) (Set.uIcc a b) := by
    intro x hx
    have hana := han x hx
    have heq : logDeriv f = fun w => deriv f w / f w := by funext w; rw [logDeriv_apply]
    have hcAt : ContinuousAt (logDeriv f) (γ x) := by
      rw [heq]
      exact (hana.deriv.continuousAt).div hana.continuousAt (hfne x hx)
    exact (ContinuousAt.comp (g := logDeriv f) (f := γ) hcAt
      (hγ x).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => logDeriv f (γ x)) MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint
  have him := congrArg Complex.im hFTC
  rw [Complex.sub_im, Complex.log_im, Complex.log_im] at him
  show (∫ y in a..b, logDeriv f (γ y)).im = θ + (c * f (γ b)).arg - (θ + (c * f (γ a)).arg)
  rw [him]
  ring

/-! ## 3. The chain of pieces -/

/-- **The general half-plane tracking theorem.**  Breakpoints `p 0, ..., p m` (`m ≥ 1`), chart
    directions `θ 0, ..., θ (m-1)` with `|θ (j+1) - θ j| < π`; `f` analytic along each piece and
    in the open half-plane of `θ j` on piece `j`.  Then the integrand is integrable over the whole
    path and

        Im ∫_{p 0}^{p m} logDeriv f (x + i T) dx
          = chartAngle (θ (m-1)) f(p m + i T) - chartAngle (θ 0) f(p 0 + i T). -/
theorem argChangeHoriz_chain (f : ℂ → ℂ) (T : ℝ) (p θ : ℕ → ℝ) :
    ∀ m : ℕ, 1 ≤ m →
      (∀ j < m, ∀ x ∈ Set.uIcc (p j) (p (j + 1)), AnalyticAt ℂ f ((x : ℂ) + (T : ℂ) * I)) →
      (∀ j < m, ∀ x ∈ Set.uIcc (p j) (p (j + 1)), 0 < (rot (θ j) (f ((x : ℂ) + (T : ℂ) * I))).re) →
      (∀ j, j + 1 < m → |θ (j + 1) - θ j| < Real.pi) →
      IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) MeasureTheory.volume
          (p 0) (p m) ∧
        (∫ x in p 0..p m, logDeriv f ((x : ℂ) + (T : ℂ) * I)).im
          = chartAngle (θ (m - 1)) (f ((p m : ℂ) + (T : ℂ) * I))
            - chartAngle (θ 0) (f ((p 0 : ℂ) + (T : ℂ) * I)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro han hin _
    exact piece_eq f T (p 0) (p 1) (θ 0) (han 0 (by norm_num)) (hin 0 (by norm_num))
  | succ m hm ih =>
    intro han hin hstep
    obtain ⟨hint, heq⟩ := ih (fun j hj => han j (by omega)) (fun j hj => hin j (by omega))
      (fun j hj => hstep j (by omega))
    obtain ⟨hint', heq'⟩ := piece_eq f T (p m) (p (m + 1)) (θ m) (han m (by omega))
      (hin m (by omega))
    refine ⟨hint.trans hint', ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hint hint', Complex.add_im, heq, heq']
    -- the breakpoint `p m` is in both charts
    have hjoin : chartAngle (θ (m - 1)) (f ((p m : ℂ) + (T : ℂ) * I))
        = chartAngle (θ m) (f ((p m : ℂ) + (T : ℂ) * I)) := by
      have hm1 : m - 1 + 1 = m := by omega
      apply chartAngle_eq
      · have := hin (m - 1) (by omega) (p m) (by rw [hm1]; exact Set.right_mem_uIcc)
        exact this
      · exact hin m (by omega) (p m) Set.left_mem_uIcc
      · have := hstep (m - 1) (by omega)
        rw [hm1] at this
        rw [abs_sub_comm]
        exact this
    rw [hjoin, show m + 1 - 1 = m by omega]
    ring

/-! ## 4. Octant charts: integer directions -/

/-- The octant index `k mod 8 ∈ {0, ..., 7}`. -/
def octIdx (k : ℤ) : ℕ := (k % 8).toNat

/-- First coordinate of the integer octant vector, by residue `r = k mod 8`. -/
def octAN : ℕ → ℤ
  | 0 => 1 | 1 => 1 | 2 => 0 | 3 => -1 | 4 => -1 | 5 => -1 | 6 => 0 | _ => 1

/-- Second coordinate of the integer octant vector, by residue `r = k mod 8`. -/
def octBN : ℕ → ℤ
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 0 | 5 => -1 | 6 => -1 | _ => -1

/-- First coordinate of the integer octant vector of direction `k π/4`. -/
def octA (k : ℤ) : ℤ := octAN (octIdx k)

/-- Second coordinate of the integer octant vector of direction `k π/4`. -/
def octB (k : ℤ) : ℤ := octBN (octIdx k)

theorem octIdx_lt (k : ℤ) : octIdx k < 8 := by
  unfold octIdx
  have h0 : 0 ≤ k % 8 := Int.emod_nonneg k (by norm_num)
  have h8 : k % 8 < 8 := Int.emod_lt_of_pos k (by norm_num)
  omega

theorem octIdx_cast (k : ℤ) : ((octIdx k : ℕ) : ℤ) = k % 8 := by
  unfold octIdx
  exact Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))

/-- `cos` and `sin` of `r π/4` for the eight residues `r`. -/
theorem octant_trig_residue (r : ℕ) (hr : r < 8) :
    ∃ c : ℝ, 0 < c ∧ Real.cos (r * Real.pi / 4) = c * octAN r ∧
      Real.sin (r * Real.pi / 4) = c * octBN r := by
  have hs2 : (0 : ℝ) < √2 / 2 := by positivity
  interval_cases r
  · exact ⟨1, one_pos, by simp [octAN], by simp [octBN]⟩
  · refine ⟨√2 / 2, hs2, ?_, ?_⟩
    · rw [show ((1 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 4 by push_cast; ring, Real.cos_pi_div_four]
      simp [octAN]
    · rw [show ((1 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 4 by push_cast; ring, Real.sin_pi_div_four]
      simp [octBN]
  · refine ⟨1, one_pos, ?_, ?_⟩
    · rw [show ((2 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 2 by push_cast; ring]; simp [octAN]
    · rw [show ((2 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 2 by push_cast; ring]; simp [octBN]
  · refine ⟨√2 / 2, hs2, ?_, ?_⟩
    · rw [show ((3 : ℕ) : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 by push_cast; ring,
        Real.cos_pi_sub, Real.cos_pi_div_four]; simp [octAN]
    · rw [show ((3 : ℕ) : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 by push_cast; ring,
        Real.sin_pi_sub, Real.sin_pi_div_four]; simp [octBN]
  · refine ⟨1, one_pos, ?_, ?_⟩
    · rw [show ((4 : ℕ) : ℝ) * Real.pi / 4 = Real.pi by push_cast; ring]; simp [octAN]
    · rw [show ((4 : ℕ) : ℝ) * Real.pi / 4 = Real.pi by push_cast; ring]; simp [octBN]
  · refine ⟨√2 / 2, hs2, ?_, ?_⟩
    · rw [show ((5 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 4 + Real.pi by push_cast; ring,
        Real.cos_add_pi, Real.cos_pi_div_four]; simp [octAN]
    · rw [show ((5 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 4 + Real.pi by push_cast; ring,
        Real.sin_add_pi, Real.sin_pi_div_four]; simp [octBN]
  · refine ⟨1, one_pos, ?_, ?_⟩
    · rw [show ((6 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi by push_cast; ring,
        Real.cos_add_pi]; simp [octAN]
    · rw [show ((6 : ℕ) : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi by push_cast; ring,
        Real.sin_add_pi]; simp [octBN]
  · refine ⟨√2 / 2, hs2, ?_, ?_⟩
    · rw [show ((7 : ℕ) : ℝ) * Real.pi / 4 = (Real.pi - Real.pi / 4) + Real.pi by push_cast; ring,
        Real.cos_add_pi, Real.cos_pi_sub, Real.cos_pi_div_four]; simp [octAN]
    · rw [show ((7 : ℕ) : ℝ) * Real.pi / 4 = (Real.pi - Real.pi / 4) + Real.pi by push_cast; ring,
        Real.sin_add_pi, Real.sin_pi_sub, Real.sin_pi_div_four]; simp [octBN]

/-- **Octant trigonometry.**  `cos (k π/4) = c · octA k` and `sin (k π/4) = c · octB k` with
    `c > 0` (`c = 1` on the axes, `√2/2` on the diagonals). -/
theorem octant_trig (k : ℤ) :
    ∃ c : ℝ, 0 < c ∧ Real.cos (k * Real.pi / 4) = c * octA k ∧
      Real.sin (k * Real.pi / 4) = c * octB k := by
  have hk : (k : ℝ) * Real.pi / 4 = (octIdx k : ℝ) * Real.pi / 4 + ((k / 8 : ℤ) : ℝ) * (2 * Real.pi) := by
    have h : k = k % 8 + 8 * (k / 8) := by omega
    have hc : ((octIdx k : ℕ) : ℝ) = ((k % 8 : ℤ) : ℝ) := by
      rw [← octIdx_cast]; push_cast; ring
    rw [hc]
    have h' : (k : ℝ) = ((k % 8 : ℤ) : ℝ) + 8 * ((k / 8 : ℤ) : ℝ) := by exact_mod_cast h
    rw [h']
    ring
  obtain ⟨c, hc, hcos, hsin⟩ := octant_trig_residue (octIdx k) (octIdx_lt k)
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hk, Real.cos_add_int_mul_two_pi, hcos]; rfl
  · rw [hk, Real.sin_add_int_mul_two_pi, hsin]; rfl

/-- The chart-`k` real part in integer form: `α Re w + β Im w` (a positive multiple of
    `Re (e^{-i k π/4} w)`). -/
noncomputable def octX (k : ℤ) (w : ℂ) : ℝ := (octA k : ℝ) * w.re + (octB k : ℝ) * w.im

/-- The chart-`k` imaginary part in integer form: `α Im w - β Re w`. -/
noncomputable def octY (k : ℤ) (w : ℂ) : ℝ := (octA k : ℝ) * w.im - (octB k : ℝ) * w.re

/-- The octant angle `k π/4 + arctan (octY/octX)`: the chart angle of `w` in octant `k`. -/
noncomputable def octAngle (k : ℤ) (w : ℂ) : ℝ :=
  k * Real.pi / 4 + Real.arctan (octY k w / octX k w)

theorem rot_oct (k : ℤ) (w : ℂ) : ∃ c : ℝ, 0 < c ∧
    (rot (k * Real.pi / 4) w).re = c * octX k w ∧ (rot (k * Real.pi / 4) w).im = c * octY k w := by
  obtain ⟨c, hc, hcos, hsin⟩ := octant_trig k
  refine ⟨c, hc, ?_, ?_⟩
  · rw [rot_re, hcos, hsin]; unfold octX; ring
  · rw [rot_im, hcos, hsin]; unfold octY; ring

theorem rot_oct_re_pos {k : ℤ} {w : ℂ} (h : 0 < octX k w) : 0 < (rot (k * Real.pi / 4) w).re := by
  obtain ⟨c, hc, hre, _⟩ := rot_oct k w
  rw [hre]; exact mul_pos hc h

/-- In octant `k`, the chart angle is the octant angle. -/
theorem chartAngle_oct {k : ℤ} {w : ℂ} (h : 0 < octX k w) :
    chartAngle (k * Real.pi / 4) w = octAngle k w := by
  obtain ⟨c, hc, hre, him⟩ := rot_oct k w
  have hpos : 0 < (rot (k * Real.pi / 4) w).re := by rw [hre]; exact mul_pos hc h
  unfold chartAngle octAngle
  rw [ThetaValue.arg_eq_arctan_of_re_pos hpos, hre, him, mul_div_mul_left _ _ hc.ne']

/-! ## 5. The octant certificate -/

/-- **An octant certificate** for a horizontal segment: `m` pieces with breakpoints `p 0 .. p m`
    and one octant label `k j` per piece. -/
structure OctCert where
  m : ℕ
  p : ℕ → ℝ
  k : ℕ → ℤ

namespace OctCert

/-- Consecutive octant labels differ by at most 3 (so the directions differ by less than π). -/
def StepOK (c : OctCert) : Prop := ∀ j, j + 1 < c.m → |c.k (j + 1) - c.k j| ≤ 3

/-- **No zero crossing**: on piece `j`, `f(x + i T)` stays strictly on the positive side of the
    octant line: `0 < α Re f + β Im f`. -/
def NoCross (c : OctCert) (f : ℂ → ℂ) (T : ℝ) : Prop :=
  ∀ j < c.m, ∀ x ∈ Set.uIcc (c.p j) (c.p (j + 1)), 0 < octX (c.k j) (f ((x : ℂ) + (T : ℂ) * I))

end OctCert

theorem theta_step_lt {k k' : ℤ} (h : |k' - k| ≤ 3) :
    |(k' : ℝ) * Real.pi / 4 - k * Real.pi / 4| < Real.pi := by
  have hR : |((k' - k : ℤ) : ℝ)| ≤ 3 := by exact_mod_cast h
  have e : (k' : ℝ) * Real.pi / 4 - k * Real.pi / 4 = ((k' - k : ℤ) : ℝ) * (Real.pi / 4) := by
    push_cast; ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 4)]
  have hpi := Real.pi_pos
  nlinarith

/-- **The octant reduction (exact).**  For a valid octant certificate on `[p 0, p m] + i T` with
    `f` analytic along the pieces:
        `argChangeHoriz f T (p 0) (p m) = octAngle (k (m-1)) f(p m + i T) - octAngle (k 0) f(p 0 + i T)`. -/
theorem argChangeHoriz_eq_of_octCert (f : ℂ → ℂ) (T : ℝ) (c : OctCert) (hm : 1 ≤ c.m)
    (han : ∀ j < c.m, ∀ x ∈ Set.uIcc (c.p j) (c.p (j + 1)), AnalyticAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hstep : c.StepOK) (hnc : c.NoCross f T) :
    DiffractionCore.argChangeHoriz f T (c.p 0) (c.p c.m)
      = octAngle (c.k (c.m - 1)) (f ((c.p c.m : ℂ) + (T : ℂ) * I))
        - octAngle (c.k 0) (f ((c.p 0 : ℂ) + (T : ℂ) * I)) := by
  have hchain := argChangeHoriz_chain f T c.p (fun j => (c.k j : ℝ) * Real.pi / 4) c.m hm han
    (fun j hj x hx => rot_oct_re_pos (hnc j hj x hx))
    (fun j hj => theta_step_lt (hstep j hj))
  unfold DiffractionCore.argChangeHoriz
  rw [hchain.2]
  have hlast : 0 < octX (c.k (c.m - 1)) (f ((c.p c.m : ℂ) + (T : ℂ) * I)) := by
    have := hnc (c.m - 1) (by omega) (c.p c.m)
      (by rw [show c.m - 1 + 1 = c.m by omega]; exact Set.right_mem_uIcc)
    exact this
  have hfirst : 0 < octX (c.k 0) (f ((c.p 0 : ℂ) + (T : ℂ) * I)) :=
    hnc 0 (by omega) (c.p 0) Set.left_mem_uIcc
  rw [chartAngle_oct hlast, chartAngle_oct hfirst]

/-! ## 6. Endpoint enclosures -/

/-- An affine form nonnegative at the four corners of a box is nonnegative on the box. -/
theorem affine_nonneg_of_corners {u v a0 a1 b0 b1 a b : ℝ} (ha : a0 ≤ a ∧ a ≤ a1)
    (hb : b0 ≤ b ∧ b ≤ b1) (h00 : 0 ≤ u * a0 + v * b0) (h01 : 0 ≤ u * a0 + v * b1)
    (h10 : 0 ≤ u * a1 + v * b0) (h11 : 0 ≤ u * a1 + v * b1) : 0 ≤ u * a + v * b := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonpos_left hb.2 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonpos_left hb.2 hv]

/-- An affine form positive at the four corners of a box is positive on the box. -/
theorem affine_pos_of_corners {u v a0 a1 b0 b1 a b : ℝ} (ha : a0 ≤ a ∧ a ≤ a1)
    (hb : b0 ≤ b ∧ b ≤ b1) (h00 : 0 < u * a0 + v * b0) (h01 : 0 < u * a0 + v * b1)
    (h10 : 0 < u * a1 + v * b0) (h11 : 0 < u * a1 + v * b1) : 0 < u * a + v * b := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonpos_left hb.2 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonpos_left hb.2 hv]

/-- A complex box `[a0, a1] x [b0, b1]`. -/
def InBox (w : ℂ) (a0 a1 b0 b1 : ℝ) : Prop := a0 ≤ w.re ∧ w.re ≤ a1 ∧ b0 ≤ w.im ∧ w.im ≤ b1

/-- **Range enclosure ⇒ no crossing.**  If `f(x + i T)` lies in a box whose four corners are on
    the positive side of octant `k` for every `x` of a piece, the piece does not cross. -/
theorem octX_pos_of_box {k : ℤ} {w : ℂ} {a0 a1 b0 b1 : ℝ} (hw : InBox w a0 a1 b0 b1)
    (h00 : 0 < (octA k : ℝ) * a0 + octB k * b0) (h01 : 0 < (octA k : ℝ) * a0 + octB k * b1)
    (h10 : 0 < (octA k : ℝ) * a1 + octB k * b0) (h11 : 0 < (octA k : ℝ) * a1 + octB k * b1) :
    0 < octX k w :=
  affine_pos_of_corners ⟨hw.1, hw.2.1⟩ ⟨hw.2.2.1, hw.2.2.2⟩ h00 h01 h10 h11

/-- **Point enclosure ⇒ octant-angle interval.**  If `w` is in the box, the box is on the
    positive side of octant `k` (`X > 0` at the corners), and at the corners
    `qlo · X ≤ Y ≤ qhi · X` (`X = α a + β b`, `Y = α b - β a`), then
    `k π/4 + arctan qlo ≤ octAngle k w ≤ k π/4 + arctan qhi`. -/
theorem octAngle_mem_of_box {k : ℤ} {w : ℂ} {a0 a1 b0 b1 qlo qhi : ℝ}
    (hw : InBox w a0 a1 b0 b1)
    (hX00 : 0 < (octA k : ℝ) * a0 + octB k * b0) (hX01 : 0 < (octA k : ℝ) * a0 + octB k * b1)
    (hX10 : 0 < (octA k : ℝ) * a1 + octB k * b0) (hX11 : 0 < (octA k : ℝ) * a1 + octB k * b1)
    (hL00 : qlo * ((octA k : ℝ) * a0 + octB k * b0) ≤ (octA k : ℝ) * b0 - octB k * a0)
    (hL01 : qlo * ((octA k : ℝ) * a0 + octB k * b1) ≤ (octA k : ℝ) * b1 - octB k * a0)
    (hL10 : qlo * ((octA k : ℝ) * a1 + octB k * b0) ≤ (octA k : ℝ) * b0 - octB k * a1)
    (hL11 : qlo * ((octA k : ℝ) * a1 + octB k * b1) ≤ (octA k : ℝ) * b1 - octB k * a1)
    (hH00 : (octA k : ℝ) * b0 - octB k * a0 ≤ qhi * ((octA k : ℝ) * a0 + octB k * b0))
    (hH01 : (octA k : ℝ) * b1 - octB k * a0 ≤ qhi * ((octA k : ℝ) * a0 + octB k * b1))
    (hH10 : (octA k : ℝ) * b0 - octB k * a1 ≤ qhi * ((octA k : ℝ) * a1 + octB k * b0))
    (hH11 : (octA k : ℝ) * b1 - octB k * a1 ≤ qhi * ((octA k : ℝ) * a1 + octB k * b1)) :
    0 < octX k w ∧ k * Real.pi / 4 + Real.arctan qlo ≤ octAngle k w ∧
      octAngle k w ≤ k * Real.pi / 4 + Real.arctan qhi := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ := hw
  set α : ℝ := (octA k : ℝ)
  set β : ℝ := (octB k : ℝ)
  have hX : 0 < octX k w :=
    affine_pos_of_corners (u := α) (v := β) ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hX00 hX01 hX10 hX11
  -- `Y - qlo X = (-β - qlo α) a + (α - qlo β) b`, affine in `(a, b)`
  have hlo : qlo * octX k w ≤ octY k w := by
    have h := affine_nonneg_of_corners (u := -β - qlo * α) (v := α - qlo * β)
      (a := w.re) (b := w.im) ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
      (by nlinarith [hL00]) (by nlinarith [hL01]) (by nlinarith [hL10]) (by nlinarith [hL11])
    unfold octX octY
    nlinarith [h]
  have hhi : octY k w ≤ qhi * octX k w := by
    have h := affine_nonneg_of_corners (u := qhi * α + β) (v := qhi * β - α)
      (a := w.re) (b := w.im) ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
      (by nlinarith [hH00]) (by nlinarith [hH01]) (by nlinarith [hH10]) (by nlinarith [hH11])
    unfold octX octY
    nlinarith [h]
  refine ⟨hX, ?_, ?_⟩
  · unfold octAngle
    have : qlo ≤ octY k w / octX k w := by rw [le_div_iff₀ hX]; linarith
    have := Real.arctan_le_arctan_iff.mpr this
    linarith
  · unfold octAngle
    have : octY k w / octX k w ≤ qhi := by rw [div_le_iff₀ hX]; linarith
    have := Real.arctan_le_arctan_iff.mpr this
    linarith

/-- Rational lower bound for `arctan q`: `q - q³/3` for `q ≥ 0`, `q` for `q < 0`. -/
noncomputable def atanLo (q : ℝ) : ℝ := if 0 ≤ q then q - q ^ 3 / 3 else q

/-- Rational upper bound for `arctan q`: `q` for `q ≥ 0`, `q - q³/3` for `q < 0`. -/
noncomputable def atanHi (q : ℝ) : ℝ := if 0 ≤ q then q else q - q ^ 3 / 3

theorem atanLo_le (q : ℝ) : atanLo q ≤ Real.arctan q := by
  unfold atanLo
  split_ifs with h
  · exact ArctanTaylor.self_sub_cube_le_arctan h
  · have h' : 0 ≤ -q := by linarith
    have := ArctanTaylor.arctan_le_self h'
    rw [Real.arctan_neg] at this
    linarith

theorem le_atanHi (q : ℝ) : Real.arctan q ≤ atanHi q := by
  unfold atanHi
  split_ifs with h
  · exact ArctanTaylor.arctan_le_self h
  · have h' : 0 ≤ -q := by linarith
    have := ArctanTaylor.self_sub_cube_le_arctan h'
    rw [Real.arctan_neg] at this
    nlinarith

/-- **Range enclosures ⇒ no crossing (the evaluator interface of `NoCross`).**  If on every piece
    `j` the values `f(x + i T)` lie in a box `[a0 j, a1 j] x [b0 j, b1 j]` whose four corners are
    strictly on the positive side of octant `k j`, the certificate does not cross.  So a K6c
    certificate needs only ENCLOSURES: one range box per piece and two endpoint point boxes. -/
theorem OctCert.noCross_of_boxes (c : OctCert) (f : ℂ → ℂ) (T : ℝ) (a0 a1 b0 b1 : ℕ → ℝ)
    (hbox : ∀ j < c.m, ∀ x ∈ Set.uIcc (c.p j) (c.p (j + 1)),
      InBox (f ((x : ℂ) + (T : ℂ) * I)) (a0 j) (a1 j) (b0 j) (b1 j))
    (hcorner : ∀ j < c.m,
      0 < (octA (c.k j) : ℝ) * a0 j + octB (c.k j) * b0 j ∧
      0 < (octA (c.k j) : ℝ) * a0 j + octB (c.k j) * b1 j ∧
      0 < (octA (c.k j) : ℝ) * a1 j + octB (c.k j) * b0 j ∧
      0 < (octA (c.k j) : ℝ) * a1 j + octB (c.k j) * b1 j) :
    c.NoCross f T := by
  intro j hj x hx
  obtain ⟨h00, h01, h10, h11⟩ := hcorner j hj
  exact octX_pos_of_box (hbox j hj x hx) h00 h01 h10 h11

/-! ## 7. The ζ edge in binder form -/

/-- ζ is analytic along every horizontal line off the real axis. -/
theorem zeta_analyticAt_horiz {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    AnalyticAt ℂ riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
  apply analyticOn_riemannZeta
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hT this

/-- **K6c, exact form for the RvM edge `[2, -1] + i T`.**  For `T ≠ 0` and a valid octant
    certificate from `2` to `-1`:
        `argChangeHoriz ζ T 2 (-1) = octAngle (k (m-1)) ζ(-1 + i T) - octAngle (k 0) ζ(2 + i T)`. -/
theorem argChangeHoriz_zeta_eq_of_octCert {T : ℝ} (hT : T ≠ 0) (c : OctCert) (hm : 1 ≤ c.m)
    (hp0 : c.p 0 = 2) (hpm : c.p c.m = -1) (hstep : c.StepOK) (hnc : c.NoCross riemannZeta T) :
    DiffractionCore.argChangeHoriz riemannZeta T 2 (-1)
      = octAngle (c.k (c.m - 1)) (riemannZeta (((-1 : ℝ) : ℂ) + (T : ℂ) * I))
        - octAngle (c.k 0) (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)) := by
  have h := argChangeHoriz_eq_of_octCert riemannZeta T c hm
    (fun _ _ x _ => zeta_analyticAt_horiz hT x) hstep hnc
  rw [hp0, hpm] at h
  exact h

/-- **K6c in the exact `hAHt` / `hAHb` binder form.**  A valid octant certificate from `2` to `-1`
    at height `T ≠ 0` (labels `StepOK`, pieces `NoCross`), plus TWO POINT ENCLOSURES
    `ζ(2 + i T) ∈ [a0, a1] x [b0, b1]` and `ζ(-1 + i T) ∈ [c0, c1] x [d0, d1]` whose corner checks
    give the slope brackets `[qlo0, qhi0]` (octant `k 0`) and `[qlo1, qhi1]` (octant `k (m-1)`),
    and any `L`, `H` with
        `L ≤ (k (m-1) - k 0) π/4 + arctan qlo1 - arctan qhi0`,
        `(k (m-1) - k 0) π/4 + arctan qhi1 - arctan qlo0 ≤ H`,
    give `argChangeHoriz riemannZeta T 2 (-1) ∈ Set.Icc L H`. -/
theorem hAH_of_octCert_boxes {T L H : ℝ} (hT : T ≠ 0) (c : OctCert) (hm : 1 ≤ c.m)
    (hp0 : c.p 0 = 2) (hpm : c.p c.m = -1) (hstep : c.StepOK) (hnc : c.NoCross riemannZeta T)
    {a0 a1 b0 b1 qlo0 qhi0 : ℝ}
    (hw0 : InBox (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)) a0 a1 b0 b1)
    (hS0 : ∀ a ∈ ({a0, a1} : Set ℝ), ∀ b ∈ ({b0, b1} : Set ℝ),
      0 < (octA (c.k 0) : ℝ) * a + octB (c.k 0) * b ∧
      qlo0 * ((octA (c.k 0) : ℝ) * a + octB (c.k 0) * b) ≤ (octA (c.k 0) : ℝ) * b - octB (c.k 0) * a ∧
      (octA (c.k 0) : ℝ) * b - octB (c.k 0) * a ≤ qhi0 * ((octA (c.k 0) : ℝ) * a + octB (c.k 0) * b))
    {c0 c1 d0 d1 qlo1 qhi1 : ℝ}
    (hw1 : InBox (riemannZeta (((-1 : ℝ) : ℂ) + (T : ℂ) * I)) c0 c1 d0 d1)
    (hS1 : ∀ a ∈ ({c0, c1} : Set ℝ), ∀ b ∈ ({d0, d1} : Set ℝ),
      0 < (octA (c.k (c.m - 1)) : ℝ) * a + octB (c.k (c.m - 1)) * b ∧
      qlo1 * ((octA (c.k (c.m - 1)) : ℝ) * a + octB (c.k (c.m - 1)) * b)
        ≤ (octA (c.k (c.m - 1)) : ℝ) * b - octB (c.k (c.m - 1)) * a ∧
      (octA (c.k (c.m - 1)) : ℝ) * b - octB (c.k (c.m - 1)) * a
        ≤ qhi1 * ((octA (c.k (c.m - 1)) : ℝ) * a + octB (c.k (c.m - 1)) * b))
    (hL : L ≤ ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4 + Real.arctan qlo1 - Real.arctan qhi0)
    (hH : ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4 + Real.arctan qhi1 - Real.arctan qlo0 ≤ H) :
    DiffractionCore.argChangeHoriz riemannZeta T 2 (-1) ∈ Set.Icc L H := by
  rw [argChangeHoriz_zeta_eq_of_octCert hT c hm hp0 hpm hstep hnc]
  have m00 := hS0 a0 (by simp) b0 (by simp)
  have m01 := hS0 a0 (by simp) b1 (by simp)
  have m10 := hS0 a1 (by simp) b0 (by simp)
  have m11 := hS0 a1 (by simp) b1 (by simp)
  have n00 := hS1 c0 (by simp) d0 (by simp)
  have n01 := hS1 c0 (by simp) d1 (by simp)
  have n10 := hS1 c1 (by simp) d0 (by simp)
  have n11 := hS1 c1 (by simp) d1 (by simp)
  obtain ⟨_, h0lo, h0hi⟩ := octAngle_mem_of_box hw0 m00.1 m01.1 m10.1 m11.1
    m00.2.1 m01.2.1 m10.2.1 m11.2.1 m00.2.2 m01.2.2 m10.2.2 m11.2.2
  obtain ⟨_, h1lo, h1hi⟩ := octAngle_mem_of_box hw1 n00.1 n01.1 n10.1 n11.1
    n00.2.1 n01.2.1 n10.2.1 n11.2.1 n00.2.2 n01.2.2 n10.2.2 n11.2.2
  constructor
  · have e : ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4
        = (c.k (c.m - 1) : ℝ) * Real.pi / 4 - (c.k 0 : ℝ) * Real.pi / 4 := by ring
    rw [e] at hL
    linarith
  · have e : ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4
        = (c.k (c.m - 1) : ℝ) * Real.pi / 4 - (c.k 0 : ℝ) * Real.pi / 4 := by ring
    rw [e] at hH
    linarith

/-! ## 8. Non-vacuity: the certificate on `f = id` -/

/-- Non-vacuity of the octant machinery: on `f = id` at height `1`, the one-piece certificate
    with octant `2` (`Im w > 0`) is valid and evaluates the horizontal argument change exactly:
    `argChangeHoriz id 1 2 (-1) = π/4 + arctan 2` (`= arg(-1 + i) - arg(2 + i)`). -/
theorem argChangeHoriz_id_one :
    DiffractionCore.argChangeHoriz (fun s : ℂ => s) 1 2 (-1) = Real.pi / 4 + Real.arctan 2 := by
  let c : OctCert := ⟨1, fun j => if j = 0 then 2 else -1, fun _ => 2⟩
  have hA : octA 2 = 0 := by decide
  have hB : octB 2 = 1 := by decide
  have hnc : c.NoCross (fun s : ℂ => s) 1 := by
    intro j _ x _
    simp only [octX, hA, hB, c]
    simp
  have hstep : c.StepOK := by
    intro j hj
    simp only [c] at hj
    omega
  have h := argChangeHoriz_eq_of_octCert (fun s : ℂ => s) 1 c (by simp [c])
    (fun _ _ x _ => analyticAt_id) hstep hnc
  have hp0 : c.p 0 = 2 := by simp [c]
  have hp1 : c.p c.m = -1 := by simp [c]
  rw [hp0, hp1] at h
  rw [h]
  simp only [c, octAngle, octX, octY, hA, hB]
  norm_num

/-- The exact value is not off by a turn (the certificate pins the winding, not just the value
    mod 2π). -/
theorem argChangeHoriz_id_one_ne :
    DiffractionCore.argChangeHoriz (fun s : ℂ => s) 1 2 (-1)
      ≠ Real.pi / 4 + Real.arctan 2 - 2 * Real.pi := by
  rw [argChangeHoriz_id_one]
  have := Real.pi_pos
  intro h
  linarith

end ArgHoriz
