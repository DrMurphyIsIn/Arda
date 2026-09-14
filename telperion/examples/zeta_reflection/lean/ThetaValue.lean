/-  ThetaValue.lean -- ANDÚRIL A4 θ-value instrument: toward a kernel box for
    φ(t) = arg Γℝ(1/2+it) = the Riemann–Siegel θ, with NO numeric hypotheses.

    ## THE ROUTE (Euler/Weierstrass limit form, γ-free).

    Γℝ(s) = π^{-s/2}·Γ(s/2), so with `s = 1/2+it`, `t = 14`:

        φ(14) = arg Γℝ(1/2+14i) = −7·log π + Im log Γ(1/4 + 7i).

    (Numerically φ(14) = θ_RS(14) ≈ −1.7829487; verified in the driver against mpmath's
    `siegeltheta(14)` and against `arg Γℝ` directly.)

    For `Im log Γ(z)` with `z = x+iy` (`x = 1/4`, `y = 7`) we use Mathlib's Gauss product
    `GammaSeq z n = n^z·n!/∏_{k=0}^n (z+k) → Γ(z)` (`Complex.GammaSeq_tendsto_Gamma`).  Its
    principal-log has imaginary part (this file's `imLn_formula`, PROVED):

        Im L_n = y·log n − Σ_{k=0}^n arctan(y/(x+k)),
        L_n := z·log n + log(n!) − Σ_{k=0}^n log(z+k)   (all principal complex logs),

    and `exp(L_n) = GammaSeq z n` (this file's `exp_Ln_eq_gammaSeq`, PROVED).  Each `arctan`
    term is boxed by the reusable `ArctanTaylor.arctan_bracket` instrument (no ψ, no Γ anchor).

    ## WHAT IS PROVED HERE (all axiom-clean, no numeric hypotheses).

      * `arg_eq_arctan_of_re_pos` : `w.arg = arctan(im w/re w)` for `re w > 0`  (the per-factor atom).
      * `imLn_formula`            : the exact `Im L_n` formula above, GENERAL in `(x,y,n)`, `x>0`.
      * `exp_Ln_eq_gammaSeq`      : `exp(L_n) = GammaSeq z n`, the bridge to the Gauss product.

    Together with `ArctanTaylor.arctan_bracket` these are a COMPLETE finite kernel pipeline: for
    any `n` they reduce `Im L_n` to a rational interval with no numeric hypotheses.

    ## THE PRECISE REMAINING GAP (named Props, honestly stated -- see mission "land D1 + the gap").

    Two obligations separate the proven finite `Im L_n` from the target `φ(14)` box:

      * `ThetaGap.ConvergenceObligation` (branch bridge) : `imLnVal x y n → Λ` for a real `Λ` that
        is a genuine argument of `Γ(z)` (`Γ(z) = ‖Γ(z)‖·exp(IΛ)`).  IMPORTANT honest correction,
        driver-verified: `Im L_n` converges to the CONTINUOUS unwrapped value `Im loggamma(1/4+7i)
        ≈ 6.230`, which is `arg Γ(z) + 2π` — NOT the principal `(Complex.log (Γ z)).im ≈ −0.053`.
        (`Im L_n` sweeps from `−2.93` at `n=1` up through `6.23`, crossing far outside `(−π,π)`.)  So
        the correct target is `Λ` characterized by the exp identity, not a principal-branch equality.
        This is the one genuine limit-interchange (from `exp_Ln_eq_gammaSeq` +
        `Complex.GammaSeq_tendsto_Gamma` + `exp` continuity, tracking the winding); a `Tendsto`
        obligation, NOT a numeric hypothesis.

      * `ThetaGap.RateObligation` (rate) : `|Λ − imLnVal x y n| ≤ C(x,y)/n` with an EXPLICIT
        elementary `C` -- provable by the integral-comparison harmonic-tail bound (`1/(2n)`-type
        `∑ 1/(x+k)` vs `log`) plus the cubic `arctan(u)=u−r`, `0<r<u³/3` residual, using only
        elementary calculus in Mathlib and this file's arctan corollaries.  Driver: at `n=2000`,
        honest `k≤30`, box width ≈ 9.4e-4 < the 2e-3 target.

    With both, `φ(14) = −7·log π + Λ` (continuous branch) is boxed by `−7·[log π box] +
    [imLnVal box] ± [rate]` -- a kernel interval of width ≤ 2e-3, no hypotheses.  `log π` is boxed
    by the corpus verified-log pattern, exactly as `TrigReduceOperating` boxes `log 2`.  The shape
    of the final consumption is recorded in `ThetaGap.PhiTargetShape`.

    conjecture1_proved = False.  The finite Im-part pipeline of the θ-value, kernel-clean; the θ
    VALUE box itself awaits the two named Props above (rate + branch bridge).  NOT a proof of RH.
-/
import ArctanTaylor
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Complex Real

namespace ThetaValue

/-! ### The per-factor atom: `arg` of a right-half-plane point is an `arctan`. -/

/-- For a complex number with positive real part, `arg w = arctan (im w / re w)`.  This is the
    per-factor imaginary-log contribution used throughout the θ series. -/
theorem arg_eq_arctan_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    w.arg = Real.arctan (w.im / w.re) := by
  have hne : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hcos : Real.cos w.arg = w.re / ‖w‖ := cos_arg hne
  have hnorm : 0 < ‖w‖ := by positivity
  have hcospos : 0 < Real.cos w.arg := by rw [hcos]; positivity
  have hpi := Real.pi_pos
  have hlt : w.arg < π/2 ∧ -(π/2) < w.arg := by
    refine ⟨?_, ?_⟩
    · by_contra h; push_neg at h
      have : Real.cos w.arg ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [arg_le_pi w])
      linarith
    · by_contra h; push_neg at h
      have hge : -π < w.arg := (arg_mem_Ioc w).1
      have : Real.cos w.arg ≤ 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      linarith
  rw [← tan_arg w, Real.arctan_tan hlt.2 hlt.1]

/-! ### The exact imaginary part of the finite log-Weierstrass sum `L_n`. -/

/-- **`Im L_n` formula.**  With `L_n = z·log n + log(n!) − Σ_{k=0}^n log(z+k)` (all principal
    complex logs) and `z = x+iy`, `x > 0`, `Im L_n = y·log n − Σ_{k=0}^n arctan(y/(x+k))`. -/
theorem imLn_formula (x y : ℝ) (hx : 0 < x) (n : ℕ) :
    (((x:ℂ) + (y:ℂ)*I) * Complex.log (n:ℂ) + Complex.log ((Nat.factorial n : ℕ):ℂ)
       - ∑ k ∈ Finset.range (n+1), Complex.log (((x:ℂ) + (y:ℂ)*I) + (k:ℂ))).im
      = y * Real.log n - ∑ k ∈ Finset.range (n+1), Real.arctan (y/(x+k)) := by
  have hlogn : (Complex.log (n:ℂ)).im = 0 := by rw [Complex.log_im, Complex.natCast_arg]
  have hlognfac : (Complex.log ((Nat.factorial n : ℕ):ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.natCast_arg]
  have hlognre : (Complex.log (n:ℂ)).re = Real.log n := by
    rw [Complex.log_re, Complex.norm_natCast]
  have hzre : (↑x + ↑y * I : ℂ).re = x := by simp
  have hzim : (↑x + ↑y * I : ℂ).im = y := by simp
  have hsum : (∑ k ∈ Finset.range (n+1), Complex.log ((↑x + ↑y*I) + (k:ℂ))).im
      = ∑ k ∈ Finset.range (n+1), Real.arctan (y/(x+k)) := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.log_im]
    have hre : ((↑x + ↑y*I) + (k:ℂ)).re = x + k := by simp
    have him : ((↑x + ↑y*I) + (k:ℂ)).im = y := by simp
    rw [arg_eq_arctan_of_re_pos (by rw [hre]; positivity), hre, him]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, hlogn, hlognfac, hzre, hzim,
    hlognre, hsum]
  ring

/-! ### The bridge to the Gauss product: `exp(L_n) = GammaSeq z n`. -/

/-- **Gauss-product bridge.**  `exp(L_n) = GammaSeq z n` for `n ≥ 1` and all `z+k ≠ 0`. -/
theorem exp_Ln_eq_gammaSeq (z : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hzk : ∀ k ∈ Finset.range (n+1), z + (k:ℂ) ≠ 0) :
    Complex.exp (z * Complex.log (n:ℂ) + Complex.log ((Nat.factorial n : ℕ):ℂ)
       - ∑ k ∈ Finset.range (n+1), Complex.log (z + (k:ℂ))) = Complex.GammaSeq z n := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hfac : ((Nat.factorial n : ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_sum,
    show Complex.exp (z * Complex.log (n:ℂ)) = (n:ℂ)^z from by
        rw [Complex.cpow_def_of_ne_zero hnc]; ring_nf,
    Complex.exp_log hfac,
    show (∏ k ∈ Finset.range (n+1), Complex.exp (Complex.log (z + (k:ℂ))))
        = ∏ k ∈ Finset.range (n+1), (z + (k:ℂ)) from by
        apply Finset.prod_congr rfl; intro k hk; exact Complex.exp_log (hzk k hk),
    Complex.GammaSeq, mul_div_assoc, div_eq_mul_inv]

/-! ### Concrete instrument demonstration: a kernel box for a θ-series arctan term.

    These show the `ArctanTaylor` instrument produces REAL numeric boxes with no hypotheses --
    the atomic step the θ-series scale-up repeats per term.  We box the two `n₀ = 1` terms
    (`k = 0, 1`) of the `x = 1/4, y = 7` series: `arctan(7/(1/4)) = arctan 28` and
    `arctan(7/(1/4+1)) = arctan(28/5)`. -/

/-- `atanPS (1/28) 2 = 2351/65856` (kernel evaluation of the 2-term Taylor sum). -/
theorem atanPS_inv28 : ArctanTaylor.atanPS (1/28) 2 = 2351/65856 := by
  rw [ArctanTaylor.atanPS]; simp [Finset.sum_range_succ]; norm_num

/-- **Kernel box for `arctan(1/28)`** via the instrument (N = 2): width ≈ 2.3e-8, no hypotheses. -/
theorem arctan_inv28_box :
    |Real.arctan (1/28) - 2351/65856| ≤ 1/86051840 := by
  have h := ArctanTaylor.arctan_bracket (1/28) (by norm_num) 2
  rw [atanPS_inv28] at h
  calc |Real.arctan (1/28) - 2351/65856| ≤ (1/28)^(2*2+1)/(2*2+1) := h
    _ ≤ 1/86051840 := by norm_num

/-- **Kernel box for `arctan 28`** (the `k = 0` term of the `x=1/4,y=7` series), via the reflection
    `arctan 28 = π/2 − arctan(1/28)` and `arctan_inv28_box`.  Width ≈ 2.3e-8, no hypotheses. -/
theorem arctan28_box :
    |Real.arctan 28 - (Real.pi/2 - 2351/65856)| ≤ 1/86051840 := by
  have hrefl : Real.arctan (1/28) = Real.pi/2 - Real.arctan 28 := by
    have := Real.arctan_inv_of_pos (x := 28) (by norm_num)
    rwa [show (28:ℝ)⁻¹ = 1/28 from by norm_num] at this
  have h := arctan_inv28_box
  rw [hrefl] at h
  calc |Real.arctan 28 - (Real.pi/2 - 2351/65856)|
      = |(Real.pi/2 - Real.arctan 28) - 2351/65856| := by rw [abs_sub_comm]; ring_nf
    _ ≤ 1/86051840 := h

end ThetaValue

/-! ## The precise remaining gap -- named `Prop`s, honestly stated. -/

namespace ThetaGap

open ThetaValue

/-- The finite θ-series partial value `Im L_n = y·log n − Σ_{k=0}^n arctan(y/(x+k))`. -/
noncomputable def imLnVal (x y : ℝ) (n : ℕ) : ℝ :=
  y * Real.log n - ∑ k ∈ Finset.range (n+1), Real.arctan (y/(x+k))

/-- **CONVERGENCE + LIMIT CHARACTERIZATION (the remaining core).**  There is a real limit `Λ`
    (the CONTINUOUS `arg Γℝ`-companion, i.e. the unwrapped `Im log Γ(z)`) with:

      (i)  `imLnVal x y n → Λ`   (`Filter.Tendsto`), and
      (ii) `Γ(z) = ‖Γ(z)‖ · exp(I·Λ)`   (Λ is a genuine argument of `Γ(z)`, mod `2π`).

    NOTE the honest correction (driver-verified): `Im L_n` converges to the CONTINUOUS log value
    (`Im loggamma(z) ≈ 6.230` at `z=1/4+7i`), which is `arg Γ(z) + 2π` — it is NOT the principal
    `(Complex.log (Γ z)).im`.  Characterizing `Λ` by (ii) captures the correct branch without
    committing to a wrong principal-branch identity.  Condition (i) is the genuine
    limit-interchange (from `exp_Ln_eq_gammaSeq` + `Complex.GammaSeq_tendsto_Gamma` + `exp`
    continuity, tracking the winding); (ii) fixes the branch.  Neither is a numeric hypothesis. -/
def ConvergenceObligation : Prop :=
  ∀ (x y : ℝ), 0 < x → Complex.Gamma ((x:ℂ) + (y:ℂ)*I) ≠ 0 →
    ∃ Λ : ℝ,
      Filter.Tendsto (imLnVal x y) Filter.atTop (nhds Λ) ∧
      Complex.Gamma ((x:ℂ) + (y:ℂ)*I)
        = (‖Complex.Gamma ((x:ℂ) + (y:ℂ)*I)‖ : ℂ) * Complex.exp (Complex.I * (Λ:ℂ))

/-- **RATE (remaining).**  Once `Λ` exists (`ConvergenceObligation`), the finite `imLnVal` reaches
    it at an EXPLICIT elementary `C/n` rate.  Provable by integral-comparison on the harmonic tail
    `Σ 1/(x+k)` plus the cubic arctan residual (`ArctanTaylor.self_sub_cube_le_arctan` /
    `ArctanTaylor.arctan_le_self`).  Driver: at `n=2000`, honest `k≤30`, width ≈ 9.4e-4 < 2e-3.
    NOT a numeric hypothesis. -/
def RateObligation : Prop :=
  ∀ (x y : ℝ), 0 < x → ∀ Λ : ℝ,
    Filter.Tendsto (imLnVal x y) Filter.atTop (nhds Λ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |Λ - imLnVal x y n| ≤ C / n

/-- **THE ASSEMBLY LEMMA (proved).**  This is the kernel-checkable step that turns the finite
    instrument output into a `φ` box, given the (non-numeric) obligations.  Concretely: if `Λ` is
    a limit reached at rate `C/n` from `imLnVal`, and at some order `n₀ ≥ 1` the instrument has
    boxed the partial value `imLnVal x y n₀ ∈ [a, b]`, and `log π ∈ [lp, hp]`, then

        −7·log π + Λ  ∈  [−7·hp + a − C/n₀,  −7·lp + b + C/n₀].

    The rate `C/n₀` widens the partial-value box to a box for `Λ`; the `log π` box and the `−7`
    factor complete `φ = −7 log π + Λ`.  All the remaining work is producing `[a,b]` (via
    `ArctanTaylor.arctan_bracket` per term, mechanical) and discharging `ConvergenceObligation` /
    `RateObligation`.  NO numeric hypotheses beyond the boxes the instrument itself supplies. -/
theorem phi_box_of_rate_and_partial
    (x y Λ C lp hp a b : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hC : 0 ≤ C)
    (hrate : |Λ - imLnVal x y n₀| ≤ C / n₀)
    (hpartial_lo : a ≤ imLnVal x y n₀) (hpartial_hi : imLnVal x y n₀ ≤ b)
    (hlogpi_lo : lp ≤ Real.log Real.pi) (hlogpi_hi : Real.log Real.pi ≤ hp) :
    (-7 * hp + a - C / (n₀:ℝ)) ≤ -7 * Real.log Real.pi + Λ ∧
      -7 * Real.log Real.pi + Λ ≤ (-7 * lp + b + C / (n₀:ℝ)) := by
  have hn₀R : (1:ℝ) ≤ (n₀:ℝ) := by exact_mod_cast hn₀
  have hCn : 0 ≤ C / (n₀:ℝ) := by positivity
  rw [abs_le] at hrate
  constructor
  · have h1 : Λ ≥ imLnVal x y n₀ - C / n₀ := by linarith [hrate.1]
    have h2 : Λ ≥ a - C / n₀ := by linarith
    have h3 : -7 * Real.log Real.pi ≥ -7 * hp := by linarith
    linarith
  · have h1 : Λ ≤ imLnVal x y n₀ + C / n₀ := by linarith [hrate.2]
    have h2 : Λ ≤ b + C / n₀ := by linarith
    have h3 : -7 * Real.log Real.pi ≤ -7 * lp := by linarith
    linarith

end ThetaGap
