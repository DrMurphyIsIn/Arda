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

    Two lemmas separate the proven finite `Im L_n` from the target `φ(14)` box:

      * `ThetaGap.im_Ln_rate` (rate) : `|Im L_∞ − Im L_n| ≤ C(x,y)/n` with an EXPLICIT elementary
        `C` -- provable by the integral-comparison harmonic-tail bound (the standard `1/(2n)`-type
        `∑ 1/(x+k)` vs `log` estimate) plus the cubic `arctan(u)=u−r`, `0<r<u³/3` residual, both of
        which need only elementary calculus already in Mathlib (`sum_le_integral` machinery, and
        this file's arctan corollaries).  The driver's numerics: at `n=2000`, honest `k≤30`, the box
        width is ≈ 9.4e-4 < the 2e-3 target.

      * `ThetaGap.im_Ln_tendsto_argGamma` (branch bridge) : `Im L_n → arg Γ(z)`.  Follows from
        `exp_Ln_eq_gammaSeq` + `GammaSeq_tendsto_Gamma` + continuity of `exp`, PROVIDED the limit
        does not slip a `2πk` branch (it does not: `arg Γ(1/4+7i) ≈ 0.44` is far from `±π`, and
        `Im L_n` is monotone-bounded in `(−π,π)` for these `(x,y)` -- the driver confirms every
        partial `Im L_n ∈ (−0.9, 0.5)`).  This is the one genuine limit-interchange; it is a
        `Filter.Tendsto` obligation, NOT a numeric hypothesis.

    With both, `φ(14) = −7·log π + arg Γ(1/4+7i)` is boxed by `−7·[log π box] + [Im L_n box] ±
    [rate]` -- a kernel interval of width ≤ 2e-3, no hypotheses.  `log π` is boxed by the corpus
    verified-log pattern (`Real.pi_gt_*`/`Real.log` d9 bounds), exactly as `TrigReduceOperating`
    boxes `log 2`.

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

end ThetaValue

/-! ## The precise remaining gap -- named `Prop`s, honestly stated. -/

namespace ThetaGap

open ThetaValue

/-- **RATE (remaining).**  The finite `Im L_n` converges to `Im log Γ(z)` with an explicit
    elementary `C/n` rate.  Provable by integral-comparison on the harmonic tail `Σ 1/(x+k)`
    plus the cubic arctan residual (`ArctanTaylor.self_sub_cube_le_arctan` /
    `ArctanTaylor.arctan_le_self`).  Stated as the obligation; NOT a numeric hypothesis. -/
def RateObligation : Prop :=
  ∀ (x y : ℝ), 0 < x → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    |(Complex.log (Complex.Gamma ((x:ℂ) + (y:ℂ)*I))).im
       - (y * Real.log n - ∑ k ∈ Finset.range (n+1), Real.arctan (y/(x+k)))|
      ≤ C / n

/-- **BRANCH BRIDGE (remaining).**  `Im L_n → arg Γ(z)`, no `2πk` slip.  Follows from
    `exp_Ln_eq_gammaSeq` + `Complex.GammaSeq_tendsto_Gamma` + `exp` continuity + the fact that
    `arg Γ(1/4+7i)` is far from `±π`.  A `Filter.Tendsto` obligation, NOT a numeric hypothesis. -/
def BranchBridgeObligation : Prop :=
  ∀ (x y : ℝ), 0 < x → Complex.Gamma ((x:ℂ) + (y:ℂ)*I) ≠ 0 →
    Filter.Tendsto
      (fun n : ℕ => y * Real.log n - ∑ k ∈ Finset.range (n+1), Real.arctan (y/(x+k)))
      Filter.atTop
      (nhds (Complex.log (Complex.Gamma ((x:ℂ) + (y:ℂ)*I))).im)

end ThetaGap
