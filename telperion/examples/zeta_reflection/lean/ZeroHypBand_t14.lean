/-  ZeroHypBand_t14.lean -- ANDÚRIL G2-full: toward the FIRST zero-hypothesis reflected band.

    THE SUMMIT GOAL (mission): a kernel theorem locating a nontrivial ζ zero with NO numeric
    hypotheses of ANY kind -- `theorem zero_hyp_band : ∃ x ∈ Set.Icc 14 15, completedRiemannZeta
    (1/2 + x*I) = 0`, axiom print `[propext, Classical.choice, Quot.sound]`, taking NO arguments.

    ## THE DESIGN DECISION FOR GAP (B) -- Γℝ factor -- AND THE HONEST BUDGET

    `gLine t = Re Λ(1/2+it)` with `Λ = Γℝ·ζ`.  Since `Λ` is real on the line
    (`ZetaZeroLocalization.completedZeta_im_eq_zero`), the SIGN chain the IVT (`XiLineZeros`,
    `CheckBand`) consumes is `sign(gLine tᵢ)`.  Writing `Γℝ(1/2+it) = |Γℝ|·e^{iφ}` with `|Γℝ| > 0`
    (Γℝ never vanishes on the line) and dropping the positive modulus:

        sign(gLine t) = sign( cos φ · Re ζ(1/2+it)  −  sin φ · Im ζ(1/2+it) ),   φ = arg Γℝ(1/2+it).

    Verified numerically (mpmath, 40 dps) at the grid points: `φ = arg Γℝ(1/2+it) = θ_RS(t)` (the
    Riemann–Siegel theta), and the sign quantity equals `Z(t) = e^{iθ}ζ` -- the Hardy Z-function --
    whose sign is `(−, +, −)` at `t ∈ {14, 15, 22}` giving two zeros in `[14, 22]`.  `|Z(14)| ≈ 0.106`,
    a comfortable sign margin.

    ### ROUTE CHOSEN: **B1 (phase decomposition)** -- and why.

    B1 needs ONE real quantity, the phase `φ = arg Γℝ`, and drops the modulus (provably positive) --
    strictly cheaper than B2 (which boxes both `Re Γℝ` and `Im Γℝ` and hits the digamma anchor for the
    magnitude too).  B3 (functional-equation |Γℝ| cancellation) is not needed at these heights.

    ### THE HONEST REFUSAL ARITHMETIC (why the full band is BEYOND REACH, reported not worked around).

    B1 reduces gap (B) to boxing `φ = arg Γℝ(1/2+it)` -- equivalently `θ_RS(t)` -- as a kernel interval.
    The corpus (`StirlingBinet.logDeriv_gammaR_enclosure`) encloses `logDeriv Γℝ`, i.e. the θ INTEGRAND
    `θ'(t)`, NOT the θ VALUE.  Getting `φ(t)` requires integrating the enclosed integrand over `[0, t]`
    with a kernel-checkable quadrature remainder -- an instrument (`argChangeVert` VALUE enclosure) that
    does NOT exist in the corpus.  Moreover `StirlingBinet`'s every enclosure theorem carries the
    unresolved complex-anchor hypothesis `ψ(w+N) − log(w+N) → 0` (the identity-theorem lift, `DlvpTheta`
    brick 3b′-iii, future work) -- itself a non-numeric hypothesis that would leak into the conclusion.
    Build-level confirmation: `StirlingBinet` is not even compiled in this island (its `DiffractionCore`
    dependency from the sibling `zeta_zero_localization` island is unbuilt).

    So of the two blockers the FullyReflectedBand budget named, instrument A (mod-2π trig,
    `TrigReduceOperating`) CLEARED gap (A), but gap (B) -- the Γℝ-value / phase enclosure -- is GENUINELY
    UNBUILT.  A full zero-hypothesis two-zero band is therefore NOT reachable with current corpus
    machinery, independent of compute budget.

    ## WHAT THIS FILE DELIVERS (the strongest honest zero-hypothesis advance).

    The maximum honest in-kernel advance is to CLOSE THE ζ HALF of a `gLine` box with ZERO hypotheses,
    isolating gap (B) as the sole residual.  Concretely we prove, with NO numeric hypotheses:

      * `term_re` / `term_im` -- the ATOM: `Re/Im (n^{-(1/2+it)}) = n^{-1/2}·cos/∓sin(t·log n)`.  This
        is the per-term building block of the Euler–Maclaurin ζ finite part `Σ_{n<N} n^{-s}`
        (`EMZetaComplex.em_cpow_partial` relates that sum to `EMZetaTail.emZetaFinite3`).
      * `inv_sqrt2_box` -- a kernel rational box for `2^{-1/2}` (the `n=2` amplitude).
      * `re_term2_t14_box` -- **the headline zero-hypothesis sign box**: `Re(2^{-(1/2+14i)}) ∈
        [−0.6798, −0.6796]`, strictly negative, decided in-kernel by composing the atom, the amplitude
        box, and instrument A `TrigReduceOperating.cos_14log2`.  NO arguments, NO numeric hypotheses.

    This is the FIRST kernel-computed, hypothesis-free evaluation of a ζ-series term on the critical
    line at real height -- the `gLine` ζ half, made concrete.  The residual to a full band is exactly
    gap (B) above (the φ = arg Γℝ value box) plus the mechanical scale-up (all N terms + the elementary
    `1/(s−1)`, endpoint, and `bernoulli 2` pieces of `emZetaFinite3`, then the `Γℝ` product, then
    `checkBandFull`).

    ## THE EMITTER CHARTER (scaling to arbitrary bands).

    `term_re`/`term_im` are GENERAL in `(n, t)`.  A driver (`zero_hyp_emit.py`) scales this file by, per
    grid height `t` and per term `n < N`:
      1. emit `TrigReduceOperating`-style `cos(t·log n)` / `sin(t·log n)` operating-point certs (the
         ~26-step π-free double-angle climb; ~700 Int-ops/pair per the mod2pi budget);
      2. emit the `n^{-1/2}` amplitude box (the `inv_sqrt2_box` shape, general `n`);
      3. compose via `term_re`/`term_im` into per-term `Re`/`Im` boxes (this file's `re_term2_t14_box`
         shape, a sign-aware interval product);
      4. sum the term boxes + the elementary `emZetaFinite3` pieces + the `≤ 1/1000` order-3 tail
         (`EMZetaTail.em_zeta_critical_line3_number`) into `Re ζ` / `Im ζ` boxes;
      5. **[BLOCKED on gap (B)]** box `φ = arg Γℝ(1/2+it)`, form `cos φ·Re ζ − sin φ·Im ζ`, feed the
         sign chain to `FullyReflectedBand_t14.checkBandFull` → `XiLineZeros`' IVT.
    Budget (per mod2pi's measured numbers): step 1 dominates at ~700 Int-ops/pair × N terms × grid
    points; at N=200, ~14 grid points this is ~2·10⁶ Int-ops of straight-line climb -- affordable as
    unrolled per-term lemmas (the BraggH100 heartbeat lesson: one declaration per term, not one giant
    `decide`).  Steps 2–4 are cheap `norm_num`/`linarith` interval arithmetic.  Step 5 awaits the θ-value
    instrument.

    conjecture1_proved = False.  Finite interval arithmetic on the ζ half of the completed-zeta sign
    chain, NOT a proof of RH, and NOT (yet) a hypothesis-free zero-existence theorem.
-/
import TrigReduceOperating

open Complex TrigReduceOperating

namespace ZeroHypBand_t14

/-! ## 1.  The atom: real/imag part of a ζ-series term on the critical line.

    `n^{-(1/2+it)} = exp(−(1/2+it)·log n) = n^{-1/2}·(cos(t·log n) − i·sin(t·log n))`.  These two
    lemmas are GENERAL in `(n, t)`; they turn instrument A's `cos(t·log n)` / `sin(t·log n)` boxes into
    boxes for the `Re`/`Im` of the term.  No numeric hypotheses. -/

/-- **ζ-term real part.**  `Re((n:ℂ)^{-(1/2+it)}) = n^{-1/2}·cos(t·log n)` for `n > 0`. -/
theorem term_re (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ((n : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * I))).re
      = Real.exp (-(1 / 2) * Real.log n) * Real.cos (t * Real.log n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hhalf : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hne,
    show Complex.log (n : ℂ) = (Real.log n : ℂ) by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le],
    hhalf, Complex.exp_re]
  have hre : (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re
      = -(1 / 2) * Real.log n := by
    rw [show (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          = -((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (Real.log n : ℂ)) by ring]
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have him : (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im
      = -(t * Real.log n) := by
    rw [show (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          = -((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (Real.log n : ℂ)) by ring]
    simp only [Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [hre, him, Real.cos_neg]

/-- **ζ-term imaginary part.**  `Im((n:ℂ)^{-(1/2+it)}) = −n^{-1/2}·sin(t·log n)` for `n > 0`. -/
theorem term_im (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ((n : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * I))).im
      = -(Real.exp (-(1 / 2) * Real.log n) * Real.sin (t * Real.log n)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hhalf : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hne,
    show Complex.log (n : ℂ) = (Real.log n : ℂ) by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le],
    hhalf, Complex.exp_im]
  have hre : (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re
      = -(1 / 2) * Real.log n := by
    rw [show (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          = -((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (Real.log n : ℂ)) by ring]
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have him : (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im
      = -(t * Real.log n) := by
    rw [show (((Real.log n : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          = -((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (Real.log n : ℂ)) by ring]
    simp only [Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [hre, him, Real.sin_neg]; ring

/-! ## 2.  The `n = 2` amplitude box: `2^{-1/2}` in rationals (no hypotheses). -/

/-- **Amplitude box for `n = 2`.**  `2^{-1/2} ∈ [0.7071067, 0.7071068]`, via the `√2 ∈
    [1.41421356, 1.41421357]` bracket.  The general `n^{-1/2}` amplitude box (the emitter's step 2)
    has the identical shape. -/
theorem inv_sqrt2_box :
    (7071067 / 10000000 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ)
      ∧ (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ (7071068 / 10000000 : ℝ) := by
  have h2 : (2 : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]
  rw [h2]
  have hs2lo : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356 : ℝ) = Real.sqrt (1.41421356 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs2hi : Real.sqrt 2 ≤ (1.41421357 : ℝ) := by
    rw [show (1.41421357 : ℝ) = Real.sqrt (1.41421357 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  refine ⟨?_, ?_⟩
  · calc (7071067 / 10000000 : ℝ) ≤ (1.41421357 : ℝ)⁻¹ := by norm_num
      _ ≤ (Real.sqrt 2)⁻¹ := inv_anti₀ (by norm_num) hs2hi
  · calc (Real.sqrt 2)⁻¹ ≤ (1.41421356 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs2lo
      _ ≤ (7071068 / 10000000 : ℝ) := by norm_num

/-! ## 3.  The headline: a ZERO-HYPOTHESIS sign box for a ζ-term at `t = 14`.

    Composing the atom (`term_re`), the amplitude box (`inv_sqrt2_box`), and instrument A
    (`TrigReduceOperating.cos_14log2`) via a sign-aware interval product, the `n = 2` term of `Re ζ`'s
    Euler–Maclaurin finite part on the critical line at `t = 14` is decided STRICTLY NEGATIVE by the
    kernel, with NO numeric hypotheses. -/

/-- **ZERO-HYPOTHESIS ζ-TERM SIGN BOX.**  `Re((2:ℂ)^{-(1/2+14i)}) ∈ [−0.6798, −0.6796]` -- strictly
    negative, no arguments, no numeric hypotheses.  True value ≈ −0.67971.  This is the first
    kernel-computed, hypothesis-free evaluation of a ζ-series term on the critical line at real height:
    the `gLine` ζ half made concrete.  The interval product is sign-aware: the amplitude `E = 2^{-1/2}`
    is nonneg and the cos box `C = cos(14·log 2)` is strictly negative, so `E·C ∈ [E_hi·C_lo, E_lo·C_hi]`. -/
theorem re_term2_t14_box :
    (((2 : ℕ) : ℂ) ^ (-((1 : ℂ) / 2 + (14 : ℝ) * I))).re ≤ (-6796 / 10000 : ℝ)
      ∧ (-6798 / 10000 : ℝ) ≤ (((2 : ℕ) : ℂ) ^ (-((1 : ℂ) / 2 + (14 : ℝ) * I))).re := by
  have hterm := term_re 2 (by norm_num) 14
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num] at hterm
  rw [hterm,
    show Real.exp (-(1 / 2) * Real.log 2) = (2 : ℝ) ^ (-(1 / 2) : ℝ) by
        rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf]
  obtain ⟨hElo, hEhi⟩ := inv_sqrt2_box
  obtain ⟨hClo, hChi⟩ := cos_14log2
  set E := (2 : ℝ) ^ (-(1 / 2) : ℝ) with hE
  set C := Real.cos (14 * Real.log 2) with hC
  have hEpos : (0 : ℝ) ≤ E := by rw [hE]; positivity
  have hCub : C ≤ ((-138531218710871479 / 144115188075855872) + (1 / 134217728) : ℝ) := hChi
  have hClb : ((-554125208006725529 / 576460752303423488) - (1 / 134217728) : ℝ) ≤ C := hClo
  have hCub_neg : ((-138531218710871479 / 144115188075855872) + (1 / 134217728) : ℝ) < 0 := by
    norm_num
  have hClb_neg : ((-554125208006725529 / 576460752303423488) - (1 / 134217728) : ℝ) < 0 := by
    norm_num
  refine ⟨?_, ?_⟩
  · -- upper bound: E·C ≤ E·C_hi ≤ E_lo·C_hi  (E ≥ 0, C_hi < 0)
    have h1 : E * C ≤ E * ((-138531218710871479 / 144115188075855872) + (1 / 134217728)) :=
      mul_le_mul_of_nonneg_left hCub hEpos
    have h2 : E * ((-138531218710871479 / 144115188075855872) + (1 / 134217728))
        ≤ (7071067 / 10000000) * ((-138531218710871479 / 144115188075855872) + (1 / 134217728)) :=
      mul_le_mul_of_nonpos_right hElo (le_of_lt hCub_neg)
    calc E * C ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ (-6796 / 10000 : ℝ) := by norm_num
  · -- lower bound: E·C ≥ E·C_lo ≥ E_hi·C_lo  (E ≥ 0, C_lo < 0)
    have h1 : E * ((-554125208006725529 / 576460752303423488) - (1 / 134217728)) ≤ E * C :=
      mul_le_mul_of_nonneg_left hClb hEpos
    have h2 : (7071068 / 10000000) * ((-554125208006725529 / 576460752303423488) - (1 / 134217728))
        ≤ E * ((-554125208006725529 / 576460752303423488) - (1 / 134217728)) :=
      mul_le_mul_of_nonpos_right hEhi (le_of_lt hClb_neg)
    calc (-6798 / 10000 : ℝ)
        ≤ (7071068 / 10000000) * ((-554125208006725529 / 576460752303423488) - (1 / 134217728)) := by
          norm_num
      _ ≤ E * ((-554125208006725529 / 576460752303423488) - (1 / 134217728)) := h2
      _ ≤ E * C := h1

end ZeroHypBand_t14
