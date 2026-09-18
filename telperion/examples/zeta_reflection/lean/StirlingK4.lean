/-  StirlingK4.lean -- A2 Theorem 2, the HONEST higher-rate Binet ingredients (guard-imported).

    This file lands the session-reachable, kernel-clean components of the K ≥ 2 Stirling/Binet
    sharpening whose EXACT charter form (`StirlingBinetWip.norm_binetRemK_le`, the cos-form
    `|B_{2K}|/((2K−1)(2K)|w|^{2K−1}cos^{2K}(arg w/2))`) is BLOCKED by a Mathlib/corpus gap: Mathlib
    defines `Complex.digamma := logDeriv Gamma` with NO series representation (no trigamma/polygamma
    exist in Mathlib), so the order-`K` Bernoulli peel — whose leading explicit term is the trigamma
    `(1/2)Σ(w+k)^{-2}` — cannot be identified in closed form.  See the module tail for the precise
    remaining obligations.

    What IS reachable and lands here:

      * `binetTail_height_norm_le` — the HEIGHT-AWARE per-term Binet bound.  The corpus
        `ZeroFreeBridge.binetTail_norm_le` bounds each Binet-series term by `(3/2)/(3/2+k)²`, using
        only `‖w+k‖ ≥ Re(w+k)`.  At LARGE HEIGHT (`|Im w|` large — precisely the reflection track's
        operating regime, `Im(z/2) = 7` at the pilot `s = 1/2+14i`) this throws away the dominant
        `Im w` contribution to `‖w+k‖² = (Re w+k)² + (Im w)²`.  This lemma keeps it:
            ‖binetTail w k‖ ≤ (3/2) · 1/((Re w+k)² + (Im w)²).
        Summed, this is the `O(1/|Im w|)` large-height Binet decay (vs the corpus `O(1)` in height),
        the honest source of the enclosure sharpening the K = 4 form would deliver — WITHOUT the
        trigamma closed form, hence provable now.

    The shifted-base tail engine `EMZetaTail.em_tail_integral_bound_shifted` (deliverable 1 of the
    handoff, already landed and guarded) is the OTHER half: it bounds the `(w+x)^{-a}` tail integral
    the exact cos-form is built on, once the digamma↔trigamma bridge exists.

    conjecture1_proved = False.  A per-term analytic bound, NOT a proof of RH.
-/
import StirlingBinet

open Complex

namespace ZetaReflection

/-- **Height-aware per-term Binet bound.**  For `Re w > 3/2`, each Binet-series term obeys
        ‖binetTail w k‖ ≤ (3/2) · 1/((Re w + k)² + (Im w)²),
    keeping the full `‖w+k‖² = (Re w+k)² + (Im w)²` in the denominator (the corpus
    `ZeroFreeBridge.binetTail_norm_le` drops the `(Im w)²` term).  At large height this is the
    dominant sharpening: at `w = 1/4 + 7i + m`, the `(Im w)² = 49` term shrinks each summand by
    roughly `49/(Re w+k)²` relative to the corpus bound. -/
theorem binetTail_height_norm_le {w : ℂ} (hw : 3/2 < w.re) (k : ℕ) :
    ‖ZeroFreeBridge.binetTail w k‖ ≤ (3/2) * (1 / ((w.re + k) ^ 2 + (w.im) ^ 2)) := by
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  -- ‖w+k‖² = (Re w + k)² + (Im w)²  (exact, via normSq).
  have hnormsq : ‖w + (k : ℂ)‖ ^ 2 = (w.re + k) ^ 2 + (w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, add_zero]
    ring
  have hden_pos : (0:ℝ) < (w.re + k) ^ 2 + (w.im) ^ 2 := by positivity
  -- ‖w+k‖ lower bounds: ≥ Re(w+k) = w.re + k > 3/2, so ‖w+k‖ > 3/2 > 1.
  have hre_le : (w.re + k : ℝ) ≤ ‖w + (k : ℂ)‖ := by
    have h := Complex.re_le_norm (w + (k : ℂ))
    simpa only [Complex.add_re, Complex.natCast_re] using h
  have hnorm_gt : (3/2 : ℝ) < ‖w + (k : ℂ)‖ := lt_of_lt_of_le (by linarith) hre_le
  have h1 : (1:ℝ) < ‖w + (k : ℂ)‖ := by linarith
  have hnorm_pos : (0:ℝ) < ‖w + (k : ℂ)‖ := by linarith
  -- corpus step bound: ‖binetTail‖ ≤ ‖u‖²·(1−‖u‖)⁻¹/2, with u = (w+k)⁻¹.
  have hb := ZeroFreeBridge.norm_inv_sub_log_one_add_inv_le (s := w + (k : ℂ)) h1
  -- ‖u‖ = 1/‖w+k‖ ≤ 2/3.
  have htv : ‖(w + (k : ℂ))⁻¹‖ = 1 / ‖w + (k : ℂ)‖ := by rw [norm_inv, inv_eq_one_div]
  have hth : ‖(w + (k : ℂ))⁻¹‖ ≤ 2/3 := by
    rw [htv, div_le_div_iff₀ hnorm_pos (by norm_num)]; linarith
  have htnn : (0:ℝ) ≤ ‖(w + (k : ℂ))⁻¹‖ := norm_nonneg _
  -- (1−‖u‖)⁻¹ ≤ 3.
  have hinv3 : (1 - ‖(w + (k : ℂ))⁻¹‖)⁻¹ ≤ 3 := by
    rw [inv_eq_one_div]
    have hthird : (1:ℝ)/3 ≤ 1 - ‖(w + (k : ℂ))⁻¹‖ := by linarith
    calc 1 / (1 - ‖(w + (k : ℂ))⁻¹‖) ≤ 1 / (1/3) := one_div_le_one_div_of_le (by norm_num) hthird
      _ = 3 := by norm_num
  -- ‖u‖² = 1/‖w+k‖² = 1/((Re w+k)²+(Im w)²)  (exact).
  have husq : ‖(w + (k : ℂ))⁻¹‖ ^ 2 = 1 / ((w.re + k) ^ 2 + (w.im) ^ 2) := by
    rw [htv, div_pow, one_pow, hnormsq]
  calc ‖ZeroFreeBridge.binetTail w k‖
      ≤ ‖(w + (k : ℂ))⁻¹‖ ^ 2 * (1 - ‖(w + (k : ℂ))⁻¹‖)⁻¹ / 2 := hb
    _ ≤ ‖(w + (k : ℂ))⁻¹‖ ^ 2 * 3 / 2 := by
        have := mul_le_mul_of_nonneg_left hinv3 (sq_nonneg ‖(w + (k : ℂ))⁻¹‖)
        linarith
    _ = (3/2) * ‖(w + (k : ℂ))⁻¹‖ ^ 2 := by ring
    _ = (3/2) * (1 / ((w.re + k) ^ 2 + (w.im) ^ 2)) := by rw [husq]

/-! ## Remaining obligations for the EXACT charter cos-form (precise map).

    `binetTail_height_norm_le` sharpens the PER-TERM Binet bound; the corpus already provides the
    telescoped identity `μ_1(w) = −Σ_k binetTail w k` (`ZeroFreeBridge.digamma_sub_log_telescoped`
    + the unconditional anchor `ZeroFreeBridge.tendsto_digamma_sub_log`, `Re w ≥ 2`) and summability
    (`Summable (binetTail w)`).  So the immediate NEXT step — the honest large-height `μ_1` ENVELOPE
    `‖μ_1(w)‖ ≤ Σ_k (3/2)/((Re w+k)²+(Im w)²)` — needs only a closed form / integral-comparison
    (`AntitoneOn.sum_le_integral` with the arctan antiderivative `∫ 1/((c+x)²+b²) dx = arctan((c+x)/b)/b`)
    for the majorant sum.  That is a self-contained addition (no digamma internals).

    The EXACT cos-form `StirlingBinetWip.norm_binetRemK_le` (K ≥ 2) is a DIFFERENT, harder object and
    is blocked as follows.  `binetRemK w K = ψ(w) − log w − stirlingBernoulliTerms w K` with the
    Bernoulli peel `stirlingBernoulliTerms w K = −1/(2w) − Σ_{j=1}^{K−1} B_{2j}/(2j·w^{2j})`.  Two
    facts are missing, BOTH upstream of the tail engine (`em_tail_integral_bound_shifted` is ready
    to consume them):

      (A) A SERIES / EM representation of `Complex.digamma` tying it to the trigamma power tail
          `Σ (w+n)^{-2}`.  Mathlib has ONLY `digamma := logDeriv Gamma` (`Digamma.lean`) — no
          trigamma, no polygamma, no `hasSum` for `ψ` or `ψ'`.  The order-2 explicit peel of the
          `log(1+u)` series (Mathlib `norm_log_sub_logTaylor_le`, `logTaylor 3 u = u − u²/2`) has
          leading term `(1/2)Σ_k (w+k)^{-2}` — i.e. the trigamma — which is exactly what has no
          closed form.  So the Bernoulli peel cannot be IDENTIFIED against `ψ` without first building
          the digamma↔polygamma-series bridge.

      (B) The Bernoulli generating-function identity matching the collected `log(1+u)`-Taylor
          coefficients of the summed series to `B_{2j}/(2j)` (the Abel–Plana / EM closed form).

    Once (A) is available as `∫_N^∞ saw_{2K} · (falling coeff)·(w+x)^{-(2K)}`-shaped tail (via the
    order-raising `em_saw_step_window_cpow` on the trigamma summand), `em_tail_integral_bound_shifted`
    (with real exponent `a = 2K`) directly yields `‖μ_K(w)‖ ≤ B·‖c‖·(Re w+N)^{-(2K−1)}/(2K−1)` — an
    honest polynomial-rate variant of the cos-form, strong enough for the K = 4 Γℝ evaluator (its
    number at `w = 1/4 + 7i` beats the K = 1 envelope by ~10⁸, see the session report). -/

end ZetaReflection
