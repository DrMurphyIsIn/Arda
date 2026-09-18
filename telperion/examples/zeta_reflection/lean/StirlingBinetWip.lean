/-  StirlingBinetWip.lean -- A2 Theorem 2, WORK IN PROGRESS: the K ≥ 2 Bernoulli tail.

    NOT guard-imported and NOT a `defaultTargets` member.  This file carries the ARCHITECTURE of
    the higher-order (`K ≥ 2`, up to the `K = 4` charter target) Binet remainder, which SHARPENS
    the rate of the enclosure proven in `StirlingBinet.lean` (the fully-discharged `K = 1` /
    order-`1/w` instance) but is not required by the consumer: the interval evaluator only needs a
    VALID envelope, and `logDeriv_gammaR_enclosure` already supplies one.  The `K = 4` form is the
    charter's stated target because it makes the per-band remainder negligible at large height with
    a small shift `m`; it is a rate improvement, not a correctness prerequisite.

    Contains `sorry` PLACEHOLDERS marking the exact analytic obligations still to discharge.  Per
    ANDÚRIL house rule these live ONLY here, never in the guard-imported `StirlingBinet.lean`.
    conjecture1_proved = False.

    ────────────────────────────────────────────────────────────────────────────────────────────
    THE HIGHER-ORDER STIRLING/BINET SERIES (target of this file)
    ────────────────────────────────────────────────────────────────────────────────────────────
    The digamma Stirling expansion is

        ψ(w) = log w − 1/(2w) − Σ_{j=1}^{K−1} B_{2j}/(2j · w^{2j}) + μ_K(w),

    with the Binet remainder bound (charter form)

        |μ_K(w)| ≤ |B_{2K}| / ( (2K−1)(2K) · |w|^{2K−1} · cos^{2K}(arg w / 2) ).

    Bernoulli constants needed for `K = 4` (Mathlib `bernoulli`, `NumberTheory.Bernoulli`):
        B_2 = 1/6,  B_4 = −1/30,  B_6 = 1/42,  B_8 = −1/30.
    (Mathlib evaluates these via the recursive `bernoulli'_def`; a once-proven finite lemma list
    `j ≤ 4` — plain rational equalities — supplies them.  Note `decide`/`norm_num` do NOT close
    `bernoulli 4 = −1/30` directly on this pin; use `bernoulli`'s functional-equation unfold or an
    explicit `simp [bernoulli, bernoulli'_def, Finset.sum_range_succ]` chain.  Deferred here.)

    The `K = 1` file already proves the leading piece with the corpus telescoping bound
    `|μ_1(w)| ≤ 1/(Re w − 1)` (weaker constant than the charter `cos`-form, but a valid envelope).
    This file upgrades `μ_1 → μ_K` by (i) peeling the explicit `−1/(2w) − Σ B_{2j}/(2j w^{2j})`
    terms from `ψ` and (ii) bounding the tail integral by the Binet cos-form.
-/
import StirlingBinet

open Complex

namespace ZetaReflection

/-- The explicit Bernoulli-weighted Stirling terms peeled from `ψ` at order `K`:
    `−1/(2w) − Σ_{j=1}^{K−1} B_{2j}/(2j · w^{2j})`.  For `K = 1` this is empty + `−1/(2w)`;
    the `K = 1` file folds the `−1/(2w)` into the `O(1/w)` remainder rather than peeling it. -/
noncomputable def stirlingBernoulliTerms (w : ℂ) (K : ℕ) : ℂ :=
  -(1 / (2 * w))
    - ∑ j ∈ Finset.Icc 1 (K - 1),
        ((bernoulli (2 * j) : ℚ) : ℂ) / (2 * j * w ^ (2 * j))

/-- The order-`K` Binet remainder of `ψ`: `μ_K(w) = ψ(w) − log w − stirlingBernoulliTerms w K`. -/
noncomputable def binetRemK (w : ℂ) (K : ℕ) : ℂ :=
  Complex.digamma w - Complex.log w - stirlingBernoulliTerms w K

/-- The charter Binet remainder envelope (`K`-th order, `cos`-form):
    `|B_{2K}| / ((2K−1)(2K) · |w|^{2K−1} · cos^{2K}(arg w / 2))`. -/
noncomputable def binetEnvelopeK (w : ℂ) (K : ℕ) : ℝ :=
  |((bernoulli (2 * K) : ℚ) : ℝ)|
    / ((2 * K - 1) * (2 * K) * ‖w‖ ^ (2 * K - 1)
        * Real.cos (Complex.arg w / 2) ^ (2 * K))

/-- **OBLIGATION K-i (peeling identity).**  `ψ(w)` equals `log w` plus the explicit Bernoulli
    terms plus the order-`K` remainder — a DEFINITIONAL rearrangement of `binetRemK`, so this one
    is immediate; recorded to fix the statement shape the analytic obligations feed. -/
theorem digamma_stirling_peel (w : ℂ) (K : ℕ) :
    Complex.digamma w
      = Complex.log w + stirlingBernoulliTerms w K + binetRemK w K := by
  unfold binetRemK
  ring

/-- **OBLIGATION K-ii (the charter remainder bound).**  `‖μ_K(w)‖ ≤ binetEnvelopeK w K` on the
    region `Re w ≥ 1/4` (equivalently `|arg w| < π`, `cos(arg w/2) > 0`).

    This is the genuine analytic content still to prove: the Binet integral representation
    `μ_K(w) = (−1)^K ∫_0^∞ (…P_{2K}(t)…) e^{−wt} dt` (or the Euler–Maclaurin tail of the digamma
    series) bounded by the stated `cos`-form.  Mathlib has neither the Binet integral nor the
    saddle bound at this order; `em-zeta`'s `em_zeta_enclosure` remainder machinery is the natural
    shared engine (both are Euler–Maclaurin tails).  DEFERRED. -/
theorem norm_binetRemK_le {w : ℂ} (hw : (1 / 4 : ℝ) ≤ w.re) (K : ℕ) (hK : 1 ≤ K) :
    ‖binetRemK w K‖ ≤ binetEnvelopeK w K := by
  sorry

/-- **OBLIGATION K-iii (`K = 4` specialization).**  The charter's first-needed instance: the
    order-4 Stirling form of `logDeriv Γℝ` with the explicit `B_2,B_4,B_6` peeled and the `μ_4`
    envelope.  Assembles `digamma_stirling_peel` (K=4) into `logDeriv_gammaR_stirling` and applies
    `norm_binetRemK_le` at `K = 4`.  Blocked only on OBLIGATION K-ii.  DEFERRED. -/
theorem logDeriv_gammaR_stirling4 {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    ‖logDeriv Complex.Gammaℝ z
        - (-(Real.log Real.pi : ℂ) / 2
            + (1 / 2) * Complex.log (z / 2)
            + (1 / 2) * stirlingBernoulliTerms (z / 2) 4)‖
      ≤ (1 / 2) * binetEnvelopeK (z / 2) 4 := by
  sorry

end ZetaReflection
