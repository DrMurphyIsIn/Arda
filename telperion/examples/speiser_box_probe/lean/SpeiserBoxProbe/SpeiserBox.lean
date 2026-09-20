/-
  # MM_speiser_box_probe -- the Face-7 pilot box for `zeta'`

  ## SCOPE, stated once and meant literally

  Target: `deriv riemannZeta` has no zero in the closed rectangle `[1/4, 3/8] x [6, 10]`.

  This is **NOT** the Speiser wall.  Speiser (1935) showed that non-vanishing of `zeta'`
  on the *whole* open left strip `0 < re s < 1/2` is *equivalent* to the Riemann
  Hypothesis.  A single bounded rectangle is a finitely-checkable probe of the winding
  certificate *face*, retargeted from `zeta` to `zeta'`.  Verifying it -- or a thousand
  like it -- decides nothing whatsoever about RH, because the Speiser equivalence consumes
  the strip as a whole and no finite union of boxes exhausts it.  Nothing in this file is
  a step toward RH.  `conjecture1_proved = False`.

  ## What is proved here, unconditionally and in-kernel

  * `convex_box`, `gridSet_subset_box`, `box_covered` -- the box is convex and the eight
    explicit grid points form a `13/50`-net of it.  Pure geometry, kernel-clean.
  * `hasDerivWithinAt_zeta_deriv` -- `deriv riemannZeta` is complex-differentiable on the
    box, with derivative `deriv (deriv riemannZeta)`.  Derived from Mathlib's
    `differentiableAt_riemannZeta` via analyticity; kernel-clean.
  * `speiser_box_probe_of_numeric` -- the box claim, **modulo exactly two named numeric
    obligations** (`SecondDerivBoundOnBox`, `GridModulusLowerBound`) and nothing else.

  ## What is NOT proved here

  The two numeric obligations below.  They are the entire remaining content, and they are
  stated so that they can be attacked cold, without reading anything else in this repo.
  They are *not* `sorry` in disguise: they are hypotheses of the theorem, and the theorem
  is honest about needing them.

  ## Why this route instead of a winding integral

  The node's discharge note budgeted for "second-derivative machinery for the winding
  integrand", because a winding certificate for `zeta'` integrates `zeta''/zeta'` and so
  needs a *numerical evaluator* for `zeta''` along the contour.  The grid-modulus
  instrument (`GridNonvanishing.lean`) needs only a crude *uniform upper bound* on
  `zeta''` plus finitely many point lower bounds on `zeta'`.  That is strictly less
  numerical machinery, and the box's geometry makes it cheap: the box is only `1/8` wide
  while `|zeta'|` on it is bounded below by roughly `0.191` and `|zeta''|` above by roughly
  `0.283`, so a *single column of eight points* suffices.  The trade-off is that this
  instrument certifies zero-freeness only; it cannot certify a nonzero zero count, which a
  genuine winding certificate can.
-/
import Mathlib
import SpeiserBoxProbe.GridNonvanishing

open Complex

namespace SpeiserBoxProbe

/-! ## The box -/

/-- The concrete probe rectangle `[1/4, 3/8] x [6, 10]`, strictly left of the critical
    line `re s = 1/2`. -/
def box : Set ℂ := {z : ℂ | 1 / 4 ≤ z.re ∧ z.re ≤ 3 / 8 ∧ 6 ≤ z.im ∧ z.im ≤ 10}

theorem mem_box {z : ℂ} :
    z ∈ box ↔ 1 / 4 ≤ z.re ∧ z.re ≤ 3 / 8 ∧ 6 ≤ z.im ∧ z.im ≤ 10 := Iff.rfl

theorem convex_box : Convex ℝ box := by
  rintro x ⟨hx1, hx2, hx3, hx4⟩ y ⟨hy1, hy2, hy3, hy4⟩ a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      add_zero] <;> nlinarith

/-! ## The certificate grid: one column of eight points at `re = 5/16` -/

/-- The eight grid points, all on the vertical line `re s = 5/16` (the box's mid-line),
    at imaginary parts `25/4, 27/4, ..., 39/4` (i.e. `6.25, 6.75, ..., 9.75`). -/
def gridSet : Set ℂ :=
  {⟨5 / 16, 25 / 4⟩, ⟨5 / 16, 27 / 4⟩, ⟨5 / 16, 29 / 4⟩, ⟨5 / 16, 31 / 4⟩,
   ⟨5 / 16, 33 / 4⟩, ⟨5 / 16, 35 / 4⟩, ⟨5 / 16, 37 / 4⟩, ⟨5 / 16, 39 / 4⟩}

theorem gridSet_subset_box : gridSet ⊆ box := by
  rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- One cell of the net: the half-width in `re` is `1/16`, the half-height in `im` is
    `1/4`, so the half-diagonal is `sqrt(1/256 + 1/16) = sqrt 17 / 16 < 13/50`. -/
private theorem cell (z : ℂ) (c : ℝ)
    (hx1 : 1 / 4 ≤ z.re) (hx2 : z.re ≤ 3 / 8)
    (hy1 : c - 1 / 4 ≤ z.im) (hy2 : z.im ≤ c + 1 / 4) :
    ‖z - (⟨5 / 16, c⟩ : ℂ)‖ ≤ 13 / 50 := by
  refine norm_sub_le_of_sq_le (by norm_num) ?_
  have hre : (⟨(5 : ℝ) / 16, c⟩ : ℂ).re = 5 / 16 := rfl
  have him : (⟨(5 : ℝ) / 16, c⟩ : ℂ).im = c := rfl
  rw [hre, him]
  nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2),
             mul_nonneg (sub_nonneg.2 hy1) (sub_nonneg.2 hy2)]

/-- The eight grid points form a `13/50`-net of the box. -/
theorem box_covered : ∀ z ∈ box, ∃ g ∈ gridSet, ‖z - g‖ ≤ 13 / 50 := by
  rintro z ⟨hx1, hx2, hy1, hy2⟩
  rcases le_or_gt z.im (13 / 2) with h | h
  · exact ⟨_, Or.inl rfl, cell z (25 / 4) hx1 hx2 (by linarith) (by linarith)⟩
  rcases le_or_gt z.im 7 with h' | h'
  · exact ⟨_, Or.inr (Or.inl rfl), cell z (27 / 4) hx1 hx2 (by linarith) (by linarith)⟩
  rcases le_or_gt z.im (15 / 2) with h'' | h''
  · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)),
      cell z (29 / 4) hx1 hx2 (by linarith) (by linarith)⟩
  rcases le_or_gt z.im 8 with h₃ | h₃
  · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      cell z (31 / 4) hx1 hx2 (by linarith) (by linarith)⟩
  rcases le_or_gt z.im (17 / 2) with h₄ | h₄
  · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      cell z (33 / 4) hx1 hx2 (by linarith) (by linarith)⟩
  rcases le_or_gt z.im 9 with h₅ | h₅
  · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      cell z (35 / 4) hx1 hx2 (by linarith) (by linarith)⟩
  rcases le_or_gt z.im (19 / 2) with h₆ | h₆
  · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
      cell z (37 / 4) hx1 hx2 (by linarith) (by linarith)⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))),
      cell z (39 / 4) hx1 hx2 (by linarith) (by linarith)⟩

/-! ## Holomorphy of `zeta'` on the box (kernel-derived from Mathlib) -/

theorem box_subset_compl_one : box ⊆ ({1} : Set ℂ)ᶜ := by
  rintro z ⟨_, _, hy1, _⟩ hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz] at hy1
  norm_num at hy1

theorem zeta_analyticOnNhd : AnalyticOnNhd ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt)
    isOpen_compl_singleton

theorem zeta_deriv_analyticOnNhd : AnalyticOnNhd ℂ (deriv riemannZeta) ({1} : Set ℂ)ᶜ :=
  zeta_analyticOnNhd.deriv

/-- `deriv riemannZeta` is complex-differentiable at every point of the box, with
    derivative `deriv (deriv riemannZeta)`. -/
theorem hasDerivWithinAt_zeta_deriv :
    ∀ z ∈ box, HasDerivWithinAt (deriv riemannZeta) (deriv (deriv riemannZeta) z) box z :=
  fun z hz =>
    ((zeta_deriv_analyticOnNhd z (box_subset_compl_one hz)).differentiableAt.hasDerivAt
      ).hasDerivWithinAt

/-! ## The two numeric obligations

The *entire* remaining content of the probe.  Neither is proved here or anywhere else in
this repository.

**The concrete attack route, for whoever takes these cold.**  This repository already
contains an unconditional, kernel-proved Euler-Maclaurin evaluator for `riemannZeta` on
the island `telperion/examples/zeta_reflection/lean/` -- and it is pinned to the SAME
Mathlib (`leanprover/lean4:v4.32.0`) as this island, so no version migration is needed.
The load-bearing pieces are:

* `ZetaReflection.em_zeta_strip3_enclosure` (`EMZetaTail.lean`) -- an order-3
  Euler-Maclaurin enclosure `‖riemannZeta s - emZetaFinite3 s N‖ ≤ ...`, parametric in
  `s` and the cut `N`, valid on `0 < s.re`, `s ≠ 1, -1, -2`.  Our box has `s.re ≥ 1/4`
  and `s.im ≥ 6`, so every side condition is immediate.
* `ZetaEMSum.emZetaFinite3_eq_dirichlet` -- rewrites the finite part as an elementary
  Dirichlet sum `∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) + ...`, removing the integral.
* `TrigReduce` / `CertVerify` / `ArctanTaylor` -- a dyadic interval-arithmetic (no `sorry`)
  evaluator for `cos`, `sin` and `log`, which is what turns `(n : ℂ) ^ (-s)` into rational
  brackets (`ForgeZ14Terms.lean` does exactly this for `s = 1/2 + 14i`).

What is missing is the DERIVATIVE variant: the same saw-Bernoulli representation
differentiated once (for `zeta'`, giving N2) and twice (for `zeta''`, giving N1).  That is
the "second-derivative machinery" the node's discharge note budgeted for, and it is real
work, not a rewrite -- differentiating under the `Ioi` integral and re-deriving the tail
bound.  N2 needs the result at eight isolated points; N1 needs it uniformly over a
continuum, so N1 additionally needs a subdivision sweep (or a monotone envelope) on top.

N1 is therefore strictly the harder of the two. -/

/-- **Numeric obligation N1 (uniform second-derivative bound).**

    `‖zeta''(s)‖ ≤ 3/10` for every `s` in the closed box `[1/4, 3/8] x [6, 10]`.

    This is the *only* infinitary obligation, and the harder of the two.  A numerical
    sweep gives `sup |zeta''| = 0.2823...` on the box, so the claimed constant `3/10`
    carries about a 6% margin.

    `3/10` is a tunable, not a cliff: `nonvanishing_of_grid` is parametric in `M`, and
    weakening `M` only requires refining the grid so that `M * delta < L` still holds.
    With `M = 1` a single column of 40 points suffices.  What it is NOT is reachable by a
    Cauchy estimate off a crude `|zeta|` bound -- on a disc large enough to be useful the
    resulting `M` is of order `10^4`, which would demand a grid of some `10^9` points, so
    the evaluator route above is the only practical one. -/
def SecondDerivBoundOnBox : Prop :=
  ∀ z ∈ box, ‖deriv (deriv riemannZeta) z‖ ≤ 3 / 10

/-- **Numeric obligation N2 (eight point lower bounds).**

    `‖zeta'(5/16 + i t)‖ ≥ 1/10` for `t in {25/4, 27/4, 29/4, 31/4, 33/4, 35/4, 37/4, 39/4}`.

    Eight isolated point evaluations.  The true values are
    `0.20198, 0.21718, 0.23576, 0.25784, 0.28361, 0.31330, 0.34713, 0.38536`,
    so the claimed floor `1/10` carries a factor of at least `2.01`. -/
def GridModulusLowerBound : Prop :=
  ∀ g ∈ gridSet, (1 : ℝ) / 10 ≤ ‖deriv riemannZeta g‖

/-- N2 in fully expanded, point-by-point form, for a cold attacker. -/
theorem gridModulusLowerBound_of_points
    (h1 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 25 / 4⟩‖)
    (h2 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 27 / 4⟩‖)
    (h3 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 29 / 4⟩‖)
    (h4 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 31 / 4⟩‖)
    (h5 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 33 / 4⟩‖)
    (h6 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 35 / 4⟩‖)
    (h7 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 37 / 4⟩‖)
    (h8 : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta ⟨5 / 16, 39 / 4⟩‖) :
    GridModulusLowerBound := by
  rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption

/-! ## The probe -/

/-- **The Face-7 pilot box, modulo its two numeric obligations.**

    Given the uniform bound `‖zeta''‖ ≤ 3/10` on the box (N1) and the eight point lower
    bounds `‖zeta'‖ ≥ 1/10` on the grid (N2), `zeta'` has no zero in
    `[1/4, 3/8] x [6, 10]`.

    The gap condition that makes the certificate close is `(3/10) * (13/50) = 39/500 < 1/10`,
    re-derived below by `norm_num` from the constants themselves rather than asserted.

    NOT the Speiser wall; not a step toward RH.  `conjecture1_proved = False`. -/
theorem speiser_box_probe_of_numeric
    (hM : SecondDerivBoundOnBox) (hL : GridModulusLowerBound) :
    ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 8 → 6 ≤ s.im → s.im ≤ 10 →
      deriv riemannZeta s ≠ 0 := by
  intro s h1 h2 h3 h4
  exact nonvanishing_of_grid convex_box hasDerivWithinAt_zeta_deriv hM box_covered
    gridSet_subset_box hL (by norm_num) s ⟨h1, h2, h3, h4⟩

end SpeiserBoxProbe
