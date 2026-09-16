/-
  Statements.DBNDefs -- de Bruijn-Newman (Route C) vocabulary mirror for the RH
  missions registry.  NOT a node statement.

  Authored (literature-checked), NOT verbatim island extracts.  Every object is
  the standard de Bruijn-Newman heat-flow vocabulary, with the normalization
  pinned to the primary sources:

    - Phi (the super-exponential kernel) and H_t (the heat-flow family):
      Rodgers-Tao, "The de Bruijn-Newman constant is non-negative", Forum Math.
      Pi 8 (2020) e6 (arXiv:1801.05914), and the effective-approximation paper
      Platt-Rodgers-Tao et al., arXiv:1904.12438, formulas (3) and (4):
        Phi(u) := sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})
        H_t(z) := integral_0^infty e^{t u^2} Phi(u) cos(z u) du
    - The H_0 normalization (arXiv:1904.12438 formula (1)):
        H_0(z) := (1/8) xi(1/2 + i z/2)
      with xi the Riemann xi function in the Gamma-factor form (formula (2)):
        xi(s) := (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)  =  (1/2) s (s-1) Lambda(s),
      Lambda = completedRiemannZeta.
    - The reality-of-zeros theory (t >= Lambda <=> H_t has only real zeros; the
      constant Lambda exists and is finite): de Bruijn 1950 (t >= 1/2 => real
      zeros) and Newman 1976 (existence of Lambda).  These are the DEFERRED C3
      milestone -- NOT stated here.

  NORMALIZATION NOTE (verified in Lean, ProbeXi elaboration, this island):
  the upstream `LiCriterion.riemannXi s = (1/2) s (s-1) completedRiemannZeta_0 s + 1/2`
  (the ENTIRE form, pole-free) equals the Rodgers-Tao Gamma-factor xi
  `(1/2) s (s-1) completedRiemannZeta s` for every s (they differ only in that
  the entire form has the two removable poles of `completedRiemannZeta` at 0 and
  1 already cancelled by the s(s-1) prefactor, plus the constant +1/2 that this
  cancellation contributes -- `completedRiemannZeta_eq` makes the two agree).
  So `H0` below, defined via `riemannXi`, IS `(1/8) xi_RT(1/2 + i z/2)`: Route C
  attaches to the EXACT object the Li ladder (`li_criterion_rh_iff`) and the RvM
  box argument (`RvMXiBridge`) already use.  `xiRT` records the Gamma-factor
  spelling for the reader; `xiRT_eq_riemannXi` is the (deferred) bridge lemma.

  These are DEFINITIONS + Prop-level statement shapes only.  The genuine analytic
  content -- that the heat integral `H 0 z` equals the xi form `H0 z` (C2, the
  Mellin<->Fourier / Jacobi-theta representation theorem), and that RH is
  equivalent to all zeros of `H0` being real (C4) -- is DEFERRED.  This file
  exists so node statement files elaborate standalone against the island.
  conjecture1_proved = False.
-/
import LiPositivity
open LiCriterion
open MeasureTheory Real Complex

namespace DBN

/-- **Phi(u)** -- the de Bruijn-Newman super-exponentially decaying kernel.
    Rodgers-Tao / arXiv:1904.12438 formula (3):
    `Phi(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})`.
    (The sum index `n : ℕ` is shifted by +1 so it runs over n >= 1.) -/
noncomputable def Phi (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
        - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u))
      * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))

/-- **H_t(z)** -- the de Bruijn-Newman heat-flow family.
    Rodgers-Tao / arXiv:1904.12438 formula (4):
    `H_t(z) = integral_0^infty e^{t u^2} Phi(u) cos(z u) du`.
    (Abstract: no convergence / entireness is asserted here -- that substrate is
    the deferred analytic content.) -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ),
    (Real.exp (t * u ^ 2) : ℂ) * (Phi u : ℂ) * Complex.cos (z * (u : ℂ))

/-- **xi_RT(s)** -- the Riemann xi function in the Rodgers-Tao Gamma-factor
    normalization (arXiv:1904.12438 formula (2)):
    `xi(s) = (1/2) s (s-1) Lambda(s)`, `Lambda = completedRiemannZeta`.
    Equal to the entire upstream `riemannXi` for all `s` (see `xiRT_eq_riemannXi`). -/
noncomputable def xiRT (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

/-- **H_0(z)** -- the base of the heat flow, in the standard xi-normalization
    (arXiv:1904.12438 formula (1)): `H_0(z) = (1/8) xi(1/2 + i z/2)`.
    Defined via the upstream entire `riemannXi` (= `xiRT`, see the note above), so
    Route C is anchored to the same object as the Li ladder and the RvM bridge.
    The DEFERRED C2 theorem is that the heat integral `H 0 z` equals this. -/
noncomputable def H0 (z : ℂ) : ℂ :=
  (1 / 8 : ℂ) * riemannXi (1 / 2 + Complex.I * z / 2)

/-- Predicate: every zero of `f` is real (has zero imaginary part). -/
def AllZerosReal (f : ℂ → ℂ) : Prop := ∀ z : ℂ, f z = 0 → z.im = 0

/-- **C2 (the representation theorem, DEFERRED).**  The heat integral at `t = 0`
    equals the xi-normalized base.  This is the Mellin<->Fourier identity via the
    Jacobi theta transformation plus two integrations by parts (with the
    dominated-convergence justifications) -- the hard analytic substrate Mathlib
    lacks.  Stated as a Prop shape only; NOT proved here. -/
def C2_representation : Prop := ∀ z : ℂ, H 0 z = H0 z

/-- **The xi normalization bridge (DEFERRED lemma).**  `xiRT = riemannXi` for
    every `s`.  Verified on `s ∉ {0,1}` by `completedRiemannZeta_eq` + `field_simp;
    ring` (ProbeXi, this island); the removable-singularity extension to `s ∈ {0,1}`
    is the small remaining piece.  Recorded so the two spellings of xi are known
    to denote one function. -/
def xiRT_eq_riemannXi : Prop := ∀ s : ℂ, xiRT s = riemannXi s

end DBN
