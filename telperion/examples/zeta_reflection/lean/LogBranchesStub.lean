/-  LogBranchesStub.lean -- WS-A statement-level de-risk (A0).

    STATEMENT ONLY of the FTC bridge that A2 will discharge:

        argChangeVert_eq_im_log_sub

    "For `f` with a holomorphic branch `L` on a neighborhood of the vertical segment
     `{σ + i y : y ∈ [T0, T1]}`, with `L' = logDeriv f` pointwise there and `f` nonvanishing
     on the segment, the argument change UP the segment equals the imaginary-part difference
     of `L` at the endpoints:
        argChangeVert f σ T0 T1 = (L (σ + T1·i)).im − (L (σ + T0·i)).im."

    This is the FTC bridge that (per the ANDÚRIL plan) converts 4 of the 5 box-edge argument
    quantities from integrals to POINT evaluations.  It is stated here as a `def` of type `Prop`
    (NO `theorem`, NO `sorry`, NO `:= by ...`) purely to CONFIRM IT ELABORATES against the real
    `DiffractionCore.argChangeVert`.  A2 will restate it as a theorem and prove it.

    conjecture1_proved = False.
-/
import DiffractionCore

open Complex

namespace ZetaReflection

/-- Statement of the FTC bridge, as an elaboration-checked `Prop`-valued `def`.

    `L` is the holomorphic branch of `log f` on the segment neighborhood; `S` is an open set
    containing the segment on which `L` is analytic and agrees with the antiderivative of
    `logDeriv f`.  The `argChangeVert` symbol is the REAL one from `DiffractionCore`
    (`(∫ y in T0..T1, logDeriv f ((σ:ℂ) + y*I)).re`). -/
noncomputable def argChangeVert_eq_im_log_sub
    (f L : ℂ → ℂ) (σ T0 T1 : ℝ) (S : Set ℂ) : Prop :=
  -- hypotheses (as an implication chain inside the Prop):
  (T0 ≤ T1) →
  (IsOpen S) →
  -- the vertical segment lies in S
  (∀ y : ℝ, y ∈ Set.Icc T0 T1 → ((σ : ℂ) + (y : ℂ) * I) ∈ S) →
  -- L is holomorphic on S
  (AnalyticOnNhd ℂ L S) →
  -- L' = logDeriv f pointwise on S (L is a log-branch of f)
  (∀ z ∈ S, deriv L z = logDeriv f z) →
  -- f nonvanishing on the segment
  (∀ y : ℝ, y ∈ Set.Icc T0 T1 → f ((σ : ℂ) + (y : ℂ) * I) ≠ 0) →
  -- conclusion: argument change up the segment = Im(L(top)) − Im(L(bottom))
  DiffractionCore.argChangeVert f σ T0 T1
    = (L ((σ : ℂ) + (T1 : ℂ) * I)).im - (L ((σ : ℂ) + (T0 : ℂ) * I)).im

end ZetaReflection
