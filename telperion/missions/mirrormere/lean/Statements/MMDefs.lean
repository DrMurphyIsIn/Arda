/-
  Statements.MMDefs -- vocabulary mirror for the MIRRORMERE missions registry.  NOT a node
  statement.

  Definitions below are VERBATIM copies from the v4.32 islands (toolchain
  leanprover/lean4:v4.32.0), source module + line range cited above each extract:
  the Quasicrystal block from telperion/examples/quasicrystal/lean/ (TwoFreqRigidity,
  InvolutionDictionary, BoundaryLemmas), the RHLinalg/DefectDictionary blocks from
  telperion/examples/zeta_zero_localization/lean/ (RHLinalg/, DefectDictionary.lean,
  R2Rigidity.lean), the BraggDefect block from BraggDefect.lean.  To be
  regenerated/diffed by missions/mirrormere/build_mmdefs.py (grant-pass deliverable).

  ONE AUTHORED (non-verbatim) definition: `Quasicrystal.zetaOrdinates`.  The island
  keeps the ordinate set as a FREE variable (BoundaryLemmas takes `Ordinates : Set ℝ`);
  the registry's unconditional W2c nodes need it pinned.  Flagged for the blind
  read-back audit cycle.  conjecture1_proved = False.

  CONTEXT MIRROR (CI fix 2026-09-14): the island source files declare
  `noncomputable section` (TwoFreqRigidity.lean:36, InvolutionDictionary.lean:54,
  RHLinalg/PosIndex.lean:28, DefectDictionary.lean:53) and PosIndex.lean:30-31
  declares file-level `open Matrix Finset` + `open scoped ComplexOrder`; the
  original extraction dropped these, so the verbatim def bodies failed to compile
  here.  The section/open context below restores the sources' elaboration
  environment; the def bodies remain verbatim.
-/
import Mathlib

noncomputable section

namespace Quasicrystal

-- ===== TwoFreqRigidity.lean:40-42 (v4.32 quasicrystal island) =====
def twoFreq (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) : ℂ :=
  c₁ * Complex.exp ((lam₁ : ℂ) * x * Complex.I)
    + c₂ * Complex.exp ((lam₂ : ℂ) * x * Complex.I)

open Polynomial in
-- ===== InvolutionDictionary.lean:115-117 =====
def hardyZ (p : ℂ[X]) (u : ℂ) (ω x : ℝ) : ℂ :=
  u * Complex.exp (-(((p.natDegree : ℝ) * ω * x / 2 : ℝ) : ℂ) * Complex.I)
    * p.eval (Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I))

-- ===== BoundaryLemmas.lean:42-43 =====
def IsUniformlyDiscrete (S : Set ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → δ ≤ |x - y|

-- ===== BoundaryLemmas.lean:342-344 =====
def RvMUnboundedMeanDensity (S : Set ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ (F : Finset ℝ) (a L : ℝ),
    0 ≤ L ∧ (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ r * L + 1 < F.card

-- ===== AUTHORED for the registry (NOT in the island; BoundaryLemmas keeps
-- `Ordinates : Set ℝ` free).  The ordinates of the nontrivial zeta zeros. =====
def zetaOrdinates : Set ℝ :=
  {t : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im = t}

-- ===== AUTHORED for the recurrence dictionary (QC_RECURRENCE section 4.2 / W3d;
-- NOT in the island).  The recurrence deficit of an off-line displacement delta:
-- the algebraic identity recurrenceDeficit delta = e^delta + e^(-delta) - 2 ties
-- it to BraggDefect.excess at delta = 1/10 (node MM_recurrence_deficit_eq_excess). =====
noncomputable def recurrenceDeficit (δ : ℝ) : ℝ :=
  (Real.exp δ - 1) * (1 - Real.exp (-δ))

-- ===== AUTHORED for the torus-section ladder (QC_TORUS_SECTION_LADDER memo, T1;
-- NOT in the island).  The cut-and-project vocabulary: the orbit of the Kronecker
-- line through T^N, the linear form on the torus, and the 1-D exponential-sum
-- section.  twoFreq (verbatim above) is the N=2 instance under the dictionary
-- identity (node MM_torus_section_dictionary). =====
noncomputable def torusOrbit (N : ℕ) (lam : Fin N → ℝ) (x : ℂ) : Fin N → ℂ :=
  fun j => Complex.exp ((lam j : ℂ) * x * Complex.I)

def linearTorusForm (N : ℕ) (c : Fin N → ℂ) (z : Fin N → ℂ) : ℂ :=
  ∑ j, c j * z j

noncomputable def expSum (N : ℕ) (c : Fin N → ℂ) (lam : Fin N → ℝ) (x : ℂ) : ℂ :=
  ∑ j, c j * Complex.exp ((lam j : ℂ) * x * Complex.I)

end Quasicrystal

namespace RHLinalg

open Matrix Finset
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

-- ===== RHLinalg/Sylvester.lean:43-44 (v4.32 zeta_zero_localization island) =====
def hermForm (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ (A *ᵥ x))

-- ===== RHLinalg/Sylvester.lean:47-48 =====
def PosDefOn (A : Matrix n n 𝕜) (W : Submodule 𝕜 (n → 𝕜)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermForm A x

-- ===== RHLinalg/PosIndex.lean:41-42 =====
def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  #{i | 0 < hA.eigenvalues i}

end RHLinalg

namespace DefectDictionary

open Matrix Finset Submodule RHLinalg
open scoped ComplexOrder BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

-- ===== DefectDictionary.lean:73 =====
def defect {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ := posIndex hA.neg

-- ===== R2Rigidity.lean:74-80 =====
structure NegativeWitness {A : Matrix n n 𝕜} (hA : A.IsHermitian) (p : ℕ) where
  /-- the subspace on which `A` is negative definite -/
  W : Submodule 𝕜 (n → 𝕜)
  /-- `-A` is positive definite on `W` (i.e. `A` is negative definite there) -/
  posDefOn_neg : PosDefOn (-A) W
  /-- `W` has dimension exactly `p` -/
  finrank_eq : Module.finrank 𝕜 W = p

end DefectDictionary

namespace BraggDefect

-- ===== BraggDefect.lean:53 =====
def Aon : ℝ := 2

-- ===== BraggDefect.lean:56 =====
noncomputable def Aoff : ℝ := Real.exp (1 / 10) + Real.exp (-(1 / 10))

-- ===== BraggDefect.lean:60 =====
noncomputable def excess : ℝ := Aoff - Aon

-- ===== BraggDefect.lean:64 =====
def defectFunctional (d : ℝ) : ℝ := -(d ^ 2)

-- ===== BraggDefect.lean:68-69 =====
noncomputable def expLo : ℝ := (442068367230259049924676660787771898883 / 400000000000000000000000000000000000000 : ℝ)
noncomputable def expHi : ℝ := (11051709180756476248117094953514706601127 / 10000000000000000000000000000000000000000 : ℝ)

end BraggDefect

namespace RHInBoxAnalytic

open Complex Filter MeasureTheory Real
open scoped Topology

-- ===== RvMRHInBox.lean (v4.34 li_positivity island; cross-island vocabulary per
-- design section 2).  SUPPORT LEMMA carried as `sorry` HERE ONLY so that
-- `zeroFinset` elaborates: it is PROVED on the li island (same file) and is NOT
-- a registry node; the sorry is vocabulary scaffolding in the statement package,
-- the same trust class as the node statements themselves. =====
theorem divisor_ball_support_finite_of_one_notMem
    (c : ℂ) (R : ℝ) (hs1 : (1 : ℂ) ∉ Metric.ball c R) :
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).support.Finite := by sorry

-- ===== RvMRHInBox.lean:310-311 =====
noncomputable def zeroFinset (c : ℂ) (R : ℝ) (hs1 : (1 : ℂ) ∉ Metric.ball c R) : Finset ℂ :=
  (divisor_ball_support_finite_of_one_notMem c R hs1).toFinset

end RHInBoxAnalytic

namespace DiffractionCore

open Complex MeasureTheory Real
open scoped Topology

-- ===== RvMBraggBridge.lean:52-55 (v4.34 li_positivity island, W3b) =====
noncomputable def braggTerm (sigma1 T0 T1 : ℝ) (n : ℕ) : ℂ :=
  (LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) ((sigma1 : ℂ) + T1 * I) n
      - LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) ((sigma1 : ℂ) + T0 * I) n)
    / (-(I * (Real.log n : ℂ)))

end DiffractionCore

end
