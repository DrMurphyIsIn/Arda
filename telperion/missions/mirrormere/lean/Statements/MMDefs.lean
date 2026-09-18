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

/-
  ===== CROSS-CAMPAIGN VOCABULARY MIRROR (2026-09-18, W3c goal authoring) =====
  The six definitions of the `WeilExplicit` namespace below are a VERBATIM copy of
  telperion/missions/rh/lean/Statements/RHDefs.lean lines 118-167 (branch rh/e8-statement,
  the AUTHORED E8 block), the same discipline as the RHInBoxAnalytic / DiffractionCore
  cross-island blocks above: the rh campaign owns them, MIRRORMERE mirrors them so its own
  goal statement elaborates standalone.  The upstream block is itself the verbatim vocabulary
  of the kernel-checked artifact telperion/examples/rvm_bridge/lean/E6Bridge4.lean
  (RvMBridge4.limit_explicit_formula, v4.33.0-rc2 island, on main).  SECOND COPY WARNING: any
  edit upstream must be mirrored here; build_mmdefs.py (grant-pass deliverable) is to diff
  both copies.  The block elaborates unchanged at the v4.32.0 pin (Complex.digamma is present
  at this Mathlib rev: Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean).
  Two AUTHORED definitions (`autocorr`, `weilForm`) are appended inside the namespace and are
  flagged AUTHORED where they appear.  conjecture1_proved = False.
-/
namespace WeilExplicit
open MeasureTheory Complex

-- ===== AUTHORED for the registry (NOT in the island; 2026-09-18 E8 limit explicit formula,
-- design memo telperion/docs/E8_LIMIT_EXPLICIT_FORMULA_DESIGN_2026-09-18.md).  Vocabulary for
-- RH_limit_explicit_formula: the Weil 1952 / Guinand 1948 identity on the class of smooth
-- compactly supported complex test functions g on the line (Iwaniec-Kowalski Thm 5.12 shape).
-- The test function lives on the PRIME (direct) side; its transform weilKernel g is an ENTIRE
-- function of s defined by one Bochner integral, so its values at off-line zeros are literal
-- (no analytic continuation -- this is what survives the Paley-Wiener obstruction, roadmap D3).
-- Compact support makes the prime side a FINITE sum, so the PNT growth Sum Lambda(n)/sqrt n
-- ~ 2e^{R/2} (roadmap section 1) never enters.  Smoothness index is C^infinity, written
-- ((top : ENat) : WithTop ENat); top alone would mean ANALYTIC and, with compact support on
-- the line, collapse the class to {0}.  No evenness hypothesis: the identity holds for every
-- g in the class (numerically checked with a shifted Gaussian, memo section 4). =====

/-- The E8 test class: smooth, compactly supported g : R -> C. -/
def IsWeilTest (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g

/-- H_g(s) = ∫ g(u) e^{(s - 1/2) u} du, the zero-side transform.  With s = 1/2 + i r this is
    h(r) = ∫ g(u) e^{i r u} du (the Iwaniec-Kowalski pair); entire for compactly supported g,
    so H_g(ρ) at a zero ρ = 1/2 + iγ is h(γ) with γ complex when ρ is off the line.
    H_g(0) = h(i/2) and H_g(1) = h(-i/2) are the two pole terms. -/
noncomputable def weilKernel (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp ((s - 1 / 2) * (u : ℂ))

/-- Multiplicity of ρ as a nontrivial zero: the order of ζ at ρ on the open critical strip
    (0 off the strip and at non-zeros).  The SAME divisor expression as
    RvMCount.zetaZeroCount, so the E8 zero side and the RvM count carry identical weights. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ :=
  ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat

/-- The archimedean integrand h(r) · Re ψ(1/4 + i r/2), ψ = Γ'/Γ = Complex.digamma. -/
noncomputable def archIntegrand (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  weilKernel g (1 / 2 + (r : ℂ) * I) * ((Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)).re : ℂ)

/-- The archimedean side: h(i/2) + h(-i/2) - g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + i r/2) dr. -/
noncomputable def archSide (g : ℝ → ℂ) : ℂ :=
  weilKernel g 0 + weilKernel g 1 - g 0 * (Real.log Real.pi : ℂ)
    + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, archIntegrand g r

/-- The prime side: Σ_n Λ(n)/√n · (g(log n) + g(-log n)); a finite sum for compactly
    supported g (Λ(0) = Λ(1) = 0; the two terms are the two vertical edges of the finite
    explicit formula rect_explicit_formula in the T → ∞ limit). -/
noncomputable def primeSide (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (g (Real.log n) + g (-Real.log n))

-- ===== AUTHORED for the MIRRORMERE registry (NOT in any island, NOT in RHDefs): the two
-- definitions the W3c membership goal needs on top of the mirrored E8 vocabulary.  Design
-- memo telperion/docs/MM_w3c_goal_weil_membership_DESIGN_2026-09-18.md.  Flagged for the
-- blind read-back audit cycle.  conjecture1_proved = False. =====

/-- AUTHORED.  The Hermitian autocorrelation `g ⋆ g̃` with `g̃ u = conj (g (-u))`:
    `(g ⋆ g̃) u = ∫ g v * conj (g (v - u)) dv`.  For `g` smooth and compactly supported so is
    `autocorr g` (Mathlib compact-support convolution smoothness), so `archSide`/`primeSide`
    take honest values on it and the membership statement is not a junk-value sentence.
    Its transform factors: `weilKernel (autocorr g) s = weilKernel g s * conj (weilKernel g
    (1 - conj s))`, which on the critical line `s = 1/2 + i r`, `r : ℝ`, is `‖h (r)‖ ^ 2` —
    the Weil-criterion positivity shape.  `autocorr g` is Hermitian-even, NOT even: its
    imaginary part is odd (E8 memo section 3.4), which is why the mirrored class keeps `g`
    complex-valued with no parity hypothesis. -/
noncomputable def autocorr (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, g v * (starRingEnd ℂ) (g (v - u))

/-- AUTHORED.  The Weil functional READ FROM THE PRIMES SIDE: `archSide f - primeSide f`.
    By the kernel-checked E8 limit explicit formula (`RvMBridge4.limit_explicit_formula`,
    rvm_bridge island, node `RH_limit_explicit_formula`) this value is exactly the zero-side
    sum `∑_ρ zeroMult ρ * weilKernel f ρ`, so `weilForm` is the diffraction pairing of the
    regularized triple (zero comb against `h`, prime comb against `g`, archimedean density
    against `h`) with NO temperedness claim about any comb (the naive dual-comb temperedness
    clause is unconditionally false, roadmap section 1). -/
noncomputable def weilForm (f : ℝ → ℂ) : ℂ := archSide f - primeSide f

end WeilExplicit

end
