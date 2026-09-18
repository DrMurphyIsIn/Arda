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

  ADDED 2026-09-18 (MIRRORMERE D3 authoring, node MM_weil_form_certified_height): a second
  MIRROR block `WeilExplicit` -- the six E8 definitions carried VERBATIM from the v4.34
  missions/rh RHDefs.lean AUTHORED block (branch rh/e8-statement), the same text that
  examples/rvm_bridge/lean/E6Bridge4.lean mirrors at v4.33.0-rc2, so a cross-island grant's
  normalized-containment gate can fire -- and an AUTHORED block `MMWeil` (autocorr, weilForm,
  zeroSideBelow), Weil's functional in g-coordinates.  Design memo:
  telperion/docs/MM_mm-d3-certified-height-weil-bound_DESIGN_2026-09-18.md.

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

namespace WeilExplicit

open MeasureTheory Complex

-- ===== MIRROR of the AUTHORED `WeilExplicit` block of
-- missions/rh/lean/Statements/RHDefs.lean (branch rh/e8-statement, v4.34 island), carried
-- here VERBATIM as the v4.32 copy; the same six definitions are mirrored verbatim in
-- examples/rvm_bridge/lean/E6Bridge4.lean (v4.33.0-rc2, the E8 proof island).  The node
-- MM_weil_form_certified_height is stated in this vocabulary, so `zeroMult`, `weilKernel`,
-- `archSide` and `primeSide` must read here EXACTLY as they read there or the cross-island
-- grant gate (normalized containment) cannot fire.  Flagged for the blind read-back audit
-- cycle.  conjecture1_proved = False. =====

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

end WeilExplicit

namespace MMWeil

open MeasureTheory Complex WeilExplicit

-- ===== AUTHORED for the D3 reformulation (routes-roadmap D3, memo
-- MM_mm-d3-certified-height-weil-bound_DESIGN_2026-09-18.md; NOT in any island).  Weil's
-- positivity functional in g-COORDINATES: the test function on the prime side is the
-- autocorrelation f = g ⋆ g~ (g~(u) = conj (g (-u))), whose transform factors as
-- H_f(s) = H_g(s) · conj (H_g (1 - conj s)) -- equal to ‖H_g(s)‖² exactly on Re s = 1/2
-- (the on-line square channel, the emit_unit_modulus_sos shape), and NOT a square off it.
-- Off-line values of H_g are literal (the transform is entire), so the Paley-Wiener
-- obstruction that refuted the band-limited D3 does not arise.  conjecture1_proved = False. =====

/-- The autocorrelation f = g ⋆ g~ with g~(u) = conj (g (-u)), written as the correlation
    integral: (g ⋆ g~)(u) = ∫ g(u + v) conj (g v) dv.  Smooth with compact support when g is
    (a classical convolution fact, carried as the hypothesis `IsWeilTest (autocorr g)`). -/
noncomputable def autocorr (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => ∫ v : ℝ, g (u + v) * (starRingEnd ℂ) (g v)

/-- Weil's functional read off the PRIMES side: W(f) = archSide f - primeSide f.  By the
    limit explicit formula (RH_limit_explicit_formula, proved on the rvm_bridge island) this
    equals the zero-side sum Σ_ρ m(ρ) H_f(ρ); Weil positivity is the assertion that
    W (autocorr g) has nonnegative real part for every test g. -/
noncomputable def weilForm (f : ℝ → ℂ) : ℂ :=
  WeilExplicit.archSide f - WeilExplicit.primeSide f

/-- The zero-side summand truncated at height T: the E8 summand m(ρ) H_f(ρ) for |Im ρ| ≤ T
    and 0 beyond it.  Summing this family is the CERTIFIED-HEIGHT part of the zero side --
    the part the zero ladder controls. -/
noncomputable def zeroSideBelow (f : ℝ → ℂ) (T : ℝ) (ρ : ℂ) : ℂ :=
  if |ρ.im| ≤ T then (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel f ρ else 0

end MMWeil

end
