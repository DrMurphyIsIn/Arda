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

  AUTHORED (non-verbatim) definitions, flagged for the blind read-back audit cycle:
  `Quasicrystal.zetaOrdinates` (below), `Quasicrystal.recurrenceDeficit`, the torus-section
  trio, and (2026-09-18, node MM_weil_gram_trace) `WeilExplicit.crossCorr` +
  `WeilExplicit.weilGram`.  The six other `WeilExplicit` definitions are a CROSS-REGISTRY
  MIRROR of the RH registry's E8 block (RHDefs.lean, branch rh/e8-statement) and are verbatim;
  see the block comment there.  (`zetaOrdinates` exists because the island keeps the ordinate
  set as a FREE variable -- BoundaryLemmas takes `Ordinates : Set ℝ` -- while the registry's
  unconditional W2c nodes need it pinned.)  conjecture1_proved = False.

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

-- ===== MIRRORED VERBATIM (2026-09-18) from the AUTHORED `WeilExplicit` block of
-- telperion/missions/rh/lean/Statements/RHDefs.lean (branch rh/e8-statement), the
-- vocabulary of the RH-registry node RH_limit_explicit_formula (E8, the unconditional
-- Weil 1952 / Guinand 1948 limit explicit formula; design memo
-- telperion/docs/E8_LIMIT_EXPLICIT_FORMULA_DESIGN_2026-09-18.md).  Cross-registry mirror
-- for the MIRRORMERE D2 node MM_weil_gram_trace: the six definitions below are copied
-- CHARACTER FOR CHARACTER so that a future rvm_bridge drift check (examples/rvm_bridge/
-- generate.py, the E6Bridge4 pattern) can compare the two registries' blocks directly.
-- DO NOT re-word them here; re-word them in RHDefs.lean and re-mirror.
-- The two AUTHORED D2 definitions (crossCorr, weilGram) follow the six and are NOT part
-- of the mirror.  conjecture1_proved = False. =====

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

-- ===== AUTHORED for the registry, D2 / MM_weil_gram_trace (2026-09-18; design memo
-- telperion/docs/MM_mm-d2-weil-gram-trace_DESIGN_2026-09-18.md).  NOT in any island. =====

/-- **The cross-correlation of two test functions**, `(g₁ ⋆ g₂⁻)(u) = ∫ g₁(v) conj(g₂(v - u)) dv`.
    It is the polarisation of the Weil autocorrelation: `crossCorr g g` is the `autocorr g`
    of the Weil-positivity vocabulary (`f ⋆ f̃` with `f̃(u) = conj (f (-u))`), so the diagonal
    of `weilGram` below is the Weil form of an honest autocorrelation.  Two facts fix its
    normalisation and are the whole content of D2's Hermitian-ness (both PROVED on the proof
    island, neither hypothesised here):

    * `crossCorr g₂ g₁ u = conj (crossCorr g₁ g₂ (-u))` (substitute `v ↦ v + u`), whence
      `weilGram` is Hermitian on the PRIMES side alone -- no zero symmetry is used;
    * `weilKernel (crossCorr g₁ g₂) s = weilKernel g₁ s * conj (weilKernel g₂ (1 - conj s))`
      (Fubini on compact supports), which is the factorisation the trace conjunct reads.

    `crossCorr g₁ g₂` is again smooth with compact support when `g₁` and `g₂` are (support in
    `supp g₁ - supp g₂`; smoothness from `HasCompactSupport.contDiff_convolution_*`), so the
    Bochner integrals of `archSide`/`primeSide` applied to it are honest, NOT junk-valued. -/
noncomputable def crossCorr (g₁ g₂ : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, g₁ v * (starRingEnd ℂ) (g₂ (v - u))

/-- **The primes-side Weil-Gram matrix of a finite test family** (routes-roadmap D2).
    Entry `(i, j)` is the Weil functional `archSide - primeSide` of `crossCorr (g i) (g j)`:
    a FINITE von Mangoldt sum, two transform values, one `log π` term, and one digamma
    integral.  No zero of ζ occurs in the definition -- the zeros enter only through the
    trace conjunct of `MM_weil_gram_trace`, which is where the instrument reads them.
    The archimedean `Re ψ` integral inside `archSide` is exactly the term the finite Bragg
    bridge does NOT have (roadmap D2 skeptic); building this matrix from `braggTerm` instead
    would give a non-Hermitian object that is not the Weil form. -/
noncomputable def weilGram {k : ℕ} (g : Fin k → ℝ → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => archSide (crossCorr (g i) (g j)) - primeSide (crossCorr (g i) (g j))

end WeilExplicit

end
