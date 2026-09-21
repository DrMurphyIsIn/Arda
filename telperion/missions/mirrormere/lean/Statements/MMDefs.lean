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

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-20, Weil converse reduction) =====
  Three definitions from the vendored Zeta23 package (anthropics/formal-math, commit
  fbdc36bbf17d20af3fd0447c6d1a8a02773c9844, the rvm_bridge island's lake-manifest pin),
  VERBATIM, each with its source file and line cited; they are the names the RvMBridge6 block
  below consumes (paperFT, gammaOf, IsNontrivialZero).  Then the six definitions of
  telperion/examples/rvm_bridge/lean/E6Bridge6.lean (namespace RvMBridge6, v4.33 island),
  VERBATIM with their docstrings, mirrored inside the same namespace so the qualified names
  match: hermitianTransform, zeroSide, gaussTest, GaussianTransfer, GaussianDominance,
  GaussianApprox.  The two obligations and the approximation clause are `def ... : Prop`,
  consumed by RvMBridge6.weil_positivity_implies_rh_of only as hypotheses; mirroring them here
  proves nothing.  The elaboration context (file-level opens) is restored per block as the
  sources declare it.  conjecture1_proved = False.
-/
namespace Zeta23
open Complex MeasureTheory Set
open scoped ComplexConjugate

-- ===== Zeta23/Defs.lean:44 (Zeta23 @ fbdc36b) =====
def paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))

-- ===== Zeta23/Defs.lean:105 (Zeta23 @ fbdc36b) =====
def gammaOf (ρ : ℂ) : ℂ := (ρ - 1 / 2) / Complex.I

-- ===== Zeta23/Statement.lean:38 (Zeta23 @ fbdc36b) =====
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

end Zeta23

namespace RvMBridge6
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit

-- ===== E6Bridge6.lean:81-99 (rvm_bridge island; section A) =====
/-! ## A. Vocabulary: the zero-side functional on entire transforms. -/

/-- The Hermitian transform of a test g: H(z) = h_g(z) conj (h_g (conj z)), h_g = paperFT g.
This is paperFT (g * g~) (Zeta23.EF.paperFT_weilTest); on the real axis it is |h_g|^2. -/
def hermitianTransform (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  paperFT g z * conj (paperFT g (conj z))

/-- The zero side of the explicit formula for an arbitrary transform H: Sum_rho m(rho) H(gamma_rho)
over ALL rho : C, with the registry multiplicity (zero off the nontrivial zeros), gammaOf rho =
(rho - 1/2)/i. -/
def zeroSide (H : ℂ → ℂ) : ℂ :=
  ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ)

/-- The Gaussian-derivative Hermitian transform G_{c,lam}(z) = (z - c)^2 exp (-2 lam (z - c)^2)
(= h h* for h(z) = (z - c) exp (-lam (z - c)^2), the transform of a frequency-shifted derivative
of a Gaussian).  Real and nonnegative on the real axis; at gamma = c + i y it equals
-y^2 exp (2 lam y^2) < 0. -/
def gaussTest (c lam : ℝ) (z : ℂ) : ℂ :=
  (z - c) ^ 2 * Complex.exp (-(2 * lam) * (z - c) ^ 2)

-- ===== E6Bridge6.lean:284-311 (section E: the two named obligations) =====
/-! ## E. The two named analytic obligations. -/

/-- **Obligation O1 (Gaussian transfer).**  For every real centre c and every lam > 0, the
Gaussian-derivative Hermitian transform G_{c,lam}(z) = (z - c)^2 exp (-2 lam (z - c)^2) is a limit
of Hermitian transforms of smooth compactly supported tests FOR THE ZERO-SIDE FUNCTIONAL: there
are Weil tests g_n with Re zeroSide (hermitianTransform g_n) -> Re zeroSide G_{c,lam}.
Intended witness: g_n = (frequency-shifted derivative of a Gaussian) times a smooth cutoff
chi(u/n); the transforms converge pointwise on the strip |Im z| <= 1/2 with a truncation-uniform
bound C/(1 + (Re z)^2)^2 (two integrations by parts), and Sum_rho m(rho)/(1+|gamma_rho|^2) < infty
(Zeta23.WeilEF.zero_sum_inv_sq) gives dominated convergence of the zero sum.  Independent of RH. -/
def GaussianTransfer : Prop :=
  ∀ (c lam : ℝ), 0 < lam → ∃ g : ℕ → (ℝ → ℂ), (∀ n, IsWeilTest (g n)) ∧
    Tendsto (fun n => (zeroSide (hermitianTransform (g n))).re) atTop
      (𝓝 (zeroSide (gaussTest c lam)).re)

/-- **Obligation O2 (Gaussian dominance).**  If rho_0 is a nontrivial zero off the critical line,
then for some real centre c and some lam > 0 the Gaussian-weighted zero sum
Sum_rho m(rho) (gamma_rho - c)^2 exp (-2 lam (gamma_rho - c)^2) has NEGATIVE real part.
Intended proof: choose c within |1/2 - Re rho_0| of Im rho_0 and generic; the maximiser of
(Im gamma)^2 - (Re gamma - c)^2 over the zeros is attained, off the line, unique up to the pair
rho <-> 1 - conj rho, and its pair term is -2 m y^2 e^{2 lam M} (x = 0) or has a phase
2 arg w - 4 lam x y that can be set to pi along lam_k -> infty; all other zeros contribute
o(e^{2 lam M}) by the local zero count.  A statement about the zeros of zeta alone; it is
vacuous under RH and its intended proof never uses RH. -/
def GaussianDominance : Prop :=
  ∀ ρ₀ : ℂ, IsNontrivialZero ρ₀ → ρ₀.re ≠ 1 / 2 →
    ∃ (c lam : ℝ), 0 < lam ∧ (zeroSide (gaussTest c lam)).re < 0


-- ===== E6Bridge6.lean:560-572 (section H: the zero-free form of O1) =====
/-- **Obligation O1' (Gaussian approximation on the strip), a statement about test functions
only.**  For every real centre c and lam > 0 there are Weil tests g_n whose Hermitian transforms
converge to G_{c,lam} pointwise on the strip |Im z| <= 1/2 with a truncation-uniform bound
C/(1 + |z|^2) there.  Intended witness: g_n(u) = e^{-icu} phi(u) chi(u/n) with phi the inverse
transform of (z - c) e^{-lam (z - c)^2} (a derivative of a Gaussian, Mathlib
integral_cexp_quadratic) and chi a smooth cutoff (ContDiffBump); the C/(1+x^2) bound is two
integrations by parts with derivatives of g_n bounded uniformly in n against e^{|u|/2}. -/
def GaussianApprox : Prop :=
  ∀ (c lam : ℝ), 0 < lam → ∃ g : ℕ → (ℝ → ℂ), (∀ n, IsWeilTest (g n)) ∧
    (∃ C : ℝ, ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖hermitianTransform (g n) z‖ ≤ C / (1 + Complex.normSq z)) ∧
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => hermitianTransform (g n) z) atTop (𝓝 (gaussTest c lam z)))

end RvMBridge6

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, WALL ASSAULT seam A) =====
  VERBATIM from the rvm_bridge island (v4.33), with docstrings and source lines cited:
  RvMBridge8.gaussB / gaussK / gaussPhi (E6Bridge8.lean:156-169, the non-compactly-supported
  Gaussian-derivative test whose Hermitian transform is RvMBridge6.gaussTest) and
  RvMBridge10.GaussianPositivity (E6Bridge10.lean:50-52, the Wall in two real parameters).
  Vocabulary for MM_rh_iff_gaussian_positivity, MM_gaussian_explicit_formula and
  MM_rh_iff_gaussian_prime_le_arch; all three are equivalences or identities and prove nothing
  about either side.  conjecture1_proved = False.
-/
namespace RvMBridge8
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit

-- ===== E6Bridge8.lean:156-157 =====
/-- b = 1/(4 lam): the Gaussian width whose transform has width lam. -/
def gaussB (lam : ℝ) : ℝ := 1 / (4 * lam)

-- ===== E6Bridge8.lean:162-164 =====
/-- The normalising constant K = (2 lam i (pi/b)^{1/2})^{-1}. -/
def gaussK (lam : ℝ) : ℂ :=
  (2 * (lam : ℂ) * I * ((Real.pi : ℂ) / (gaussB lam : ℂ)) ^ (1 / 2 : ℂ))⁻¹

-- ===== E6Bridge8.lean:166-169 =====
/-- phi(u) = K u exp (-b u^2 - i c u): the (non-compactly-supported) inverse transform of
gaussHalf. -/
def gaussPhi (c lam : ℝ) (u : ℝ) : ℂ :=
  gaussK lam * (u : ℂ) * cexp (-(gaussB lam : ℂ) * (u : ℂ) ^ 2 - I * c * u)

end RvMBridge8

namespace RvMBridge10
open WeilExplicit RvMBridge6 RvMBridge8

-- ===== E6Bridge10.lean:50-52 =====
/-- Gaussian positivity: the Wall in two real parameters. -/
def GaussianPositivity : Prop :=
  ∀ (c lam : ℝ), 0 < lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

end RvMBridge10

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, WALL ASSAULT seam C) =====
  VERBATIM from the rvm_bridge island (v4.33), source lines cited: RvMBridge7.constB
  (E6Bridge7.lean:441-444, the lam = 1 local-count majorant constant) and RvMBridge12.WindowOnLine
  / lamThreshold (E6Bridge12.lean:73-76, 104-107).  Vocabulary for MM_gaussian_positivity_of_window,
  the single-near-zero form of the ladder-certified region.  The DOMINANCE form
  (gaussian_positivity_of_window_dominance) is NOT registered: its vocabulary zeroWindow /
  windowSum / tailEnvelope rests on the THEOREM zeroWindowSet_finite (Zeta23.zetaSeam.finite_window),
  which is not mirrorable as a definition on this statement island.  WindowOnLine is a HYPOTHESIS
  supplied cross-island by the Turing ladder at registry level, never a Lean import; nothing here
  proves anything about RH.  conjecture1_proved = False.
-/
namespace RvMBridge7
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit

-- ===== E6Bridge7.lean:441-444 =====
def constB (c : ℝ) : ℝ :=
  ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℝ)
    * ((Real.exp (1 / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 1) ^ 2)
        / (1 + Complex.normSq (gammaOf ρ)))

end RvMBridge7

namespace RvMBridge12
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit RvMBridge6 RvMBridge7

-- ===== E6Bridge12.lean:73-76 =====
/-- All nontrivial zeros with ordinate within D of c lie on the line (what the Turing ladder
certifies for c <= T - D; carried here as a hypothesis, cross-island). -/
def WindowOnLine (c D : ℝ) : Prop :=
  ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - c| ≤ D → ρ.re = 1 / 2

-- ===== E6Bridge12.lean:104-107 =====
/-- The lam threshold: max 1 (B e^{2 (D^2 - 1/4)} / (2 kappa delta^2)), kappa = D^2 - 1/4 - d^2,
B = constB c. -/
def lamThreshold (c D d δ : ℝ) : ℝ :=
  max 1 (constB c * Real.exp (2 * (D ^ 2 - 1 / 4)) / (2 * (D ^ 2 - 1 / 4 - d ^ 2) * δ ^ 2))

-- ===== E6Bridge12.lean:83-84 (added 2026-09-21 for MM_effective_gaussian_dominance) =====
/-- The ordinate window as an index set. -/
def winSet (c D : ℝ) : Set ℂ := {ρ : ℂ | |ρ.im - c| ≤ D}

-- ===== E6Bridge12.lean:383-385 =====
/-- The nontrivial zeros with |Im rho - c| <= D: finite by the local zero count
(Zeta23.zetaSeam.finite_window), generalised from E6Bridge7's centre rho_0 to (c, D). -/
def zeroWindowSet (c D : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ} ∩ winSet c D

-- ===== E6Bridge12.lean:387-392 (rvm_bridge island, v4.33).  SUPPORT LEMMA carried as `sorry`
-- HERE ONLY so that `zeroWindow` elaborates: it is PROVED on the rvm_bridge island (same file,
-- via Zeta23.zetaSeam.finite_window) and is NOT a registry node; the sorry is vocabulary
-- scaffolding in the statement package, the same trust class as the node statements
-- themselves, and never enters an axiom guard (same precedent as
-- RHInBoxAnalytic.divisor_ball_support_finite_of_one_notMem above). =====
lemma zeroWindowSet_finite (c D : ℝ) : (zeroWindowSet c D).Finite := by sorry

/-- The certified window as a Finset. -/
def zeroWindow (c D : ℝ) : Finset ℂ := (zeroWindowSet_finite c D).toFinset

end RvMBridge12

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, WALL ASSAULT seam B + wall map) =====
  VERBATIM from telperion/examples/rvm_bridge/lean/E6Bridge11.lean (namespace RvMBridge11,
  v4.33 island), source lines cited: GaussianExplicitFormula (63-69, the named hypothesis seam B
  consumes; discharged by seam A's RvMBridge10.zeroSide_gaussTest_eq in E6Bridge13) and lam₀
  (91-92, the absolute width threshold 1e-7).  Vocabulary for
  MM_gaussian_positivity_small_lam_prime_side, MM_gaussian_positivity_small_lam and MM_wall_map.
  Nothing here proves anything about RH.  conjecture1_proved = False.
-/
namespace RvMBridge11
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit

-- ===== E6Bridge11.lean:63-69 =====
/-- The explicit formula for the Gaussian-derivative test (NOT compactly supported, so outside
the E8 class; a parallel file proves it by the same Tannery/DCT transfer as E6Bridge8).  Restated
verbatim, consumed only as a hypothesis of gaussian_positivity_small_lam_of. -/
def GaussianExplicitFormula : Prop := ∀ (c lam : ℝ), 0 < lam →
  (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re
    = (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))
        - WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re

-- ===== E6Bridge11.lean:91-92 =====
/-- The absolute width threshold. -/
def lam₀ : ℝ := 1 / 10000000

-- ===== E6Bridge11.lean:1370-1374 (the envelope form, added later on 2026-09-21) =====
/-- The explicit envelope threshold c₁(lam). -/
def envelopeX (lam : ℝ) : ℝ :=
  4 * Real.exp (2 * lam) * Real.sqrt (32 * Real.pi * lam) + 16 * Real.exp (16 * lam)

def envelopeC (lam : ℝ) : ℝ := 2 * Real.exp (9 + 2 * envelopeX lam) + 2 / Real.sqrt lam

end RvMBridge11

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, effective Gaussian dominance) =====
  VERBATIM from telperion/examples/rvm_bridge/lean/E6Bridge14.lean (namespace RvMBridge14, v4.33
  island), source lines cited: effectiveThreshold (63-68), the explicit lam threshold of open
  lemma 1.  Vocabulary for MM_effective_threshold_unbounded.  The main theorem
  RvMBridge14.effective_gaussian_dominance is NOT registered as a node: its window-count
  hypothesis sums over RvMBridge12.zeroWindow, which rests on the THEOREM zeroWindowSet_finite
  (Zeta23.zetaSeam.finite_window) and is not mirrorable as a definition on this statement island;
  it is recorded as a cross-island prose link in the registry ledger and docs.
  Nothing here proves anything about RH.  conjecture1_proved = False.
-/
namespace RvMBridge14
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit RvMBridge6 RvMBridge7 RvMBridge12

-- ===== E6Bridge14.lean:63-68 =====
/-- The explicit lam threshold for effective Gaussian dominance with parameters
(y0 = distance floor from the line, xmin = ordinate spacing floor, N = window count,
B = tail constant, D = window half-width). -/
def effectiveThreshold (y0 xmin : ℝ) (N : ℕ) (B D : ℝ) : ℝ :=
  max 1 (max (Real.log (max 1 (4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2)) / (2 * xmin ^ 2))
             (Real.log (max 1 (4 * B / y0 ^ 2)) / (2 * y0 ^ 2)))

end RvMBridge14

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, the sharp envelope of the Wall) =====
  VERBATIM from telperion/examples/rvm_bridge/lean/E6Bridge16.lean (namespace RvMBridge16, v4.33
  island), source lines cited: primeAbsTerm (390-393), primeAbs (395-397), tailRadius (651-652),
  envelopeCsharp (654-657).  Vocabulary for MM_gaussian_positivity_envelope_sharp.  Nothing here
  proves anything about RH.  conjecture1_proved = False.
-/
namespace RvMBridge16
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit RvMBridge11

-- ===== E6Bridge16.lean:390-393 =====
/-- The n-th absolute prime term, in units of A. -/
def primeAbsTerm (lam : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n
    * (|1 - (Real.log n) ^ 2 / (4 * lam)| * Real.exp (-(Real.log n) ^ 2 / (8 * lam)))

-- ===== E6Bridge16.lean:395-397 =====
/-- primeAbs lam = 2 Σ_n Λ(n) n^{-1/2} |1 - (log n)^2/(4 lam)| e^{-(log n)^2/(8 lam)}: the exact
size of the c-uniform prime side in units of A. -/
def primeAbs (lam : ℝ) : ℝ := 2 * ∑' n : ℕ, primeAbsTerm lam n

-- ===== E6Bridge16.lean:651-652 =====
/-- The tail radius: lam L^2 = 16 + 2 primeAbs lam, so the tail is e^{-16 - 2 P}. -/
def tailRadius (lam : ℝ) : ℝ := Real.sqrt ((16 + 2 * primeAbs lam) / lam)

-- ===== E6Bridge16.lean:654-657 =====
/-- THE SHARP ENVELOPE THRESHOLD: c1(lam) = 2 pi e^{primeAbs lam + 1/2} + tailRadius lam
+ 3/sqrt lam + 1. -/
def envelopeCsharp (lam : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (primeAbs lam + 1 / 2) + tailRadius lam + 3 / Real.sqrt lam + 1

end RvMBridge16

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, the Theta face) =====
  VERBATIM from telperion/examples/rvm_bridge/lean/E6Bridge17.lean (namespace RvMBridge17, v4.33
  island), source lines cited: plainGauss (43-44), Theta (46-47), heatVar (498-500), heatKernel
  (502-503), ThetaFree (884-885), ThetaWidths (887-888).  Vocabulary for MM_rh_iff_theta_positivity,
  MM_theta_heat_monotone and MM_rh_iff_theta_widths.  Nothing here proves anything about RH.
  conjecture1_proved = False.
-/
namespace RvMBridge17
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit RvMBridge6 RvMBridge7 RvMBridge12 RvMBridge14

-- ===== E6Bridge17.lean:43-44 =====
/-- The plain Gaussian transform G_{c,lam}(z) = exp (-2 lam (z - c)^2). -/
def plainGauss (c lam : ℝ) (z : ℂ) : ℂ := Complex.exp (-(2 * lam) * (z - c) ^ 2)

-- ===== E6Bridge17.lean:46-47 =====
/-- The plain Gaussian face Theta(c, lam) = Re Sum_rho m(rho) G_{c,lam}(gamma_rho). -/
def Theta (c lam : ℝ) : ℝ := (zeroSide (plainGauss c lam)).re

-- ===== E6Bridge17.lean:498-500 =====
/-- The variance of the heat step from width lam to width lam' < lam:
sigma^2 = 1/(4 lam') - 1/(4 lam) = (lam - lam')/(4 lam lam'). -/
def heatVar (lam' lam : ℝ) : ℝ := (lam - lam') / (4 * lam * lam')

-- ===== E6Bridge17.lean:502-503 =====
/-- The Gaussian (heat) kernel of variance sigma^2. -/
def heatKernel (σ2 u : ℝ) : ℝ := Real.exp (-(u ^ 2) / (2 * σ2)) / Real.sqrt (2 * Real.pi * σ2)

-- ===== E6Bridge17.lean:884-885 =====
/-- Width lam is Theta-free: Theta(c, lam) >= 0 at every centre. -/
def ThetaFree (lam : ℝ) : Prop := ∀ c : ℝ, 0 ≤ Theta c lam

-- ===== E6Bridge17.lean:887-888 =====
/-- The set of positive free widths; Lambda_Theta is its supremum (possibly 0 or infinity). -/
def ThetaWidths : Set ℝ := {lam : ℝ | 0 < lam ∧ ThetaFree lam}

end RvMBridge17

end
