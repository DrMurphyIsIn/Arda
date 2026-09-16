/-
  Statements.ANDDefs -- vocabulary mirror for the ANDURIL missions registry.  NOT a node statement.

  Every definition below is a VERBATIM copy from the v4.32 islands (toolchain
  leanprover/lean4:v4.32.0), source module + line range cited above each extract:
  the ZetaReflection block from telperion/examples/zeta_reflection/lean/
  (EMZeta.lean, EMZetaTail.lean, StirlingBinet.lean, CheckBand.lean), the DIntvProd
  block from zeta_reflection/lean/DIntvDef.lean + DIntvCorrect.lean, the XiLineZeros
  block from zeta_zero_localization/lean/XiLineZeros.lean.  To be regenerated/diffed
  by missions/anduril/build_anddefs.py (grant-pass deliverable).  This file exists so
  that node statement files elaborate standalone against Mathlib; the *registry
  statements* are the node files, which the verify gate matches against the real
  island artifacts by normalized containment.  conjecture1_proved = False.

  Mathlib-provenance notes: `bernoulliFun`, `Complex.digamma`, `Complex.Gammaℝ`,
  `completedRiemannZeta`, `logDeriv` are upstream Mathlib at this pin (the islands
  use them unqualified/qualified without local defs).
-/
import Mathlib
open MeasureTheory

namespace DIntvProd

-- ===== DIntvDef.lean:26-30 (v4.32 zeta_reflection island) =====
structure DIntv where
  lo : Int
  hi : Int
  e  : Int
deriving Repr, DecidableEq

namespace DIntv

-- ===== DIntvDef.lean:36-37 =====
noncomputable def memR (x : ℝ) (I : DIntv) : Prop :=
  (I.lo : ℝ) * (2 : ℝ) ^ I.e ≤ x ∧ x ≤ (I.hi : ℝ) * (2 : ℝ) ^ I.e

-- ===== DIntvCorrect.lean:77 =====
def isPos (I : DIntv) : Bool := 0 < I.lo

-- ===== DIntvCorrect.lean:80 =====
def isNeg (I : DIntv) : Bool := I.hi < 0

-- ===== DIntvCorrect.lean:84-87 =====
def sign? (I : DIntv) : Option Bool :=
  if isPos I then some true
  else if isNeg I then some false
  else none

end DIntv

end DIntvProd

namespace XiLineZeros

-- ===== zeta_zero_localization/lean/XiLineZeros.lean:30 (v4.32 island) =====
noncomputable def gLine (t : ℝ) : ℝ := (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re

end XiLineZeros

namespace ZetaReflection

-- ===== EMZeta.lean:56 (v4.32 zeta_reflection island) =====
noncomputable def sawBernoulli (k : ℕ) (x : ℝ) : ℝ := bernoulliFun k (Int.fract x)

-- ===== EMZetaTail.lean:443 =====
noncomputable def emTailCoeff3 (s : ℂ) : ℂ := -(s * (s + 1) * (s + 2))

-- ===== StirlingBinet.lean:55 =====
noncomputable def binetRem (w : ℂ) : ℂ := Complex.digamma w - Complex.log w

-- ===== CheckBand.lean:79-85 =====
def checkLine : List DIntvProd.DIntv → Bool
  | [] => true
  | [b] => (DIntvProd.DIntv.sign? b).isSome
  | b :: c :: rest =>
    match DIntvProd.DIntv.sign? b, DIntvProd.DIntv.sign? c with
    | some sb, some sc => (sb != sc) && checkLine (c :: rest)
    | _, _ => false

-- ===== CheckBand.lean:65-68 =====
structure BandData where
  /-- Supplied dyadic enclosures of `gLine` at the `n+1` grid heights. -/
  boxes : List DIntvProd.DIntv
deriving Repr

-- ===== CheckBand.lean:88 =====
@[inline] def BandData.check (d : BandData) : Bool := checkLine d.boxes

end ZetaReflection
