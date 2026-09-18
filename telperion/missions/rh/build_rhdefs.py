#!/usr/bin/env python3
"""Assemble lean/Statements/RHDefs.lean from VERBATIM extracts of the RH Lean islands.

Run from telperion/missions/rh/.  Every in-repo definition is copied by exact line range
from its source module on the v4.34 li_positivity island (cited inline); re-running this
script and diffing detects mirror drift.  The three upstream LiCriterion definitions
(phi, taylorCoeff, riemannXi) are embedded as literals below, copied verbatim from
nicholasbulka/li-criterion-rh-equivalence-lean @ 35df682f3b709ffe5fbcfdd452dfa964bd622b87
Lc/LiCriterion/Basic.lean (lines cited); `--verify-upstream` re-fetches that file from
GitHub at the pinned rev and asserts the literals still match byte-for-byte.
"""
import sys
import urllib.request
from pathlib import Path

LI = Path(__file__).resolve().parents[2] / "examples" / "li_positivity" / "lean"
# Route C (de Bruijn-Newman) island: same toolchain/Mathlib pin as li_positivity, separate Lake
# project (examples/dbn/lean); the DBN block below is extracted from it by exact line range.
DBN = Path(__file__).resolve().parents[2] / "examples" / "dbn" / "lean"
OUT = Path(__file__).resolve().parent / "lean" / "Statements" / "RHDefs.lean"

UPSTREAM_REV = "35df682f3b709ffe5fbcfdd452dfa964bd622b87"
UPSTREAM_URL = (
    "https://raw.githubusercontent.com/nicholasbulka/li-criterion-rh-equivalence-lean/"
    f"{UPSTREAM_REV}/Lc/LiCriterion/Basic.lean"
)

# Verbatim from upstream Lc/LiCriterion/Basic.lean @ 35df682f -- line ranges cited.
UPSTREAM_EXTRACTS = [
    # Basic.lean:379
    "noncomputable def phi (f : ℂ → ℂ) (z : ℂ) : ℂ := f (1 / (1 - z))",
    # Basic.lean:525-526
    "noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=\n"
    "  (deriv^[n] (logDeriv (phi f))) 0 / n.factorial",
    # Basic.lean:1236-1237
    "noncomputable def riemannXi (s : ℂ) : ℂ :=\n"
    "  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)",
]
UPSTREAM_LINE_RANGES = [(379, 379), (525, 526), (1236, 1237)]


def ex(module: str, lo: int, hi: int) -> str:
    lines = (LI / module).read_text().split("\n")
    return "\n".join(lines[lo - 1:hi])


def exd(module: str, lo: int, hi: int) -> str:
    lines = (DBN / module).read_text().split("\n")
    return "\n".join(lines[lo - 1:hi])


def verify_upstream() -> None:
    text = urllib.request.urlopen(UPSTREAM_URL, timeout=30).read().decode()
    lines = text.split("\n")
    for extract, (lo, hi) in zip(UPSTREAM_EXTRACTS, UPSTREAM_LINE_RANGES):
        actual = "\n".join(lines[lo - 1:hi])
        if actual != extract:
            raise SystemExit(
                f"upstream drift at Basic.lean:{lo}-{hi}:\n{actual!r}\n!=\n{extract!r}")
    print(f"upstream extracts verified against {UPSTREAM_REV[:12]}")


# 2026-09-18 E8 (RH_limit_explicit_formula): the Weil test class and the three sides of the
# limit explicit formula.  Design memo: docs/E8_LIMIT_EXPLICIT_FORMULA_DESIGN_2026-09-18.md.
WEIL_EXPLICIT_BLOCK = """
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

end WeilExplicit"""

parts = [
    """/-
  Statements.RHDefs -- vocabulary mirror for the RH missions registry.  NOT a node statement.

  Every definition below is a VERBATIM copy: the ZeroFreeBridge/DiffractionCore/Backlund
  blocks by exact line range from the v4.34 li_positivity island (toolchain
  leanprover/lean4:v4.34.0-rc1) and the DBN block from the v4.34 examples/dbn island
  (Route C, same pin), source module cited above each extract; the LiCriterion block from
  the upstream pinned dependency nicholasbulka/li-criterion-rh-equivalence-lean @ 35df682f,
  Lc/LiCriterion/Basic.lean, lines cited.  The copies are regenerated/diffed by
  missions/rh/build_rhdefs.py (--verify-upstream re-fetches and diffs the upstream block).
  This file exists so that node statement files elaborate standalone against Mathlib; the
  *registry statements* are the node files, which the verify gate matches against the real
  island artifacts by normalized containment.  conjecture1_proved = False.
-/
import Mathlib
open MeasureTheory

namespace LiCriterion

-- ===== upstream Lc/LiCriterion/Basic.lean:379 (rev 35df682f) =====""",
    UPSTREAM_EXTRACTS[0],
    "\n-- ===== upstream Lc/LiCriterion/Basic.lean:525-526 (rev 35df682f) =====",
    UPSTREAM_EXTRACTS[1],
    "\n-- ===== upstream Lc/LiCriterion/Basic.lean:1236-1237 (rev 35df682f) =====",
    UPSTREAM_EXTRACTS[2],
    """
end LiCriterion

namespace ZeroFreeBridge
""",
    "-- ===== StripRepr.lean:42,45-46,49,52 (v4.34 island) =====",
    ex("StripRepr.lean", 42, 42),
    "",
    ex("StripRepr.lean", 45, 46),
    "",
    ex("StripRepr.lean", 49, 49),
    "",
    ex("StripRepr.lean", 52, 52),
    "\n-- ===== DlvpZetaRateEffective.lean:23-25,28 (v4.34 island) =====",
    ex("DlvpZetaRateEffective.lean", 23, 25),
    "",
    ex("DlvpZetaRateEffective.lean", 28, 28),
    """
end ZeroFreeBridge

namespace DiffractionCore
open Real Complex
""",
    "-- ===== RvMDiffractionCore.lean:916-917,921-922 (v4.34 island) =====",
    ex("RvMDiffractionCore.lean", 916, 917),
    "",
    ex("RvMDiffractionCore.lean", 921, 922),
    "\n-- ===== RvMDiffractionCore.lean:1001-1002 (v4.34 island) =====",
    ex("RvMDiffractionCore.lean", 1001, 1002),
    "\n-- ===== RvMDiffractionCore.lean:1691-1692 (v4.34 island) =====",
    ex("RvMDiffractionCore.lean", 1691, 1692),
    """
end DiffractionCore

namespace Backlund
open Complex
""",
    "-- ===== RvMBacklundAux.lean:24-25 (v4.34 island) =====",
    ex("RvMBacklundAux.lean", 24, 25),
    """
end Backlund

namespace RvMCount

-- ===== AUTHORED for the registry (NOT in the island; 2026-09-17 critical-path nodes).  The
-- nontrivial-zero count to height T WITH MULTIPLICITY: a finsum over the strip zeros with
-- 0 < Im <= T of the order given by zeta's meromorphic divisor on the open critical strip.
-- RECTANGLE-based by design: a ball-based count (the island's RHInBoxAnalytic.zeroFinset shape)
-- miscounts conjugates (routes roadmap section 9).  finsum is 0 on infinite support, so the
-- definition is total; finiteness of the support is a theorem, not an assumption. =====
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
    ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat

end RvMCount

namespace DBN
""",
    "-- ===== examples/dbn/lean/DBNDefs.lean:40-41 (v4.34 dbn island, Route C) =====",
    exd("DBNDefs.lean", 40, 41),
    "\n-- ===== examples/dbn/lean/DBNDefs.lean:211-214 (v4.34 dbn island, Route C) =====",
    exd("DBNDefs.lean", 211, 214),
    "\n-- ===== examples/dbn/lean/DBNDefs.lean:408-409 (v4.34 dbn island, Route C) =====",
    exd("DBNDefs.lean", 408, 409),
    "\n-- ===== examples/dbn/lean/DBNDefs.lean:413 (v4.34 dbn island, Route C) =====",
    exd("DBNDefs.lean", 413, 413),
    """
end DBN""",
    # ===== AUTHORED (2026-09-18 E8): Weil test class + the three sides of the limit explicit formula =====
    WEIL_EXPLICIT_BLOCK,
]


def main() -> int:
    if "--verify-upstream" in sys.argv:
        verify_upstream()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(parts) + "\n")
    print(f"wrote {OUT} ({len(OUT.read_text().splitlines())} lines)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
