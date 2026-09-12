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


def verify_upstream() -> None:
    text = urllib.request.urlopen(UPSTREAM_URL, timeout=30).read().decode()
    lines = text.split("\n")
    for extract, (lo, hi) in zip(UPSTREAM_EXTRACTS, UPSTREAM_LINE_RANGES):
        actual = "\n".join(lines[lo - 1:hi])
        if actual != extract:
            raise SystemExit(
                f"upstream drift at Basic.lean:{lo}-{hi}:\n{actual!r}\n!=\n{extract!r}")
    print(f"upstream extracts verified against {UPSTREAM_REV[:12]}")


parts = [
    """/-
  Statements.RHDefs -- vocabulary mirror for the RH missions registry.  NOT a node statement.

  Every definition below is a VERBATIM copy: the ZeroFreeBridge block by exact line range
  from the v4.34 li_positivity island (toolchain leanprover/lean4:v4.34.0-rc1), source
  module cited above each extract; the LiCriterion block from the upstream pinned
  dependency nicholasbulka/li-criterion-rh-equivalence-lean @ 35df682f,
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
end ZeroFreeBridge""",
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
