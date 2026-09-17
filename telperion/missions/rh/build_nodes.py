#!/usr/bin/env python3
"""Create the RH campaign nodes via the real `telperion mission add` CLI.

Statement bodies for PROVEN strata are VERBATIM declaration extracts from the island
artifacts (line ranges cited), so the grant gate's normalized-containment check is
meaningful.  The goal node's statement is the one hand-authored rendering (Mathlib's
own `RiemannHypothesis`); it stays draft.  Run from telperion/ with PYTHONPATH=src.
"""
import subprocess
import sys
import tempfile
from pathlib import Path

TELPERION = Path(__file__).resolve().parents[2]
LI = TELPERION / "examples" / "li_positivity" / "lean"
ZFB = TELPERION / "examples" / "zero_free_bridge" / "lean"


def ex(base: Path, module: str, lo: int, hi: int, strip: str) -> str:
    lines = (base / module).read_text().split("\n")
    text = "\n".join(lines[lo - 1:hi])
    if not text.rstrip().endswith(strip):
        raise SystemExit(f"extract {module}:{lo}-{hi} does not end with {strip!r}:\n{text}")
    return text.rstrip()[: -len(strip)].rstrip()


OPEN_ZFB = "import Statements.RHDefs\nopen ZeroFreeBridge\n\n"
OPEN_DLVP = "import Statements.RHDefs\nopen ZeroFreeBridge Complex MeromorphicOn Metric\n\n"
OPEN_LI = "import Statements.RHDefs\nopen LiCriterion\n\n"

NODES = [
    # (name, title, kind, deps, statement_body)
    ("RH.zeta_repr_R1",
     "Strip representation seed (R1): zeta = stripRHS on Re s > 1, by Abel summation",
     "lemma", "",
     OPEN_ZFB + ex(LI, "StripReprR1.lean", 85, 85, ":= by")),
    ("RH.strip_repr",
     "The UNCONDITIONAL fractional-part strip representation: zeta = stripRHS on all of {0 < Re s} \\ {1}",
     "milestone", "RH_zeta_repr_R1",
     OPEN_ZFB + ex(LI, "StripReprAssembled.lean", 26, 26, ":=")),
    ("RH.zeta_log_bound",
     "The sharp near-line growth bound: |zeta(sigma+it)| <= 6(1 + log|t|) for 1 <= sigma <= 2, |t| >= 2",
     "milestone", "RH_strip_repr",
     "import Mathlib\n\n" + ex(LI, "ZetaLogBound.lean", 155, 156, ":= by")),
    ("RH.zero_free_gamma5",
     "The elementary unconditional zero-free region (Hadamard-free): beta <= 1 - c/gamma^5",
     "milestone", "RH_strip_repr",
     "import Mathlib\n\n" + ex(LI, "ZeroFreeElementary.lean", 277, 279, ":= by")),
    ("RH.zero_free_polylog",
     "The polylog-improved unconditional zero-free region: beta <= 1 - c/(gamma^4 (1 + log 2 gamma)), strictly sharper than gamma^-5",
     "milestone", "RH_zero_free_gamma5,RH_zeta_log_bound",
     "import Mathlib\n\n" + ex(LI, "ZeroFreePolylog.lean", 74, 77, ":= by")),
    ("RH.borel_caratheodory_deriv",
     "Borel-Caratheodory + Cauchy derivative bound: |deriv h c| <= 2M'/(R-r) from the real-part sup on a disk",
     "lemma", "",
     "import Mathlib\nopen Complex Metric\n\n" + ex(LI, "DlvpBCDeriv.lean", 30, 34, ":= by")),
    ("RH.dlvp_region_effective",
     "The de la Vallee Poussin region at the classical rate, EFFECTIVE constant (multiplicity-hypothesis form)",
     "milestone", "RH_borel_caratheodory_deriv,RH_strip_repr",
     OPEN_DLVP + ex(LI, "DlvpZetaRateEffective.lean", 34, 37, ":= by")),
    ("RH.dlvp_zero_free_region",
     "The SELF-CONTAINED effective dVP zero-free region (no multiplicity hypothesis; artifact on the v4.32 island)",
     "milestone", "RH_dlvp_region_effective",
     OPEN_DLVP + ex(ZFB, "DlvpZetaZeroFree.lean", 57, 59, ":= by")),
    ("RH.li_rung_certificates",
     "Li ladder rungs 0..19 (20 emitted certificates, each conditional on its Arb enclosure hypothesis); statement = the topmost rung li_rung_19",
     "lemma", "",
     OPEN_LI + ex(LI, "LiPositivity.lean", 139, 139, ":=")),
    ("RH.li_ladder_reduction",
     "The Li ladder as a reduction of RH to its tail: given a certified prefix, RH iff the infinite tail (proves NEITHER side)",
     "lemma", "",
     OPEN_LI + ex(LI, "LiLadder.lean", 35, 37, ":= by")),
    ("RH.li_neg_refutes_rh",
     "The falsifiability face: a certified NEGATIVE upper bound on any Li rung refutes RH via the upstream equivalence",
     "lemma", "",
     OPEN_LI + ex(LI, "LiPositivity.lean", 16, 18, ":=")),
    # --- the goal (draft; NOT proved; conjecture1_proved = False) ---
    ("RH.conjecture",
     "The Riemann Hypothesis (Mathlib's RiemannHypothesis) -- NOT proved; the campaign goal",
     "goal",
     ",".join(["RH_zeta_repr_R1", "RH_strip_repr", "RH_zeta_log_bound",
               "RH_zero_free_gamma5", "RH_zero_free_polylog",
               "RH_borel_caratheodory_deriv", "RH_dlvp_region_effective",
               "RH_dlvp_zero_free_region", "RH_li_rung_certificates",
               "RH_li_ladder_reduction", "RH_li_neg_refutes_rh"]),
     "import Mathlib\n\n" + "theorem RH_conjecture : RiemannHypothesis"),
]


def main() -> int:
    for name, title, kind, deps, body in NODES:
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
            f.write(body)
            tmp = f.name
        cmd = [sys.executable, "-c",
               "from telperion.cli import main; import sys; sys.exit(main(sys.argv[1:]))",
               "mission", "--missions-root", "missions", "add", "rh", name,
               "--title", title, "--kind", kind, "--statement-file", tmp]
        if deps:
            cmd += ["--deps", deps]
        r = subprocess.run(cmd, cwd=TELPERION, env={"PYTHONPATH": "src", "PATH": "/usr/bin:/bin"},
                           capture_output=True, text=True)
        print(f"== {name}: rc={r.returncode}")
        print(r.stdout.strip())
        if r.returncode != 0:
            print(r.stderr.strip())
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
