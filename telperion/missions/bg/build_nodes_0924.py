#!/usr/bin/env python3
"""2026-09-24 restructure of the BG campaign into its two honest targets (via the real CLI).

(1) GOAL -- the Brualdi-Goldwasser problem itself: the maximum of the Laplacian ratio
    per(L(T))/prod deg over n-vertex trees (Brualdi-Goldwasser 1984; open, Pant 2026 arXiv
    2605.14176).  Campaign conjecture 1 in its PINNED form: the per-size maximum is attained on a
    multi-hub cherry-backbone (R47BGConjecture.BGBackboneConjecture).  Reduced in Lean to the single
    open obligation StraightProgress_sized.
(2) MILESTONE -- the sharp rate ceiling Phi^11 <= 1 in the LITERAL planted matching-sum model
    (BGSCL): the <= half is kernel-proved (bg_ceiling); the sharp half is bell = 0 iff the
    5-arm spider rooted at its hub (the unique equality case, exhaustive over all trees n <= 16).

Statement bodies for Lean-proved nodes are VERBATIM declaration extracts (line ranges cited) so the
grant gate's normalized-containment check is meaningful.  New nodes land as DRAFT: promotion needs
an INDEPENDENT read-back (`mission audit`, refused for the authoring session) and then `mission grant`.
Run from telperion/ with PYTHONPATH=src:  python3 missions/bg/build_nodes_0924.py --session S
"""
import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

TELPERION = Path(__file__).resolve().parents[2]
R3 = TELPERION.parent / "proof" / "formalization" / "R3Cert"


def ex(module: str, lo: int, hi: int, strip: str) -> str:
    lines = (R3 / module).read_text().split("\n")
    text = "\n".join(lines[lo - 1:hi])
    if not text.rstrip().endswith(strip):
        raise SystemExit(f"extract {module}:{lo}-{hi} does not end with {strip!r}:\n{text}")
    return text.rstrip()[: -len(strip)].rstrip()


OPEN_S3 = "import Statements.BGDefs\nopen R3Cert R3Cert.Step3\n\n"
OPEN_SCL = "import Statements.BGDefs\nopen R3Cert.BGSCL\n\n"

NODES = [
    # (name, title, kind, deps, statement_body)
    ("BG.backbone_reduction",
     "One-obligation reduction: the size-preserving straightening StraightProgress_sized implies the pinned conjecture 1",
     "milestone", "",
     OPEN_S3 + ex("R47BGConjecture.lean", 62, 62, ":=")),
    ("BG.straight_progress",
     "Size-preserving straightening: every tree with positive structural defect has a same-size, Aobj-non-decreasing, defect-lowering step",
     "lemma", "",
     OPEN_S3 + "theorem straight_progress :\n"
     "    ∀ t : UTree, strDefect t ≠ 0 → ∃ t', StraightStep_sized t t'"),
    ("BG.rate_ceiling",
     "Literal rate ceiling (Phi^11 <= 1): the planted matching sum of every rooted tree is at most (621/64)^(n/11)",
     "milestone", "",
     OPEN_SCL + ex("BGSCLSubactionDispatch.lean", 280, 280, ":= ceiling_of_witness isSubaction_ρwit")),
    ("BG.tie_root_degree",
     "Equality forces a degree-6 root: bell b = 0 implies the root has exactly five children",
     "lemma", "",
     OPEN_SCL + ex("BGSCLHdom.lean", 653, 653, ":= by")),
    ("BG.ratio_rate_bound",
     "Laplacian-ratio rate bound: per(L)/prod deg of a tree rooted with d >= 1 children is at most (d+1)/d * rhoB^n",
     "lemma", "BG_phi_le_one,BG_h1_bridge",
     OPEN_S3 + ex("BGSCLRealizationBridge.lean", 60, 64, ":= by")),
    ("BG.rate_sharp",
     "Sharp rate ceiling: Phi^11 <= 1 for every rooted tree, with equality exactly at the 5-arm spider rooted at its hub (n = 11)",
     "milestone", "BG_rate_ceiling,BG_tie_root_degree",
     OPEN_SCL + "theorem bg_sharp :\n"
     "    (∀ b : Branch, bell b ≤ 0) ∧ (∀ b : Branch, bell b = 0 ↔ IsNearStarTie b)"),
    ("BG.backbone_conjecture",
     "Brualdi-Goldwasser maximizer, pinned conjecture 1: every tree is Aobj-dominated by a same-size multi-hub cherry-backbone",
     "goal", "BG_backbone_reduction,BG_straight_progress,BG_h1_bridge",
     OPEN_S3 + "theorem BG_backbone_conjecture :\n"
     "    ∀ t : UTree, ∃ s : List Hub, stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)"),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--session", required=True)
    args = ap.parse_args()
    for name, title, kind, deps, body in NODES:
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
            f.write(body)
            tmp = f.name
        cmd = [sys.executable, "-c",
               "from telperion.cli import main; import sys; sys.exit(main(sys.argv[1:]))",
               "mission", "--missions-root", "missions", "add", "bg", name,
               "--title", title, "--kind", kind, "--statement-file", tmp,
               "--session", args.session]
        if deps:
            cmd += ["--deps", deps]
        r = subprocess.run(cmd, cwd=TELPERION, env={"PYTHONPATH": "src", "PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin", "HOME": str(Path.home())},
                           capture_output=True, text=True)
        print(f"== {name}: rc={r.returncode}")
        print(r.stdout.strip())
        if r.returncode != 0:
            print(r.stderr.strip())
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
