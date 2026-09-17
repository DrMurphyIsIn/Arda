#!/usr/bin/env python3
"""Create the BG campaign nodes via the real `telperion mission add` CLI.

Statement bodies for PROVEN/REFUTED strata are VERBATIM declaration extracts from the
proof/ artifacts (line ranges cited), so the grant gate's normalized-containment check is
meaningful.  Draft-node statements are hand-authored renderings, marked in comments.
Run from telperion/ with PYTHONPATH=src.
"""
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


OPEN_R3 = "import Statements.BGDefs\nopen R3Cert\n\n"
OPEN_S3 = "import Statements.BGDefs\nopen R3Cert R3Cert.Step3\n\n"
OPEN_CJ = "import Statements.BGDefs\nopen R3Cert.CappedJointConfig R3Cert.GStepCore\n\n"

NODES = [
    # (name, title, kind, deps, statement_body)
    ("BG.cavity_recursion",
     "H2 cavity recursion node step: Zopen/Ztot ratio collapses to 1/(1+sum w r)",
     "lemma", "",
     "import Mathlib\n\n" + ex("Matching.lean", 232, 234, ":= by")),
    ("BG.h1_bridge",
     "P1 bridge capstone: Aobj IS the Laplacian permanent ratio of the realized tree (pi_utree)",
     "lemma", "BG_cavity_recursion",
     OPEN_S3 + ex("R47Tree.lean", 158, 161, ":= by")),
    ("BG.lb_classification",
     "(L)/(B) classification capstone: Pval is a valid plain potential",
     "lemma", "",
     OPEN_R3 + ex("PotentialFinal.lean", 41, 41, ":=")),
    ("BG.phi_le_one",
     "The Phi <= 1 hinge: logPhi b <= 0 for every Branch (discharging potential telescoped)",
     "milestone", "BG_lb_classification",
     OPEN_R3 + ex("PotentialFinal.lean", 49, 49, ":=")),
    ("BG.merge_layer",
     "Certified merge layer capstone: every Balanced+Capped state ordered-merges to a perL-non-decreasing normal form",
     "lemma", "BG_h1_bridge",
     OPEN_S3 + ex("R47MergePerL.lean", 31, 36, ":= by")),
    ("BG.near_star_tail",
     "Near-star tail: logPhi (N(c,k)) <= 0 for the whole family",
     "lemma", "",
     OPEN_R3 + ex("NearStar.lean", 142, 142, ":= by")),
    ("BG.near_star_tie",
     "Near-star tie diagonal: logPhi (N(c,k)) = 0 when c+k = 5 (the six 11-vertex ties)",
     "lemma", "",
     OPEN_R3 + ex("NearStar.lean", 146, 146, ":= by")),
    ("BG.fractal_asymptote",
     "Near-star asymptote arithmetic core: (3/2)^11 < (621/64)^2, i.e. D_infinity < 1",
     "lemma", "",
     "import Mathlib\n\n" + ex("FractalTail.lean", 41, 41, ":= by norm_num")),
    ("BG.gstep_closure",
     "Capped-joint g-step closure: the config g-step is <= 1 at every arity over achievable messages",
     "milestone", "",
     OPEN_CJ + ex("CappedJointClosure.lean", 142, 143, ":= by")),
    # --- open leaf: prose-PROVEN by exact toolkit arithmetic, NO kernel artifact (finding) ---
    ("BG.r2_double_near_star",
     "R2 double-near-star family bound: logPhi (DN(a,b)) < 0 for all a,b >= 2 (rooted rendering)",
     "lemma", "",
     OPEN_R3 + "theorem r2_double_near_star (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :\n"
     "    logPhi (Branch.node 0 (List.replicate a armB ++\n"
     "      [Branch.node 0 (List.replicate b armB)])) < 0"),
    # --- drafts: no faithful kernel vocabulary yet; renderings provisional (findings) ---
    ("BG.master_inequality",
     "Master inequality (arm-maximality; PROVISIONAL rendering): (2+mu_B)^11 F_B <= (64/621) 3^11 with F_B = exp(11 logPhi)",
     "lemma", "",
     OPEN_R3 + "theorem master_inequality :\n"
     "    ∀ b : Branch, (2 + cav b) ^ 11 * Real.exp (11 * logPhi b) ≤ (64 / 621) * 3 ^ 11"),
    ("BG.r2_multihub_maximality",
     "R2 multi-hub maximality (PROVISIONAL rendering): at any size carrying a DN, the best DN dominates every multi-hub tree",
     "lemma", "",
     OPEN_S3 + "theorem r2_multihub_maximality :\n"
     "    ∀ t : UTree, 2 ≤ hubCountRoot t →\n"
     "      ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →\n"
     "        usize (backboneU [([], a), ([], b)]) = usize t →\n"
     "          ∃ a' b' : ℕ, 2 ≤ a' ∧ 2 ≤ b' ∧\n"
     "            usize (backboneU [([], a'), ([], b')]) = usize t ∧\n"
     "            Aobj t ≤ Aobj (backboneU [([], a'), ([], b')])"),
    # --- the refuted capstone Hnorm (2026-09-11, R47HnormFalse52) ---
    ("BG.hnorm_capstone",
     "Capstone Hnorm (tree->hub normalization): every tree is dominated by a Balanced+Capped state of its own size -- REFUTED at n=52",
     "lemma", "",
     OPEN_S3 + "theorem hnorm_capstone :\n"
     "    ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧\n"
     "        stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)"),
    # --- the goal (draft; NOT proved; conjecture1_proved = False) ---
    ("BG.conjecture1",
     "BG <=-half sharp statement (Branch-model rendering): logPhi <= 0 everywhere, = 0 exactly on the near-star tie diagonal c+k=5",
     "goal",
     ",".join(["BG_master_inequality", "BG_r2_multihub_maximality", "BG_phi_le_one",
               "BG_h1_bridge", "BG_cavity_recursion", "BG_merge_layer", "BG_gstep_closure",
               "BG_near_star_tail", "BG_near_star_tie", "BG_fractal_asymptote",
               "BG_lb_classification", "BG_r2_double_near_star"]),
     OPEN_R3 + "theorem BG_conjecture1 :\n"
     "    (∀ b : Branch, logPhi b ≤ 0) ∧\n"
     "    (∀ b : Branch, logPhi b = 0 ↔ ∃ c k : ℕ, c + k = 5 ∧ b = nearStarB c k)"),
]


def main() -> int:
    for name, title, kind, deps, body in NODES:
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
            f.write(body)
            tmp = f.name
        cmd = [sys.executable, "-c",
               "from telperion.cli import main; import sys; sys.exit(main(sys.argv[1:]))",
               "mission", "--missions-root", "missions", "add", "bg", name,
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
