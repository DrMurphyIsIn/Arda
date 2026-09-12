#!/usr/bin/env python3
"""Readbacks, artifact links, and grants for the BG migration.

Every status flip goes through the real CLI verbs: `audit` (draft -> open, records the
read-back) and `grant` (open -> proved/refuted via the verify gate).  Grant failures are
reported, not papered over: the node stays open and the caller ledgers a NoGo attempt.
Run from telperion/ with PYTHONPATH=src.
"""
import subprocess
import sys
from pathlib import Path

TELPERION = Path(__file__).resolve().parents[2]
AUDITOR = "migration-session-2026-09-12"
ART = "../../../proof/formalization/R3Cert"

READBACKS = {
    "BG_cavity_recursion":
        "For a rooted-tree node with finitely many children whose total partition functions are "
        "nonzero, the ratio of root-unmatched to total matching partition function equals "
        "1/(1 + sum of edge weight times child cavity ratio) -- the per-node step the tree "
        "induction turns into the H2 recursion.",
    "BG_h1_bridge":
        "For every bare rooted tree, the permanent of the Laplacian of its true-degree "
        "realization divided by the product of vertex degrees equals the raw matching partition "
        "function Aobj -- the machine-checked per(L) bridge (P1 capstone).",
    "BG_lb_classification":
        "The explicit piecewise potential Pval is nonnegative and satisfies the per-node "
        "super-solution inequality at every plain node -- the classification capstone the "
        "telescoped Phi<=1 bound consumes.",
    "BG_phi_le_one":
        "The log-amplitude of every branch of the DEC cavity model is at most zero, i.e. "
        "Phi <= 1 holds unconditionally over the Branch model (non-strict half; the sharp "
        "statement remains open).",
    "BG_merge_layer":
        "Every balanced capped hub state rewrites by ordered merges to a stuck normal form "
        "whose Laplacian-permanent ratio is no smaller -- the certified merge layer in perL form.",
    "BG_near_star_tail":
        "Every near-star N(c,k) has log-amplitude at most zero -- the all-n near-star tail bound.",
    "BG_near_star_tie":
        "Whenever c+k = 5 the near-star N(c,k) has log-amplitude exactly zero -- the six "
        "eleven-vertex ties of the rooted invariant.",
    "BG_fractal_asymptote":
        "The rational inequality (3/2)^11 < (621/64)^2 -- the arithmetic core certifying that "
        "the near-star family's per-vertex density limit lies strictly below 1.",
    "BG_gstep_closure":
        "For every list of achievable cavity messages, the capped-joint g-step value "
        "(base^11 times the product of per-child caps over gamma) is at most 1, at every arity.",
    "BG_r2_double_near_star":
        "Rooted at one of its two hubs, the double near-star DN(a,b) with a,b >= 2 arms has "
        "strictly negative log-amplitude -- registry rendering of the toolkit's exact-arithmetic "
        "R2 family bound; NO kernel artifact exists yet, so this node stays open (finding).",
    "BG_hnorm_capstone":
        "The tree-to-hub normalization Hnorm: every bare tree would be Aobj-dominated by some "
        "balanced capped hub state of exactly its own vertex count -- REFUTED 2026-09-11 by the "
        "exact four-core witness T(6,6,6,6) at n = 52 (R47HnormFalse52).",
}

LINKS = {
    "BG_cavity_recursion": f"{ART}/Matching.lean",
    "BG_h1_bridge": f"{ART}/R47Tree.lean",
    "BG_lb_classification": f"{ART}/PotentialFinal.lean",
    "BG_phi_le_one": f"{ART}/PotentialFinal.lean",
    "BG_merge_layer": f"{ART}/R47MergePerL.lean",
    "BG_near_star_tail": f"{ART}/NearStar.lean",
    "BG_near_star_tie": f"{ART}/NearStar.lean",
    "BG_fractal_asymptote": f"{ART}/FractalTail.lean",
    "BG_gstep_closure": f"{ART}/CappedJointClosure.lean",
    "BG_hnorm_capstone": f"{ART}/R47HnormFalse52.lean",
    # BG_r2_double_near_star: intentionally NO artifact (toolkit-exact only; finding)
}

GRANTS = list(LINKS)


def cli(*args: str) -> int:
    r = subprocess.run(
        [sys.executable, "-c",
         "from telperion.cli import main; import sys; sys.exit(main(sys.argv[1:]))",
         "mission", "--missions-root", "missions", *args],
        cwd=TELPERION, env={"PYTHONPATH": "src", "PATH": "/usr/bin:/bin"},
        capture_output=True, text=True)
    print(f"$ mission {' '.join(args[:2])}...: rc={r.returncode} | {r.stdout.strip()}"
          + (f" | ERR {r.stderr.strip()}" if r.returncode != 0 and r.stderr.strip() else ""))
    return r.returncode


def main() -> int:
    print("== read-backs (draft -> open) ==")
    for slug, text in READBACKS.items():
        cli("audit", slug, "--campaign", "bg", "--text", text, "--auditor", AUDITOR)
    print("== artifact links ==")
    for slug, artifact in LINKS.items():
        cli("link", slug, "--campaign", "bg", "--artifact", artifact,
            "--kind", "lean_module", "--via", "direct")
    print("== grants (the gate) ==")
    failures = []
    for slug in GRANTS:
        if cli("grant", slug, "--campaign", "bg") != 0:
            failures.append(slug)
    if failures:
        print(f"GRANT FAILURES (leave open + ledger NoGo): {failures}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
