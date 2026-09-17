#!/usr/bin/env python3
"""Readbacks, artifact links, and grants for the RH migration.

Every status flip goes through the real CLI verbs: `audit` (draft -> open, records the
read-back) and `grant` (open -> proved/refuted via the verify gate).  Grant failures are
reported, not papered over: the node stays open and the caller ledgers a NoGo attempt.
The goal node RH_conjecture is deliberately never audited: it stays draft.
Run from telperion/ with PYTHONPATH=src.
"""
import subprocess
import sys
from pathlib import Path

TELPERION = Path(__file__).resolve().parents[2]
AUDITOR = "rh-migration-session-2026-09-11"
LI = "../../examples/li_positivity/lean"
ZFB = "../../examples/zero_free_bridge/lean"

READBACKS = {
    "RH_zeta_repr_R1":
        "On the half-plane Re s > 1, the Riemann zeta function equals "
        "s/(s-1) - s * integral over x > 1 of {x} x^-(s+1) dx (the stripRHS) -- the "
        "Abel-summation seed identity of the fractional-part strip representation.",
    "RH_strip_repr":
        "The fractional-part strip representation zeta(s) = s/(s-1) - s * integral of "
        "{x} x^-(s+1) holds UNCONDITIONALLY on the whole punctured right half-plane "
        "{0 < Re s} minus {1}, assembled by the identity theorem from the discharged "
        "R1 (Abel summation), R2 (differentiation under the integral), and R3 "
        "(preconnectedness) inputs.",
    "RH_zeta_log_bound":
        "For 1 <= sigma <= 2 and |t| >= 2, the norm of zeta(sigma + it) is at most "
        "6 (1 + log |t|) -- the sharp near-line growth bound with explicit uniform "
        "constant 6.",
    "RH_zero_free_gamma5":
        "There is c > 0 such that every zero beta + i gamma of zeta with gamma >= 2 "
        "satisfies beta <= 1 - c / gamma^5 -- the elementary, Hadamard-free, "
        "unconditional zero-free region at polynomial rate.  Not a proof of RH.",
    "RH_zero_free_polylog":
        "There is c > 0 such that every zero beta + i gamma of zeta with gamma >= 2 "
        "satisfies beta <= 1 - c / (gamma^4 (1 + log 2 gamma)) -- strictly sharper than "
        "the elementary gamma^-5 region, still unconditional and Hadamard-free; the "
        "2t factor is upgraded via the sharp zeta log bound.  Not a proof of RH.",
    "RH_borel_caratheodory_deriv":
        "Borel-Caratheodory composed with a Cauchy estimate: if h is holomorphic on "
        "ball c R and its real part exceeds its centre value by at most M' > 0 on the "
        "disk, then |deriv h c| <= 2 M' / (R - r) for every 0 < r < R -- the "
        "derivative-from-real-part control the dVP region consumes.",
    "RH_dlvp_region_effective":
        "Every zeta-zero beta + i gamma with 3/4 <= beta < 1, |gamma| >= 55/16, and "
        "divisor value k >= 1 in the disk of radius 11/8 about 2 + i gamma satisfies "
        "beta <= 1 - dlvpRateC / log |gamma|, with dlvpRateC an explicit closed-form "
        "positive constant -- the classical de la Vallee Poussin rate made effective; "
        "the disk multiplicity datum enters as a hypothesis (discharged by the "
        "self-contained v4.32 wrapper node).",
    "RH_dlvp_zero_free_region":
        "Self-contained form: zeta(beta + i gamma) is nonzero whenever "
        "|gamma| >= 55/16 and beta > 1 - dlvpRateC / log |gamma| -- no multiplicity "
        "hypothesis remains.  The artifact lives on the v4.32 zero_free_bridge island "
        "(it was NOT among the 66 files #483 ported); cross-island grant per design "
        "section 2, kernel-checked by that island's own CI (AxiomGuardDlvp).",
    "RH_li_rung_certificates":
        "The topmost of the 20 emitted Li rungs: 0 <= lambda_20 = "
        "(taylorCoeff riemannXi 19).re, GIVEN the certified rational lower bound as an "
        "explicit hypothesis (the Arb enclosure trust seam).  Representative of the 20 "
        "homogeneous generated rungs n = 0..19, each a finite necessary-condition "
        "check conditional on its own enclosure hypothesis; NO finite prefix proves RH.",
    "RH_li_ladder_reduction":
        "Given nonnegativity of the first N Li coefficients, the Riemann Hypothesis is "
        "EQUIVALENT to nonnegativity of the infinite tail from N onward -- the ladder "
        "is a reduction of RH to its tail via the upstream li_criterion_rh_iff and "
        "proves NEITHER side of RH.",
    "RH_li_neg_refutes_rh":
        "The falsifiability face of the ladder: a certified NEGATIVE upper bound on any "
        "Li coefficient (taylorCoeff riemannXi n).re refutes RH through the upstream "
        "Li-criterion equivalence.  Never expected to fire; emitted so the ladder is "
        "falsifiable rather than confirmation-only.",
}

LINKS = {
    "RH_zeta_repr_R1": f"{LI}/StripReprR1.lean",
    "RH_strip_repr": f"{LI}/StripReprAssembled.lean",
    "RH_zeta_log_bound": f"{LI}/ZetaLogBound.lean",
    "RH_zero_free_gamma5": f"{LI}/ZeroFreeElementary.lean",
    "RH_zero_free_polylog": f"{LI}/ZeroFreePolylog.lean",
    "RH_borel_caratheodory_deriv": f"{LI}/DlvpBCDeriv.lean",
    "RH_dlvp_region_effective": f"{LI}/DlvpZetaRateEffective.lean",
    "RH_dlvp_zero_free_region": f"{ZFB}/DlvpZetaZeroFree.lean",
    "RH_li_rung_certificates": f"{LI}/LiPositivity.lean",
    "RH_li_ladder_reduction": f"{LI}/LiLadder.lean",
    "RH_li_neg_refutes_rh": f"{LI}/LiPositivity.lean",
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
        cli("audit", slug, "--campaign", "rh", "--text", text, "--auditor", AUDITOR)
    print("== artifact links ==")
    for slug, artifact in LINKS.items():
        cli("link", slug, "--campaign", "rh", "--artifact", artifact,
            "--kind", "lean_module", "--via", "direct")
    print("== grants (the gate) ==")
    failures = []
    for slug in GRANTS:
        if cli("grant", slug, "--campaign", "rh") != 0:
            failures.append(slug)
    if failures:
        print(f"GRANT FAILURES (leave open + ledger NoGo): {failures}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
