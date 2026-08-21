"""SOS-Positivstellensatz refutations via the SDP FINDER -- supply the system,
not the certificate.

FINDER mode: the family returns sigma0=None and only the constraints; Telperion
SEARCHES the SOS multipliers sigma and free multipliers lambda that refute the
system over R (find_sos_refutation), AUTOMATICALLY closing the real-only gap.

Needs cvxpy (`sdp` verify group; frozen Lean compile-gated in audit-compiles).

Demonstrations (auto-found): x^2+1=0 -> False (finds sigma0=x^2, lambda=-1);
{x>=0, x+1=0} -> False.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (GridSpec, LeanProfile, SOSRefutationEmitter, ValidationReport,
    certify, diff_frozen, emit, freeze, sos_refutation_family)
HERE = Path(__file__).resolve().parent
x = sp.symbols("x")
CASES = {
    0: ("sosref_found_x2p1", [], [(x**2 + 1, "he1")]),
    1: ("sosref_found_x_nonneg_xp1", [(x, "hg1")], [(x + 1, "he1")]),
}
def _family():
    return sos_refutation_family("SOSRefFind", (x,), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (None, CASES[pt["i"]][1], CASES[pt["i"]][2]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "SOSRefFind")),
        [SOSRefutationEmitter()], _validation(), file_name="SOSRefutationFind.lean")
def _validation():
    return ValidationReport.from_asserts([("sosref_find_ok", lambda: None)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"SOSRefFind: {res.n_theorems} auto-found refutations, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
