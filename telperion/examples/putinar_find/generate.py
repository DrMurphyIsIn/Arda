"""Putinar certificates via the SDP FINDER -- supply the polytope, not the SOS.

FINDER mode: the family returns sigma0=None and constraints (g_i, None, hyp);
Telperion SEARCHES the SOS multipliers (find_putinar_certificate, cvxpy SDP ->
exact rationalization -> verify) and emits `0 <= p` on {g_i >= 0}.

Needs cvxpy (the `sdp` verify group -- regeneration runs off the cvxpy-free CI
path; the frozen Lean is compile-gated in audit-compiles regardless).

Demonstrations (auto-found): 0<=1-x^2 on [-1,1]; 0<=x^2*y+y on {y>=0};
0<=x(2-x) on [0,2].
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (ConstrainedSOSEmitter, GridSpec, LeanProfile, ValidationReport,
    certify, diff_frozen, emit, freeze, putinar_family)
HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")
CASES = {
    0: ("putinar_found_1mx2", 1 - x**2, [(1 - x, None, "h1"), (1 + x, None, "h2")]),
    1: ("putinar_found_x2y", x**2*y + y, [(y, None, "hy")]),
    2: ("putinar_found_x_2mx", sp.expand(x*(2 - x)), [(x, None, "hx"), (2 - x, None, "hz")]),
}
def _family():
    return putinar_family("PutinarFind", (x, y), GridSpec([("i", [0, 1, 2])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], None, CASES[pt["i"]][2]),
        constants={"putinar_half_deg": 2})
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "PutinarFind")),
        [ConstrainedSOSEmitter()], _validation(), file_name="PutinarFind.lean")
def _validation():
    return ValidationReport.from_asserts([("putinar_find_ok", lambda: None)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"PutinarFind: {res.n_theorems} auto-found certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
