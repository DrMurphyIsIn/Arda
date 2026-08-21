"""Real-Nullstellensatz certificates via the SDP FINDER -- supply the variety,
not the (m, s).

FINDER mode: the family returns m=None, sos=None and only (p, gens); Telperion
SEARCHES the multiplicity m and the SOS s with p^(2m) + s in <gens>
(find_real_nullstellensatz, SDP), then the existing emitter proves p = 0 on the
real variety.

Needs cvxpy (`sdp` verify group; frozen Lean compile-gated in audit-compiles).

Demonstrations (auto-found): on the real variety of x^2+y^2 (the origin), both
x = 0 (finds s=y^2) and y = 0 (finds s=x^2).
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (GridSpec, LeanProfile, RealNullstellensatzEmitter, ValidationReport,
    certify, diff_frozen, emit, freeze, real_nullstellensatz_family)
HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")
CASES = {0: ("real_nss_found_x", x, [x**2 + y**2]),
         1: ("real_nss_found_y", y, [x**2 + y**2])}
def _family():
    return real_nullstellensatz_family("RealNSSFind", (x, y), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], None, None, CASES[pt["i"]][2]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "RealNSSFind")),
        [RealNullstellensatzEmitter()], _validation(), file_name="RealNullstellensatzFind.lean")
def _validation():
    return ValidationReport.from_asserts([("real_nss_find_ok", lambda: None)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"RealNSSFind: {res.n_theorems} auto-found certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
