"""Degree-3 Jensen-Polya hyperbolicity for the Riemann xi, compile-gated.

Certifies the cubic Jensen polynomial J^{3,n} of xi is hyperbolic (discriminant
> 0) for shifts n=0,1,2 over imported rational enclosures of gamma_k = k! a_k,
via the worst-corner bound and the once-proved `cubic_jensen_pos_of_enclosure`
bridge.  RH-necessary (Laguerre-Polya), NOT sufficient; finite; enclosure-
conditional.  conjecture1_proved=False.

    python3 examples/jensen_xi/generate.py [--check]
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CubicJensenCertificate,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent


def _cert() -> CubicJensenCertificate:
    enc = json.loads((HERE / "gammas.json").read_text())["enclosures"]
    tup = tuple((enc[str(k)][0], enc[str(k)][1]) for k in range(len(enc)))
    return CubicJensenCertificate(name="cubic_jensen_xi", enclosures=tup)


def build():
    cert = _cert()
    body = cert.lean()
    n = 1 + len(cert.certified_shifts())            # bridge + per-shift theorems
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_root()), LeanProfile(namespace=("JensenXi",)),
                [em], _validation(), file_name="CubicJensen.lean")


def _root():
    return InequalityFamily(
        name="JensenXi", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda p: "jensen_root", target=lambda p: sp.Integer(0))


def _validation() -> ValidationReport:
    cert = _cert()

    def exact_discriminants():
        assert cert.check()
        for n in cert.certified_shifts():
            assert cert.disc_lo(n) > 0

    return ValidationReport.from_asserts([("cubic_jensen_worst_corner", exact_discriminants)])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        r = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if r.ok else "FAILED")
        return 0 if r.ok else 1
    freeze(res, HERE / "frozen")
    print(f"CubicJensen: {res.n_theorems} theorems (bridge + hyperbolicity n=0,1,2), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
