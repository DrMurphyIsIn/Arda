"""Total-positivity (3x3 Toeplitz minor) certificates for the Riemann xi, compile-
gated.  RH => G(u)=sum a_k u^k is a Polya-frequency function => its Toeplitz
matrix is totally positive; the 3x3 minors are certified positive for m=2..5 over
imported rational enclosures of a_k = [z^{2k}] xi(1/2+z).  RH-necessary, finite,
enclosure-conditional.  conjecture1_proved=False.

    python3 examples/toeplitz_xi/generate.py [--check]
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec, InequalityFamily, LeanProfile, ToeplitzMinorCertificate,
    ValidationReport, certify, diff_frozen, emit, freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent


def _cert():
    enc = json.loads((HERE / "a_coeffs.json").read_text())["enclosures"]
    tup = tuple((enc[str(k)][0], enc[str(k)][1]) for k in range(len(enc)))
    return ToeplitzMinorCertificate(name="toeplitz3_xi", enclosures=tup)


def build():
    cert = _cert()
    body = cert.lean()
    n = 1 + len(cert.certified_m())
    em = CustomAssemblyEmitter(statement_template="«thms»«branches»", branch_template="",
                               fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_root()), LeanProfile(namespace=("ToeplitzXi",)),
                [em], _validation(), file_name="ToeplitzXi.lean")


def _root():
    return InequalityFamily(name="ToeplitzXi", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "toeplitz_root", target=lambda p: sp.Integer(0))


def _validation():
    cert = _cert()

    def exact():
        assert cert.check()
        for m in cert.certified_m():
            assert cert.minor_lo(m) > 0
    return ValidationReport.from_asserts([("toeplitz_worst_corner", exact)])


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
    print(f"ToeplitzXi: {res.n_theorems} theorems (bridge + minors m=2..5), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
