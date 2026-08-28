"""Newton inequalities for the Jensen sequence of the Riemann xi, compile-gated.

The correctly-normalized log-concavity: gamma_k^2 > gamma_{k-1} gamma_{k+1} for
gamma_k = k! a_k (a_k = [z^{2k}] xi(1/2+z)) -- Newton's inequalities for the
Jensen polynomials, sharper than the raw-a_k Turan inequality (`turan_xi`) and
the pairwise NECESSARY condition for Jensen-polynomial hyperbolicity, hence for
RH.  Reuses the proven `TuranEnclosureCertificate` product-vs-square bridge over
the gamma enclosures; certified for k=1..6.  RH-necessary, finite, enclosure-
conditional.  conjecture1_proved=False.

    python3 examples/newton_xi/generate.py [--check]
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec, InequalityFamily, LeanProfile, TuranEnclosureCertificate,
    ValidationReport, certify, diff_frozen, emit, freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent


def _cert():
    enc = json.loads((HERE / "gammas.json").read_text())["enclosures"]
    tup = tuple((enc[str(k)][0], enc[str(k)][1]) for k in range(len(enc)))
    # Newton = Turan product-vs-square, applied to gamma_k = k! a_k
    return TuranEnclosureCertificate(name="newton_xi", enclosures=tup)


def build():
    cert = _cert()
    body = cert.lean()
    n = 1 + len(cert.certified_indices())
    em = CustomAssemblyEmitter(statement_template="«thms»«branches»", branch_template="",
                               fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_root()), LeanProfile(namespace=("NewtonXi",)),
                [em], _validation(), file_name="NewtonXi.lean")


def _root():
    return InequalityFamily(name="NewtonXi", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "newton_root", target=lambda p: sp.Integer(0))


def _validation():
    cert = _cert()

    def exact():
        assert cert.check()
        for k in cert.certified_indices():
            assert cert.margin(k) > 0
    return ValidationReport.from_asserts([("newton_margins", exact)])


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
    print(f"NewtonXi: {res.n_theorems} theorems (bridge + Newton k=1..6), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
