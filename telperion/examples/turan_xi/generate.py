"""Turan / Laguerre inequalities for the Riemann xi function, compile-gated.

Certifies a_{k-1} a_{k+1} < a_k^2 for the even Taylor coefficients
a_k = [z^{2k}] xi(1/2+z) over IMPORTED rational enclosures (../enclosures.json),
via the worst-corner margin hi_{k-1} hi_{k+1} < lo_k^2 and the once-proved
`turan_from_enclosure` bridge.  RH-necessary (CNV 1986), NOT sufficient; finite
indices; enclosure-conditional.  See README.md.  conjecture1_proved=False.

    python3 examples/turan_xi/generate.py [--check]
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LeanProfile,
    TuranEnclosureCertificate,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent


def _cert() -> TuranEnclosureCertificate:
    enc = json.loads((HERE / "enclosures.json").read_text())["enclosures"]
    tup = tuple((enc[str(k)][0], enc[str(k)][1]) for k in range(len(enc)))
    return TuranEnclosureCertificate(name="turan_xi", enclosures=tup)


def build():
    cert = _cert()
    body = cert.lean()
    n = 1 + len(cert.certified_indices())          # bridge lemma + per-k theorems
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {},
        theorems=n)
    return emit(certify(_root()), LeanProfile(namespace=("RiemannTuran",)),
                [em], _validation(), file_name="RiemannTuran.lean")


def _root():
    return InequalityFamily(
        name="RiemannTuran", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda p: "turan_root", target=lambda p: sp.Integer(0))


def _validation() -> ValidationReport:
    cert = _cert()

    def exact_margins():
        # the exact-rational facts each emitted norm_num goal will close
        assert cert.check()
        for k in cert.certified_indices():
            assert cert.margin(k) > 0

    return ValidationReport.from_asserts([("turan_exact_margins", exact_margins)])


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
    print(f"RiemannTuran: {res.n_theorems} theorems (bridge + Turan k=1,2,3), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
