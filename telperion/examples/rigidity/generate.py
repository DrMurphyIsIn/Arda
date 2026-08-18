"""Arithmetic rigidity certificate, compile-gated.

The one sharpened crux tool with a genuine finite certificate: the tie's zero is
an INTEGER coincidence, 64·243·23 = 621·576, pinning R(5) = 1 exactly with strict
local maximum (R(4) < 1, R(6) < 1).  This is why every smooth tool overshoots the
tie -- they osculate the continuous critical point c* ≈ 3.82, not the integer 5.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.bg import (  # noqa: E402
    ArithmeticRigidityCertificate,
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


def build():
    cert = ArithmeticRigidityCertificate()
    emitter = CustomAssemblyEmitter(
        statement_template="«thms»«branches»",
        branch_template="",
        fills=lambda fam: {"thms": cert.lean()},
        branch_fills=lambda inst: {},
        theorems=4,
    )
    return emit(certify(_trivial()), LeanProfile(namespace=("G1", "Rigidity")),
                [emitter], _validation(), file_name="Rigidity.lean")


def _trivial() -> InequalityFamily:
    return InequalityFamily(
        name="Rigidity", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "rigidity_root", target=lambda pt: sp.Integer(0))


def _validation() -> ValidationReport:
    def rigidity():
        assert ArithmeticRigidityCertificate().check()
    return ValidationReport.from_asserts([("arithmetic_rigidity", rigidity)])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok:
            print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"Rigidity: {res.n_theorems} arithmetic-rigidity facts (tie identity + "
          f"R(5)=1 strict max), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
