"""Dimensional-lift certificates (1-D -> 2-D -> general d), compile-gated.

Lifts the near-star bridge crossing to ℤ^d: certifies f <= 1 on the integer
lattice via a finite base box + monotone tails per direction.  Demonstrated on a
genuine 2-D crux family -- hub with k1 arms + k2 leaves -- whose maximum lives on
the k2=0 EDGE (the 1-D near-star), with monotone decrease into the interior.
The base-box facts are emitted here; the k1-tail is the near-star bridge and the
k2-tail is leaf-monotone.  conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LatticeBoxCertificate,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent

ARM = Fr(64, 621) * Fr(3, 2) ** 11 * Fr(64, 621)
LEAF = Fr(64, 621)


def phi(x):
    k1, k2 = x
    S = Fr(k1, 3) + k2
    d = k1 + k2 + 1
    z = Fr(3, 3 * d)
    return Fr(64, 621) * (1 + z * S) ** 11 * ARM ** k1 * LEAF ** k2


CERT = LatticeBoxCertificate("arms_leaves_2d", 2, phi, (5, 2), Fr(1))


def build():
    body = CERT.lean()
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "LatticeBox")), [em],
                _v(), file_name="LatticeBox.lean")


def _t():
    return InequalityFamily(name="LatticeBox", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "latticebox_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def lifts():
        assert CERT.check()                              # base box + monotone tails
        mx, argmax, pinned = CERT.extremal_face()
        assert mx == 1 and argmax == [(5, 0)]            # tie on the near-star edge
        assert pinned == (1,)                            # 2-D max on the 1-D k2=0 face
    return ValidationReport.from_asserts([("dimensional_lift", lifts)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    res = build()
    if a.check:
        r = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if r.ok else "FAILED")
        return 0 if r.ok else 1
    freeze(res, HERE / "frozen")
    print(f"LatticeBox: {res.n_theorems} base-box facts (2-D lift; max on 1-D "
          f"near-star edge), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
