"""Bregman/entropy permanent-bound certificates (degree-normalized), compile-gated.

Avenue C: per(A) <= prod_v (d_v!)^(1/d_v), cleared to the exact integer inequality
per(A)^L <= prod (d_v!)^(L/d_v), L = lcm(d_v).  Natively degree-normalized (matches
the prod-deg denominator); equality iff the entropy independence condition -- a tie
candidate.  An independent cross-check on avenues A/B.  conjecture1_proved=False.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    BregmanCertificate,
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
CERTS = [
    BregmanCertificate("bregman_path3", ((1, 1, 0), (1, 1, 1), (0, 1, 1))),
    BregmanCertificate("bregman_c4",
                       ((1, 1, 0, 1), (1, 1, 1, 0), (0, 1, 1, 1), (1, 0, 1, 1))),
]


def build():
    body = "\n".join(c.lean() for c in CERTS)
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {},
        theorems=len(CERTS))
    return emit(certify(_t()), LeanProfile(namespace=("G1", "Entropy")), [em],
                _v(), file_name="Entropy.lean")


def _t():
    return InequalityFamily(name="Entropy", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "entropy_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def ok():
        assert all(c.check() for c in CERTS)
    return ValidationReport.from_asserts([("bregman", ok)])


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
    print(f"Entropy: {res.n_theorems} Bregman bounds, hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
