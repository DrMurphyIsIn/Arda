"""Product-telescope certificate — the integration end of the gauge tower, compile-gated.

Certifies PROD_{t<s}(1-1/q(t)) = 3(s+1)/(4s+3) (telescoping via the shifted potentials P1=t+1,
P2=4t+3), giving the closed form R(s)=(621/64)(529/486)^s(3(s+1)/(4s+3))^11 with resonance R(5)=1.
The dual of the differencing/unimodality end; together they bracket the near-star from both ends of
the tower and meet at the lone integer identity 64*243*23=621*576.  conjecture1_proved=False.

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
    LeanProfile,
    TelescopeCertificate,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
    telescope_q,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent

CERT = TelescopeCertificate(anchor=5, reach=3)


def build():
    body = CERT.lean()
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "TelescopeProduct")), [em],
                _v(), file_name="TelescopeProduct.lean")


def _t():
    return InequalityFamily(name="TelescopeProduct", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "telescopeproduct_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def telescopes():
        assert CERT.check()
        assert CERT.key_identity()                    # q-1=(t+2)(4t+3), q=(t+1)(4t+7), shifts
        # the direct product equals the telescoped closed form at every base point
        assert all(CERT.telescoped_product(s) == CERT.closed_product(s) for s in range(0, 9))

    def recovery():
        # the integrated closed form reproduces the exact sequence, incl. the resonance
        assert CERT.recovers_closed_form()
        assert CERT.R(5) == 1 and CERT.closed_product(5) == Fr(18, 23)
        # spot-check a telescoping value: PROD_{t<3}(1-1/q) = 4/5, q(0,1,2)=7,22,45
        assert telescope_q(0) == 7 and telescope_q(1) == 22 and telescope_q(2) == 45
        assert CERT.telescoped_product(3) == Fr(4, 5)

    return ValidationReport.from_asserts(
        [("product_telescopes", telescopes), ("closed_form_recovery", recovery)])


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
    print(f"TelescopeProduct: {res.n_theorems} facts (integration end; product telescopes to "
          f"closed form, resonance R(5)=1), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
