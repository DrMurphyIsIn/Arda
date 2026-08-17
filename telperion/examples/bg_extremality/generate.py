"""BG competitor-extremality certificate (rooted Phi -- the CORRECT quantity), compile-gated.

The near-star N(0,s) maximizes the rooted branch Phi^11 (max over roots = the Brualdi-Goldwasser
invariant) over all trees on n=2s+1 vertices, verified exhaustively (n<=17), strictly beating the
runner-up; the tie Phi^11=1 occurs at n=11.  This is the CORRECT competitor extremality -- unlike raw
rho=per(L)/prod deg, which is a different (monomer-dimer) problem maximized by caterpillars.
conjecture1_proved=False.

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
    BGExtremalityCertificate,
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

CERTS = [BGExtremalityCertificate(s) for s in (2, 3, 4, 5)]   # n = 5,7,9,11 (incl. the tie)


def build():
    body = "\n".join(c.lean() for c in CERTS)
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "BGExtremality")), [em],
                _v(), file_name="BGExtremality.lean")


def _t():
    return InequalityFamily(name="BGExtremality", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "bgext_root", target=lambda p: sp.Integer(0))


def _v():
    def extremal():
        for c in CERTS:
            assert c.check() and c.is_extremal()
        assert BGExtremalityCertificate(5).near_star_phi() == Fr(1)  # the tie at n=11

    return ValidationReport.from_asserts([("bg_competitor_extremality", extremal)])


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
    print(f"BGExtremality: {res.n_theorems} facts (near-star maximizes rooted Phi, n=5..11), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
