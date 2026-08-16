"""Competitor-extremality certificate (crux b), compile-gated.

rho(T)=per(L)/prod(deg) is the monomer-dimer partition function; the near-star N(0,s) maximizes it
over all trees on 2s+1 vertices (verified), winning because length-2 legs maximize the matching
free-energy density. Emits the binding witness rho(N(0,s)) > runner-up. All-n statement OPEN.
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
    CompetitorExtremalityCertificate,
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

# s=2..5 (n=5,7,9,11) — includes the tie N(0,5); keeps the all-trees verification tractable.
CERTS = [CompetitorExtremalityCertificate(s) for s in (2, 3, 4, 5)]


def build():
    body = "\n".join(c.lean() for c in CERTS)
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "CompetitorExtremality")), [em],
                _v(), file_name="CompetitorExtremality.lean")


def _t():
    return InequalityFamily(name="CompetitorExtremality", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "compext_root", target=lambda p: sp.Integer(0))


def _v():
    def extremal():
        for c in CERTS:
            assert c.check() and c.is_extremal()
        # the tie N(0,5) is the maximizer at n=11 with rho = 81/8
        assert CompetitorExtremalityCertificate(5).near_star_rho() == Fr(81, 8)

    return ValidationReport.from_asserts([("competitor_extremality", extremal)])


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
    print(f"CompetitorExtremality: {res.n_theorems} facts (near-star maximizes rho, n=5..11), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
