"""Termwise-scope / obstruction certificate, compile-gated.

Demonstrates the honest scope boundary of termwise-nonnegativity arguments: on a FOREST support the
argument is valid (matching collapse, nonnegative weights); on a CYCLIC support there is a PSD
frustration witness with a negative permutation-product, so the method fails (why the tree
permanental-dominance proof does not reach Lieb's general PSD conjecture).  conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LeanProfile,
    TermwiseScopeCertificate,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent

# in-scope (path P4, a forest) and out-of-scope (triangle, the minimal frustrated cycle)
FOREST = TermwiseScopeCertificate(4, ((0, 1), (1, 2), (2, 3)))
CYCLE = TermwiseScopeCertificate(3, ((0, 1), (1, 2), (0, 2)))


def build():
    body = FOREST.lean() + CYCLE.lean()
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "Scope")), [em],
                _v(), file_name="Scope.lean")


def _t():
    return InequalityFamily(name="Scope", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "scope_root", target=lambda p: sp.Integer(0))


def _v():
    def scope():
        assert FOREST.in_scope() and FOREST.check()
        assert FOREST.frustration_witness() is None
        assert not CYCLE.in_scope() and CYCLE.check()

    def obstruction():
        A, perm, prod = CYCLE.frustration_witness()
        assert prod < 0                                   # negative permutation-product
        assert all(e >= 0 for e in sp.Matrix(A).eigenvals())  # PSD
        assert CYCLE._diagonally_dominant(A)              # => PSD by Gershgorin

    return ValidationReport.from_asserts(
        [("scope_boundary", scope), ("frustration_witness_is_PSD", obstruction)])


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
    print(f"Scope: {res.n_theorems} facts (forest in-scope; triangle frustration witness), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
