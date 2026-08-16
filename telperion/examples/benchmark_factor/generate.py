"""Benchmark-factor isolation certificate, compile-gated.

Splits Phi^11(N(0,s)) = rho(s)^11 * B(s): the raw Laplacian ratio rho=(4/3)(3/2)^s is gauge-flat
(rho(s+1)/rho(s)=3/2, zero curvature — the Laplacian is inert), and the benchmark factor B carries
ALL the curvature (q=(s+1)(4s+7), a Laplacian minor) and the 23-content (621^2=3^6*23^2).  The crux
is localized to B; at s=5 the Laplacian growth cancels the benchmark exactly (integer identity).
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
    BenchmarkFactorCertificate,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    benchmark,
    certify,
    diff_frozen,
    emit,
    freeze,
    phi11,
    rho,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent

CERT = BenchmarkFactorCertificate(anchor=5, reach=3)


def build():
    body = CERT.lean()
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "BenchmarkFactor")), [em],
                _v(), file_name="BenchmarkFactor.lean")


def _t():
    return InequalityFamily(name="BenchmarkFactor", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "benchmarkfactor_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def isolates():
        assert CERT.check()
        # Laplacian is inert: rho ratio is exactly 3/2 everywhere
        assert all(rho(s + 1) / rho(s) == Fr(3, 2) for s in range(0, 8))
        # the factorization is exact and the curvature/23-content live in B
        assert all(phi11(s) == rho(s) ** 11 * benchmark(s) for s in range(0, 8))
        assert CERT.curvature_in_benchmark()

    def resonance():
        # rho(5)^11 * B(5) = 1 and the integer identity
        assert rho(5) ** 11 * benchmark(5) == 1 and phi11(5) == 1
        step, q, cn, cd = CERT.benchmark_step()
        assert sp.factor(q) == (sp.Symbol("s") + 1) * (4 * sp.Symbol("s") + 7)
        assert cn == 2 ** 12 and cd == 621 ** 2 == 3 ** 6 * 23 ** 2

    return ValidationReport.from_asserts(
        [("benchmark_isolation", isolates), ("resonance_cancellation", resonance)])


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
    print(f"BenchmarkFactor: {res.n_theorems} facts (Laplacian flat; benchmark carries "
          f"curvature+23-content), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
