"""M-convexity (discrete-convex) certificates, compile-gated.

The integer-native structure: a function on a finite integer support is M-concave
iff the exchange axiom holds -- a FINITE family of exact rational inequalities.
Tropicalized Lorentzian polynomials ARE M-convex functions on ℤ (Branden-Huh /
Murota), so this is the discrete side of the one framework built for our failure
mode (smooth fails at the tie, integer works).

Demonstrated on the separable-concave f(x) = -Σ xᵢ² on the base {Σ xᵢ = 2}
(canonical M-concave), with a non-concave negative control checked in validation.
Aiming this at the normalized matching generating polynomial (Lorentzian => its
log-coefficients M-concave, tight at the integer tie s=5) is the research target.

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
    MConvexityCertificate,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
    is_m_concave,
    separable_concave_on_base,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent

F = separable_concave_on_base(2, 3, lambda t: -t ** 2)   # M-concave on {Σ=2}


def build():
    cert = MConvexityCertificate("mconcave_sepsq", F)
    body = cert.lean()
    n = body.count("theorem ")
    emitter = CustomAssemblyEmitter(
        statement_template="«thms»«branches»",
        branch_template="",
        fills=lambda fam: {"thms": body},
        branch_fills=lambda inst: {},
        theorems=n,
    )
    return emit(certify(_trivial()), LeanProfile(namespace=("G1", "MConvex")),
                [emitter], _validation(), file_name="MConvex.lean")


def _trivial() -> InequalityFamily:
    return InequalityFamily(
        name="MConvex", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "mconvex_root", target=lambda pt: sp.Integer(0))


def _validation() -> ValidationReport:
    def discriminates():
        assert MConvexityCertificate("t", F).check()          # separable-concave: M-concave
        # non-concave control is NOT M-concave
        from fractions import Fraction as Fr
        g = {x: Fr((x[0] * 7 + x[1] * 3) % 5) for x in F}
        assert not is_m_concave(g)
    return ValidationReport.from_asserts([("mconvex_discriminates", discriminates)])


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
    print(f"MConvex: {res.n_theorems} exchange inequalities (M-concavity on ℤ), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
