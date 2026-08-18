"""Root-interlacing certificates, compile-gated + grounded on matching polynomials.

Certifies interlacing via Wronskian sign-definiteness (Hermite-Kakeya-Obreschkoff),
the tool the Brualdi-Goldwasser telescoping wall structurally lacks (interlacing >
log-concavity, handles non-additive recursions -- the MSS avenue).

Demonstrations:
  * (x^2-1, x): the textbook interlacing pair, Wronskian x^2+1;
  * (mu(P3), mu(P2)) = (x^3-2x, x^2-1): the LAPLACIAN MATCHING POLYNOMIALS of the
    path recursion P3 -> P2 -- exactly the object the interlacing avenue targets;
    their roots interlace (Heilmann-Lieb real-rootedness) and the Wronskian
    x^4-x^2+2 = (x^2-1/2)^2 + 7/4 is SOS-certified sign-definite.

A NEGATIVE CONTROL (x^2-1, x^2-4, which do NOT interlace -> W = -6x sign-changing)
is checked in validation to confirm the certificate discriminates.

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
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402
from telperion.bg.interlacing import InterlacingCertificate, interlaces  # noqa: E402

HERE = Path(__file__).resolve().parent
x = sp.symbols("x")

PAIRS = [
    ("interlace_x2m1_x", x**2 - 1, x),
    ("interlace_matching_P3_P2", x**3 - 2 * x, x**2 - 1),
]
NEG_CONTROL = (x**2 - 1, x**2 - 4)   # do NOT interlace


def certs():
    return [InterlacingCertificate(name, p, q, x) for name, p, q in PAIRS]


def build():
    body = "\n".join(c.lean() for c in certs())
    emitter = CustomAssemblyEmitter(
        statement_template="«thms»«branches»",
        branch_template="",
        fills=lambda fam: {"thms": body},
        branch_fills=lambda inst: {},
        theorems=len(PAIRS),
    )
    return emit(certify(_trivial()), LeanProfile(namespace=("G1", "Interlacing")),
                [emitter], _validation(), file_name="Interlacing.lean")


def _trivial() -> InequalityFamily:
    return InequalityFamily(
        name="Interlacing", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "interlacing_root", target=lambda pt: sp.Integer(0))


def _validation() -> ValidationReport:
    def discriminates():
        for c in certs():
            assert c.check(), c.name              # positives interlace
        p, q = NEG_CONTROL
        assert not interlaces(p, q, x)            # negative control does NOT
        # and the SOS identity is exact for every emitted certificate
        for c in certs():
            assert "positivity" in c.lean()
    return ValidationReport.from_asserts([("interlacing_discriminates", discriminates)])


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
    print(f"Interlacing: {res.n_theorems} interlacing certificates "
          f"(incl. matching-polynomial pair), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
