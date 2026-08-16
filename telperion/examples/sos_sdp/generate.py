"""SDP-SOS certificates with complementary-slackness duality, compile-gated.

The LP -> SDP upgrade: certify p >= 0 by a PSD Gram matrix (off-diagonal
coupling), reaching polynomials that vanish at INTERIOR points -- the tie shapes
Polya lifting cannot handle -- and reading the equality variety off the dual
(the square bases' common zeros) FOR FREE.

Demonstrated on a polynomial with an interior tight zero at x = y = 1 (Polya/
lifting refuses these; the SDP certifies it and reports the tie automatically).
This is the certificate layer the occupancy method / "SOS for limits of trees"
runs on; aiming it at the recursive matching-functional profile so the dual lands
on the integer tie s=5 is the named research program.  conjecture1_proved=False.

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
from telperion.sos_sdp import lean_certificate, sos_sdp_certificate  # noqa: E402

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

# interior tight zero at (1,1): 3/2(x-y)^2 + 2(1-(x+y)/2)^2 -- Polya/lifting refuses
# these (vanish at an interior point); the SDP certifies + reports the tie.
P_INTERIOR = 2 * x**2 - 2 * x * y + 2 * y**2 - 2 * x - 2 * y + 2


def build():
    thms = [lean_certificate("sdp_sos_interior_tie", P_INTERIOR, [x, y])]
    body = "\n".join(t for t in thms if t)
    emitter = CustomAssemblyEmitter(
        statement_template="«thms»«branches»",
        branch_template="",
        fills=lambda fam: {"thms": body},
        branch_fills=lambda inst: {},
        theorems=len([t for t in thms if t]),
    )
    return emit(certify(_trivial()), LeanProfile(namespace=("G1", "SOSSDP")),
                [emitter], _validation(), file_name="SOSSDP.lean")


def _trivial() -> InequalityFamily:
    return InequalityFamily(
        name="SOSSDP", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "sossdp_root", target=lambda pt: sp.Integer(0))


def _validation() -> ValidationReport:
    def sdp_sos():
        cert, tight = sos_sdp_certificate(P_INTERIOR, [x, y])
        assert sp.expand(cert.as_expr() - P_INTERIOR) == 0        # exact SOS
        # complementary slackness: common zeros of the square bases = the tie
        sol = sp.solve([t for t in tight], [x, y], dict=True)
        assert {x: sp.Integer(1), y: sp.Integer(1)} in sol         # tie at (1,1)
        assert lean_certificate("t", P_INTERIOR, [x, y]) is not None
    return ValidationReport.from_asserts([("sdp_sos_with_duality", sdp_sos)])


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
    print(f"SOSSDP: {res.n_theorems} SDP-SOS certificates (interior tie + duality), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
