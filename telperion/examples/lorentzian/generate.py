"""Lorentzian / Hodge-Riemann certificates, compile-gated.

Certifies the NON-SEPARABLE Hodge-index inequality (reverse Cauchy-Schwarz) of a
Lorentzian form -- the one crux handle that sees mixed second derivatives across
different children (the N(11,11) collectivity that every scalar/separable tool
missed).  Demonstrated on the elementary symmetric polynomial e_2 (the canonical
Lorentzian polynomial, a matching-type generating polynomial) in 3 and 4
variables; the Heilmann-Lieb matching polynomial is Lorentzian by the same
Branden-Huh route.

HONEST SCOPE: certifies the Hodge-index inequality of a given Lorentzian form.
The crux needs this MARRIED to integrality (exact at the tie) -- an arithmetic
Hodge-Riemann relation no framework yet supplies.  This builds the untested
handle; it is not a proof.  conjecture1_proved = False.

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
from telperion.lorentzian import (  # noqa: E402
    HodgeRiemannCertificate,
    hessian,
    is_lorentzian_form,
)

HERE = Path(__file__).resolve().parent


def _e2(n):
    xs = sp.symbols(f"x1:{n+1}")
    e2 = sum(xs[i] * xs[j] for i in range(n) for j in range(i + 1, n))
    return e2, xs


def certs():
    out = []
    for n in (3, 4):
        e2, xs = _e2(n)
        ws = sp.symbols(f"w1:{n+1}")
        out.append(HodgeRiemannCertificate(f"hodge_riemann_e2_n{n}", e2, xs,
                                           tuple([1] * n), ws))
    return out


def build():
    body = "\n".join(c.lean() for c in certs())
    emitter = CustomAssemblyEmitter(
        statement_template="«thms»«branches»",
        branch_template="",
        fills=lambda fam: {"thms": body},
        branch_fills=lambda inst: {},
        theorems=len(certs()),
    )
    return emit(certify(_trivial()), LeanProfile(namespace=("G1", "Lorentzian")),
                [emitter], _validation(), file_name="Lorentzian.lean")


def _trivial() -> InequalityFamily:
    return InequalityFamily(
        name="Lorentzian", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "lorentzian_root", target=lambda pt: sp.Integer(0))


def _validation() -> ValidationReport:
    def hodge_index():
        for n in (3, 4):
            e2, xs = _e2(n)
            H = hessian(e2, list(xs))
            assert is_lorentzian_form(H), n          # signature (1, n-1)
        for c in certs():
            assert c.check()                          # timelike v + Lorentzian
            assert "positivity" in c.lean()
    return ValidationReport.from_asserts([("hodge_index_signature", hodge_index)])


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
    print(f"Lorentzian: {res.n_theorems} Hodge-Riemann certificates (non-separable), "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
