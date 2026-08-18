"""Bridge crossing (near-star span), compile-gated.

Crosses the 1-D span of the crux bridge: certifies R(n) <= 1 for ALL integers n
even though the continuous relaxation R_cont(4.822) = 1.00046 > 1 -- a certificate
valid on Z but false on R, tight at the integer tie s=5.

Mechanism (integer-Positivstellensatz via finite base + monotone tail):
  (1) finite integer base cases n = 0..5 (exact, norm_num);
  (2) monotone tail: rho(t)=R(t+1)/R(t) <= 1 for real t >= 5, cleared to
      P(5+u) >= 0 with ALL NONNEGATIVE COEFFICIENTS (Polya-trivial, positivity);
  base + anchor R(5)=1 + tail-monotonicity => R(n) <= 1 for all n in Z.

This is the design that crosses the bridge; the multivariate general span needs a
finite recursive profile (open -- no finite basis). conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.bg import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LeanProfile,
    NearStarBridgeCertificate,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
    near_star_R,
    near_star_tail_poly,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent


def build():
    cert = NearStarBridgeCertificate(anchor=5)
    body = cert.lean()
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "Bridge")), [em],
                _v(), file_name="Bridge.lean")


def _t():
    return InequalityFamily(name="Bridge", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "bridge_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def crosses():
        c = NearStarBridgeCertificate(anchor=5)
        assert c.check()                                   # base + tail verify
        assert near_star_R(5) == 1                          # the tie
        _, nonneg = near_star_tail_poly(5)
        assert nonneg                                       # tail all-nonneg-coeffs
        # continuous relaxation DOES exceed 1 (so the certificate is genuinely
        # integer-only, not a smooth bound)
        rc = lambda s: (64 / 621) ** (2 * s + 1) * 1.5 ** (11 * s) * ((4 * s + 3) / (3 * (s + 1))) ** 11
        assert max(rc(4 + i / 100) for i in range(200)) > 1
    return ValidationReport.from_asserts([("bridge_crosses_nearstar", crosses)])


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
    print(f"Bridge: {res.n_theorems} theorems (near-star span CROSSED: base + "
          f"monotone tail), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
