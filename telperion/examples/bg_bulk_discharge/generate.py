"""BG bulk-discharge full-edge atoms — Handelman box-positivity, compile-gated (warm-up).

The classical-BG upper bound reduces to a pointwise discharge `phi_v <= F* = log(621/64)/11` on the cavity-field
box (`docs/BG_STAR_OF_BROOMS_RESULT.md` Sec 5b, `docs/BG_23ADIC_RECONCILIATION_20260831.md`).  This example
kernel-gates the FULL-EDGE atom of that inequality (the loosest discharge, `tau = 1`: the vertex absorbs every
incident edge term).  For a degree-`m+1` hub carrying `c`-cherry brooms, exponentiating and clearing the
transcendental `F*` (at the optimum `c = 5`, `1 + 2c = 11` makes `total(5)^11 = 621/64` RATIONAL — the 11th root
cancels) leaves the rational box-positivity statement

    0 <= P_c(h1, h2) := numerator[ (1 + h1 hv1)(1 + h2 hv2) - a_c (1 + z(h1+h2)) ]   on [0,1]^2,

with `z = 3/(3d+c)`, `hv_i = z/(1 + z h_j)`, `a_c = total(c)/(621/64)` (`total(c) = (3/2)^c (1 + c/(3d))`).  The
`621 = 27*23` tie constant is manifest in `a_c` (its denominator carries the factor `23`); `c = 5` is the tight
optimum.  Each `P_c >= 0` is certified by an explicit **Handelman** certificate — a nonnegative combination of
products of the box constraints `{h1, 1-h1, h2, 1-h2}` (the Bernstein degree-3 basis) — verified `P = Sum`
exactly with all coefficients `>= 0`, and refused otherwise (negative control in validation).

This is the ATOM (free-field, `tau = 1`, has slack), NOT the open core: the universal tight discharge `tau`
making `phi_v <= F*` everywhere remains open (naive rules are spoofed by the acyclicity/surface barrier).  The
same Handelman engine certifies RH's zero-free `(1+x)^n` witness -- one box-positivity cone, cf.
`probe/bg-handelman-shared-engine`.  conjecture1_proved = False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp
from sympy import Rational as R, binomial as Cbin

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, HandelmanEmitter, LeanProfile,
    ValidationReport, certify, diff_frozen, emit, freeze, handelman_family,
)

HERE = Path(__file__).resolve().parent
h1, h2 = sp.symbols("h1 h2")
_M = 2  # two-hub spine context (matches the domination-bridge convention)


def _atom(c: int):
    """Return `(P, a)` — the exact full-edge atom polynomial `P_c(h1,h2) >= 0` on `[0,1]^2` and `a_c`."""
    d = _M + c
    z = R(3, 3 * d + c)
    a = R(3, 2) ** c * (1 + R(c, 3 * d)) / R(621, 64)
    Rv = 1 + z * (h1 + h2)
    hv1, hv2 = z / (1 + z * h2), z / (1 + z * h1)
    num = sp.fraction(sp.together((1 + h1 * hv1) * (1 + h2 * hv2) - a * Rv))[0]
    return sp.Poly(sp.expand(num), h1, h2), a


def _handelman_terms(P):
    """Explicit degree-3 Bernstein -> Handelman terms `(coef, exps)` over `[h1, 1-h1, h2, 1-h2]`
    (`coef * h1^i (1-h1)^{3-i} h2^j (1-h2)^{3-j}`), coefficients exact and nonnegative when `P` is box-positive."""
    amat = {(k, l): P.coeff_monomial(h1 ** k * h2 ** l) for k in range(4) for l in range(4)}
    terms = []
    for i in range(4):
        for j in range(4):
            bij = sum(R(Cbin(i, k) * Cbin(j, l), Cbin(3, k) * Cbin(3, l)) * amat.get((k, l), 0)
                      for k in range(min(i, 3) + 1) for l in range(min(j, 3) + 1))
            coef = Cbin(3, i) * Cbin(3, j) * bij
            if coef != 0:
                terms.append((coef, (i, 3 - i, j, 3 - j)))
    return terms


# certified full-edge atoms: c = 5 (the tight optimum) and c = 4 (neighbour); both deg-3 Handelman.
_CS = (4, 5)
_CASES = {}
for _k, _c in enumerate(_CS):
    _P, _a = _atom(_c)
    _CASES[_k] = (f"bg_bulk_fulledge_c{_c}", _P.as_expr(),
                  [(h1, "hx0"), (1 - h1, "hx1"), (h2, "hy0"), (1 - h2, "hy1")],
                  _handelman_terms(_P))


def _family():
    return handelman_family(
        "BGBulkDischarge", (h1, h2), GridSpec([("i", list(range(len(_CS))))]),
        lambda pt: _CASES[pt["i"]][0],
        lambda pt: (_CASES[pt["i"]][1], _CASES[pt["i"]][2], _CASES[pt["i"]][3]),
        max_deg=3)


def build():
    return emit(certify(_family()), LeanProfile(namespace=("BG", "BulkDischarge")),
                [HandelmanEmitter()], _validation(), file_name="BGBulkDischarge.lean")


def _validation() -> ValidationReport:
    def discriminates():
        bad = handelman_family(
            "Bad", (h1,), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (1 - h1 ** 2, [(1 - h1, "h1")], [(1, (1,))]))  # (1-h1) != 1-h1^2
        try:
            certify(bad)
            raise AssertionError("bad Handelman certificate was NOT refused")
        except CertificationError:
            pass
    return ValidationReport.from_asserts([("bg_bulk_discharge_discriminates", discriminates)])


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
    print(f"BGBulkDischarge: {res.n_theorems} full-edge box-positivity certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
