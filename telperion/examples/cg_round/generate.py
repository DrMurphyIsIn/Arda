"""Chvatal-Gomory integer-rounding certificates (VIPR-style), compile-gated.

Proves a linear goal over INTEGER variables from a derivation of two rules:
`lincomb` (a nonnegative rational combination of prior facts) and `cg_round`
(from an integer-coefficient fact `Sigma c_j x_j >= v`, since the integer LHS is
an integer, derive `Sigma c_j x_j >= ceil(v)` -- a Chvatal-Gomory cut).  `omega`
discharges the linear-integer chain in the emitted Lean.

Demonstrations:
  * `3x >= 2 ==> x >= 1` over the integers (scale by 1/3 then round `2/3` up to
    `1`) -- FALSE over the reals (x = 2/3), so the rounding is load-bearing;
  * `x >= 1, y >= 1 ==> x + y >= 2` (a plain nonnegative combination, no round).

NEGATIVE CONTROLS (in validation): a non-integer rounding coefficient, a vacuous
round (bound already integer), a negative lincomb multiplier, an undominated
goal, and a non-load-bearing (rounding-insensitive) certificate are all refused
at certification.

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
    CertificationError, CGRoundEmitter, GridSpec, LeanProfile,
    ValidationReport, certify, cg_round_family, diff_frozen, emit, freeze,
)

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

# pt index -> (lean_name, facts, deriv, goal)
CASES = {
    0: ("cg_cut_3x_ge_2",
        [({"x": 3}, Fr(2))],
        [{"rule": "lincomb", "combo": {0: Fr(1, 3)}, "const": Fr(0)},  # x >= 2/3
         {"rule": "cg_round", "src": 1}],                              # x >= 1
        ({"x": 1}, Fr(1))),
    1: ("cg_sum_xy_ge_2",
        [({"x": 1}, Fr(1)), ({"y": 1}, Fr(1))],
        [{"rule": "lincomb", "combo": {0: Fr(1), 1: Fr(1)}, "const": Fr(0)}],
        ({"x": 1, "y": 1}, Fr(2))),
}


def _family():
    return cg_round_family(
        "CGRound", (x, y), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))


def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "CGRound")),
                [CGRoundEmitter()], _validation(), file_name="CGRound.lean")


def _validation() -> ValidationReport:
    def refuses(label, spec):
        bad = cg_round_family("Bad", (x, y), GridSpec([("i", [0])]),
                              lambda pt: "bad", spec)
        try:
            certify(bad)
            raise AssertionError(f"{label}: bad certificate was NOT refused")
        except CertificationError:
            pass

    return ValidationReport.from_asserts([
        # non-integer rounding coefficient
        ("cg_refuses_noninteger_round", lambda: refuses(
            "noninteger_round",
            lambda pt: ([({"x": Fr(1, 2)}, Fr(1, 4))],
                        [{"rule": "cg_round", "src": 0}],
                        ({"x": Fr(1, 2)}, Fr(1, 2))))),
        # vacuous round (bound already integer)
        ("cg_refuses_vacuous_round", lambda: refuses(
            "vacuous_round",
            lambda pt: ([({"x": 1}, Fr(2))],
                        [{"rule": "cg_round", "src": 0}],
                        ({"x": 1}, Fr(2))))),
        # negative lincomb multiplier
        ("cg_refuses_negative_multiplier", lambda: refuses(
            "negative_multiplier",
            lambda pt: ([({"x": 1}, Fr(1)), ({"y": 1}, Fr(1))],
                        [{"rule": "lincomb", "combo": {0: Fr(1), 1: Fr(-1)},
                          "const": Fr(0)}],
                        ({"x": 1, "y": -1}, Fr(0))))),
        # goal not dominated
        ("cg_refuses_undominated_goal", lambda: refuses(
            "undominated_goal",
            lambda pt: ([({"x": 3}, Fr(2))],
                        [{"rule": "lincomb", "combo": {0: Fr(1, 3)},
                          "const": Fr(0)},
                         {"rule": "cg_round", "src": 1}],
                        ({"x": 1}, Fr(2))))),
        # rounding not load-bearing (sensitivity gate)
        ("cg_refuses_insensitive_cert", lambda: refuses(
            "insensitive_cert",
            lambda pt: ([({"x": 3}, Fr(2))],
                        [{"rule": "lincomb", "combo": {0: Fr(1, 3)},
                          "const": Fr(0)},
                         {"rule": "cg_round", "src": 1}],
                        ({"x": 1}, Fr(2, 3))))),
    ])


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
    print(f"CGRound: {res.n_theorems} integer-rounding certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
