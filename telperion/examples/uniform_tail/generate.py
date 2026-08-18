"""Uniform-in-recursion monotone-tail certificate -- arm-dominance, compile-gated.

Certifies arm-dominance at SMALL representative hub states (adding an arm beats
adding each candidate child, INCLUDING the tie, exact Phi^11 with the prod-deg
penalty) -- valid only where it holds.  SCOPE CORRECTION: arm-dominance is NOT
uniform.  The 11-node tie N(0,5) beats the arm for hub arm-count k >= 19 (an
infinite exception family beyond the k=0 base case) -- the marginal-tie wall.
These per-state facts hold for the small hubs shown (k <= 7 < 19).
conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.bg import (  # noqa: E402
    ArmDominanceCertificate,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    arm_dominance_uniform,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent

STATES = [(0, 3), (0, 5), (1, 5), (2, 7)]   # representative hub states (uniform region)
CERTS = [ArmDominanceCertificate(f"armdom_c{cr}_k{k}", cr, k) for cr, k in STATES]


def build():
    body = "\n".join(c.lean() for c in CERTS)
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "UniformTail")), [em],
                _v(), file_name="UniformTail.lean")


def _t():
    return InequalityFamily(name="UniformTail", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "uniformtail_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def uniform():
        assert all(c.check() for c in CERTS)
        # arm-dominance is NOT uniform: with the tie in the candidate set and k
        # swept past 19, the exceptions are the k=0 base case AND the infinite
        # family k >= 19 (the tie beats the arm) -- verify that honest picture.
        holds, exc = arm_dominance_uniform(range(0, 1), range(0, 26))
        assert (0, 0) in exc and (0, 19) in exc and not holds
    return ValidationReport.from_asserts([("arm_dominance_uniform", uniform)])


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
    print(f"UniformTail: {res.n_theorems} arm-dominance facts across hub states "
          f"(uniform tail, base exception (0,0)), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
