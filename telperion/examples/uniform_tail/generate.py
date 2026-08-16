"""Uniform-in-recursion monotone-tail certificate -- arm-dominance, compile-gated.

Certifies ARM-DOMINANCE at representative hub states: adding an arm beats adding
any other child (exact Phi^11, with the prod-deg penalty).  This is the
recursion-uniform monotone tail -- every non-arm direction decreases Phi more, so
the all-arm near-star is the extremizer at every hub.  Arm-dominance holds
uniformly across ALL hub states except the single base case (cr=0,k=0), so the
uniform tail has the same base+tail structure as the 1-D bridge, lifted to
hub-state space.  conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
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
        holds, exc = arm_dominance_uniform(range(0, 4), range(0, 8))
        assert exc == [(0, 0)]                    # uniform except the single base case
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
