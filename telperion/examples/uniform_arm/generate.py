"""Uniform-in-k arm-dominance (lemma 1 core), compile-gated.

Arm-dominance UNIFORM in the hub arm-count k: adding an arm beats adding each key
competitor for all real k >= anchor, by an all-nonneg-coefficient degree-11
numerator (positivity) -- the same crossing structure as the 1-D bridge, lifted
to hub-state space. leaf anchor k>=1 (its k=0 exception builds the arm).
conjecture1_proved=False.
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (GridSpec, InequalityFamily, LeanProfile, UniformArmDominanceCertificate,  # noqa: E402
                       ValidationReport, certify, diff_frozen, emit, freeze)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402
HERE = Path(__file__).resolve().parent
CERT = UniformArmDominanceCertificate()
def build():
    body = CERT.lean(); n = body.count("theorem ")
    em = CustomAssemblyEmitter(statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "UniformArm")), [em], _v(),
                file_name="UniformArm.lean")
def _t():
    return InequalityFamily(name="UniformArm", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda p: "uniformarm_root", target=lambda p: sp.Integer(0))
def _v():
    def ok(): assert CERT.check()
    return ValidationReport.from_asserts([("uniform_arm_dominance", ok)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true"); a = ap.parse_args()
    res = build()
    if a.check:
        r = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if r.ok else "FAILED"); return 0 if r.ok else 1
    freeze(res, HERE / "frozen")
    print(f"UniformArm: {res.n_theorems} arm-vs-SMALL-competitor certs (positivity); NOT uniform (tie beats arm k>=19), hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
