"""Equational-consequence certificates, compile-gated.

Proves `lhs = rhs` follows from polynomial equation hypotheses `{a_i = b_i}` via
cofactors of `lhs − rhs` modulo the hypothesis differences (Gröbner-computed).

Demonstrations: `x = y ⟹ x³ = y³`; `x = 1, y = 1 ⟹ x² + y² = 2`.
NEGATIVE CONTROL: `x = y ⟹ x² = 2y` is not a consequence -> refused.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, ConsequenceEmitter, GridSpec, LeanProfile,
    ValidationReport, certify, consequence_family, diff_frozen, emit, freeze)
HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")
CASES = {0: ("consequence_cubes", x**3, y**3, [(x, y, "h")]),
         1: ("consequence_sum_of_squares", x**2 + y**2, sp.Integer(2),
             [(x, sp.Integer(1), "hx"), (y, sp.Integer(1), "hy")])}
def _family():
    return consequence_family("Consequence", (x, y), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "Consequence")),
        [ConsequenceEmitter()], _validation(), file_name="Consequence.lean")
def _validation():
    def d():
        bad = consequence_family("Bad", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (x**2, 2*y, [(x, y, "h")]))
        try: certify(bad); raise AssertionError("non-consequence not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([("consequence_discriminates", d)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"Consequence: {res.n_theorems} certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
