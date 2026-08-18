"""phi_arm-gauge dimensional lift certificate (general d), compile-gated.

Lifts the near-star crossing to Z^d in the VALUE gauge: Phi^11(n) = (prod_i phi_i^n_i) * a11 *
(1+zS)^11, the Moebius factor a ratio of 11th powers of linear forms.  Demonstrated on a genuine
3-D type set — arm + arm2 + tie — where the two CHARGE directions (phi<1) close by base box +
geometric tail, and the single NEUTRAL tie-direction (phi=1) is the residual 23-adic crux.  The
lift proves the dimensional obstruction is confined to value-neutral children.  conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.bg import (  # noqa: E402
    ARM,
    ARM2,
    GridSpec,
    GaugeLiftCertificate,
    InequalityFamily,
    LeanProfile,
    TIE,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
    per_step_multiplier_limit,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402
from telperion.bg.gauge_lift import curvature_diff_tower  # noqa: E402

HERE = Path(__file__).resolve().parent

# 3-D type set: two charge axes (arm, arm2) + one neutral axis (tie).  Modest box keeps Lean small.
# ORDER 2: the neutral (tie) direction's unimodality is discharged by the curvature-stripping tail
# (kinematic tower q -> 8s+15 -> 8 -> 0), leaving ONLY the integer resonance identity as residual.
CERT = GaugeLiftCertificate("gauge_lift_3d", (ARM, ARM2, TIE), box=(6, 3, 2), cr=0, order=2)


def build():
    body = CERT.lean()
    n = body.count("theorem ")
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {}, theorems=n)
    return emit(certify(_t()), LeanProfile(namespace=("G1", "GaugeLift")), [em],
                _v(), file_name="GaugeLift.lean")


def _t():
    return InequalityFamily(name="GaugeLift", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "gaugelift_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def lifts():
        assert CERT.check()                                   # base box + charge tails + curvature tail
        # exactly two charge axes close; order-2 reduces the neutral residual to one integer identity
        assert [CERT.types[i].name for i in CERT.charge_dirs()] == ["arm", "arm2"]
        assert CERT.residual() == ["integer-identity:64*243*23=621*576"]
        # the per-step multiplier limits ARE the charges: <1 for charge, =1 for neutral
        assert per_step_multiplier_limit(ARM) < 1 and per_step_multiplier_limit(ARM2) < 1
        assert per_step_multiplier_limit(TIE) == 1

    def curvature_tower():
        # the kinematic tower of the curvature quadratic TERMINATES at jerk = 0 (q is quadratic),
        # so finitely many gauge orders pin the whole near-star sequence incl. the resonance R(5)=1.
        q, dq, d2q, d3q = curvature_diff_tower()
        assert str(dq) == "8*s + 15" and d2q == 8 and d3q == 0
        assert CERT.curvature_tail_holds() and CERT.tie_resonance_identity()

    def gauge_identity():
        # Phi^11 = charge-monomial * Moebius-L exactly on a sweep
        import itertools
        for n in itertools.product(range(0, 4), repeat=3):
            assert CERT.phi11(n) == CERT._charge(n) * CERT._mobius(n)
            # bound <=> L <= budget
            assert (CERT.phi11(n) <= 1) == (CERT._mobius(n) <= CERT.budget(n))

    return ValidationReport.from_asserts(
        [("dimensional_lift_gauge", lifts), ("gauge_identity_and_budget", gauge_identity),
         ("curvature_tower_terminates", curvature_tower)])


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
    print(f"GaugeLift: {res.n_theorems} facts (3-D gauge lift; 2 charge axes close, "
          f"tie residual), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
