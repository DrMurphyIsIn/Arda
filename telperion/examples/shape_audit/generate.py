"""Statement-SHAPE audit certificates (kind ``bounded_hypothesis_collapse``).

Audits the registry shape

    exists C >= 0, forall T >= T0, P T -> -(C * log T / T^k) <= W

-- a decaying error, a height-indexed hypothesis family P (the certified zero
ladder), and a T-INDEPENDENT conclusion W.  The emitted theorem is the COLLAPSE
WITNESS: the explicit constant ``max 0 (-W) * B^k / log T0`` closes the shape for
every W, every P and every finite height B above which P fails, so the shape
carries none of its intended content.  Dogfooded by the MIRRORMERE D3 authoring
pass (node MM_weil_form_certified_height): the first instance below is exactly
the shape proposed for that node, and the emitted witness is why the registered
statement hoists its summability and tail conjuncts OUT of the ladder implication.

Instances: (T0 = 2, k = 1) -- the D3 headline shape; (T0 = 2, k = 3) -- the same
shape at the sharper tail exponent, to show the collapse is not an artifact of
the weak exponent.

NEGATIVE CONTROLS (all refused at certify time): no decay (k = 0); a degenerate
base (T0 = 1, log T0 = 0); an empty hypothesis range (B < T0 -- vacuity, a
different defect); a benign conclusion (W >= 0, which collapses by C := 0).

This refutes a SENTENCE, never a theorem.  conjecture1_proved = False.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (BoundedHypothesisCollapseEmitter, CertificationError, GridSpec,
    LeanProfile, ValidationReport, bounded_hypothesis_collapse_certificate,
    bounded_hypothesis_collapse_family, certify, diff_frozen, emit, freeze)

HERE = Path(__file__).resolve().parent

# (lean_name, T0, k, adversarial (W, B, T) samples)
CASES = {
    1: ("headline_alone_is_trivial", 2, 1,
        [(-3, 100, 50), (-1, 10, 2), (sp.Rational(-1, 7), 640000, 100)]),
    3: ("headline_alone_is_trivial_cubed", 2, 3,
        [(-3, 100, 50), (sp.Rational(-1, 7), 640000, 100)]),
}


def _family():
    return bounded_hypothesis_collapse_family(
        "ShapeAudit", GridSpec([("k", [1, 3])]),
        lambda pt: CASES[pt["k"]][0],
        lambda pt: (CASES[pt["k"]][1], CASES[pt["k"]][2], CASES[pt["k"]][3]))


def build():
    return emit(certify(_family()), LeanProfile(namespace=("Telperion", "ShapeAudit")),
        [BoundedHypothesisCollapseEmitter()], _validation(), file_name="ShapeAudit.lean")


def _refuses(*args, **kw):
    try:
        bounded_hypothesis_collapse_certificate(*args, **kw)
    except ValueError:
        return
    raise AssertionError(f"not refused: {args}")


def _validation():
    return ValidationReport.from_asserts([
        ("no_decay_refused", lambda: _refuses(2, 0, [(-1, 10, 2)])),
        ("degenerate_base_refused", lambda: _refuses(1, 1, [(-1, 10, 2)])),
        ("empty_hypothesis_range_refused", lambda: _refuses(2, 1, [(-1, 1, 1)])),
        ("benign_conclusion_refused", lambda: _refuses(2, 1, [(1, 10, 2)])),
        ("probe_outside_range_refused", lambda: _refuses(2, 1, [(-1, 10, 50)])),
        ("no_samples_refused", lambda: _refuses(2, 1, [])),
    ])


def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"ShapeAudit: {res.n_theorems} collapse witnesses, hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
