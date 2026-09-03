"""Generate the achievability-closure example: certify -> emit -> write.

    python examples/achievability/generate.py           # write lean/Achievability.lean
    python examples/achievability/generate.py --check    # drift check (no write)

Replace a relaxed inequality ``Q(x) ≥ 0`` — FALSE on its relaxed domain ``[l, d]``
— by its restriction to the ACHIEVABLE subset ``[l, b] ⊂ [l, d]`` where it holds.
Models ``proof/formalization/R3Cert/CappedJointAchievable.lean`` (PR #20): the
cavity message ``μ = 1/(j+1+S)`` (``j ≥ 1, S ≥ 0``) is never in the ``(1/2, 1)``
band, so the g-step factor — false there — is discharged on ``μ ≤ 1/2``.

Two instances:
  - cavity_half:    the μ ≤ 1/2 characterization itself, Q(x) = 1 - 2x on [0, 1/2]
                    (= 0 at 1/2, < 0 on (1/2, 1]); with the 1/(j+1+S) ≤ 1/2
                    achievability derivation helper.
  - quadratic_half: Q(x) = (1-x)(1-2x) = 1 - 3x + 2x^2 on [0, 1/2] (< 0 on
                    (1/2, 1), e.g. Q(3/4) = -1/8) — a genuinely quadratic
                    restricted-true inequality.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_achievability import (  # noqa: E402
    AchievabilityClosureEmitter,
    achievability_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
import sympy as sp  # noqa: E402

_HALF = sp.Rational(1, 2)

# The `achievability` kind is not yet registered in certify._SPECIAL_KINDS /
# _SPECIAL_DISPATCH (that is a REPORTED shared-file edit).  Until it lands, register
# the dispatch locally at runtime so the real certify()->emit() path exercises the
# emitter exactly as it would once the two one-line registrations are in place.



# spec: pt -> {"coeffs": ascending, "l":, "b":, "d":, "derivation": bool}
_SPECS = {
    0: {"coeffs": (1, -2), "l": 0, "b": _HALF, "d": 1, "derivation": True},
    1: {"coeffs": (1, -3, 2), "l": 0, "b": _HALF, "d": 1, "derivation": False},
}
_NAMES = {0: "ach_cavity_half", 1: "ach_quadratic_half"}
_OUT = Path(__file__).resolve().parent / "lean" / "Achievability.lean"


def build() -> str:
    fam = achievability_family(
        "Achievability",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: {
            "coeffs": _SPECS[pt["case"]]["coeffs"],
            "l": _SPECS[pt["case"]]["l"],
            "b": _SPECS[pt["case"]]["b"],
            "d": _SPECS[pt["case"]]["d"],
            "derivation": _SPECS[pt["case"]]["derivation"],
        },
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("Achievability",)),
        [AchievabilityClosureEmitter()],
        ValidationReport(checks=(("achievability", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: Achievability.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
