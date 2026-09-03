"""Generate the symmetric-quad example: certify -> emit -> write.

    python examples/symmetric_quad/generate.py           # write lean/SymmetricQuad.lean
    python examples/symmetric_quad/generate.py --check    # drift check (no write)

The SYMBOLIC-IN-n level-1 moment-matrix PSD certificate — the marquee P=NP
unblocker.  A degree-1 subset-indexed moment form

    Φ = f0·A² + 2·f1·A·X + f2·X² + (f1 − f2)·Q   (A=x_∅, X=Σxᵢ, Q=Σxᵢ²)

is PSD for EVERY population size n at once, proved by the exact
completing-the-square / Cauchy–Schwarz congruence

    Φ = f0·(A + (f1/f0)·X)² + cCS·(N·Q − X²),   cCS = (f1 − f2)/N,

modeled line-for-line on the PROVEN `examples/g1_floors/lean/Hsq.lean`
`subsetForm_d1`.  One certificate covers all n symbolically.

Two instances:
  - knapsack: the knapsack harmonic moments f0=1, f1=1/2, f2=(N−2)/(4(N−1))
              (exactly the Hsq.lean subsetForm_d1 object).
  - scaled:   a second valid harmonic triple f0=2, f1=1, f2=(N−2)/(2N−2)
              (rank-collapse-consistent), showing the certificate is not
              hard-wired to a single moment table.

NOTE: the `symmetric_quad` kind is not yet registered in certify._SPECIAL_KINDS /
_SPECIAL_DISPATCH (that is a REPORTED shared-file edit).  This script uses the
emitter/family directly, so the real certify()->emit() path exercises the
emitter exactly as it will once the one-line registration lands; no runtime
monkeypatch is performed (the maintainer registers the kind).
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_symmetric_quad import (  # noqa: E402
    SymmetricQuadFormEmitter,
    _N,
    symmetric_quad_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

N = _N

# spec: pt -> {"f0": …, "f1": …, "f2": …, "n_min": int} in the free symbol N.
_SPECS = {
    0: {
        "f0": sp.Integer(1),
        "f1": sp.Rational(1, 2),
        "f2": (N - 2) / (4 * (N - 1)),
        "n_min": 3,
    },
    1: {
        "f0": sp.Integer(2),
        "f1": sp.Integer(1),
        "f2": (N - 2) / (2 * N - 2),
        "n_min": 3,
    },
}
_NAMES = {0: "sq_moment_d1_knapsack", 1: "sq_moment_d1_scaled"}
_OUT = Path(__file__).resolve().parent / "lean" / "SymmetricQuad.lean"


def build() -> str:
    fam = symmetric_quad_family(
        "SymmetricQuad",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("SymmetricQuad",)),
        [SymmetricQuadFormEmitter()],
        ValidationReport(checks=(("symmetric_quad", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: SymmetricQuad.lean does not match regeneration")
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
