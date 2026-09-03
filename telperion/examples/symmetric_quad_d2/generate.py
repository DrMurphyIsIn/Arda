"""Generate the d=2 symmetric-quad example: certify -> emit -> write.

    python examples/symmetric_quad_d2/generate.py           # write lean/SymmetricQuadD2.lean
    python examples/symmetric_quad_d2/generate.py --check    # drift check (no write)

The SYMBOLIC-IN-n level-2 moment-matrix PSD certificate — the d=2 sibling of
``examples/symmetric_quad`` (which ships the d=1 object ``subsetForm_d1``).  The
degree-2 subset-indexed knapsack moment form

    Q2(x; n) = Σ_{|S|,|T| ≤ 2} x_S x_T f(n, |S∪T|)   ≥ 0   (∀ n symbolically)

reduces (grouping by association-scheme orbits) to a collective-coordinate form
in ``A, s1, s2, QY, P, W, CYz`` that decomposes EXACTLY as the three-piece
completing-the-square + centered-Cauchy–Schwarz certificate of
``examples/knapsack_sos/D2_CERTIFICATE.md``:

    Q2 = (A + f1·s1 + f2·s2)²  +  pcoef·(T2 − s1²/n)  +  a·N2,

with pcoef = n/(4(n−1)) ≥ 0, a = μ₂ = n(n−2)/(16(n−3)(n−1)) > 0 (n>3).  The
completing-the-square assembly is proved symbolically in n; the two level ≥ 1
nonnegativity facts (centered CS ``s1² ≤ n·T2`` and the level-2 J(n,2) projection
positivity ``N2 ≥ 0``) are supplied as hypotheses, at the SAME altitude as the
shipped d=1 emitter's Cauchy–Schwarz hypothesis ``X² ≤ n·Q``.

One instance: the knapsack harmonic moments f(n,0..4).

NOTE: the ``symmetric_quad_d2`` kind is a REPORTED one-line registration in
certify._SPECIAL_KINDS / _SPECIAL_DISPATCH (a shared-file edit the maintainer
lands).  So the certify() dispatch table can resolve the kind, this script
applies that exact registration IN-PROCESS at import time (``_register()``
below) — it appends the same two entries the maintainer will add to the source,
nothing more; it does not alter any emitter behavior.  This lets the example
exercise the REAL certify()->emit() path end-to-end today.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_symmetric_quad_d2 import (  # noqa: E402
    SymmetricQuadD2Emitter,
    _knapsack_f,
    symmetric_quad_d2_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# The `symmetric_quad_d2` kind is registered in telperion/certify.py.

# spec: pt -> {"f0":…, …, "f4":…, "n_min": int} in the free symbol N.
_SPECS = {
    0: {
        "f0": _knapsack_f(0),
        "f1": _knapsack_f(1),
        "f2": _knapsack_f(2),
        "f3": _knapsack_f(3),
        "f4": _knapsack_f(4),
        "n_min": 4,
    },
}
_NAMES = {0: "sq_moment_d2_knapsack"}
_OUT = Path(__file__).resolve().parent / "lean" / "SymmetricQuadD2.lean"


def build() -> str:
    fam = symmetric_quad_d2_family(
        "SymmetricQuadD2",
        GridSpec([("case", [0])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("SymmetricQuadD2",)),
        [SymmetricQuadD2Emitter()],
        ValidationReport(checks=(("symmetric_quad_d2", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: SymmetricQuadD2.lean does not match regeneration")
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
