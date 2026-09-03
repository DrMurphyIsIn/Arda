"""Generate the polytope-max example: certify -> emit -> write.

    python examples/polytope_max/generate.py           # write lean/PolytopeMax.lean
    python examples/polytope_max/generate.py --check    # drift check (no write)

Multi-affine (degree ≤ 1 per variable) worst-corner box-positivity — the
general-d generalization of the shipped bilinear-corner emitter ("Handelman
Route B": corner dispatch + per-edge affine slice).  A multi-affine polynomial on
an axis-aligned box attains its extremum at a corner, so 0 ≤ p at all 2^d corners
implies 0 ≤ p on the box; the certificate is the barycentric convex-combination
identity p(x) = Σ_corner λ_corner·p(corner) with λ ≥ 0.

Three instances:
  - product_unit_3:  p = (1+x)(1+y)(1+z) on [0,1]^3   (d=3, all subset coeffs 1)
  - mixed_slopes_3:  p = 4 − x − y − z + x·y·z on [0,1]^3   (d=3, genuine mix)
  - bilinear_d2:     p = 3 − x − 2y + x·y on [0,1]^2   (d=2 — recovers bilinear)

NOTE: the `polytope_max` kind is not yet registered in certify._SPECIAL_KINDS
(that is a REPORTED shared-file edit).  Until it is, this script registers the
dispatch locally at runtime so the real certify()->emit() path exercises the
emitter exactly as it would once the one-line registration lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402

# the certify SUBMODULE (not the re-exported certify() function) — its dispatch
from telperion.emit_polytope_max import (  # noqa: E402
    PolytopeMaxMonotoneEmitter,
    _all_subsets,
    polytope_max_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


# spec: pt -> (coeffs, lo, hi)  with coeffs a dict subset-of-axes -> rational.
_SPECS = {
    # (1+x)(1+y)(1+z): every multi-affine monomial coefficient is 1.
    0: ({frozenset(S): 1 for S in _all_subsets(3)}, (0, 0, 0), (1, 1, 1)),
    # 4 - x - y - z + x*y*z on [0,1]^3.
    1: (
        {
            frozenset(): 4,
            frozenset((0,)): -1,
            frozenset((1,)): -1,
            frozenset((2,)): -1,
            frozenset((0, 1, 2)): 1,
        },
        (0, 0, 0),
        (1, 1, 1),
    ),
    # 3 - x - 2y + x*y on [0,1]^2 (the bilinear mixed_slopes instance, d=2).
    2: (
        {
            frozenset(): 3,
            frozenset((0,)): -1,
            frozenset((1,)): -2,
            frozenset((0, 1)): 1,
        },
        (0, 0),
        (1, 1),
    ),
}
_NAMES = {0: "pm_product_unit_3", 1: "pm_mixed_slopes_3", 2: "pm_bilinear_d2"}
_OUT = Path(__file__).resolve().parent / "lean" / "PolytopeMax.lean"


def build() -> str:
    fam = polytope_max_family(
        "PolytopeMax",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        # d=3 nlinarith slices can be heartbeat-heavy; raise the budget.
        LeanProfile(
            namespace=("PolytopeMax",),
            options=("set_option maxHeartbeats 1000000",),
        ),
        [PolytopeMaxMonotoneEmitter()],
        ValidationReport(checks=(("polytope_max", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: PolytopeMax.lean does not match regeneration")
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
