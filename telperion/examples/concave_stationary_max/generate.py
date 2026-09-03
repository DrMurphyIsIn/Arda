"""Generate the concave-stationary-max example: certify -> emit -> write.

    python examples/concave_stationary_max/generate.py           # write lean/ConcaveStationaryMax.lean
    python examples/concave_stationary_max/generate.py --check    # drift check (no write)

Kelly-fraction optimality (Arda trading, src/arda/risk/risk_bounds.py:64): the
log-growth objective g(f) = wr·ln(1+f·b) + (1-wr)·ln(1-f) on f in (0,1) has its
unique maximizer at the Kelly fraction f* = (wr·b - (1-wr))/b.  This emitter
ships the two LOAD-BEARING certified facts underlying that optimality:
  - the first-order condition  g'(f*) = 0  (a rational identity, norm_num), and
  - strict concavity  -g''(f) > 0 on (0,1)  (positive SOS-over-denominators,
    positivity),
from which the unique-max conclusion g(f) < g(f*) (f != f*) follows classically.

Instances:
  - csm_kelly_wr55_b2:  wr=0.55, b=2   => f* = 13/40 = 0.325
  - csm_kelly_wr60_b15: wr=0.6,  b=3/2 => f* = 1/3

The `concave_stationary_max` kind is registered in telperion/certify.py.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_concave_stationary_max import (  # noqa: E402
    ConcaveStationaryMaxEmitter,
    concave_stationary_max_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


# spec: pt -> {"wr": ..., "b": ...}  (fstar defaults to the Kelly fraction)
_SPECS = {
    0: {"wr": (55, 100), "b": 2},
    1: {"wr": (6, 10), "b": (3, 2)},
}
_NAMES = {0: "csm_kelly_wr55_b2", 1: "csm_kelly_wr60_b15"}
_OUT = Path(__file__).resolve().parent / "lean" / "ConcaveStationaryMax.lean"


def _rat(x):
    import sympy as sp

    if isinstance(x, (tuple, list)):
        return sp.Rational(x[0], x[1])
    return sp.nsimplify(x)


def build() -> str:
    fam = concave_stationary_max_family(
        "ConcaveStationaryMax",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: {
            "wr": _rat(_SPECS[pt["case"]]["wr"]),
            "b": _rat(_SPECS[pt["case"]]["b"]),
        },
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ConcaveStationaryMax",)),
        [ConcaveStationaryMaxEmitter()],
        ValidationReport(checks=(("concave_stationary_max", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: ConcaveStationaryMax.lean does not match regeneration")
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
