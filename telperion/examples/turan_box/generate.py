"""Generate the TuranBox example (#5): log-concavity a1^2 >= a0*a2 over a box.

    python examples/turan_box/generate.py           # write lean/TuranBox.lean
    python examples/turan_box/generate.py --check    # drift check (no write)

This example certifies the 3-term log-concavity condition `a1^2 - a0*a2 >= 0`
for a log-concave triple (a0=1, a1=2, a2=1) using a thin delegation to the
box_robust (#2) infrastructure.  The emitted theorem is:

    theorem turan_triple_1_2_1 : forall a0 a1 a2 : R,
        1 <= a0 -> a0 <= 1 ->
        2 <= a1 -> a1 <= 2 ->
        1 <= a2 -> a2 <= 1 ->
        (0:R) <= a1 ^ 2 - a0 * a2

discharged by `nlinarith` seeded with the box's `sq_nonneg` and corner
`mul_nonneg` facts.

The certified margin is `a1^2 - a0*a2 = 4 - 1 = 3` (exact rational lower bound
via `box_min_lower_bound` over the point boxes [1,1] x [2,2] x [1,1]).

conjecture1_proved = False.
"""
import argparse
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_box_robust import BoxRobustEmitter  # noqa: E402
from telperion.emit_turan_box import turan_box_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_OUT = Path(__file__).resolve().parent / "lean" / "TuranBox.lean"


def _spec(pt):
    # a0=1, a1=2, a2=1: a1^2 - a0*a2 = 4 - 1 = 3 > 0 (log-concave).
    return (F(1), F(1)), (F(2), F(2)), (F(1), F(1))


def build() -> str:
    fam = turan_box_family(
        "TuranBox",
        (),
        GridSpec([("case", [0])]),
        lambda pt: "turan_triple_1_2_1",
        spec=_spec,
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("TuranBox",)),
        [BoxRobustEmitter()],
        ValidationReport(checks=(("box_robust", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: TuranBox.lean does not match regeneration")
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
