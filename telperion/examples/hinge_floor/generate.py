"""Generate the hinge-floor example: the BG G1 L2 profile→equal-children reduction.

    python examples/hinge_floor/generate.py           # write lean/HingeFloor.lean
    python examples/hinge_floor/generate.py --check    # drift check (no write)

Σ(yᵢ−t0)₊ ≥ (Σyᵢ − k·t0)₊ (posPart subadditivity) = the Jensen "min at equal
children" step for the convex hinge φ=c·(y−t0)₊ — L2's missing half, general in
the hinge constants (c t0 binders).
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.hinge import hinge_floor_module  # noqa: E402

ARITIES = [2, 3, 4, 5]  # child counts the class floors range over
_OUT = Path(__file__).resolve().parent / "lean" / "HingeFloor.lean"


def build() -> str:
    return hinge_floor_module(ARITIES, namespace="HingeFloor")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    text = build()
    if args.check:
        cur = _OUT.read_text(encoding="utf-8") if _OUT.exists() else ""
        if cur != text:
            print("DRIFT: HingeFloor.lean does not match generator output")
            return 1
        print(f"check: OK ({len(ARITIES)} arities, byte-identical)")
        return 0
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(ARITIES)} arities)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
