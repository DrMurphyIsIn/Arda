"""Legs certificates: certify -> validate -> emit -> freeze.  --check = drift."""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from family import family, profile, spelling, validation  # noqa: E402

from telperion import ExactFactEmitter, certify, diff_frozen, emit, freeze  # noqa: E402

HERE = Path(__file__).resolve().parent


def build():
    return emit(
        certify(family()),
        profile(),
        [ExactFactEmitter(spelling=spelling, tactic="norm_num", type_ascription="ℚ")],
        validation(),
        file_name="LegsCerts.lean",
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        if not rep.ok:
            print("DRIFT:", *rep.details, sep="\n  ")
        print("check:", "OK" if rep.ok else "FAILED")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"LegsCerts: {res.n_theorems} kernel facts, hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
